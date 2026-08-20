import Autosubst2.Deriving

/-!
# Macro test: single-sort backends on verbatim (`.other`) payload arguments.

Regression test for the bugs that forced `Heifer/LogRel/Model/Lang.lean` to
hand-write its σ-chain: the single-sort `analyse`

* dropped EXPLICIT `Nat` payload args (mistaking them for the implicit scope
  binder), producing ill-typed patterns for `loc : Nat → Tm k`;
* hardcoded binder depth 0 for bare `Tm (k + 1)` recursive args (only the
  `Bind Tm k` marker was recognised);
* emitted empty `rw []` legs for payload-only constructors (`intt`);
* (unscoped) regenerated `.other` payloads at type `Tm.U` instead of their
  source types.

Both backends are exercised on a `Lang.lean`-shaped fragment: `var`/`lam`/`app`
plus `intt : Int`, `binop : BinOp` selector, `loc : Nat` payloads, with the
binder written as a bare `Tm (k + 1)` (no `Bind` marker).
-/

namespace Autosubst2.GenPayload

open Autosubst2

inductive BinOp where
  | add
  | mul
  | eq

inductive Tm : Nat → Type
  | var {k} : Idx k → Tm k
  | lam {k} : Tm (k + 1) → Tm k             -- bare binder, no `Bind` marker
  | app {k} : Tm k → Tm k → Tm k
  | intt {k} : Int → Tm k                   -- verbatim Int payload
  | binop {k} : BinOp → Tm k → Tm k → Tm k  -- verbatim BinOp selector
  | loc {k} : Nat → Tm k                    -- verbatim (explicit) Nat payload

derive_autosubst% Tm

/-! ## Scoped: the full generated chain type-checks. -/
#guard_msgs (drop info) in #check (ren : (Idx 0 → Idx 1) → Tm 0 → Tm 1)
#guard_msgs (drop info) in #check (subst : (Idx 0 → Tm 1) → Tm 0 → Tm 1)
#guard_msgs (drop info) in #check @ren_ren
#guard_msgs (drop info) in #check @subst_ren
#guard_msgs (drop info) in #check @ren_subst
#guard_msgs (drop info) in #check @subst_subst
#guard_msgs (drop info) in #check @subst_id
#guard_msgs (drop info) in #check @ren_id
#guard_msgs (drop info) in #check @subst0_subst_up
#guard_msgs (drop info) in #check @subst_var
#guard_msgs (drop info) in #check @ren_var

/-- Payloads are carried verbatim through subst; the binder lifts. -/
example (sg : Idx 0 → Tm 0) (op : BinOp) (i : Int) (l : Nat) :
    subst sg (.binop op (.intt i) (.loc l)) = .binop op (.intt i) (.loc l) := rfl

/-- The bare `Tm (k + 1)` binder is recognised: `lam` lifts with `up`. -/
example (sg : Idx 0 → Tm 0) :
    subst sg (.lam (.var var_zero)) = .lam (.var var_zero) := rfl

end Autosubst2.GenPayload

namespace Autosubst2.GenPayloadU

open Autosubst2

inductive Tm : Nat → Type
  | var {k} : Idx k → Tm k
  | lam {k} : Tm (k + 1) → Tm k
  | app {k} : Tm k → Tm k → Tm k
  | intt {k} : Int → Tm k
  | binop {k} : GenPayload.BinOp → Tm k → Tm k → Tm k
  | loc {k} : Nat → Tm k

derive_autosubst% (unscoped) Tm

/-! ## Unscoped: payload ctors keep their SOURCE types in `Tm.U`. -/
#guard_msgs (drop info) in #check (Tm.U.intt : Int → Tm.U)
#guard_msgs (drop info) in #check (Tm.U.binop : GenPayload.BinOp → Tm.U → Tm.U → Tm.U)
#guard_msgs (drop info) in #check (Tm.U.loc : Nat → Tm.U)
#guard_msgs (drop info) in #check @Tm.U.ren_ren
#guard_msgs (drop info) in #check @Tm.U.subst_ren
#guard_msgs (drop info) in #check @Tm.U.ren_subst
#guard_msgs (drop info) in #check @Tm.U.subst_comp
#guard_msgs (drop info) in #check @Tm.U.subst_id
#guard_msgs (drop info) in #check @Tm.U.subst0_subst_up

example (sg : Nat → Tm.U) (op : GenPayload.BinOp) (i : Int) (l : Nat) :
    Tm.U.subst sg (.binop op (.intt i) (.loc l)) = .binop op (.intt i) (.loc l) := rfl

example (u : Tm.U) : Tm.U.subst0 (.app (.var 0) (.intt 3)) u = .app u (.intt 3) := rfl

end Autosubst2.GenPayloadU
