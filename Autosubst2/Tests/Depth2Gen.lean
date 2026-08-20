import Autosubst2.Deriving

/-!
# Macro test: binder arguments of depth 2 (single-sort backends).

Regression test for σ-chain generation on constructors whose recursive
arguments sit under TWO binders (`split : Tm (k + 2) → Tm k → Tm k`), the
shape that previously forced `Heifer/LogRel/Model/Lang.lean` to hand-write its
chain.  The family is a miniature clone of `Lang.lean`'s binder inventory:
`var`, `lam` (depth 1), `caseSum` (a depth-0 scrutinee plus two depth-1 arms),
`split` (a depth-2 arg mixed with a depth-0 arg), and a verbatim payload
(`intt : Int`).

The unscoped single-sort backend has its own (parallel) alt generator with the
same generalisation, so it is exercised on the same family below.  The
MULTI-sort backends remain depth ≤ 1: the unscoped mutual backend rejects
deeper binders explicitly, and the scoped multi-sort ops only lift once per
bound column.
-/

namespace Autosubst2.GenDepth2

open Autosubst2

inductive Tm : Nat → Type
  | var {k} : Idx k → Tm k
  | lam {k} : Tm (k + 1) → Tm k
  | app {k} : Tm k → Tm k → Tm k
  | intt {k} : Int → Tm k
  | caseSum {k} : Tm k → Tm (k + 1) → Tm (k + 1) → Tm k
  | split {k} : Tm (k + 2) → Tm k → Tm k

derive_autosubst% Tm

/-! ## The full generated chain type-checks. -/
#guard_msgs (drop info) in #check (ren : (Idx 0 → Idx 1) → Tm 0 → Tm 1)
#guard_msgs (drop info) in #check (subst : (Idx 0 → Tm 1) → Tm 0 → Tm 1)
#guard_msgs (drop info) in #check @ren_ren
#guard_msgs (drop info) in #check @subst_ren
#guard_msgs (drop info) in #check @ren_subst
#guard_msgs (drop info) in #check @subst_subst
#guard_msgs (drop info) in #check @up_ids_eq
#guard_msgs (drop info) in #check @up_ren_id
#guard_msgs (drop info) in #check @subst_id
#guard_msgs (drop info) in #check @ren_eq_subst
#guard_msgs (drop info) in #check @ren_id
#guard_msgs (drop info) in #check @subst0_subst_up
#guard_msgs (drop info) in #check @subst_var
#guard_msgs (drop info) in #check @ren_var

/-! ## Depth-2 substitution computes. -/

/-- The depth-2 arg lifts with `up (up σ)`: both bound variables survive. -/
example (sg : Idx 0 → Tm 0) :
    subst sg (.split (.app (.var var_zero) (.var (shift var_zero))) (.intt 1))
      = .split (.app (.var var_zero) (.var (shift var_zero))) (.intt 1) := rfl

/-- A free variable under two binders is substituted and shifted twice back
past both binders (payload check: the substituted value survives verbatim). -/
example :
    subst (fun _ => (.intt 5 : Tm 0))
        (Tm.split (k := 1) (.var (shift (shift var_zero))) (.var var_zero))
      = .split (.intt 5) (.intt 5) := rfl

/-! ## σ-chain lemmas fire on the depth-2 family. -/
example {n : Nat} (t : Tm n) : subst ids t = t := by rw [subst_id]
example {n : Nat} (t : Tm n) : ren id t = t := ren_id t
example {m n : Nat} (sg : Idx m → Tm n) (e : Tm (m + 1)) (u : Tm n) :
    subst0 (subst (up sg) e) u = subst (u .: sg) e := subst0_subst_up sg e u

end Autosubst2.GenDepth2

namespace Autosubst2.GenDepth2U

open Autosubst2

inductive Tm : Nat → Type
  | var {k} : Idx k → Tm k
  | lam {k} : Tm (k + 1) → Tm k
  | app {k} : Tm k → Tm k → Tm k
  | intt {k} : Int → Tm k
  | caseSum {k} : Tm k → Tm (k + 1) → Tm (k + 1) → Tm k
  | split {k} : Tm (k + 2) → Tm k → Tm k

derive_autosubst% (unscoped) Tm

/-! ## Unscoped chain type-checks on the depth-2 family. -/
#guard_msgs (drop info) in #check @Tm.U.ren_ren
#guard_msgs (drop info) in #check @Tm.U.subst_ren
#guard_msgs (drop info) in #check @Tm.U.ren_subst
#guard_msgs (drop info) in #check @Tm.U.subst_comp
#guard_msgs (drop info) in #check @Tm.U.up_ids_eq
#guard_msgs (drop info) in #check @Tm.U.subst_id
#guard_msgs (drop info) in #check @Tm.U.subst0_subst_up

/-- Unscoped depth-2 substitution: indices 0 and 1 are bound by `split`, index
2 is free and substituted (shifted twice back past both binders). -/
example :
    Tm.U.subst (fun _ => .intt 5) (.split (.var 2) (.var 0))
      = .split (.intt 5) (.intt 5) := rfl

example (t : Tm.U) : Tm.U.subst Tm.U.ids t = t := by rw [Tm.U.subst_id]

end Autosubst2.GenDepth2U
