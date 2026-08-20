import Autosubst2.Deriving

/-!
# Macro test: UNSCOPED MUTUAL (shared-scope) family with payloads.

The exact combination `Indirection/Prototype/ProgramLogic.lean` needs: an
unscoped de Bruijn theory for a mutual two-sort `Expr`/`Val` family where

* variables live only in `Expr` (the first, variable-bearing sort);
* `Val.clos` embeds an `Expr` under ONE binder (foreign-under-binder);
* both sorts carry verbatim payloads (`Int`, `Loc`).

The well-scoped mutual family below is the single source of truth for binder
depths; `derive_autosubst% (unscoped) Expr Val` generates the mutual unscoped
inductives `Expr.U`/`Val.U`, `ren`/`subst` per sort over ONE shared
`Nat → Expr.U` map, and the mutual σ-chain.
-/

namespace Autosubst2.GenUnscopedMulti

open Autosubst2

abbrev Loc := Nat

mutual
/-- Well-scoped clone of the Prototype's `Expr` (variable-bearing, FIRST). -/
inductive Expr : Nat → Type
  | val {k} : Val k → Expr k
  | var {k} : Idx k → Expr k
  | app {k} : Expr k → Expr k → Expr k
  | letin {k} : Expr k → Expr (k + 1) → Expr k
  | ifz {k} : Expr k → Expr k → Expr k → Expr k
  | add {k} : Expr k → Expr k → Expr k
  | ref {k} : Expr k → Expr k
  | load {k} : Expr k → Expr k
  | store {k} : Expr k → Expr k → Expr k
  | faa {k} : Expr k → Expr k → Expr k
  | fork {k} : Expr k → Expr k

/-- Well-scoped clone of the Prototype's `Val` (var-less; payloads + a
foreign-under-binder closure body). -/
inductive Val : Nat → Type
  | int {k} : Int → Val k
  | unit {k} : Val k
  | loc {k} : Loc → Val k
  | clos {k} : Expr (k + 1) → Val k
end

derive_autosubst% (unscoped) Expr Val

/-! ## Generated ops: one shared substitute map `Nat → Expr.U`. -/
#guard_msgs (drop info) in #check (Expr.U.ren : (Nat → Nat) → Expr.U → Expr.U)
#guard_msgs (drop info) in #check (Val.U.ren : (Nat → Nat) → Val.U → Val.U)
#guard_msgs (drop info) in #check (Expr.U.subst : (Nat → Expr.U) → Expr.U → Expr.U)
#guard_msgs (drop info) in #check (Val.U.subst : (Nat → Expr.U) → Val.U → Val.U)
#guard_msgs (drop info) in #check (Expr.U.up : (Nat → Expr.U) → Nat → Expr.U)
#guard_msgs (drop info) in #check (Expr.U.ids : Nat → Expr.U)
#guard_msgs (drop info) in #check (Expr.U.subst0 : Expr.U → Expr.U → Expr.U)

/-! ## Payload ctors keep their source types. -/
#guard_msgs (drop info) in #check (Val.U.int : Int → Val.U)
#guard_msgs (drop info) in #check (Val.U.loc : Loc → Val.U)
#guard_msgs (drop info) in #check (Val.U.clos : Expr.U → Val.U)

/-! ## The full mutual σ-chain. -/
#guard_msgs (drop info) in #check @Expr.U.ren_ren
#guard_msgs (drop info) in #check @Val.U.ren_ren
#guard_msgs (drop info) in #check @Expr.U.subst_ren
#guard_msgs (drop info) in #check @Val.U.subst_ren
#guard_msgs (drop info) in #check @Expr.U.ren_subst
#guard_msgs (drop info) in #check @Val.U.ren_subst
#guard_msgs (drop info) in #check @Expr.U.subst_comp
#guard_msgs (drop info) in #check @Val.U.subst_comp
#guard_msgs (drop info) in #check (@Expr.U.subst_id : ∀ t, Expr.U.subst Expr.U.ids t = t)
#guard_msgs (drop info) in #check (@Val.U.subst_id : ∀ v, Val.U.subst Expr.U.ids v = v)
#guard_msgs (drop info) in #check @Expr.U.subst0_subst_up

/-! ## Computational sanity. -/

/-- Payloads pass through subst verbatim (both sorts). -/
example (sg : Nat → Expr.U) (i : Int) (l : Loc) :
    Expr.U.subst sg (.add (.val (.int i)) (.val (.loc l)))
      = .add (.val (.int i)) (.val (.loc l)) := rfl

/-- The closure body (foreign-under-binder) lifts with the shared `up`. -/
example (sg : Nat → Expr.U) (e : Expr.U) :
    Val.U.subst sg (.clos e) = .clos (Expr.U.subst (Expr.U.up sg) e) := rfl

/-- `letin` binds in its second argument only. -/
example (u : Expr.U) :
    Expr.U.subst0 (.letin (.var 0) (.var 0)) u = .letin u (.var 0) := rfl

/-- β through a closure: `subst0` reaches under the binder correctly. -/
example (sg : Nat → Expr.U) (u : Expr.U) :
    Expr.U.subst0 (Expr.U.subst (Expr.U.up sg) (.var 0)) u
      = Expr.U.subst (Expr.U.cons u sg) (.var 0) :=
  Expr.U.subst0_subst_up sg (.var 0) u

end Autosubst2.GenUnscopedMulti
