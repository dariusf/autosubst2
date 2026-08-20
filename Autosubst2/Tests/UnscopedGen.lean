import Autosubst2.Deriving

/-!
# Macro sanity test: generated UNSCOPED substitution theory.

We declare the WELL-SCOPED lambda source `Tm : Nat → Type`, run
`derive_autosubst% (unscoped) Tm`, and check that the generated unscoped
inductive `Tm.U : Type` and its ops/lemmas have `Nat`-indexed (unscoped) types.
-/

namespace Autosubst2.UGen

open Autosubst2

/-- Well-scoped source inductive (binder structure for the unscoped backend). -/
inductive Tm : Nat → Type
  | var {n : Nat} : Idx n → Tm n
  | app {n : Nat} : Tm n → Tm n → Tm n
  | lam {n : Nat} : Bind Tm n → Tm n

derive_autosubst% (unscoped) Tm

open Tm.U

/-! ## The generated type is unscoped (`Tm.U : Type`). -/
#guard_msgs (drop info) in #check (Tm.U : Type)
#guard_msgs (drop info) in #check (Tm.U.var : Nat → Tm.U)
#guard_msgs (drop info) in #check (Tm.U.lam : Tm.U → Tm.U)

/-! ## Ops have unscoped (`Nat → _`) types. -/
#guard_msgs (drop info) in #check (Tm.U.ren : (Nat → Nat) → Tm.U → Tm.U)
#guard_msgs (drop info) in #check (Tm.U.up : (Nat → Tm.U) → Nat → Tm.U)
#guard_msgs (drop info) in #check (Tm.U.subst : (Nat → Tm.U) → Tm.U → Tm.U)
#guard_msgs (drop info) in #check (Tm.U.ids : Nat → Tm.U)
#guard_msgs (drop info) in #check (Tm.U.subst0 : Tm.U → Tm.U → Tm.U)

/-! ## σ-chain lemmas type-check with unscoped statements. -/
#guard_msgs (drop info) in #check @Tm.U.ren_ren
#guard_msgs (drop info) in #check @Tm.U.subst_ren
#guard_msgs (drop info) in #check @Tm.U.ren_subst
#guard_msgs (drop info) in #check @Tm.U.subst_comp
#guard_msgs (drop info) in #check @Tm.U.subst_id
#guard_msgs (drop info) in #check @Tm.U.subst0_subst_up

/-! ## Simple computational goals. -/

/-- `subst0 (var 0) u = u`. -/
example (u : Tm.U) : Tm.U.subst0 (.var 0) u = u := rfl

/-- A β example by `rfl`: substitute the identity for the bound variable. -/
example :
    Tm.U.subst0 (Tm.U.app (.var 0) (.var 0)) (Tm.U.lam (.var 0))
      = Tm.U.app (Tm.U.lam (.var 0)) (Tm.U.lam (.var 0)) := rfl

/-- `subst_id` via rewrite. -/
example (t : Tm.U) : Tm.U.subst Tm.U.ids t = t := by rw [Tm.U.subst_id]

/-- The headline lemma at a concrete body. -/
example (sigma : Nat → Tm.U) (u : Tm.U) :
    Tm.U.subst0 (Tm.U.subst (Tm.U.up sigma) (.var 0)) u
      = Tm.U.subst (Tm.U.cons u sigma) (.var 0) :=
  Tm.U.subst0_subst_up sigma (.var 0) u

end Autosubst2.UGen
