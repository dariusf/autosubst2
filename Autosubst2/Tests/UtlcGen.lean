import Autosubst2.Deriving

/-!
# Macro sanity test: generated UTLC substitution theory.

We define a fresh copy `Tm` of the untyped lambda calculus in its own namespace,
run `derive_autosubst%` on it, and re-check the `UtlcTests` sanity properties
against the GENERATED operations and lemmas.
-/

namespace Autosubst2.Gen

open Autosubst2

/-- Well-scoped terms (copy of the golden inductive). -/
inductive Tm : Nat → Type
  | var {n : Nat} : Idx n → Tm n
  | app {n : Nat} : Tm n → Tm n → Tm n
  | lam {n : Nat} : Bind Tm n → Tm n

derive_autosubst% Tm

/-! ## Sanity checks against the generated defs/lemmas -/

/-- The closed identity function `λ 0`. -/
example : Tm 0 := Tm.lam (Tm.var var_zero)

/-- β-substituting the bound variable returns the argument. -/
example {n : Nat} (u : Tm n) : subst0 (Tm.var var_zero) u = u := rfl

/-- A β example by `rfl`. -/
example :
    subst0 (Tm.app (Tm.var var_zero) (Tm.var var_zero)) (Tm.lam (Tm.var var_zero) : Tm 0)
      = Tm.app (Tm.lam (Tm.var var_zero)) (Tm.lam (Tm.var var_zero)) := rfl

/-- `ren_ren` at a concrete term. -/
example (xi zeta : Idx 1 → Idx 1) :
    ren zeta (ren xi (Tm.var var_zero)) = ren (fun x => zeta (xi x)) (Tm.var var_zero) := rfl

/-- `subst_subst` at a concrete term. -/
example (sigma tau : Idx 1 → Tm 1) :
    subst tau (subst sigma (Tm.var var_zero))
      = subst (fun x => subst tau (sigma x)) (Tm.var var_zero) := rfl

/-- The headline lemma at a concrete body, via the generated `subst0_subst_up`. -/
example {n : Nat} (sigma : Idx 0 → Tm n) (u : Tm n) :
    subst0 (subst (up sigma) (Tm.var var_zero)) u = subst (u .: sigma) (Tm.var var_zero) :=
  subst0_subst_up sigma (Tm.var var_zero) u

/-- `subst_id` via rewrite. -/
example {n : Nat} (t : Tm n) : subst ids t = t := by rw [subst_id]

/-- The full generated lemma chain is available (type-checks the statements). -/
example := @ren_ren
example := @subst_ren
example := @ren_subst
example := @subst_subst
example := @up_ids
example := @subst_id
example := @ren_id
example := @subst0_subst_up

end Autosubst2.Gen
