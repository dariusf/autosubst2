import Autosubst2.Examples.Utlc

/-!
# Sanity tests for the well-scoped UTLC substitution theory.
-/

namespace Autosubst2

/-- The closed identity function `λ 0`. -/
example : Tm 0 := Tm.lam (Tm.var var_zero)

/-- β-substituting the bound variable returns the argument. -/
example {n : Nat} (u : Tm n) : subst0 (Tm.var var_zero) u = u := rfl

/-- A β example: substituting `0 0` with `λ0` for index 0. -/
example :
    subst0 (Tm.app (Tm.var var_zero) (Tm.var var_zero)) (Tm.lam (Tm.var var_zero) : Tm 0)
      = Tm.app (Tm.lam (Tm.var var_zero)) (Tm.lam (Tm.var var_zero)) := rfl

/-- `ren_ren` instantiated at a concrete term, checked by `rfl`. -/
example (xi zeta : Idx 1 → Idx 1) :
    ren zeta (ren xi (Tm.var var_zero)) = ren (fun x => zeta (xi x)) (Tm.var var_zero) := rfl

/-- `subst_subst` instantiated at a concrete term, checked by `rfl`. -/
example (sigma tau : Idx 1 → Tm 1) :
    subst tau (subst sigma (Tm.var var_zero))
      = subst (fun x => subst tau (sigma x)) (Tm.var var_zero) := rfl

/-- The headline lemma at a concrete body. -/
example {n : Nat} (sigma : Idx 0 → Tm n) (u : Tm n) :
    subst0 (subst (up sigma) (Tm.var var_zero)) u = subst (u .: sigma) (Tm.var var_zero) :=
  subst0_subst_up sigma (Tm.var var_zero) u

/-- `subst_id` via rewrite. -/
example {n : Nat} (t : Tm n) : subst ids t = t := by rw [subst_id]

end Autosubst2
