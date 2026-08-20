import Autosubst2.Examples.SysF

/-!
# Sanity checks for the System F vector substitution theory.
-/

namespace Autosubst2

/-- The polymorphic identity `Λα. λx:α. x` as a closed term `Tm 0 0`.
`tlam` opens a type scope (now `m = 1`); `lam` annotates with `tvar 0` (the
freshly bound type variable) and opens a term scope; the body is `var 0`. -/
def polyId : Tm 0 0 :=
  .tlam (.lam (.tvar var_zero) (.var var_zero))

/-- A polymorphic-identity application skeleton: `(Λα. λx:α. x) [σ]` reduces by
β to `λx:σ. x`.  Here we check that type-applying via `substTy0`-style single
type substitution computes by `rfl`. -/
example (sigma : Ty 0) :
    substTm (sigma .: idsTy) ids (.lam (.tvar var_zero) (.var var_zero))
      = (.lam sigma (.var var_zero) : Tm 0 0) := rfl

/-- Identity vector substitution is the identity (instance of `substTm_id`). -/
example : substTm idsTy ids polyId = polyId := substTm_id polyId

/-- Identity on a non-trivial open term. -/
example {m n : Nat} (e : Tm m n) : substTm idsTy ids e = e := substTm_id e

/-- A concrete `substTm` computation by `rfl`: substituting `u` for the single
free term variable of `app (var 0) (var 0)`. -/
example (u : Tm 0 0) :
    substTm idsTy (u .: ids) (.app (.var var_zero) (.var var_zero))
      = .app u u := rfl

/-- `subst0` β-redex check: `(λx. x) [u/0]`-style substitution of a body. -/
example (u : Tm 0 0) : subst0 (.var var_zero) u = u := rfl

/-- Type-level single substitution computes by `rfl`. -/
example (a : Ty 0) : substTy0 (.tvar var_zero) a = a := rfl

/-- Renaming the closed `polyId` by any pair of renamings is itself
(closed term, nothing to rename) — checked by `rfl`. -/
example : renTm (id : Idx 0 → Idx 0) (id : Idx 0 → Idx 0) polyId = polyId := rfl

end Autosubst2
