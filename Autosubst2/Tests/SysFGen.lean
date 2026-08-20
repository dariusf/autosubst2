import Autosubst2.Deriving

/-!
# Macro sanity test: generated System F vector substitution theory.

A fresh copy of `Ty`/`Tm` in namespace `Autosubst2.GenF`, with the multi-sort
`derive_autosubst% Ty Tm`, re-checking the `SysFTests` sanity properties against
the GENERATED defs/lemmas.
-/

namespace Autosubst2.GenF

open Autosubst2

inductive Ty : Nat → Type
  | tvar {m : Nat} : Idx m → Ty m
  | arr {m : Nat} : Ty m → Ty m → Ty m
  | all {m : Nat} : Ty (m + 1) → Ty m

inductive Tm : Nat → Nat → Type
  | var {m n : Nat} : Idx n → Tm m n
  | app {m n : Nat} : Tm m n → Tm m n → Tm m n
  | lam {m n : Nat} : Ty m → Tm m (n + 1) → Tm m n
  | tapp {m n : Nat} : Tm m n → Ty m → Tm m n
  | tlam {m n : Nat} : Tm (m + 1) n → Tm m n

derive_autosubst% Ty Tm

/-! ## Sanity checks against the generated defs/lemmas -/

def polyId : Tm 0 0 :=
  .tlam (.lam (.tvar var_zero) (.var var_zero))

example (sigma : Ty 0) :
    substTm (sigma .: idsTy) ids (.lam (.tvar var_zero) (.var var_zero))
      = (.lam sigma (.var var_zero) : Tm 0 0) := rfl

example (u : Tm 0 0) :
    substTm idsTy (u .: ids) (.app (.var var_zero) (.var var_zero))
      = .app u u := rfl

example (u : Tm 0 0) : subst0 (.var var_zero) u = u := rfl

example (a : Ty 0) : substTy0 (.tvar var_zero) a = a := rfl

example : renTm (id : Idx 0 → Idx 0) (id : Idx 0 → Idx 0) polyId = polyId := rfl

/-! ## The generated composition chain is available with the right types. -/

-- type level
#guard_msgs (drop info) in #check @renTy_renTy
#guard_msgs (drop info) in #check @substTy_renTy
#guard_msgs (drop info) in #check @renTy_substTy
#guard_msgs (drop info) in #check @substTy_substTy
#guard_msgs (drop info) in #check (@renTy_id_eq : ∀ {m : Nat} (t : Ty m), renTy id t = t)

-- term level (vector)
#guard_msgs (drop info) in #check @renTm_renTm
#guard_msgs (drop info) in #check @substTm_renTm
#guard_msgs (drop info) in #check @renTm_substTm
#guard_msgs (drop info) in #check @substTm_substTm
#guard_msgs (drop info) in #check (@upTm_up_ren)
#guard_msgs (drop info) in #check (@upTmTy_up_ren)
#guard_msgs (drop info) in #check (@upTm_ren_subst)
#guard_msgs (drop info) in #check (@upTmTy_ren_subst)
#guard_msgs (drop info) in #check (@upTm_subst)
#guard_msgs (drop info) in #check (@upTmTy_subst)
#guard_msgs (drop info) in #check (@subst0_subst_up)

/-- A `subst0_subst_up`-style sanity goal closed via the GENERATED lemma. -/
example {n : Nat} (sigma : Idx n → Tm 0 n) (u : Tm 0 n) :
    subst0 (substTm idsTy (upTm sigma) (.var var_zero)) u
      = substTm idsTy (u .: sigma) (.var var_zero) :=
  subst0_subst_up sigma (.var var_zero) u

/-- And a concrete `rfl`/`asimpl`-level instance of the same. -/
example (u : Tm 0 0) :
    substTm idsTy (u .: ids) (.app (.var var_zero) (.var var_zero)) = .app u u := rfl

end Autosubst2.GenF
