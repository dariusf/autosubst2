import Autosubst2.Deriving
import Autosubst2.Notation

/-!
# Unit tests for the generic `Autosubst2.Notation`

A fresh copy `Tm` is derived (also getting a `Subst` instance via the macro);
each `rfl` confirms the notation desugars to the expected `Subst` call.
-/

namespace Autosubst2.NotationGen

open Autosubst2 Autosubst2.Notation

/-- Well-scoped terms (copy of the golden inductive). -/
inductive Tm : Nat → Type
  | var {n : Nat} : Idx n → Tm n
  | app {n : Nat} : Tm n → Tm n → Tm n
  | lam {n : Nat} : Bind Tm n → Tm n

derive_autosubst% Tm

section NotationTests

variable {m n k : Nat}

/-- `e[σ]` desugars to `subst σ e`. -/
example (σ : Idx m → Tm n) (e : Tm m) : e[σ] = subst σ e := rfl

/-- `e⟨ξ⟩` desugars to `ren ξ e`. -/
example (ξ : Idx m → Idx n) (e : Tm m) : e⟨ξ⟩ = ren ξ e := rfl

/-- `s..` desugars to `scons s ids`. -/
example (s : Tm n) : s.. = scons s ids := rfl

/-- `↑` is `shift`. -/
example : (↑ : Idx n → Idx (n + 1)) = shift := rfl

/-- `e[σ][τ]` parses left-associatively as `(e[σ])[τ]` = `subst τ (subst σ e)`. -/
example (σ : Idx m → Tm n) (τ : Idx n → Tm k) (e : Tm m) :
    e[σ][τ] = subst τ (subst σ e) := rfl

/-- `e⟨ξ⟩⟨ζ⟩` parses left-associatively. -/
example (ξ : Idx m → Idx n) (ζ : Idx n → Idx k) (e : Tm m) :
    e⟨ξ⟩⟨ζ⟩ = ren ζ (ren ξ e) := rfl

/-- Mixed: renaming then substitution. -/
example (ξ : Idx m → Idx n) (τ : Idx n → Tm k) (e : Tm m) :
    e⟨ξ⟩[τ] = subst τ (ren ξ e) := rfl

/-- `s..` is the substitution used in single-variable substitution:
    `e[s..] = subst0 e s`. -/
example (e : Tm (n + 1)) (s : Tm n) : e[s..] = subst0 e s := rfl

end NotationTests

end Autosubst2.NotationGen
