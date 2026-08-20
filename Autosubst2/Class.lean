import Autosubst2.Basic

/-!
# `Subst` typeclass: instance-generic single-sort substitution

Abstracts a well-scoped single-sort de Bruijn syntax `T : Nat → Type` over its
three core operations so that the `asimpl` tactic and the substitution notation
can be written once in the library and reused for every derived syntax.

## Design

The class carries exactly the three primitive operations:

* `vr`    — the variable embedding `Idx n → T n` (`ids`),
* `ren`   — renaming,
* `subst` — substitution.

The binder-lifting `up`, the identity substitution `ids`, and the
single-variable substitution `subst0` are **generic library definitions** over
`Subst T` (not class fields).  This is the minimal interface; it matches the
shape of the operations emitted by `derive_autosubst%` (whose generated `up`,
`ids`, `subst0` are *definitionally equal* to these generic ones, so the
instance fields can point at the generated bare `ren`/`subst`/`var`).
-/

namespace Autosubst2

/-- A well-scoped single-sort syntax `T : Nat → Type` with variable embedding,
renaming, and substitution. -/
class Subst (T : Nat → Type) where
  /-- Variable embedding `Idx n → T n`. -/
  vr    : {n : Nat} → Idx n → T n
  /-- Renaming. -/
  ren   : {m n : Nat} → (Idx m → Idx n) → T m → T n
  /-- Substitution. -/
  subst : {m n : Nat} → (Idx m → T n) → T m → T n

/-- The identity substitution: variables to themselves. -/
abbrev Subst.ids {T : Nat → Type} [Subst T] {n : Nat} : Idx n → T n := Subst.vr

/-- Lift a substitution under a binder. -/
def Subst.up {T : Nat → Type} [Subst T] {m n : Nat}
    (sigma : Idx m → T n) : Idx (m + 1) → T (n + 1) :=
  (Subst.vr var_zero) .: (fun x => Subst.ren shift (sigma x))

/-- Single-variable substitution: substitute `u` for the newest variable. -/
def Subst.subst0 {T : Nat → Type} [Subst T] {n : Nat}
    (e : T (n + 1)) (u : T n) : T n :=
  Subst.subst (u .: Subst.vr) e

end Autosubst2
