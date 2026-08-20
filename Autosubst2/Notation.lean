import Autosubst2.Class

/-!
# Autosubst-2 notation, generic over `Subst`

Mirrors the Coq `subst_scope` notations from `fintype.v`, but parameterised over
any `Subst T` instance via the typeclass rather than a concrete object language.

| Lean             | Coq    | Meaning                       |
|------------------|--------|-------------------------------|
| `e[σ]`  (scoped) | `s[σ]` | `Subst.subst σ e`             |
| `e⟨ξ⟩`  (scoped) | `s⟨ξ⟩` | `Subst.ren ξ e`               |
| `s..`   (scoped) | `s..`  | `scons s Subst.vr`            |
| `↑`     (scoped) | `↑`    | `shift`                       |

**Enabling**: `open Autosubst2.Notation` (or `open scoped Autosubst2.Notation`).

### Bracket choice vs Coq

`e[σ]` conflicts with Lean's `GetElem` notation (`e[i]`).  By placing the
notation in a *scoped* namespace it is only active when opened; the elaborator
resolves the overload because `σ : Idx _ → T _` is not a `GetElem` instance.

### Parse order for `e[σ][τ]`

Both `[·]` and `⟨·⟩` are at precedence 75, left associative, so `e[σ][τ]` parses
as `(e[σ])[τ]` = `subst τ (subst σ e)`.
-/

namespace Autosubst2.Notation

/-- Postfix substitution application: `e[σ]` means `Subst.subst σ e`. -/
scoped notation:75 e "[" σ "]" => Autosubst2.Subst.subst σ e

/-- Postfix renaming application: `e⟨ξ⟩` means `Subst.ren ξ e`. -/
scoped notation:75 e "⟨" ξ "⟩" => Autosubst2.Subst.ren ξ e

/-- `s..` is the single-variable substitution `scons s Subst.vr`. -/
scoped notation:arg s ".." => scons s Autosubst2.Subst.vr

/-- `↑` for the shift renaming `Idx n → Idx (n+1)`. -/
scoped notation "↑" => Autosubst2.shift

end Autosubst2.Notation
