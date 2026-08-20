import Autosubst2.Deriving

/-!
# Macro smoke test: multi-sort `.other` (verbatim payload) arguments.

A small two-sort family where one constructor carries a plain `Nat` payload and
another carries a `Prop` payload.  These are classified as `MArg.other`: they
appear verbatim in patterns/terms and are never traversed by ren/subst.
-/

namespace Autosubst2.GenOther

open Autosubst2

inductive Ty : Nat → Type
  | tvar {m : Nat} : Idx m → Ty m
  | arr {m : Nat} : Ty m → Ty m → Ty m
  | all {m : Nat} : Ty (m + 1) → Ty m

inductive Tm : Nat → Nat → Type
  | var {m n : Nat} : Idx n → Tm m n
  | app {m n : Nat} : Tm m n → Tm m n → Tm m n
  | lam {m n : Nat} : Ty m → Tm m (n + 1) → Tm m n
  | tlam {m n : Nat} : Tm (m + 1) n → Tm m n
  -- `.other` payloads: a plain `Nat` and a `Prop`, carried verbatim.
  | lit {m n : Nat} : Nat → Tm m n
  | guard {m n : Nat} : Prop → Tm m n → Tm m n

derive_autosubst% Ty Tm

/-- subst leaves the `Nat` payload untouched. -/
example (sg0 : Idx 0 → Ty 0) (sg1 : Idx 0 → Tm 0 0) (k : Nat) :
    substTm sg0 sg1 (.lit k) = .lit k := rfl

/-- subst leaves the `Prop` payload untouched, recursing only in the term arg. -/
example (sg0 : Idx 0 → Ty 0) (sg1 : Idx 1 → Tm 0 0) (P : Prop) :
    substTm sg0 sg1 (.guard P (.var var_zero))
      = .guard P (sg1 var_zero) := rfl

/-- ren likewise leaves payloads verbatim. -/
example (xi0 : Idx 0 → Idx 0) (xi1 : Idx 0 → Idx 0) (P : Prop) (k : Nat) :
    renTm xi0 xi1 (.guard P (.lit k)) = .guard P (.lit k) := rfl

end Autosubst2.GenOther
