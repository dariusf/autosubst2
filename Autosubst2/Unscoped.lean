
/-!
# Unscoped de Bruijn runtime primitives

Lean port of the Coq Autosubst 2 unscoped runtime header (`unscoped.v`).
De Bruijn indices are plain `Nat` (`fin := nat`).  This is the runtime the
unscoped backend of `derive_autosubst% (unscoped) T` targets; it is the
reusable-library version of the operations that `Heifer/LogRel/Lambda/Subst.lean`
inlines (`upren`, `up`-style lifts, `scons`, `funcomp`).

Written in the regular, uniform shape the generator emits.
-/

namespace Autosubst2.Unscoped

/-- The freshly-bound (newest) variable: index `0`. -/
@[match_pattern, reducible] def var_zero : Nat := 0

/-- The shift renaming `Nat → Nat` (Coq `shift := S`). -/
@[reducible] def shift : Nat → Nat := Nat.succ

/-- Forward function composition (autosubst `>>`): first `f`, then `g`. -/
def funcomp {X Y Z : Sort _} (g : Y → Z) (f : X → Y) : X → Z := fun x => g (f x)

/-- Extend a mapping `f : Nat → X` with a new value `x` for index `0`,
giving a mapping `Nat → X` (Coq `scons`). -/
def uscons {X : Sort _} (x : X) (f : Nat → X) : Nat → X
  | 0     => x
  | n + 1 => f n

@[inherit_doc] infixr:55 " .: " => uscons

/-- Generic lifting of a renaming under a binder. -/
def upren (xi : Nat → Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => Nat.succ (xi n)

/-! ## Pointwise lemmas -/

@[simp] theorem uscons_zero {X : Sort _} (x : X) (f : Nat → X) :
    (x .: f) 0 = x := rfl

@[simp] theorem uscons_succ {X : Sort _} (x : X) (f : Nat → X) (n : Nat) :
    (x .: f) (Nat.succ n) = f n := rfl

/-- Lifting of renamings composes (autosubst `up_ren_ren`). -/
theorem upren_comp (xi zeta : Nat → Nat) (n : Nat) :
    upren zeta (upren xi n) = upren (fun m => zeta (xi m)) n := by
  cases n <;> rfl

end Autosubst2.Unscoped
