
/-!
# Well-scoped de Bruijn runtime primitives

Lean port of the Coq Autosubst 2 scoped runtime header (`fintype.v`).
De Bruijn indices are drawn from finite types `Idx n`, implemented as the
`n`-fold iteration of `Option` (with `Idx 0 = Empty`).  This is the autosubst
`fin` type; we deliberately avoid Lean core `Fin`.

Written in the regular, uniform shape a `deriving`-style generator will emit.
-/

namespace Autosubst2

/-- The finite type with `n` elements, as the `n`-fold iteration of `Option`. -/
def Idx : Nat → Type
  | 0 => Empty
  | n + 1 => Option (Idx n)

def Idx.decEq : (n : Nat) → (a b : Idx n) → Decidable (a = b)
  | 0, a, _ => a.elim
  | _ + 1, a, b => match a, b with
    | none, none => isTrue rfl
    | none, some _ => isFalse (by simp)
    | some _, none => isFalse (by simp)
    | some x, some y =>
      match Idx.decEq _ x y with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro he; exact h (by injection he))

instance {n : Nat} : DecidableEq (Idx n) := Idx.decEq n

/-- The freshly-bound (newest) variable in a non-empty scope. -/
@[match_pattern] def var_zero {n : Nat} : Idx (n + 1) := none

/-- The shift renaming `Idx n → Idx (n+1)`. -/
@[match_pattern] def shift {n : Nat} : Idx n → Idx (n + 1) := some

/-- Forward function composition (autosubst `>>`): first `f`, then `g`. -/
def funcomp {X Y Z : Type _} (g : Y → Z) (f : X → Y) : X → Z := fun x => g (f x)

infixr:50 " >> " => fun f g => funcomp g f

/-- Extend a mapping `f : Idx n → X` with a new value `x` for the freshest
index, giving a mapping `Idx (n+1) → X`. -/
def scons {X : Type _} {n : Nat} (x : X) (f : Idx n → X) : Idx (n + 1) → X
  | var_zero => x
  | shift i => f i

@[inherit_doc] infixr:55 " .: " => scons

/-- Generic lifting of a renaming under a binder. -/
def up_ren {m n : Nat} (xi : Idx m → Idx n) : Idx (m + 1) → Idx (n + 1) :=
  var_zero .: (fun x => shift (xi x))

/-! ## Pointwise lemmas -/

/-- Eta for the empty scope: any two maps out of `Idx 0` are equal. -/
theorem idx_zero_eta {X : Type _} (f g : Idx 0 → X) : f = g := by
  funext x; exact x.elim

@[simp] theorem scons_var_zero {X : Type _} {n : Nat} (x : X) (f : Idx n → X) :
    (x .: f) var_zero = x := rfl

@[simp] theorem scons_shift {X : Type _} {n : Nat} (x : X) (f : Idx n → X) (i : Idx n) :
    (x .: f) (shift i) = f i := rfl

/-- `scons_var_zero` in the literal `none` spelling produced by `cases` on an
`Idx (n + 1)` (the `var_zero` pattern does not match a literal `none`). -/
@[simp] theorem scons_none {X : Type _} {n : Nat} (x : X) (f : Idx n → X) :
    (x .: f) none = x := rfl

/-- `scons_shift` in the literal `some` spelling produced by `cases`. -/
@[simp] theorem scons_some {X : Type _} {n : Nat} (x : X) (f : Idx n → X) (i : Idx n) :
    (x .: f) (some i) = f i := rfl

/-- `scons` distributes through post-composition. -/
theorem scons_comp {X Y : Type _} {n : Nat} (x : X) (f : Idx n → X) (g : X → Y) :
    (fun i => g ((x .: f) i)) = (g x) .: (fun i => g (f i)) := by
  funext i; cases i <;> rfl

/-- Eta for `scons`: reconstructing a map from its head and tail. -/
theorem scons_eta {X : Type _} {n : Nat} (f : Idx (n + 1) → X) :
    (f var_zero) .: (fun i => f (shift i)) = f := by
  funext i; cases i <;> rfl

/-- Identity instance of `scons_eta`. -/
theorem scons_eta_id {n : Nat} :
    (var_zero .: (fun i => shift i)) = (id : Idx (n + 1) → Idx (n + 1)) := by
  funext i; cases i <;> rfl

/-- Lifting of renamings composes (autosubst `up_ren_ren`). -/
theorem up_ren_ren {k l m : Nat} (xi : Idx k → Idx l) (zeta : Idx l → Idx m)
    (rho : Idx k → Idx m) (E : ∀ x, zeta (xi x) = rho x) :
    ∀ x, up_ren zeta (up_ren xi x) = up_ren rho x := by
  intro x; cases x with
  | none => rfl
  | some y => simp only [up_ren, scons, shift]; rw [E]

end Autosubst2
