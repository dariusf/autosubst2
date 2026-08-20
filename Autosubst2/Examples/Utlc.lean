import Autosubst2.Basic
import Autosubst2.Bind

/-!
# Single-sorted untyped lambda calculus (well-scoped)

Hand-written in the uniform shape the `deriving`-style macro will emit for the
signature `utlc.sig` (`app : tm -> tm -> tm`, `lam : (tm -> tm) -> tm`).

Mirrors the unscoped autosubst-1 lemma chain (`Heifer/LogRel/Lambda/Subst.lean`);
the proofs are structurally identical but indices are intrinsic.
-/

namespace Autosubst2

/-- Well-scoped terms: `Tm n` has free variables in `Idx n`. -/
inductive Tm : Nat → Type
  | var {n : Nat} : Idx n → Tm n
  | app {n : Nat} : Tm n → Tm n → Tm n
  | lam {n : Nat} : Bind Tm n → Tm n

/-- Renaming, structural on the term. -/
def ren {m n : Nat} (xi : Idx m → Idx n) : Tm m → Tm n
  | .var x => .var (xi x)
  | .app a b => .app (ren xi a) (ren xi b)
  | .lam e => .lam (ren (up_ren xi) e)

/-- Lifting of a substitution under a binder. -/
def up {m n : Nat} (sigma : Idx m → Tm n) : Idx (m + 1) → Tm (n + 1) :=
  (Tm.var var_zero) .: (fun x => ren shift (sigma x))

/-- Substitution, structural on the term. -/
def subst {m n : Nat} (sigma : Idx m → Tm n) : Tm m → Tm n
  | .var x => sigma x
  | .app a b => .app (subst sigma a) (subst sigma b)
  | .lam e => .lam (subst (up sigma) e)

/-- The identity substitution. -/
def ids {n : Nat} : Idx n → Tm n := Tm.var

/-- Single-variable substitution `e[u/0]`. -/
def subst0 {n : Nat} (e : Tm (n + 1)) (u : Tm n) : Tm n :=
  subst (u .: ids) e

/-! ## The σ-lemma chain -/

theorem ren_ren {m n k : Nat} (xi : Idx m → Idx n) (zeta : Idx n → Idx k) :
    ∀ t : Tm m, ren zeta (ren xi t) = ren (fun x => zeta (xi x)) t
  | .var _ => rfl
  | .app a b => by simp only [ren]; rw [ren_ren, ren_ren]
  | .lam e => by
    simp only [ren]
    rw [ren_ren]
    have h : (fun x => up_ren zeta (up_ren xi x)) = up_ren (fun x => zeta (xi x)) := by
      funext x; exact up_ren_ren xi zeta _ (fun _ => rfl) x
    rw [h]

theorem up_up_ren {m n k : Nat} (sigma : Idx m → Tm n) (xi : Idx k → Idx m) (x : Idx (k + 1)) :
    up sigma (up_ren xi x) = up (fun y => sigma (xi y)) x := by
  cases x <;> simp [up, up_ren, scons, shift, var_zero]

theorem subst_ren {m n k : Nat} (sigma : Idx n → Tm k) (xi : Idx m → Idx n) :
    ∀ t : Tm m, subst sigma (ren xi t) = subst (fun x => sigma (xi x)) t
  | .var _ => rfl
  | .app a b => by simp only [ren, subst]; rw [subst_ren, subst_ren]
  | .lam e => by
    simp only [ren, subst]
    rw [subst_ren]
    have h : (fun x => up sigma (up_ren xi x)) = up (fun x => sigma (xi x)) := by
      funext x; exact up_up_ren sigma xi x
    rw [h]

theorem up_ren_subst {m n k : Nat} (xi : Idx n → Idx k) (sigma : Idx m → Tm n) (x : Idx (m + 1)) :
    up (fun y => ren xi (sigma y)) x = ren (up_ren xi) (up sigma x) := by
  cases x with
  | none => rfl
  | some y =>
    simp only [up, scons, shift]
    rw [ren_ren, ren_ren]
    rfl

theorem ren_subst {m n k : Nat} (xi : Idx n → Idx k) (sigma : Idx m → Tm n) :
    ∀ t : Tm m, ren xi (subst sigma t) = subst (fun x => ren xi (sigma x)) t
  | .var _ => rfl
  | .app a b => by simp only [subst, ren]; rw [ren_subst, ren_subst]
  | .lam e => by
    simp only [subst, ren]
    rw [ren_subst]
    have h : (fun x => ren (up_ren xi) (up sigma x)) = up (fun x => ren xi (sigma x)) := by
      funext x; exact (up_ren_subst xi sigma x).symm
    rw [h]

theorem up_subst {m n k : Nat} (sigma : Idx m → Tm n) (tau : Idx n → Tm k) (x : Idx (m + 1)) :
    up (fun y => subst tau (sigma y)) x = subst (up tau) (up sigma x) := by
  cases x with
  | none => rfl
  | some y =>
    simp only [up, scons, shift]
    rw [ren_subst, subst_ren]
    rfl

theorem subst_subst {m n k : Nat} (sigma : Idx m → Tm n) (tau : Idx n → Tm k) :
    ∀ t : Tm m, subst tau (subst sigma t) = subst (fun x => subst tau (sigma x)) t
  | .var _ => rfl
  | .app a b => by simp only [subst]; rw [subst_subst, subst_subst]
  | .lam e => by
    simp only [subst]
    rw [subst_subst]
    have h : (fun x => subst (up tau) (up sigma x)) = up (fun x => subst tau (sigma x)) := by
      funext x; exact (up_subst sigma tau x).symm
    rw [h]

theorem up_ids {n : Nat} (x : Idx (n + 1)) : up ids x = ids x := by
  cases x <;> rfl

theorem subst_id : ∀ {n : Nat} (t : Tm n), subst ids t = t
  | _, .var _ => rfl
  | _, .app a b => by simp only [subst]; rw [subst_id, subst_id]
  | n, .lam e => by
    simp only [subst]
    have h : up (m := n) (n := n) ids = ids := by funext x; exact up_ids x
    rw [h, subst_id]

theorem ren_eq_subst : ∀ {n : Nat} (t : Tm n), ren id t = subst ids t
  | _, .var _ => rfl
  | _, .app a b => by simp only [ren, subst]; rw [ren_eq_subst, ren_eq_subst]
  | n, .lam e => by
    simp only [ren, subst]
    have hup : (up_ren (id : Idx n → Idx n)) = id := by funext x; cases x <;> rfl
    have hids : up (n := n) ids = ids := by funext x; exact up_ids x
    rw [hup, ren_eq_subst, hids]

theorem ren_id {n : Nat} (t : Tm n) : ren id t = t := by
  rw [ren_eq_subst, subst_id]

/-! ## Headline downstream lemma -/

/-- Instantiating under a binder then β-substituting equals substituting with
the extended substitution `u .: σ`. -/
theorem subst0_subst_up {m n : Nat} (sigma : Idx m → Tm n) (e : Tm (m + 1)) (u : Tm n) :
    subst0 (subst (up sigma) e) u = subst (u .: sigma) e := by
  unfold subst0
  rw [subst_subst]
  congr 1
  funext x
  cases x with
  | none => rfl
  | some y =>
    simp only [up, scons, shift]
    rw [subst_ren]
    have h : (fun z => (u .: ids) (some z)) = ids := by funext z; rfl
    rw [h, subst_id]

end Autosubst2
