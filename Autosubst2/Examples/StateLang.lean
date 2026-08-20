import Autosubst2.Basic

/-!
# State language `{Tm, Assn}` (well-scoped, mutual, single shared scope)

Hand-written golden reference for the deep-embedded mutual `Tm`/`Assn` surface
syntax of `Heifer/LogRel/Lambda/Lang.lean`, in the uniform shape the
`deriving`-style macro should emit.  This is the *spec* the macro will be checked
against; nothing here uses `derive_autosubst%`.

## Structural shape (and how it departs from `SysF.lean`)

* There is ONE shared term-variable scope `k`, threaded through BOTH sorts.  Only
  `Tm` has a variable constructor (`Tm.var`); `Assn` has NO own variable
  constructor — its variables appear solely via embedded `Tm` (inside `pts`).
* The substitute sort is `Tm` for BOTH sorts: `subst`/`substAssn` share the same
  map type `Idx k → Tm n`.  (Contrast SysF, where `Tm` carries two independent
  scopes and a *vector* of two substitutions.)
* True mutual cycle in both directions: `Tm` embeds `Assn` (`produce`/`consume`),
  `Assn` embeds `Tm` (`pts`).  So `rename`/`renameAssn` and `subst`/`substAssn`
  are mutually recursive.
* Two binders extend the shared scope: `lam` (in `Tm`) and `sep_ex` (in `Assn`).
  Both lift with the SAME `up_ren`/`up`.
* `Assn` carries NO verbatim non-syntactic payload: `eq` deep-embeds a pure
  equality assertion as TWO embedded `Tm` subterms (so it substitutes exactly
  like `pts`/`app`).  The only literal payloads anywhere are `Nat`s: `loc`'s
  location and `pts`'s location.
-/

namespace Autosubst2.StateLang

open Autosubst2

mutual
/-- Well-scoped terms: `Tm k` has term-variables in `Idx k`. -/
inductive Tm : Nat → Type
  | var {k} : Idx k → Tm k
  | lam {k} : Tm (k + 1) → Tm k          -- binds a term variable
  | app {k} : Tm k → Tm k → Tm k
  | loc {k} : Nat → Tm k                 -- heap location (a Nat, not a variable)
  | alloc {k} : Tm k → Tm k
  | deref {k} : Tm k → Tm k
  | update {k} : Tm k → Tm k → Tm k
  | free {k} : Tm k → Tm k
  | produce {k} : Assn k → Tm k          -- cross-sort: embeds Assn
  | consume {k} : Assn k → Tm k

/-- Well-scoped assertions over the SAME shared scope `k`.  No own variable
constructor: variables enter only through the embedded `Tm` in `pts`. -/
inductive Assn : Nat → Type
  | emp {k} : Assn k
  | pts {k} : Nat → Tm k → Assn k        -- loc : Nat, cell value : embedded Tm
  | star {k} : Assn k → Assn k → Assn k
  | sep_ex {k} : Assn (k + 1) → Assn k   -- binds a term variable
  | eq {k} : Tm k → Tm k → Assn k        -- deep-embedded pure equality assertion
  | wand {k} : Assn k → Assn k → Assn k
end

/-! ## Mutual renaming over `Idx k → Idx n` -/

mutual
/-- Term renaming (mutual with `renameAssn`). -/
def rename {k n : Nat} (xi : Idx k → Idx n) : Tm k → Tm n
  | .var x => .var (xi x)
  | .lam e => .lam (rename (up_ren xi) e)        -- term binder
  | .app a b => .app (rename xi a) (rename xi b)
  | .loc l => .loc l
  | .alloc e => .alloc (rename xi e)
  | .deref e => .deref (rename xi e)
  | .update a b => .update (rename xi a) (rename xi b)
  | .free e => .free (rename xi e)
  | .produce H => .produce (renameAssn xi H)
  | .consume H => .consume (renameAssn xi H)

/-- Assertion renaming (mutual with `rename`). -/
def renameAssn {k n : Nat} (xi : Idx k → Idx n) : Assn k → Assn n
  | .emp => .emp
  | .pts l v => .pts l (rename xi v)
  | .star a b => .star (renameAssn xi a) (renameAssn xi b)
  | .sep_ex H => .sep_ex (renameAssn (up_ren xi) H)   -- term binder
  | .eq a b => .eq (rename xi a) (rename xi b)
  | .wand a b => .wand (renameAssn xi a) (renameAssn xi b)
end

/-! ## Mutual substitution over `Idx k → Tm n` -/

/-- Lift a substitution under a (term) binder; shared by `lam` and `sep_ex`. -/
def up {k n : Nat} (sigma : Idx k → Tm n) : Idx (k + 1) → Tm (n + 1) :=
  (Tm.var var_zero) .: (fun x => rename shift (sigma x))

mutual
/-- Term substitution (mutual with `substAssn`). -/
def subst {k n : Nat} (sigma : Idx k → Tm n) : Tm k → Tm n
  | .var x => sigma x
  | .lam e => .lam (subst (up sigma) e)          -- term binder
  | .app a b => .app (subst sigma a) (subst sigma b)
  | .loc l => .loc l
  | .alloc e => .alloc (subst sigma e)
  | .deref e => .deref (subst sigma e)
  | .update a b => .update (subst sigma a) (subst sigma b)
  | .free e => .free (subst sigma e)
  | .produce H => .produce (substAssn sigma H)
  | .consume H => .consume (substAssn sigma H)

/-- Assertion substitution (mutual with `subst`). -/
def substAssn {k n : Nat} (sigma : Idx k → Tm n) : Assn k → Assn n
  | .emp => .emp
  | .pts l v => .pts l (subst sigma v)
  | .star a b => .star (substAssn sigma a) (substAssn sigma b)
  | .sep_ex H => .sep_ex (substAssn (up sigma) H)     -- term binder
  | .eq a b => .eq (subst sigma a) (subst sigma b)
  | .wand a b => .wand (substAssn sigma a) (substAssn sigma b)
end

/-- The identity substitution. -/
def ids {k : Nat} : Idx k → Tm k := Tm.var

/-- Single-variable substitution `e[u/0]`. -/
def subst0 {k : Nat} (e : Tm (k + 1)) (u : Tm k) : Tm k :=
  subst (u .: ids) e

/-! ## σ-lemma chain

The mutual cycle `Tm ↔ Assn` forces every structural lemma to be proved as a
mutual pair (pattern-matching on the explicit syntax: Lean's `induction` does not
support mutual inductives).  Each pair mirrors the corresponding single-sort SysF
lemma, but with `up`/`up_ren` shared by both binders. -/

/-! ### Renaming composition -/

mutual
theorem rename_rename {k n p : Nat} (xi : Idx k → Idx n) (zeta : Idx n → Idx p) :
    ∀ t : Tm k, rename zeta (rename xi t) = rename (fun x => zeta (xi x)) t
  | .var _ => rfl
  | .app a b => by simp only [rename]; rw [rename_rename, rename_rename]
  | .lam e => by
    simp only [rename]
    rw [rename_rename]
    have h : (fun x => up_ren zeta (up_ren xi x)) = up_ren (fun x => zeta (xi x)) := by
      funext x; exact up_ren_ren xi zeta _ (fun _ => rfl) x
    rw [h]
  | .loc _ => rfl
  | .alloc e => by simp only [rename]; rw [rename_rename]
  | .deref e => by simp only [rename]; rw [rename_rename]
  | .update a b => by simp only [rename]; rw [rename_rename, rename_rename]
  | .free e => by simp only [rename]; rw [rename_rename]
  | .produce H => by simp only [rename]; rw [renameAssn_renameAssn]
  | .consume H => by simp only [rename]; rw [renameAssn_renameAssn]

theorem renameAssn_renameAssn {k n p : Nat} (xi : Idx k → Idx n) (zeta : Idx n → Idx p) :
    ∀ H : Assn k, renameAssn zeta (renameAssn xi H) = renameAssn (fun x => zeta (xi x)) H
  | .emp => rfl
  | .pts _ v => by simp only [renameAssn]; rw [rename_rename]
  | .star a b => by simp only [renameAssn]; rw [renameAssn_renameAssn, renameAssn_renameAssn]
  | .sep_ex H => by
    simp only [renameAssn]
    rw [renameAssn_renameAssn]
    have h : (fun x => up_ren zeta (up_ren xi x)) = up_ren (fun x => zeta (xi x)) := by
      funext x; exact up_ren_ren xi zeta _ (fun _ => rfl) x
    rw [h]
  | .eq a b => by simp only [renameAssn]; rw [rename_rename, rename_rename]
  | .wand a b => by simp only [renameAssn]; rw [renameAssn_renameAssn, renameAssn_renameAssn]
end

/-! ### up-commutation: substitution after renaming -/

theorem up_up_ren {k n p : Nat} (sigma : Idx n → Tm p) (xi : Idx k → Idx n)
    (x : Idx (k + 1)) :
    up sigma (up_ren xi x) = up (fun y => sigma (xi y)) x := by
  cases x <;> simp [up, up_ren, scons, shift, var_zero]

mutual
theorem subst_rename {k n p : Nat} (sigma : Idx n → Tm p) (xi : Idx k → Idx n) :
    ∀ t : Tm k, subst sigma (rename xi t) = subst (fun x => sigma (xi x)) t
  | .var _ => rfl
  | .app a b => by simp only [rename, subst]; rw [subst_rename, subst_rename]
  | .lam e => by
    simp only [rename, subst]
    rw [subst_rename]
    have h : (fun x => up sigma (up_ren xi x)) = up (fun x => sigma (xi x)) := by
      funext x; exact up_up_ren sigma xi x
    rw [h]
  | .loc _ => rfl
  | .alloc e => by simp only [rename, subst]; rw [subst_rename]
  | .deref e => by simp only [rename, subst]; rw [subst_rename]
  | .update a b => by simp only [rename, subst]; rw [subst_rename, subst_rename]
  | .free e => by simp only [rename, subst]; rw [subst_rename]
  | .produce H => by simp only [rename, subst]; rw [substAssn_renameAssn]
  | .consume H => by simp only [rename, subst]; rw [substAssn_renameAssn]

theorem substAssn_renameAssn {k n p : Nat} (sigma : Idx n → Tm p) (xi : Idx k → Idx n) :
    ∀ H : Assn k, substAssn sigma (renameAssn xi H) = substAssn (fun x => sigma (xi x)) H
  | .emp => rfl
  | .pts _ v => by simp only [renameAssn, substAssn]; rw [subst_rename]
  | .star a b => by simp only [renameAssn, substAssn]; rw [substAssn_renameAssn, substAssn_renameAssn]
  | .sep_ex H => by
    simp only [renameAssn, substAssn]
    rw [substAssn_renameAssn]
    have h : (fun x => up sigma (up_ren xi x)) = up (fun x => sigma (xi x)) := by
      funext x; exact up_up_ren sigma xi x
    rw [h]
  | .eq a b => by simp only [renameAssn, substAssn]; rw [subst_rename, subst_rename]
  | .wand a b => by simp only [renameAssn, substAssn]; rw [substAssn_renameAssn, substAssn_renameAssn]
end

/-! ### up-commutation: renaming after substitution -/

theorem up_ren_subst {k n p : Nat} (xi : Idx n → Idx p) (sigma : Idx k → Tm n)
    (x : Idx (k + 1)) :
    up (fun y => rename xi (sigma y)) x = rename (up_ren xi) (up sigma x) := by
  cases x with
  | none => rfl
  | some y =>
    simp only [up, scons, shift]
    rw [rename_rename, rename_rename]
    rfl

mutual
theorem rename_subst {k n p : Nat} (xi : Idx n → Idx p) (sigma : Idx k → Tm n) :
    ∀ t : Tm k, rename xi (subst sigma t) = subst (fun x => rename xi (sigma x)) t
  | .var _ => rfl
  | .app a b => by simp only [subst, rename]; rw [rename_subst, rename_subst]
  | .lam e => by
    simp only [subst, rename]
    rw [rename_subst]
    have h : (fun x => rename (up_ren xi) (up sigma x)) = up (fun x => rename xi (sigma x)) := by
      funext x; exact (up_ren_subst xi sigma x).symm
    rw [h]
  | .loc _ => rfl
  | .alloc e => by simp only [subst, rename]; rw [rename_subst]
  | .deref e => by simp only [subst, rename]; rw [rename_subst]
  | .update a b => by simp only [subst, rename]; rw [rename_subst, rename_subst]
  | .free e => by simp only [subst, rename]; rw [rename_subst]
  | .produce H => by simp only [subst, rename]; rw [renameAssn_substAssn]
  | .consume H => by simp only [subst, rename]; rw [renameAssn_substAssn]

theorem renameAssn_substAssn {k n p : Nat} (xi : Idx n → Idx p) (sigma : Idx k → Tm n) :
    ∀ H : Assn k, renameAssn xi (substAssn sigma H) = substAssn (fun x => rename xi (sigma x)) H
  | .emp => rfl
  | .pts _ v => by simp only [substAssn, renameAssn]; rw [rename_subst]
  | .star a b => by simp only [substAssn, renameAssn]; rw [renameAssn_substAssn, renameAssn_substAssn]
  | .sep_ex H => by
    simp only [substAssn, renameAssn]
    rw [renameAssn_substAssn]
    have h : (fun x => rename (up_ren xi) (up sigma x)) = up (fun x => rename xi (sigma x)) := by
      funext x; exact (up_ren_subst xi sigma x).symm
    rw [h]
  | .eq a b => by simp only [substAssn, renameAssn]; rw [rename_subst, rename_subst]
  | .wand a b => by simp only [substAssn, renameAssn]; rw [renameAssn_substAssn, renameAssn_substAssn]
end

/-! ### up-commutation: substitution after substitution -/

theorem up_subst {k n p : Nat} (sigma : Idx k → Tm n) (tau : Idx n → Tm p)
    (x : Idx (k + 1)) :
    up (fun y => subst tau (sigma y)) x = subst (up tau) (up sigma x) := by
  cases x with
  | none => rfl
  | some y =>
    simp only [up, scons, shift]
    rw [rename_subst, subst_rename]
    rfl

mutual
theorem subst_subst {k n p : Nat} (sigma : Idx k → Tm n) (tau : Idx n → Tm p) :
    ∀ t : Tm k, subst tau (subst sigma t) = subst (fun x => subst tau (sigma x)) t
  | .var _ => rfl
  | .app a b => by simp only [subst]; rw [subst_subst, subst_subst]
  | .lam e => by
    simp only [subst]
    rw [subst_subst]
    have h : (fun x => subst (up tau) (up sigma x)) = up (fun x => subst tau (sigma x)) := by
      funext x; exact (up_subst sigma tau x).symm
    rw [h]
  | .loc _ => rfl
  | .alloc e => by simp only [subst]; rw [subst_subst]
  | .deref e => by simp only [subst]; rw [subst_subst]
  | .update a b => by simp only [subst]; rw [subst_subst, subst_subst]
  | .free e => by simp only [subst]; rw [subst_subst]
  | .produce H => by simp only [subst]; rw [substAssn_substAssn]
  | .consume H => by simp only [subst]; rw [substAssn_substAssn]

theorem substAssn_substAssn {k n p : Nat} (sigma : Idx k → Tm n) (tau : Idx n → Tm p) :
    ∀ H : Assn k, substAssn tau (substAssn sigma H) = substAssn (fun x => subst tau (sigma x)) H
  | .emp => rfl
  | .pts _ v => by simp only [substAssn]; rw [subst_subst]
  | .star a b => by simp only [substAssn]; rw [substAssn_substAssn, substAssn_substAssn]
  | .sep_ex H => by
    simp only [substAssn]
    rw [substAssn_substAssn]
    have h : (fun x => subst (up tau) (up sigma x)) = up (fun x => subst tau (sigma x)) := by
      funext x; exact (up_subst sigma tau x).symm
    rw [h]
  | .eq a b => by simp only [substAssn]; rw [subst_subst, subst_subst]
  | .wand a b => by simp only [substAssn]; rw [substAssn_substAssn, substAssn_substAssn]
end

/-! ### Identity -/

theorem up_ids {k : Nat} (x : Idx (k + 1)) : up (ids (k := k)) x = ids x := by
  cases x <;> rfl

mutual
theorem subst_id : ∀ {k : Nat} (t : Tm k), subst ids t = t
  | _, .var _ => rfl
  | _, .app a b => by simp only [subst]; rw [subst_id, subst_id]
  | k, .lam e => by
    simp only [subst]
    have h : up (ids (k := k)) = ids := by funext x; exact up_ids x
    rw [h, subst_id]
  | _, .loc _ => rfl
  | _, .alloc e => by simp only [subst]; rw [subst_id]
  | _, .deref e => by simp only [subst]; rw [subst_id]
  | _, .update a b => by simp only [subst]; rw [subst_id, subst_id]
  | _, .free e => by simp only [subst]; rw [subst_id]
  | _, .produce H => by simp only [subst]; rw [substAssn_id]
  | _, .consume H => by simp only [subst]; rw [substAssn_id]

theorem substAssn_id : ∀ {k : Nat} (H : Assn k), substAssn ids H = H
  | _, .emp => rfl
  | _, .pts _ v => by simp only [substAssn]; rw [subst_id]
  | _, .star a b => by simp only [substAssn]; rw [substAssn_id, substAssn_id]
  | k, .sep_ex H => by
    simp only [substAssn]
    have h : up (ids (k := k)) = ids := by funext x; exact up_ids x
    rw [h, substAssn_id]
  | _, .eq a b => by simp only [substAssn]; rw [subst_id, subst_id]
  | _, .wand a b => by simp only [substAssn]; rw [substAssn_id, substAssn_id]
end

/-! ### Headline beta-fusion -/

/-- `subst0 (subst (up σ) e) u = subst (u .: σ) e`. -/
theorem subst0_subst_up {k n : Nat} (sigma : Idx k → Tm n) (e : Tm (k + 1)) (u : Tm n) :
    subst0 (subst (up sigma) e) u = subst (u .: sigma) e := by
  simp only [subst0]
  rw [subst_subst]
  have h : (fun x => subst (u .: ids) (up sigma x)) = (u .: sigma) := by
    funext x
    cases x with
    | none => rfl
    | some y =>
      simp only [up, scons, shift]
      rw [subst_rename]
      simp only [scons]
      exact subst_id _
  rw [h]

/-! ## Sanity checks -/

section Checks
variable {k : Nat}

#guard_msgs (drop info) in #check (rename : (Idx k → Idx k) → Tm k → Tm k)
#guard_msgs (drop info) in #check (renameAssn : (Idx k → Idx k) → Assn k → Assn k)
#guard_msgs (drop info) in #check (subst : (Idx k → Tm k) → Tm k → Tm k)
#guard_msgs (drop info) in #check (substAssn : (Idx k → Tm k) → Assn k → Assn k)

-- identity substitution is a no-op
example (e : Tm k) : subst ids e = e := subst_id e
example (H : Assn k) : substAssn ids H = H := substAssn_id H

-- `var 0` is selected by `subst0`
example (u : Tm k) : subst0 (.var var_zero) u = u := rfl

-- a closed concrete term round-trips through identity substitution
example : subst ids (Tm.lam (.var var_zero) : Tm 0) = Tm.lam (.var var_zero) := rfl

-- cross-sort: substituting into `produce`/`pts` reaches the embedded term
example (u : Tm 0) :
    subst0 (Tm.produce (.pts 3 (.var var_zero))) u
      = Tm.produce (.pts 3 u) := by
  simp only [subst0, subst, substAssn]; rfl

end Checks

end Autosubst2.StateLang
