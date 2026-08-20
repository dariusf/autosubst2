import Autosubst2.Basic

/-!
# Multi-sorted System F (well-scoped, vector substitution)

Hand-written in the uniform shape the `deriving`-style macro will emit for the
two-sort signature `sysf.sig`.

There are two variable sorts: type variables and term variables.  `Ty` mentions
only type variables and is indexed by a single scope.  `Tm` mentions both and is
indexed by a pair `(m n)` = (ty-var count, tm-var count).  Substituting a term
therefore threads a *vector* of two substitutions, one per sort.
-/

namespace Autosubst2

/-- Well-scoped System F types: `Ty m` has type-variables in `Idx m`. -/
inductive Ty : Nat → Type
  | tvar {m : Nat} : Idx m → Ty m
  | arr {m : Nat} : Ty m → Ty m → Ty m
  | all {m : Nat} : Ty (m + 1) → Ty m

/-- Well-scoped System F terms: `Tm m n` has type-variables in `Idx m` and
term-variables in `Idx n`. -/
inductive Tm : Nat → Nat → Type
  | var {m n : Nat} : Idx n → Tm m n
  | app {m n : Nat} : Tm m n → Tm m n → Tm m n
  | lam {m n : Nat} : Ty m → Tm m (n + 1) → Tm m n
  | tapp {m n : Nat} : Tm m n → Ty m → Tm m n
  | tlam {m n : Nat} : Tm (m + 1) n → Tm m n

/-! ## Type level (single sort — exactly like Utlc) -/

/-- Type renaming, structural on the type. -/
def renTy {m m1 : Nat} (xity : Idx m → Idx m1) : Ty m → Ty m1
  | .tvar x => .tvar (xity x)
  | .arr a b => .arr (renTy xity a) (renTy xity b)
  | .all a => .all (renTy (up_ren xity) a)

/-- Lifting of a type substitution under a type binder. -/
def upTy {m m1 : Nat} (sigmaty : Idx m → Ty m1) : Idx (m + 1) → Ty (m1 + 1) :=
  (Ty.tvar var_zero) .: (fun x => renTy shift (sigmaty x))

/-- Type substitution, structural on the type. -/
def substTy {m m1 : Nat} (sigmaty : Idx m → Ty m1) : Ty m → Ty m1
  | .tvar x => sigmaty x
  | .arr a b => .arr (substTy sigmaty a) (substTy sigmaty b)
  | .all a => .all (substTy (upTy sigmaty) a)

/-- The identity type substitution. -/
def idsTy {m : Nat} : Idx m → Ty m := Ty.tvar

/-! ## Term level — vector renaming and substitution -/

/-- Term renaming.  Takes one renaming per variable sort: `xity` for type
variables, `xitm` for term variables. -/
def renTm {m m1 n n1 : Nat}
    (xity : Idx m → Idx m1) (xitm : Idx n → Idx n1) : Tm m n → Tm m1 n1
  | .var x => .var (xitm x)
  | .app a b => .app (renTm xity xitm a) (renTm xity xitm b)
  -- binds a TERM variable: term renaming lifts, type renaming unchanged.
  | .lam ty e => .lam (renTy xity ty) (renTm xity (up_ren xitm) e)
  | .tapp e ty => .tapp (renTm xity xitm e) (renTy xity ty)
  -- binds a TYPE variable: type renaming lifts, term renaming unchanged
  -- (it carries no type-scope, so it needs no shift).
  | .tlam e => .tlam (renTm (up_ren xity) xitm e)

/-- Lifting a term substitution under a TERM binder.  Only the term scope grows;
the codomain term values gain one fresh term variable, so each is renamed by the
term-`shift` (with the type renaming kept at identity). -/
def upTm {m1 n n1 : Nat} (sigmatm : Idx n → Tm m1 n1) : Idx (n + 1) → Tm m1 (n1 + 1) :=
  (Tm.var var_zero) .: (fun x => renTm id shift (sigmatm x))

/-- Lifting a term substitution under a TYPE binder.  The codomain type scope
grows, so each term value is renamed by the type-`shift` (term renaming kept at
identity).  This is the cross-sort lifting. -/
def upTmTy {m1 n n1 : Nat} (sigmatm : Idx n → Tm m1 n1) : Idx n → Tm (m1 + 1) n1 :=
  fun x => renTm shift id (sigmatm x)

/-- Term substitution.  Takes a vector of two substitutions: `sigmaty` maps type
variables to types, `sigmatm` maps term variables to terms. -/
def substTm {m m1 n n1 : Nat}
    (sigmaty : Idx m → Ty m1) (sigmatm : Idx n → Tm m1 n1) : Tm m n → Tm m1 n1
  | .var x => sigmatm x
  | .app a b => .app (substTm sigmaty sigmatm a) (substTm sigmaty sigmatm b)
  -- binds a TERM variable: lift `sigmatm` via `upTm`; `sigmaty` is unchanged
  -- (the new binder is a term var, not a type var).  The annotation maps through
  -- `substTy sigmaty`.
  | .lam ty e => .lam (substTy sigmaty ty) (substTm sigmaty (upTm sigmatm) e)
  | .tapp e ty => .tapp (substTm sigmaty sigmatm e) (substTy sigmaty ty)
  -- binds a TYPE variable: lift `sigmaty` via `upTy`, AND push `sigmatm`'s
  -- codomain under the new type binder via `upTmTy` (cross-sort lifting).
  | .tlam e => .tlam (substTm (upTy sigmaty) (upTmTy sigmatm) e)

/-- The identity term substitution. -/
def ids {m n : Nat} : Idx n → Tm m n := Tm.var

/-- Single type-variable substitution into a type, `ty[u/0]`. -/
def substTy0 {m : Nat} (a : Ty (m + 1)) (u : Ty m) : Ty m :=
  substTy (u .: idsTy) a

/-- Single term-variable substitution into a term, `e[u/0]`. -/
def subst0 {m n : Nat} (e : Tm m (n + 1)) (u : Tm m n) : Tm m n :=
  substTm idsTy (u .: ids) e

/-! ## Type-level σ-lemma chain (single sort, mirrors Utlc) -/

theorem renTy_renTy {m m1 m2 : Nat} (xity : Idx m → Idx m1) (zeta : Idx m1 → Idx m2) :
    ∀ t : Ty m, renTy zeta (renTy xity t) = renTy (fun x => zeta (xity x)) t
  | .tvar _ => rfl
  | .arr a b => by simp only [renTy]; rw [renTy_renTy, renTy_renTy]
  | .all a => by
    simp only [renTy]
    rw [renTy_renTy]
    have h : (fun x => up_ren zeta (up_ren xity x)) = up_ren (fun x => zeta (xity x)) := by
      funext x; exact up_ren_ren xity zeta _ (fun _ => rfl) x
    rw [h]

theorem upTy_up_ren {m m1 k : Nat} (sigmaty : Idx m → Ty m1) (xi : Idx k → Idx m)
    (x : Idx (k + 1)) :
    upTy sigmaty (up_ren xi x) = upTy (fun y => sigmaty (xi y)) x := by
  cases x <;> simp [upTy, up_ren, scons, shift, var_zero]

theorem substTy_renTy {m m1 m2 : Nat} (sigmaty : Idx m1 → Ty m2) (xi : Idx m → Idx m1) :
    ∀ t : Ty m, substTy sigmaty (renTy xi t) = substTy (fun x => sigmaty (xi x)) t
  | .tvar _ => rfl
  | .arr a b => by simp only [renTy, substTy]; rw [substTy_renTy, substTy_renTy]
  | .all a => by
    simp only [renTy, substTy]
    rw [substTy_renTy]
    have h : (fun x => upTy sigmaty (up_ren xi x)) = upTy (fun x => sigmaty (xi x)) := by
      funext x; exact upTy_up_ren sigmaty xi x
    rw [h]

theorem upTy_ren_subst {m m1 m2 : Nat} (xi : Idx m1 → Idx m2) (sigmaty : Idx m → Ty m1)
    (x : Idx (m + 1)) :
    upTy (fun y => renTy xi (sigmaty y)) x = renTy (up_ren xi) (upTy sigmaty x) := by
  cases x with
  | none => rfl
  | some y =>
    simp only [upTy, scons, shift]
    rw [renTy_renTy, renTy_renTy]
    rfl

theorem renTy_substTy {m m1 m2 : Nat} (xi : Idx m1 → Idx m2) (sigmaty : Idx m → Ty m1) :
    ∀ t : Ty m, renTy xi (substTy sigmaty t) = substTy (fun x => renTy xi (sigmaty x)) t
  | .tvar _ => rfl
  | .arr a b => by simp only [substTy, renTy]; rw [renTy_substTy, renTy_substTy]
  | .all a => by
    simp only [substTy, renTy]
    rw [renTy_substTy]
    have h : (fun x => renTy (up_ren xi) (upTy sigmaty x)) = upTy (fun x => renTy xi (sigmaty x)) := by
      funext x; exact (upTy_ren_subst xi sigmaty x).symm
    rw [h]

theorem upTy_subst {m m1 m2 : Nat} (sigmaty : Idx m → Ty m1) (tau : Idx m1 → Ty m2)
    (x : Idx (m + 1)) :
    upTy (fun y => substTy tau (sigmaty y)) x = substTy (upTy tau) (upTy sigmaty x) := by
  cases x with
  | none => rfl
  | some y =>
    simp only [upTy, scons, shift]
    rw [renTy_substTy, substTy_renTy]
    rfl

theorem substTy_substTy {m m1 m2 : Nat} (sigmaty : Idx m → Ty m1) (tau : Idx m1 → Ty m2) :
    ∀ t : Ty m, substTy tau (substTy sigmaty t) = substTy (fun x => substTy tau (sigmaty x)) t
  | .tvar _ => rfl
  | .arr a b => by simp only [substTy]; rw [substTy_substTy, substTy_substTy]
  | .all a => by
    simp only [substTy]
    rw [substTy_substTy]
    have h : (fun x => substTy (upTy tau) (upTy sigmaty x)) = upTy (fun x => substTy tau (sigmaty x)) := by
      funext x; exact (upTy_subst sigmaty tau x).symm
    rw [h]

theorem upTy_ids {m : Nat} (x : Idx (m + 1)) : upTy idsTy x = idsTy x := by
  cases x <;> rfl

theorem substTy_id : ∀ {m : Nat} (t : Ty m), substTy idsTy t = t
  | _, .tvar _ => rfl
  | _, .arr a b => by simp only [substTy]; rw [substTy_id, substTy_id]
  | m, .all a => by
    simp only [substTy]
    have h : upTy (m := m) (m1 := m) idsTy = idsTy := by funext x; exact upTy_ids x
    rw [h, substTy_id]

/-! ## Term-level σ-lemma chain (vector) -/

/-! ### Renaming composition -/

theorem renTm_renTm {m m1 m2 n n1 n2 : Nat}
    (xity : Idx m → Idx m1) (xitm : Idx n → Idx n1)
    (zety : Idx m1 → Idx m2) (zetm : Idx n1 → Idx n2) :
    ∀ t : Tm m n,
      renTm zety zetm (renTm xity xitm t)
        = renTm (fun x => zety (xity x)) (fun x => zetm (xitm x)) t
  | .var _ => rfl
  | .app a b => by simp only [renTm]; rw [renTm_renTm, renTm_renTm]
  | .lam ty e => by
    simp only [renTm]
    rw [renTm_renTm, renTy_renTy]
    have h : (fun x => up_ren zetm (up_ren xitm x)) = up_ren (fun x => zetm (xitm x)) := by
      funext x; exact up_ren_ren xitm zetm _ (fun _ => rfl) x
    rw [h]
  | .tapp e ty => by simp only [renTm]; rw [renTm_renTm, renTy_renTy]
  | .tlam e => by
    simp only [renTm]
    rw [renTm_renTm]
    have h : (fun x => up_ren zety (up_ren xity x)) = up_ren (fun x => zety (xity x)) := by
      funext x; exact up_ren_ren xity zety _ (fun _ => rfl) x
    rw [h]

/-! ### up-commutation: substitution after renaming -/

theorem upTm_up_ren {m1 n n1 k : Nat} (sigmatm : Idx n → Tm m1 n1) (xi : Idx k → Idx n)
    (x : Idx (k + 1)) :
    upTm sigmatm (up_ren xi x) = upTm (fun y => sigmatm (xi y)) x := by
  cases x <;> simp [upTm, up_ren, scons, shift, var_zero]

/-- `upTmTy` commutes with a term renaming (the renaming doesn't touch the type
scope, so it passes straight through). -/
theorem upTmTy_up_ren {m1 n n1 k : Nat} (sigmatm : Idx n → Tm m1 n1) (xi : Idx k → Idx n)
    (x : Idx k) :
    upTmTy sigmatm (xi x) = upTmTy (fun y => sigmatm (xi y)) x := rfl

theorem substTm_renTm {m m1 m2 n n1 n2 : Nat}
    (sigmaty : Idx m1 → Ty m2) (sigmatm : Idx n1 → Tm m2 n2)
    (xity : Idx m → Idx m1) (xitm : Idx n → Idx n1) :
    ∀ t : Tm m n,
      substTm sigmaty sigmatm (renTm xity xitm t)
        = substTm (fun x => sigmaty (xity x)) (fun x => sigmatm (xitm x)) t
  | .var _ => rfl
  | .app a b => by simp only [renTm, substTm]; rw [substTm_renTm, substTm_renTm]
  | .lam ty e => by
    simp only [renTm, substTm]
    rw [substTm_renTm, substTy_renTy]
    have h : (fun x => upTm sigmatm (up_ren xitm x)) = upTm (fun x => sigmatm (xitm x)) := by
      funext x; exact upTm_up_ren sigmatm xitm x
    rw [h]
  | .tapp e ty => by simp only [renTm, substTm]; rw [substTm_renTm, substTy_renTy]
  | .tlam e => by
    simp only [renTm, substTm]
    rw [substTm_renTm]
    have hty : (fun x => upTy sigmaty (up_ren xity x)) = upTy (fun x => sigmaty (xity x)) := by
      funext x; exact upTy_up_ren sigmaty xity x
    have htm : (fun x => upTmTy sigmatm (xitm x)) = upTmTy (fun x => sigmatm (xitm x)) := by
      funext x; exact upTmTy_up_ren sigmatm xitm x
    rw [hty, htm]

/-! ### up-commutation: renaming after substitution -/

/-- Pushing a term renaming through `upTm`. -/
theorem upTm_ren_subst {m1 m2 n n1 n2 : Nat}
    (xity : Idx m1 → Idx m2) (xitm : Idx n1 → Idx n2) (sigmatm : Idx n → Tm m1 n1)
    (x : Idx (n + 1)) :
    upTm (fun y => renTm xity xitm (sigmatm y)) x
      = renTm xity (up_ren xitm) (upTm sigmatm x) := by
  cases x with
  | none => rfl
  | some y =>
    simp only [upTm, scons, shift]
    rw [renTm_renTm, renTm_renTm]
    rfl

/-- Pushing a type renaming through `upTmTy` (cross-sort). -/
theorem upTmTy_ren_subst {m1 m2 n n1 n2 : Nat}
    (xity : Idx m1 → Idx m2) (xitm : Idx n1 → Idx n2) (sigmatm : Idx n → Tm m1 n1)
    (x : Idx n) :
    upTmTy (fun y => renTm xity xitm (sigmatm y)) x
      = renTm (up_ren xity) xitm (upTmTy sigmatm x) := by
  simp only [upTmTy]
  rw [renTm_renTm, renTm_renTm]
  rfl

theorem renTm_substTm {m m1 m2 n n1 n2 : Nat}
    (xity : Idx m1 → Idx m2) (xitm : Idx n1 → Idx n2)
    (sigmaty : Idx m → Ty m1) (sigmatm : Idx n → Tm m1 n1) :
    ∀ t : Tm m n,
      renTm xity xitm (substTm sigmaty sigmatm t)
        = substTm (fun x => renTy xity (sigmaty x)) (fun x => renTm xity xitm (sigmatm x)) t
  | .var _ => rfl
  | .app a b => by simp only [substTm, renTm]; rw [renTm_substTm, renTm_substTm]
  | .lam ty e => by
    simp only [substTm, renTm]
    rw [renTm_substTm, renTy_substTy]
    have h : (fun x => renTm xity (up_ren xitm) (upTm sigmatm x))
        = upTm (fun x => renTm xity xitm (sigmatm x)) := by
      funext x; exact (upTm_ren_subst xity xitm sigmatm x).symm
    rw [h]
  | .tapp e ty => by simp only [substTm, renTm]; rw [renTm_substTm, renTy_substTy]
  | .tlam e => by
    simp only [substTm, renTm]
    rw [renTm_substTm]
    have hty : (fun x => renTy (up_ren xity) (upTy sigmaty x))
        = upTy (fun x => renTy xity (sigmaty x)) := by
      funext x; exact (upTy_ren_subst xity sigmaty x).symm
    have htm : (fun x => renTm (up_ren xity) xitm (upTmTy sigmatm x))
        = upTmTy (fun x => renTm xity xitm (sigmatm x)) := by
      funext x; exact (upTmTy_ren_subst xity xitm sigmatm x).symm
    rw [hty, htm]

/-! ### up-commutation: substitution after substitution -/

/-- `renTy id = id`, needed for the `upTm_subst` cross helper. -/
theorem renTy_id_eq {m : Nat} (t : Ty m) : renTy id t = t := by
  induction t with
  | tvar _ => rfl
  | arr _ _ iha ihb => simp only [renTy]; rw [iha, ihb]
  | @all m1 _ ih =>
    simp only [renTy]
    have h : up_ren (id : Idx m1 → Idx m1) = id := by funext x; cases x <;> rfl
    rw [h, ih]

theorem upTm_subst {m1 m2 n n1 n2 : Nat}
    (sigmatm : Idx n → Tm m1 n1) (tauty : Idx m1 → Ty m2) (tautm : Idx n1 → Tm m2 n2)
    (x : Idx (n + 1)) :
    upTm (fun y => substTm tauty tautm (sigmatm y)) x
      = substTm tauty (upTm tautm) (upTm sigmatm x) := by
  cases x with
  | none => rfl
  | some y =>
    simp only [upTm, scons, shift]
    rw [renTm_substTm, substTm_renTm]
    -- LHS type-arg: `fun x => renTy id (tauty x)` reduces to `tauty`.
    have h : (fun x => renTy id (tauty x)) = tauty := by funext z; rw [renTy_id_eq]
    rw [h]; rfl

/-- Cross-sort up-commutation for substitution: `upTmTy` of a composed
substitution.  The type-substitution `tauty` lifts via `upTy`. -/
theorem upTmTy_subst {m1 m2 n n1 n2 : Nat}
    (sigmatm : Idx n → Tm m1 n1) (tauty : Idx m1 → Ty m2) (tautm : Idx n1 → Tm m2 n2)
    (x : Idx n) :
    upTmTy (fun y => substTm tauty tautm (sigmatm y)) x
      = substTm (upTy tauty) (upTmTy tautm) (upTmTy sigmatm x) := by
  simp only [upTmTy]
  rw [renTm_substTm, substTm_renTm]
  have hty : (fun x => renTy shift (tauty x)) = (fun x => upTy tauty (shift x)) := by
    funext z; rfl
  have htm : (fun x => renTm shift id (tautm x)) = (fun x => upTmTy tautm (id x)) := by
    funext z; rfl
  rw [hty, htm]

theorem substTm_substTm {m m1 m2 n n1 n2 : Nat}
    (sigmaty : Idx m → Ty m1) (sigmatm : Idx n → Tm m1 n1)
    (tauty : Idx m1 → Ty m2) (tautm : Idx n1 → Tm m2 n2) :
    ∀ t : Tm m n,
      substTm tauty tautm (substTm sigmaty sigmatm t)
        = substTm (fun x => substTy tauty (sigmaty x))
                  (fun x => substTm tauty tautm (sigmatm x)) t
  | .var _ => rfl
  | .app a b => by simp only [substTm]; rw [substTm_substTm, substTm_substTm]
  | .lam ty e => by
    simp only [substTm]
    rw [substTm_substTm, substTy_substTy]
    have h : (fun x => substTm tauty (upTm tautm) (upTm sigmatm x))
        = upTm (fun x => substTm tauty tautm (sigmatm x)) := by
      funext x; exact (upTm_subst sigmatm tauty tautm x).symm
    rw [h]
  | .tapp e ty => by simp only [substTm]; rw [substTm_substTm, substTy_substTy]
  | .tlam e => by
    simp only [substTm]
    rw [substTm_substTm]
    have hty : (fun x => substTy (upTy tauty) (upTy sigmaty x))
        = upTy (fun x => substTy tauty (sigmaty x)) := by
      funext x; exact (upTy_subst sigmaty tauty x).symm
    have htm : (fun x => substTm (upTy tauty) (upTmTy tautm) (upTmTy sigmatm x))
        = upTmTy (fun x => substTm tauty tautm (sigmatm x)) := by
      funext x; exact (upTmTy_subst sigmatm tauty tautm x).symm
    rw [hty, htm]

/-! ### Identity -/

theorem upTm_ids {m n : Nat} (x : Idx (n + 1)) : upTm (ids (m := m)) x = ids x := by
  cases x <;> rfl

theorem upTmTy_ids {m n : Nat} (x : Idx n) : upTmTy (ids (m := m)) x = ids x := rfl

theorem substTm_id : ∀ {m n : Nat} (t : Tm m n), substTm idsTy ids t = t
  | _, _, .var _ => rfl
  | _, _, .app a b => by simp only [substTm]; rw [substTm_id, substTm_id]
  | m, n, .lam ty e => by
    simp only [substTm]
    have htm : upTm (m1 := m) (n := n) ids = ids := by funext x; exact upTm_ids x
    have hty : substTy (m := m) idsTy ty = ty := substTy_id ty
    rw [htm, hty, substTm_id]
  | _, _, .tapp e ty => by
    simp only [substTm]; rw [substTm_id, substTy_id]
  | m, n, .tlam e => by
    simp only [substTm]
    have hty : upTy (m := m) (m1 := m) idsTy = idsTy := by funext x; exact upTy_ids x
    have htm : upTmTy (m1 := m) (n := n) ids = ids := by funext x; exact upTmTy_ids x
    rw [hty, htm, substTm_id]

end Autosubst2
