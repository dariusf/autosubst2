import Autosubst2.Deriving
import Autosubst2.Asimpl

/-!
# Tests for the generic `asimpl`

A fresh copy `Tm` of the untyped lambda calculus is derived (also getting a
`Subst` instance via the macro); every goal below is closed by the generic
`asimpl` **alone** (no manual `rw`).
-/

namespace Autosubst2.AsimplGen

open Autosubst2

/-- Well-scoped terms (copy of the golden inductive). -/
inductive Tm : Nat → Type
  | var {n : Nat} : Idx n → Tm n
  | app {n : Nat} : Tm n → Tm n → Tm n
  | lam {n : Nat} : Bind Tm n → Tm n

derive_autosubst% Tm

/-- `subst_id` reproved by normalisation. -/
example {n : Nat} (t : Tm n) : subst ids t = t := by asimpl

/-- `ren_id` reproved. -/
example {n : Nat} (t : Tm n) : ren id t = t := by asimpl

/-- `subst`/`subst` composition fused into one outer substitution. -/
example {m n k : Nat} (sigma : Idx m → Tm n) (tau : Idx n → Tm k) (t : Tm m) :
    subst tau (subst sigma t) = subst (fun x => subst tau (sigma x)) t := by asimpl

/-- `ren`/`ren` composition fused. -/
example {m n k : Nat} (xi : Idx m → Idx n) (zeta : Idx n → Idx k) (t : Tm m) :
    ren zeta (ren xi t) = ren (fun x => zeta (xi x)) t := by asimpl

/-- `subst`/`ren` composition fused. -/
example {m n k : Nat} (sigma : Idx n → Tm k) (xi : Idx m → Idx n) (t : Tm m) :
    subst sigma (ren xi t) = subst (fun x => sigma (xi x)) t := by asimpl

/-- `ren`/`subst` composition fused. -/
example {m n k : Nat} (xi : Idx n → Idx k) (sigma : Idx m → Tm n) (t : Tm m) :
    ren xi (subst sigma t) = subst (fun x => ren xi (sigma x)) t := by asimpl

/-- The headline downstream lemma `subst0_subst_up`. -/
example {m n : Nat} (sigma : Idx m → Tm n) (e : Tm (m + 1)) (u : Tm n) :
    subst0 (subst (up sigma) e) u = subst (u .: sigma) e := by asimpl

/-! ## Concrete-term normalisations -/

/-- Identity substitution on a concrete term. -/
example {n : Nat} (i : Idx n) : subst ids (Tm.app (Tm.var i) (Tm.var i))
    = Tm.app (Tm.var i) (Tm.var i) := by asimpl

/-- Renaming pushed through `app`/`lam` and identity removed. -/
example {n : Nat} (t : Tm (n + 1)) : ren id (Tm.lam t) = Tm.lam t := by asimpl

/-- Double substitution on a concrete `app` fuses into a single one. -/
example {m n k : Nat} (sigma : Idx m → Tm n) (tau : Idx n → Tm k) (a b : Tm m) :
    subst tau (subst sigma (Tm.app a b))
      = subst (fun x => subst tau (sigma x)) (Tm.app a b) := by asimpl

end Autosubst2.AsimplGen
