import Autosubst2.Deriving

/-!
# Macro test: deep-embedded State language `{Tm, Assn}` (mutual, shared scope).

Generates the substitution theory of `Autosubst2/Examples/StateLang.lean` (the
hand-written GOLDEN reference) with `derive_autosubst% Tm Assn`.

GOLDEN spec (StateLang.lean):
* ONE shared term-variable scope `k`, threaded through BOTH sorts.
* Only `Tm` has a variable constructor; `Assn` has NONE (var-less).
* The substitute sort is `Tm` for BOTH sorts: `substTm, substAssn : (Idx k → Tm n) → …`.
* True mutual cycle `Tm ↔ Assn` (`produce`/`consume` embed `Assn`; `pts`/`eq`
  embed `Tm`).
* Two binders extend the shared scope: `lam` (Tm) and `sep_ex` (Assn), both lift
  with the SAME `upTm`.

RESOLVED — the multi-sort backend now supports the "shared substitute sort"
(mutual-cycle) shape via three additions (sort order `Tm Assn`):

(a) VAR-LESS SORT — `MNames.varCtor : Array (Option Name)`; for a var-less sort
    the generator skips its `ids`/`subst0`/var-pattern/var-computation lemmas and
    reuses the SHARED substitute sort's `var`/`up`/`ids` (`Tm.var`/`upTm`/`idsTm`).
(b) MUTUAL CYCLE — `MNames.shared` flag: all ops emit inside ONE `mutual` block
    (so `substTm` ↔ `substAssn` resolve), and so do all σ-lemmas (so
    `substTm_substTm` ↔ `substAssn_substAssn` resolve).  The `induction`-based
    `ren<S>_id_eq` is skipped (single column ⇒ never needed; would fail on mutual
    inductives anyway).
(c) SUBSTITUTE SORT ≠ SCOPE SORT — `MNames.substIdx`: in shared mode every sort's
    `up`/`ids`/value type ranges in the substitute sort (`sorts[0] = Tm`), so
    `substAssn` correctly gets `Idx d0 → Tm c0` maps and `upTm` is shared.

Headline lemmas are axiom-clean (`[propext, Quot.sound]`, no `Classical.choice`).
-/

namespace Autosubst2.GenState

open Autosubst2

mutual
/-- Well-scoped terms (redefined exactly as `StateLang.Tm`). -/
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

/-- Well-scoped assertions over the SAME shared scope `k`; NO own var ctor. -/
inductive Assn : Nat → Type
  | emp {k} : Assn k
  | pts {k} : Nat → Tm k → Assn k        -- loc : Nat, cell value : embedded Tm
  | star {k} : Assn k → Assn k → Assn k
  | sep_ex {k} : Assn (k + 1) → Assn k   -- binds a term variable
  | eq {k} : Tm k → Tm k → Assn k        -- deep-embedded pure equality assertion
  | wand {k} : Assn k → Assn k → Assn k
end

derive_autosubst% Tm Assn

/-! ## Sanity checks against the generated defs/lemmas.

The generated names carry sort suffixes (`substTm`/`substAssn`/`idsTm`/`substTm0`)
but the SEMANTICS exactly match the hand-written `StateLang.lean` golden:
ONE shared scope, substitute sort `Tm` for BOTH sorts, var-less `Assn`, mutual
cycle `Tm ↔ Assn`, one shared `upTm`. -/

section Checks
variable {k : Nat}

-- operations have the golden types (single shared `Idx k → Tm n` substitute map).
#guard_msgs (drop info) in #check (renTm : (Idx k → Idx k) → Tm k → Tm k)
#guard_msgs (drop info) in #check (renAssn : (Idx k → Idx k) → Assn k → Assn k)
#guard_msgs (drop info) in #check (substTm : (Idx k → Tm k) → Tm k → Tm k)
#guard_msgs (drop info) in #check (substAssn : (Idx k → Tm k) → Assn k → Assn k)

-- generated analogues of the golden headline lemmas.
#guard_msgs (drop info) in #check (@substTm_id : ∀ {k : Nat} (t : Tm k), substTm idsTm t = t)
#guard_msgs (drop info) in #check (@substAssn_id : ∀ {k : Nat} (H : Assn k), substAssn idsTm H = H)
#guard_msgs (drop info) in #check @substTm_substTm
#guard_msgs (drop info) in #check @substAssn_substAssn
#guard_msgs (drop info) in #check (@subst0_subst_up :
  ∀ {k : Nat} (sigma : Idx k → Tm k) (e : Tm (k + 1)) (u : Tm k),
    substTm0 (substTm (upTm sigma) e) u = substTm (u .: sigma) e)

-- identity substitution is a no-op (via the generated lemmas).
example (e : Tm k) : substTm idsTm e = e := substTm_id e
example (H : Assn k) : substAssn idsTm H = H := substAssn_id H

-- `var 0` is selected by `substTm0`.
example (u : Tm k) : substTm0 (.var var_zero) u = u := rfl

-- a closed concrete term round-trips through identity substitution.
example : substTm idsTm (Tm.lam (.var var_zero) : Tm 0) = Tm.lam (.var var_zero) := rfl

-- cross-sort: substituting into `produce`/`pts` reaches the embedded term.
example (u : Tm 0) :
    substTm0 (Tm.produce (.pts 3 (.var var_zero))) u
      = Tm.produce (.pts 3 u) := by
  simp only [substTm0, substTm, substAssn]; rfl

end Checks

end Autosubst2.GenState
