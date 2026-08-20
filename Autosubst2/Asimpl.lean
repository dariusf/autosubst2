import Autosubst2.Class
import Autosubst2.AsimplAttr

/-!
# `asimpl` — instance-generic substitution normalisation

Lean port of Autosubst 2's `asimpl`/`fsimpl` tactic, written once in the library
and reusable for every `Subst T` instance.

In Autosubst 2 `asimpl` is a curated, carefully-oriented `simp` set: it pushes
renamings and substitutions through term constructors, **composes** adjacent
renamings / substitutions into a single outer operation, eliminates identity
substitutions/renamings, and computes `scons` applied to `var_zero`/`shift`.

This file provides the *generic* tactic.  It names no concrete object-language
operation: the per-instance composition / identity lemmas and the `up`/`subst0`
op-unfolds are pulled in because the `derive_autosubst%` macro tags them
`@[autosubst]`.  The tactic only adds the generic library runtime
(`scons`/`var_zero`/`shift`/`up_ren`/`funcomp`) and the generic `Subst`
operations (`Subst.up`/`Subst.subst0`/`Subst.ids`/`Subst.subst`/`Subst.ren`/
`Subst.vr`) so that goals stated with the notation (`Subst.subst` etc.) reduce
to the same canonical form as goals stated with the bare generated operations.
-/

namespace Autosubst2

open Autosubst2 (Subst)

-- Compute `scons` applications on concrete indices in both spellings
-- (`var_zero`/`shift` and the literal `none`/`some` that `cases` produces), so
-- the core set can finish goals without unfolding `scons` wholesale.
attribute [autosubst] Autosubst2.scons_var_zero Autosubst2.scons_shift
  Autosubst2.scons_none Autosubst2.scons_some

/-- The core `simp only` call: the curated `autosubst` set (per-instance
composition/identity/op-unfolds, tagged by the macro) plus the generic `Subst`
operations and `funcomp`. -/
macro "asimpl_core" : tactic =>
  `(tactic| simp only [autosubst,
      Subst.subst0, Subst.up, Subst.ids, Subst.subst, Subst.ren, Subst.vr,
      Autosubst2.funcomp])

/-- Unfold the binder-lifting runtime (`scons`, `var_zero`, `shift`, `up_ren`)
together with the `autosubst` set and the generic `Subst` ops; used to compute a
lifted map applied to a concrete index after a case split. -/
macro "asimpl_up" : tactic =>
  `(tactic| simp only [autosubst,
      Subst.up, Subst.ids, Subst.subst, Subst.ren, Subst.vr,
      Autosubst2.scons, Autosubst2.var_zero, Autosubst2.shift, Autosubst2.up_ren])

set_option linter.unusedSimpArgs false in
/-- Normalise substitution/renaming expressions to canonical form.

Runs the curated `autosubst` simp set, then, when a residual goal compares two
substitution *functions* (an outer `subst`/`ren` whose function argument still
mentions a lifted map), descends with `congr`/`funext` and a case split on the
index so the lift is computed and the `scons`/composition rules fire. -/
macro "asimpl" : tactic =>
  `(tactic|
    (asimpl_core
     <;> try (congr 1 <;> funext x <;> (try asimpl_up) <;> cases x <;> (try asimpl_up)
              <;> (try asimpl_core)
              <;> (try simp only [autosubst,
                    Subst.subst, Subst.ren, Subst.vr,
                    Autosubst2.scons, Autosubst2.var_zero, Autosubst2.shift]))))

end Autosubst2
