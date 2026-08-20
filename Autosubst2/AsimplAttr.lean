import Lean

/-!
# `autosubst` simp attribute

Declared in its own module because a `register_simp_attr` only becomes usable as
an attribute in modules that *import* the declaring module (the attribute's
initialiser runs at import time).  `Autosubst2.Asimpl` imports this and tags the
substitution-normalising lemmas.
-/

/-- Simp set holding the substitution-normalising rewrites used by `asimpl`. -/
register_simp_attr autosubst
