/-!
# Binder marker for the Autosubst-2 derivation metaprogram

`Bind T n` is an explicit, reducible marker for a constructor subterm that lives
under ONE new binder (well-scoped: the scope grows by one).  The single-sort
`derive_autosubst%` macro reads binder DEPTH off the number of nested `Bind`
heads wrapping the eventual `T …`, instead of sniffing index arithmetic on
`T (n + k)`.
-/

namespace Autosubst2

/-- Binder marker: `Bind T n` is the type of a subterm under ONE new binder
    (well-scoped: scope grows by one). Reducible so it erases for typing.

    Nesting gives depth: `Bind T : Nat → Type`, so `Bind (Bind T) n = T (n+2)`,
    etc. — the macro reads binder DEPTH = number of nested `Bind` heads. -/
abbrev Bind (T : Nat → Type) (n : Nat) : Type := T (n + 1)

end Autosubst2
