import Autosubst2.Basic
import Autosubst2.Bind
import Autosubst2.Class
import Autosubst2.Notation
import Autosubst2.Asimpl
import Autosubst2.Deriving

/-!
# An extended tutorial on Autosubst2

This file is a self-contained, bottom-up tutorial for the `Autosubst2` library.
It assumes no prior knowledge of de Bruijn representation, binders, or the sigma
calculus. Every operation is introduced in isolation, with worked examples, and
the higher-level layers (typeclass, notation, tactic, code generator) are built
on top of the primitives.

The running object language is a single-sort untyped lambda calculus with
application and abstraction. The same machinery scales to multiple sorts (e.g.
System F) and to an unscoped backend; those are covered at the end.

Read top to bottom. Each `example` and `#check` is checked by the compiler, so
the claims in the prose are mechanically verified.
-/

namespace Autosubst2.Tutorial

open Autosubst2 Autosubst2.Notation

/-! # Part 1. Binders and de Bruijn indices

A binder is a construct that introduces a local name, such as `λx. x`. The name
`x` is meaningless on its own; what matters is *which* binder a variable refers
to. Working with named variables forces bookkeeping: α-renaming to avoid capture,
freshness side conditions, and so on.

The de Bruijn representation removes names entirely. A variable is a natural
number counting the number of binders between its occurrence and the binder it
refers to. The innermost (most recently introduced) binder is `0`.

```
named:     λx. λy. x        λx. x (λy. y)
de Bruijn: λ.  λ.  1        λ.  0 (λ.  0)
```

In the first term, `x` is under two binders, and `x` refers to the outer one, so
it is index `1`. In the second, the outer `0` refers to the `λ` it sits directly
under, and the inner `0` refers to its own `λ`. There are no names to rename, so
substitution becomes a purely arithmetic operation on indices.

## Well-scoped indices

A *closed* term has no free variables. A term with `n` free variables is said to
live in scope `n`: its free indices range over `0, 1, …, n-1`. We make this
precise at the type level: a term family is `T : Nat → Type`, where `T n` is the
type of terms with free variables drawn from an `n`-element index set. This is
the *well-scoped* (or *intrinsically scoped*) discipline: an ill-scoped term
(referring to a variable that does not exist) is not even typeable.
-/

/-! # Part 2. The index type `Idx`

`Autosubst2.Idx n` is the `n`-element type of de Bruijn indices. It is defined as
the `n`-fold iteration of `Option`, with the empty scope being `Empty`:

```
Idx 0 = Empty
Idx (n+1) = Option (Idx n)
```

So `Idx 0` is uninhabited (a closed scope has no free variables), `Idx 1` has one
element, `Idx 2` has two, and so on. The library deliberately uses this `Option`
tower rather than the standard library `Fin`[^fin].

[^fin]: The `Option` tower is used instead of `Fin` because `var_zero`/`shift`/
`scons` then reduce definitionally (`var_zero = none`, `shift = some`), so
substitutions compute by `rfl`; `Fin` carries a `<` proof that blocks this. -/

-- `Idx 0` is empty; `Idx 3` has three inhabitants.
example : Idx 0 = Empty := rfl
#guard_msgs (drop info) in #check (Idx 3 : Type)

/-! ## `var_zero` — the newest variable

`var_zero : Idx (n+1)` is index `0`: the variable bound by the innermost binder.
It is the `none` of the outer `Option`. It exists only in a non-empty scope. -/

example : @var_zero 2 = (none : Option (Idx 2)) := rfl
#guard_msgs (drop info) in #check (var_zero : Idx 1)   -- index 0 in a 1-scope
#guard_msgs (drop info) in #check (var_zero : Idx 5)   -- index 0 in a 5-scope

/-! ## `shift` and the `↑` notation — embedding into a larger scope

`shift : Idx n → Idx (n+1)` sends index `i` to index `i+1`. Intuitively it
"makes room" for one new binder at position `0`: every existing variable moves
one slot further out. It is the `some` of the outer `Option`.

The notation `↑` (available once `Autosubst2.Notation` is opened) abbreviates
`shift`. -/

example : (↑ : Idx 2 → Idx 3) = shift := rfl
example : @shift 2 var_zero = some var_zero := rfl

-- Building concrete indices by hand: index `2` in `Idx 3` is `shift (shift var_zero)`.
example : (shift (shift var_zero) : Idx 3) = some (some none) := rfl

/-! # Part 3. Functions out of `Idx`: maps and the sigma calculus

The central objects in Autosubst are *functions* whose domain is `Idx`:

* a **renaming** `Idx m → Idx n` relabels variables (indices to indices);
* a **substitution** `Idx m → T n` replaces variables by whole terms.

The "sigma calculus" is the small algebra of combinators for building and
composing such maps. We introduce each combinator on its own first; they apply
to renamings and substitutions alike because they are generic in the codomain.
The `>>` and `.:` notation below is global (defined in `Basic.lean`), so it is in
scope from here on.
-/

/-! ## `funcomp` and the `>>` notation — forward composition

`funcomp g f` is ordinary composition `fun x => g (f x)`. The infix form `f >> g`
is **forward** (diagrammatic) composition: do `f` first, then `g`. Note the
argument order is flipped relative to `funcomp`. -/

example {X Y Z : Type} (g : Y → Z) (f : X → Y) :
    funcomp g f = fun x => g (f x) := rfl

example {X Y Z : Type} (f : X → Y) (g : Y → Z) :
    (f >> g) = funcomp g f := rfl

-- forward order: `(f >> g) x = g (f x)`.
example {X Y Z : Type} (f : X → Y) (g : Y → Z) (x : X) :
    (f >> g) x = g (f x) := rfl

/-! ## `scons` and the `.:` notation — extending a map

`scons x f`, written `x .: f`, extends a map `f : Idx n → X` to a map
`Idx (n+1) → X` by sending the newest index `var_zero` to `x` and every shifted
index `shift i` to `f i`.

This is the workhorse for entering a binder: when you cross a `λ`, the scope
grows by one, and `x .: f` says "the fresh variable maps to `x`; everything else
follows the old map `f`". -/

example {X : Type} (x : X) (f : Idx 2 → X) :
    (x .: f) var_zero = x := rfl
example {X : Type} (x : X) (f : Idx 2 → X) (i : Idx 2) :
    (x .: f) (shift i) = f i := rfl

/-- The two computation rules are registered as `@[simp]` lemmas
`scons_var_zero` and `scons_shift`. -/
example {X : Type} (x : X) (f : Idx 2 → X) (i : Idx 2) :
    (x .: f) var_zero = x ∧ (x .: f) (shift i) = f i := by
  refine ⟨?_, ?_⟩ <;> simp only [scons_var_zero, scons_shift]

/-! ### Structural laws of `scons`

The library proves the equational theory of `scons` that the normaliser relies
on. These are pointwise (function-level) identities. -/

-- `idx_zero_eta`: any two maps out of the empty scope are equal.
example {X : Type} (f g : Idx 0 → X) : f = g := idx_zero_eta f g

-- `scons_comp`: postcomposition distributes over `scons`.
example {X Y : Type} (x : X) (f : Idx 3 → X) (g : X → Y) :
    (fun i => g ((x .: f) i)) = (g x) .: (fun i => g (f i)) := scons_comp x f g

-- `scons_eta`: a map out of `Idx (n+1)` is its head consed onto its tail.
example {X : Type} (f : Idx 4 → X) :
    (f var_zero) .: (fun i => f (shift i)) = f := scons_eta f

-- `scons_eta_id`: the eta law specialised to the identity reconstructs `id`.
example : (var_zero .: (fun i => shift i)) = (id : Idx 4 → Idx 4) := scons_eta_id

/-! ## `up_ren` — lifting a renaming under a binder

When a renaming `ρ : Idx m → Idx n` is pushed under one binder, it must become
`Idx (m+1) → Idx (n+1)`: the new variable `0` must map to the new variable `0`,
and the old variables must be renamed by `ρ` and then shifted out of the way.
This is exactly `var_zero .: (ρ >> ↑)`, packaged as `up_ren`. -/

example (ρ : Idx 2 → Idx 3) :
    up_ren ρ = var_zero .: (fun x => shift (ρ x)) := rfl

example (ρ : Idx 2 → Idx 3) : up_ren ρ var_zero = var_zero := rfl
example (ρ : Idx 2 → Idx 3) (i : Idx 2) : up_ren ρ (shift i) = shift (ρ i) := rfl

/-- `up_ren_ren`: lifting commutes with composition of renamings. If
`ρ1 ∘ ρ = ρ2` pointwise, then the same holds after lifting all three. This is the
renaming-level instance of the key "up fuses with composition" law. -/
example (ρ : Idx 1 → Idx 2) (ρ1 : Idx 2 → Idx 3) (ρ2 : Idx 1 → Idx 3)
    (E : ∀ x, ρ1 (ρ x) = ρ2 x) (x : Idx 2) :
    up_ren ρ1 (up_ren ρ x) = up_ren ρ2 x := up_ren_ren ρ ρ1 ρ2 E x

/-! # Part 4. Declaring a syntax: the `Bind` marker

We now define an object language. A well-scoped single-sort syntax is an
inductive `T : Nat → Type`. Each constructor argument is one of:

* the **variable** embedding: a single `Idx n` argument;
* a **non-recursive** argument (a constant, label, etc.);
* a **recursive** subterm. If the subterm lives under `k` new binders, its scope
  is `n + k`. Rather than writing `T (n + k)` and having the code generator infer
  `k` from index arithmetic, the library uses an explicit reducible marker
  `Bind`: `Bind T n` unfolds to `T (n + 1)`, and nesting gives depth, so
  `Bind (Bind T) n = T (n + 2)`. The generator reads `k` off the number of
  nested `Bind` heads.

Here is the untyped lambda calculus. `lam` binds one variable in its body, so the
body has type `Bind Tm n` = `Tm (n+1)`. -/

inductive Tm : Nat → Type
  | var {n : Nat} : Idx n → Tm n
  | app {n : Nat} : Tm n → Tm n → Tm n
  | lam {n : Nat} : Bind Tm n → Tm n

-- `Bind Tm n` really is `Tm (n+1)`.
example (n : Nat) : Bind Tm n = Tm (n + 1) := rfl

-- The closed identity function `λ. 0` lives in scope `0`.
example : Tm 0 := Tm.lam (Tm.var var_zero)

/-! # Part 5. Renaming

Renaming applies a relabelling `ρ : Idx m → Idx n` to every variable of a term,
recursing structurally and lifting `ρ` with `up_ren` whenever it descends under
a binder. We write it by hand here to show the shape; later the generator emits
exactly this. -/

def ren {m n : Nat} (ρ : Idx m → Idx n) : Tm m → Tm n
  | .var x => .var (ρ x)
  | .app a b => .app (ren ρ a) (ren ρ b)
  | .lam e => .lam (ren (up_ren ρ) e)

-- Renaming the body of `λ` lifts the renaming.
example {m n : Nat} (ρ : Idx m → Idx n) (e : Tm (m + 1)) :
    ren ρ (Tm.lam e) = Tm.lam (ren (up_ren ρ) e) := rfl

/-! # Part 6. Substitution

A substitution `σ : Idx m → Tm n` replaces each free variable by a term. Pushing
it under a binder requires the term-level lift `up`:

`up σ = (var var_zero) .: (σ >> ren ↑)`

i.e. the fresh variable maps to itself (as a term), and each substituted term is
shifted to make room for the new binder. Note that `up` is built from `scons`,
`ren`, and `shift` — the primitives from Parts 2–3. -/

def up {m n : Nat} (σ : Idx m → Tm n) : Idx (m + 1) → Tm (n + 1) :=
  (Tm.var var_zero) .: (fun x => ren shift (σ x))

def subst {m n : Nat} (σ : Idx m → Tm n) : Tm m → Tm n
  | .var x => σ x
  | .app a b => .app (subst σ a) (subst σ b)
  | .lam e => .lam (subst (up σ) e)

/-! ## `ids` — the identity substitution

`ids = var`: it maps each index to the variable term for that index. Substituting
with `ids` leaves a term unchanged (proved as `subst_id` below). -/

def ids {n : Nat} : Idx n → Tm n := Tm.var

example : @ids 3 = Tm.var := rfl

/-! ## `subst0` — single-variable (β) substitution

The most common operation is replacing just the newest variable, as in a β-redex
`(λ. e) u → e[u/0]`. This is `subst (u .: ids) e`: the fresh variable `0` maps to
`u`, and every other variable `i+1` maps back to `i` (via `ids` after the cons).
It is packaged as `subst0`. -/

def subst0 {n : Nat} (e : Tm (n + 1)) (u : Tm n) : Tm n :=
  subst (u .: ids) e

/-! # Part 7. The `Subst` instance and the substitution notation

The three primitives — `var`, `ren`, `subst` — now exist, so we can register a
`Subst Tm` instance and switch on the substitution notation. The notation is
generic over any `Subst` instance; the typeclass itself is detailed in Part 9.

```
class Subst (T : Nat → Type) where
  vr    : {n : Nat} → Idx n → T n          -- variable embedding (ids)
  ren   : {m n : Nat} → (Idx m → Idx n) → T m → T n
  subst : {m n : Nat} → (Idx m → T n) → T m → T n
```
-/

instance : Subst Tm where
  vr := Tm.var
  ren := ren
  subst := subst

/-! With the instance in place, `Autosubst2.Notation` (opened at the top of the
file) provides:

| Notation | Meaning              | Operation               |
|----------|----------------------|-------------------------|
| `e[σ]`   | `Subst.subst σ e`    | substitution (Part 6)   |
| `e⟨ρ⟩`   | `Subst.ren ρ e`      | renaming (Part 5)       |
| `s..`    | `scons s Subst.vr`   | single-variable subst   |
| `↑`      | `shift`              | shift (Part 2)          |

For our instance the typeclass operations are *definitionally* the bare ones, so
each notation unfolds to the hand-written function. We show both forms once: -/

example (σ : Idx 2 → Tm 3) (e : Tm 2) : e[σ] = subst σ e := rfl
example (ρ : Idx 2 → Idx 3) (e : Tm 2) : e⟨ρ⟩ = ren ρ e := rfl
example {n : Nat} (s : Tm n) : s.. = scons s ids := rfl

-- `s..` is exactly the map used by single-variable substitution: `e[s..] = subst0 e s`.
example {n : Nat} (e : Tm (n + 1)) (s : Tm n) : e[s..] = subst0 e s := rfl

/-- `e⟨ρ⟩` and `e[σ]` are both precedence 75, left-associative, so chains nest
leftward and mix freely. -/
example (ρ : Idx 1 → Idx 2) (ρ1 : Idx 2 → Idx 3) (e : Tm 1) :
    e⟨ρ⟩⟨ρ1⟩ = ren ρ1 (ren ρ e) := rfl
example (σ : Idx 1 → Tm 2) (σ1 : Idx 2 → Tm 3) (e : Tm 1) :
    e[σ][σ1] = subst σ1 (subst σ e) := rfl
example (ρ : Idx 1 → Idx 2) (σ1 : Idx 2 → Tm 3) (e : Tm 1) :
    e⟨ρ⟩[σ1] = subst σ1 (ren ρ e) := rfl

/-! From here on we state everything in notation.

A few worked computations:

* `subst0 (var 0) u = u` reads `(var 0)[u..] = u`;
* a β-step `(0 0)[λ.0 / 0]` reads `(var 0 · var 0)[(λ.0)..]`. -/

example {n : Nat} (u : Tm n) : (Tm.var var_zero)[u..] = u := rfl

example :
    (Tm.app (Tm.var var_zero) (Tm.var var_zero))[(Tm.lam (Tm.var var_zero) : Tm 0)..]
      = Tm.app (Tm.lam (Tm.var var_zero)) (Tm.lam (Tm.var var_zero)) := rfl

/-! # Part 8. The sigma-lemma chain

The point of the sigma calculus is that all the laws relating renaming,
substitution, lifting, `ids`, and `..` hold, and any composition of
substitutions/renamings normalises to a single `[·]` (or `⟨·⟩`) applied to a
fused map. The library establishes the following chain, stated here in notation.
We prove the first one to show the induction pattern; the rest follow the
identical scheme and are emitted automatically by the code generator (Part 11). -/

/-- Two renamings fuse into one: `t⟨ρ⟩⟨ρ1⟩ = t⟨ρ >> ρ1⟩`. The proof is by
structural induction: `var` is `rfl`, congruence cases recurse with the induction
hypothesis, and the binder case additionally uses `up_ren_ren` to fuse the lifted
renamings. (We drive the induction on the bare `ren`; the notation restatement
below is the same theorem, since `e⟨ρ⟩` is definitionally `ren ρ e`.) -/
theorem ren_ren {m n k : Nat} (ρ : Idx m → Idx n) (ρ1 : Idx n → Idx k) :
    ∀ t : Tm m, ren ρ1 (ren ρ t) = ren (fun x => ρ1 (ρ x)) t
  | .var _ => rfl
  | .app a b => by simp only [ren]; rw [ren_ren, ren_ren]
  | .lam e => by
    simp only [ren]
    rw [ren_ren]
    have h : (fun x => up_ren ρ1 (up_ren ρ x)) = up_ren (fun x => ρ1 (ρ x)) := by
      funext x; exact up_ren_ren ρ ρ1 _ (fun _ => rfl) x
    rw [h]

-- The same law, in notation.
example {m n k : Nat} (ρ : Idx m → Idx n) (ρ1 : Idx n → Idx k) (t : Tm m) :
    t⟨ρ⟩⟨ρ1⟩ = t⟨ρ >> ρ1⟩ := ren_ren ρ ρ1 t

/-! The full chain, with the role of each law (all stated in notation):

* `ren_ren`        : `t⟨ρ⟩⟨ρ1⟩ = t⟨ρ >> ρ1⟩`            (fuse ren∘ren)
* `subst_ren`      : `t⟨ρ⟩[σ] = t[ρ >> σ]`              (fuse subst∘ren)
* `ren_subst`      : `t[σ]⟨ρ⟩ = t[fun x => (σ x)⟨ρ⟩]`   (fuse ren∘subst)
* `subst_subst`    : `t[σ][σ1] = t[fun x => (σ x)[σ1]]` (fuse subst∘subst)
* `up_ids`         : `up ids = ids`                     (lift of identity)
* `subst_id`       : `t[ids] = t`                       (identity law)
* `ren_id`         : `t⟨id⟩ = t`                        (identity renaming)
* `subst0_subst_up`: `(e[up σ])[u..] = e[u .: σ]`       (headline β law)

The "up-commutation" helpers (`up_up_ren`, `up_ren_subst`, `up_subst`) are the
binder-case lemmas that make each fusion go through; they are also generated.

The headline law `subst0_subst_up` is what a β-reduction proof needs: it says
that instantiating a body that was itself built by substituting under a binder is
the same as one combined substitution `u .: σ`. -/

/-! # Part 9. The `Subst` typeclass, generically

Everything above is monomorphic in `Tm`. To write the notation and the `asimpl`
tactic once and reuse them for every syntax, the library abstracts the three
primitive operations into the `Subst` class shown in Part 7. Only `vr`/`ren`/
`subst` are fields. The derived operations are **generic library definitions**
over `Subst T`, not fields:

* `Subst.ids = Subst.vr`              (identity substitution)
* `Subst.up σ = (vr var_zero) .: (σ >> ren ↑)`
* `Subst.subst0 e u = subst (u .: vr) e`

These are definitionally equal to our hand-written `up`/`ids`/`subst0`, which is
exactly why the instance's fields can point straight at the bare operations: -/

example {n : Nat} (e : Tm (n + 1)) (u : Tm n) : Subst.subst0 e u = subst0 e u := rfl
example {m n : Nat} (σ : Idx m → Tm n) : Subst.up σ = up σ := rfl
example {n : Nat} : (Subst.ids : Idx n → Tm n) = ids := rfl

/-! # Part 10. The `asimpl` tactic and the `autosubst` simp set

`asimpl` is the substitution normaliser, a Lean port of Autosubst 2's tactic of
the same name. It is a curated, carefully oriented `simp` procedure that:

* pushes renaming/substitution through term constructors;
* **fuses** adjacent renamings/substitutions into one outer operation
  (the `ren_ren`/`subst_ren`/`ren_subst`/`subst_subst` chain);
* eliminates identity substitutions and renamings (`subst_id`, `ren_id`);
* computes `scons` applied to `var_zero`/`shift` and lifted maps.

It is built from three pieces:

* the `autosubst` simp **attribute** (`register_simp_attr autosubst`): the
  per-instance fusion/identity/op-unfold lemmas are tagged `@[autosubst]` (by the
  generator, or by hand);
* `asimpl_core`: `simp only [autosubst, Subst.* , funcomp]` — the one-shot
  rewrite that fuses and simplifies;
* `asimpl`: runs `asimpl_core`, then, when a residual goal compares two
  substitution *functions* whose argument still mentions a lift, descends with
  `congr`/`funext`, case-splits the index, computes the lift, and re-runs the
  core.

The next part derives a fresh copy of the syntax where the whole chain — and the
`@[autosubst]` tags — is generated, and shows `asimpl` closing the goals alone. -/

/-! # Part 11. The code generator `derive_autosubst%`

`derive_autosubst% T` runs after an inductive `T : Nat → Type` is defined (in the
same namespace) and emits, matching the hand-written shape exactly:

* the operations `ren`, `up`, `subst`, `ids`, `subst0`;
* a `Subst T` instance;
* the full sigma-lemma chain (`ren_ren`, `up_up_ren`, `subst_ren`,
  `up_ren_subst`, `ren_subst`, `up_subst`, `subst_subst`, `up_ids`, `subst_id`,
  `ren_eq_subst`, `ren_id`, `subst0_subst_up`) plus the per-constructor
  computation lemmas `subst_var`, `ren_var`;
* `@[autosubst]` tags on the fusion/identity/op-unfold lemmas, so `asimpl` works
  out of the box.

It analyses each constructor, classifying every explicit argument as the variable
`Idx`, a recursive subterm under `k` binders (read off the `Bind` nesting), or
"other". It requires exactly one scope index. -/

namespace Derived

inductive Tm : Nat → Type
  | var {n : Nat} : Idx n → Tm n
  | app {n : Nat} : Tm n → Tm n → Tm n
  | lam {n : Nat} : Bind Tm n → Tm n

derive_autosubst% Tm

-- All generated names exist and have the expected statements:
#guard_msgs (drop info) in #check @ren
#guard_msgs (drop info) in #check @up
#guard_msgs (drop info) in #check @subst
#guard_msgs (drop info) in #check @ids
#guard_msgs (drop info) in #check @subst0
#guard_msgs (drop info) in #check (inferInstance : Subst Tm)
#guard_msgs (drop info) in #check @ren_ren
#guard_msgs (drop info) in #check @subst_ren
#guard_msgs (drop info) in #check @ren_subst
#guard_msgs (drop info) in #check @subst_subst
#guard_msgs (drop info) in #check @up_ids
#guard_msgs (drop info) in #check @subst_id
#guard_msgs (drop info) in #check @ren_id
#guard_msgs (drop info) in #check @subst0_subst_up

/-! ## `asimpl` closes the whole chain by itself

With the generated `@[autosubst]` tags in place, each law below — stated in
notation — is proved by `asimpl` alone, no manual `rw`. -/

example {n : Nat} (t : Tm n) : t[ids] = t := by asimpl
example {n : Nat} (t : Tm n) : t⟨id⟩ = t := by asimpl

-- subst∘subst fusion
example {m n k : Nat} (σ : Idx m → Tm n) (σ1 : Idx n → Tm k) (t : Tm m) :
    t[σ][σ1] = t[fun x => (σ x)[σ1]] := by asimpl
-- ren∘ren fusion
example {m n k : Nat} (ρ : Idx m → Idx n) (ρ1 : Idx n → Idx k) (t : Tm m) :
    t⟨ρ⟩⟨ρ1⟩ = t⟨ρ >> ρ1⟩ := by asimpl
-- subst∘ren fusion
example {m n k : Nat} (σ : Idx n → Tm k) (ρ : Idx m → Idx n) (t : Tm m) :
    t⟨ρ⟩[σ] = t[ρ >> σ] := by asimpl
-- ren∘subst fusion
example {m n k : Nat} (ρ : Idx n → Idx k) (σ : Idx m → Tm n) (t : Tm m) :
    t[σ]⟨ρ⟩ = t[fun x => (σ x)⟨ρ⟩] := by asimpl
-- the headline β law (`subst0_subst_up`; `asimpl` leaves a residual `scons`, so
-- we invoke the generated lemma, to which this notation form is defeq)
example {m n : Nat} (σ : Idx m → Tm n) (e : Tm (m + 1)) (u : Tm n) :
    (e[up σ])[u..] = e[u .: σ] := subst0_subst_up σ e u

-- `asimpl` also normalises concrete terms, pushing through `app`/`lam`.
example {n : Nat} (i : Idx n) :
    (Tm.app (Tm.var i) (Tm.var i))[ids] = Tm.app (Tm.var i) (Tm.var i) := by asimpl
example {n : Nat} (t : Tm (n + 1)) : (Tm.lam t)⟨id⟩ = Tm.lam t := by asimpl

end Derived

/-! # Part 12. The unscoped backend

Some developments prefer plain `Nat` indices over the intrinsically-scoped `Idx`
tower. `derive_autosubst% (unscoped) T` takes a well-scoped *source* inductive
(used only to read off the binder structure) and emits an **unscoped** copy
`T.U : Type` whose operations use `Nat → _` maps. The runtime primitives live in
`Autosubst2.Unscoped`:

* `Unscoped.var_zero : Nat := 0`, `Unscoped.shift : Nat → Nat := Nat.succ`;
* `Unscoped.funcomp`, `Unscoped.uscons` (the `.:` for `Nat → X`),
  `Unscoped.upren` (lift of an unscoped renaming);
* the computation lemmas `uscons_zero`, `uscons_succ`, and `upren_comp`.

The generated `T.U` gets `var`, `app`, `lam`, …, plus `ren`, `up`, `subst`,
`ids`, `subst0`, `cons`, and the σ-chain (`ren_ren`, `subst_ren`, `ren_subst`,
`subst_comp`, `subst_id`, `subst0_subst_up`, …), all with `Nat`-indexed types.
Since `T.U : Type` is not of the form `Nat → Type`, it has no `Subst` instance,
so the `[·]`/`⟨·⟩` notation does not apply; the operations are used by name. -/

namespace UnscopedDemo

inductive Tm : Nat → Type
  | var {n : Nat} : Idx n → Tm n
  | app {n : Nat} : Tm n → Tm n → Tm n
  | lam {n : Nat} : Bind Tm n → Tm n

derive_autosubst% (unscoped) Tm

-- The generated type and ops are unscoped:
#guard_msgs (drop info) in #check (Tm.U : Type)
#guard_msgs (drop info) in #check (Tm.U.var : Nat → Tm.U)
#guard_msgs (drop info) in #check (Tm.U.ren : (Nat → Nat) → Tm.U → Tm.U)
#guard_msgs (drop info) in #check (Tm.U.subst : (Nat → Tm.U) → Tm.U → Tm.U)
#guard_msgs (drop info) in #check (Tm.U.subst0 : Tm.U → Tm.U → Tm.U)

-- `subst0 (var 0) u = u`, now over `Nat`.
example (u : Tm.U) : Tm.U.subst0 (.var 0) u = u := rfl
-- The headline β law, unscoped.
example (σ : Nat → Tm.U) (u : Tm.U) :
    Tm.U.subst0 (Tm.U.subst (Tm.U.up σ) (.var 0)) u
      = Tm.U.subst (Tm.U.cons u σ) (.var 0) :=
  Tm.U.subst0_subst_up σ (.var 0) u

end UnscopedDemo

/-! # Part 13. Multiple sorts (vector substitution)

`derive_autosubst%` also accepts several sorts at once, e.g.
`derive_autosubst% Ty Tm` for System F, where `Ty m` has type variables and
`Tm m n` has both type and term variables. With more than one variable sort,
substitution threads a *vector* of maps, one per sort:

```
renTm  : (Idx m → Idx m1) → (Idx n → Idx n1) → Tm m n → Tm m1 n1
substTm: (Idx m → Ty m1)  → (Idx n → Tm m1 n1) → Tm m n → Tm m1 n1
```

with per-sort identities `idsTy`, `ids` and single-substitutions `substTy0`,
`subst0`. The well-scoped types track each sort's scope separately, so a binder
that opens a type scope (`tlam`) increments only the first index, while one that
opens a term scope (`lam`) increments only the second. As with the unscoped
backend, `Tm m n : Nat → Nat → Type` is not single-sort, so the `[·]`/`⟨·⟩`
notation does not apply. The example file `Autosubst2/Examples/SysF.lean`
develops this in full; the same sigma laws and proof scheme generalise
componentwise.

# Part 14. Multi-sort robustness: cyclic mutual sorts with a shared scope

System F (Part 13) is the *DAG* case: the sorts can be ordered acyclically
(`Ty` before `Tm`), every sort owns its variable constructor, and each sort
carries its own scope, so substitution threads a *vector* of independent maps.
The generator handles a strictly more general shape, demonstrated here on the
deep-embedded `{Tm, Assn}` family of `Heifer/LogRel/Lambda/Lang.lean` (golden
reference: `Autosubst2/Examples/StateLang.lean`). It exercises five features the
SysF case never touches:

1. **Cyclic mutual sorts.** `Tm` embeds `Assn` (`produce`/`consume`) and `Assn`
   embeds `Tm` (`pts`/`eq`), so the sorts cannot be topologically ordered. The
   family is emitted as ONE `mutual` block, and so is the entire σ-lemma chain
   (so `substTm` ↔ `substAssn` and `substTm_substTm` ↔ `substAssn_substAssn`
   resolve their mutual recursion). The `induction`-based `ren_id_eq` step that
   the single-sort backend uses is skipped — it would not typecheck on a mutual
   inductive.
2. **One shared scope; substitute sort ≠ scope sort.** BOTH sorts are indexed by
   a single shared term-variable scope `k`, and substitution is a single map
   `Idx k → Tm n` that traverses BOTH sorts: `substAssn` rewrites Tm-terms inside
   an `Assn`. (Contrast SysF's per-sort vector.) Every sort's `up`/`ids`/value
   type therefore ranges in the substitute sort `Tm`, and the binder lift `upTm`
   is shared by both binders.
3. **Binder-bearing sort with NO own var constructor.** `Assn.sep_ex : Assn (k+1)
   → Assn k` is a real binder, yet `Assn` has no `Assn.var`: its variables enter
   only through embedded `Tm`. The generator detects var-less sorts and, for
   them, skips `ids`/`subst0`/the var pattern, reusing the shared substitute
   sort's `Tm.var`/`upTm`/`idsTm`.
4. **Deep-embedded payloads, not opaque ones.** The source semantics has an
   infinitary `sep_ex : (Nat → Assn) → Assn`; it is deep-embedded as a de Bruijn
   binder `Assn (k+1) → Assn k`. The pure-proposition leaf is deep-embedded as
   term equality `eq : Tm k → Tm k → Assn k` — a cross-sort, subst-traversed
   constructor — rather than an opaque `Prop` payload.
5. **`.other` verbatim payloads.** Genuinely non-syntactic fields are carried
   verbatim: `loc : Nat → Tm k` and the location of `pts : Nat → Tm k → Assn k`
   are `Nat`s, untouched by `ren`/`subst`. A *functional* constructor argument
   (a `Pi`-headed field such as `Nat → Tm k`) is instead REJECTED with an error
   asking you to deep-embed it as a binder — which is exactly why `sep_ex` is a
   `Assn (k+1)` binder and not a `Nat → Assn k` function.

```
mutual
inductive Tm : Nat → Type
  | var {k} : Idx k → Tm k        | lam {k} : Tm (k + 1) → Tm k
  | app {k} : Tm k → Tm k → Tm k  | loc {k} : Nat → Tm k
  | …                             | produce {k} : Assn k → Tm k   -- ↦ Assn
inductive Assn : Nat → Type       -- var-less, shares Tm's scope
  | emp {k} : Assn k              | pts {k} : Nat → Tm k → Assn k -- ↦ Tm
  | sep_ex {k} : Assn (k + 1) → Assn k   -- binder, reuses upTm
  | eq {k} : Tm k → Tm k → Assn k        -- deep-embedded pure prop
end
derive_autosubst% Tm Assn
```

The generated names carry sort suffixes (`renTm`/`renAssn`, `substTm`/
`substAssn`, `idsTm`, `substTm0`), but the semantics match the golden
`StateLang.lean` exactly. The checked demo of the generated theory lives in
`namespace MultiSortDemo` below; see also `Autosubst2/Tests/StateLangGen.lean`.

# Summary

Bottom to top, the library is:

1. `Idx n` — well-scoped de Bruijn indices, with `var_zero` and `shift` (`↑`).
2. The sigma combinators — `funcomp`/`>>`, `scons`/`.:`, `up_ren` — plus their
   equational laws (`scons_*`, `idx_zero_eta`, `up_ren_ren`).
3. A syntax `T : Nat → Type` using the `Bind` binder marker.
4. The operations `ren`, `up`, `subst`, `ids`, `subst0`.
5. The `Subst` instance and the `[σ]`, `⟨ρ⟩`, `s..` notation.
6. The sigma-lemma chain fusing and simplifying all compositions.
7. The `asimpl` tactic over the `autosubst` simp set.
8. The `derive_autosubst%` generator (scoped, unscoped, multi-sort backends).
-/

/-! ## Part 14, checked: the generated `{Tm, Assn}` theory -/

namespace MultiSortDemo

mutual
inductive Tm : Nat → Type
  | var {k} : Idx k → Tm k
  | lam {k} : Tm (k + 1) → Tm k
  | app {k} : Tm k → Tm k → Tm k
  | loc {k} : Nat → Tm k                 -- `.other` Nat payload, never substituted
  | produce {k} : Assn k → Tm k          -- cross-sort: embeds Assn
  | consume {k} : Assn k → Tm k

inductive Assn : Nat → Type              -- var-less; shares Tm's scope
  | emp {k} : Assn k
  | pts {k} : Nat → Tm k → Assn k        -- `.other` Nat + embedded Tm
  | star {k} : Assn k → Assn k → Assn k
  | sep_ex {k} : Assn (k + 1) → Assn k   -- binder, reuses `upTm`
  | eq {k} : Tm k → Tm k → Assn k        -- deep-embedded pure prop
end

derive_autosubst% Tm Assn

section Checks
variable {k : Nat}

-- One shared substitute map `Idx k → Tm n` for BOTH sorts (substitute ≠ scope).
#guard_msgs (drop info) in #check (renTm : (Idx k → Idx k) → Tm k → Tm k)
#guard_msgs (drop info) in #check (renAssn : (Idx k → Idx k) → Assn k → Assn k)
#guard_msgs (drop info) in #check (substTm : (Idx k → Tm k) → Tm k → Tm k)
#guard_msgs (drop info) in #check (substAssn : (Idx k → Tm k) → Assn k → Assn k)
-- `idsTm`/`substTm0` exist only for the var-bearing sort `Tm`; `Assn` reuses them.
#guard_msgs (drop info) in #check (idsTm : Idx k → Tm k)
#guard_msgs (drop info) in #check (substTm0 : Tm (k + 1) → Tm k → Tm k)

-- Mutual σ-lemmas resolve as one block.
#guard_msgs (drop info) in #check (@substTm_substTm :
  ∀ {k n p : Nat} (σ : Idx k → Tm n) (τ : Idx n → Tm p) (t : Tm k),
    substTm τ (substTm σ t) = substTm (fun x => substTm τ (σ x)) t)
#guard_msgs (drop info) in #check (@substAssn_substAssn :
  ∀ {k n p : Nat} (σ : Idx k → Tm n) (τ : Idx n → Tm p) (H : Assn k),
    substAssn τ (substAssn σ H) = substAssn (fun x => substTm τ (σ x)) H)
#guard_msgs (drop info) in #check (@subst0_subst_up :
  ∀ {k : Nat} (σ : Idx k → Tm k) (e : Tm (k + 1)) (u : Tm k),
    substTm0 (substTm (upTm σ) e) u = substTm (u .: σ) e)

-- Identity substitution is a no-op across the cycle (both sorts, generated lemmas).
example (e : Tm k) : substTm idsTm e = e := substTm_id e
example (H : Assn k) : substAssn idsTm H = H := substAssn_id H

-- `var 0` is selected by `substTm0`.
example (u : Tm k) : substTm0 (.var var_zero) u = u := rfl

-- Cross-sort traversal: substituting through `produce`/`pts` reaches the
-- embedded term, leaving the `.other` Nat location `3` verbatim.
example (u : Tm 0) :
    substTm0 (Tm.produce (.pts 3 (.var var_zero))) u = Tm.produce (.pts 3 u) := by
  simp only [substTm0, substTm, substAssn]; rfl

-- The shared binder `sep_ex` lifts with `upTm`, so identity subst stops at it too.
example (H : Assn (k + 1)) : substAssn idsTm (Assn.sep_ex H) = Assn.sep_ex H :=
  substAssn_id _

end Checks

end MultiSortDemo

end Autosubst2.Tutorial
