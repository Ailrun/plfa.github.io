---
title     : "Bisimulation: Relating reduction systems"
layout    : page
prev      : /More/
permalink : /Bisimulation/
next      : /Inference/
---

```
module plfa.part2.Bisimulation where
```

Some constructs can be defined in terms of other constructs.  In the
previous chapter, we saw how _let_ terms can be rewritten as an
application of an abstraction, and how two alternative formulations of
products — one with projections and one with case — can be formulated
in terms of each other.  In this chapter, we look at how to formalise
such claims.

Given two different systems, with different terms and reduction rules,
we define what it means to claim that one _simulates_ the other.
Let's call our two systems _source_ and _target_.  Let `M`, `N` range
over terms of the source, and `M†`, `N†` range over terms of the
target.  We define a relation

    M ~ M†

between corresponding terms of the two systems. We have a
_simulation_ of the source by the target if every reduction
in the source has a corresponding reduction sequence
in the target:

_Simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —↠ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —↠ --- N†

Sometimes we will have a stronger condition, where each reduction in the source
corresponds to a reduction (rather than a reduction sequence)
in the target:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

This stronger condition is known as _lock-step_ or _on the nose_ simulation.

We are particularly interested in the situation where there is also
a simulation from the target to the source: every reduction in the
target has a corresponding reduction sequence in the source.  This
situation is called a _bisimulation_.

Simulation is established by case analysis over all possible
reductions and all possible terms to which they are related.  For each
reduction step in the source we must show a corresponding reduction
sequence in the target.

For instance, the source might be lambda calculus with _let_
added, and the target the same system with `let` translated out.
The key rule defining our relation will be:

    M ~ M†
    N ~ N†
    --------------------------------
    let x = M in N ~ (ƛ x ⇒ N†) · M†

All the other rules are congruences: variables relate to
themselves, and abstractions and applications relate if their
components relate:

    -----
    x ~ x

    N ~ N†
    ------------------
    ƛ x ⇒ N ~ ƛ x ⇒ N†

    L ~ L†
    M ~ M†
    ---------------
    L · M ~ L† · M†

Covering the other constructs of our language — naturals,
fixpoints, products, and so on — would add little save length.

In this case, our relation can be specified by a function
from source to target:

    (x) †               =  x
    (ƛ x ⇒ N) †         =  ƛ x ⇒ (N †)
    (L · M) †           =  (L †) · (M †)
    (let x = M in N) †  =  (ƛ x ⇒ (N †)) · (M †)

And we have

    M † ≡ N
    -------
    M ~ N

and conversely. But in general we may have a relation without any
corresponding function.

This chapter formalises establishing that `~` as defined
above is a simulation from source to target.  We leave
establishing it in the reverse direction as an exercise.
Another exercise is to show the alternative formulations
of products in
Chapter [More](/More/)
are in bisimulation.


## Imports

We import our source language from
Chapter [More](/More/):
```
open import plfa.part2.More
```


## Simulation

The simulation is a straightforward formalisation of the rules
in the introduction:
```
infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

data _~_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ~` : ∀ {Γ A} {x : Γ ∋ A}
     ---------
   → ` x ~ ` x

  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
      ----------
    → ƛ N ~ ƛ N†

  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
      ---------------
    → L · M ~ L† · M†

  ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
    → M ~ M†
    → N ~ N†
      ----------------------
    → `let M N ~ (ƛ N†) · M†
```
The language in Chapter [More](/More/) has more constructs, which we could easily add.
However, leaving the simulation small lets us focus on the essence.
It's a handy technical trick that we can have a large source language,
but only bother to include in the simulation the terms of interest.

#### Exercise `_†` (practice)

Formalise the translation from source to target given in the introduction.
Show that `M † ≡ N` implies `M ~ N`, and conversely.

**Hint:** For simplicity, we focus on only a few constructs of the language,
so `_†` should be defined only on relevant terms. One way to do this is
to use a decidable predicate to pick out terms in the domain of `_†`, using
[proof by reflection](/Decidable/#proof-by-reflection).

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq using (cong; cong₂)
module Eqr = Eq.≡-Reasoning
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (fromWitness; toWitness; True)

data †-Domain : ∀ {Γ A} → Γ ⊢ A → Set where
  †-` : ∀ {Γ A} {x : Γ ∋ A}
     ---------------
   → †-Domain (` x)

  †-ƛ_ : ∀ {Γ A B} {N : Γ , A ⊢ B}
   → †-Domain N
     ---------------
   → †-Domain (ƛ N)

  †-_·_ : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
   → †-Domain L
   → †-Domain M
     ---------------
   → †-Domain (L · M)

  †-let : ∀ {Γ A B} {M : Γ ⊢ A} {N : Γ , A ⊢ B}
   → †-Domain M
   → †-Domain N
     ---------------
   → †-Domain (`let M N)

†-domain : ∀ {Γ A} (M : Γ ⊢ A)
  → Dec (†-Domain M)
†-domain (` x)                               = yes †-`
†-domain (ƛ M) with †-domain M
...               | yes DM                   = yes (†-ƛ DM)
...               | no ¬DM                   = no λ{ (†-ƛ DM) → ¬DM DM }
†-domain (M · N) with †-domain M | †-domain N
...                  | yes DM    | yes DN    = yes (†- DM · DN)
...                  | no ¬DM    | _         = no λ{ (†- DM · _)  → ¬DM DM }
...                  | _         | no ¬DN    = no λ{ (†- _  · DN) → ¬DN DN }
†-domain `zero                               = no (λ ())
†-domain (`suc M)                            = no (λ ())
†-domain (case L M N)                        = no (λ ())
†-domain (μ M)                               = no (λ ())
†-domain (con n)                             = no (λ ())
†-domain (M `* N)                            = no (λ ())
†-domain (`let M N) with †-domain M | †-domain N
...                    | yes DM     | yes DN = yes (†-let DM DN)
...                    | no ¬DM     | _      = no λ{ (†-let DM _)  → ¬DM DM }
...                    | _          | no ¬DN = no λ{ (†-let _  DN) → ¬DN DN }
†-domain `⟨ M , N ⟩                          = no (λ ())
†-domain (`proj₁ M)                          = no (λ ())
†-domain (`proj₂ N)                          = no (λ ())
†-domain (case× L M)                         = no (λ ())
†-domain (`inj₁ M)                           = no (λ ())
†-domain (`inj₂ M)                           = no (λ ())
†-domain (case⊎ M M₁ M₂)                     = no (λ ())
†-domain `tt                                 = no (λ ())
†-domain (case⊤ M M₁)                        = no (λ ())
†-domain (case⊥ M)                           = no (λ ())
†-domain `[]                                 = no (λ ())
†-domain (M `∷ M₁)                           = no (λ ())
†-domain (caseL M M₁ M₂)                     = no (λ ())

_†-by_ : ∀ {Γ A} (M : Γ ⊢ A) → †-Domain M → Γ ⊢ A
_†-by_ (` x)      †-`           = ` x
_†-by_ (ƛ M)      (†-ƛ DM)      = ƛ (M †-by DM)
_†-by_ (M · N)    (†- DM · DN)  = M †-by DM · N †-by DN
_†-by_ (`let M N) (†-let DM DN) = (ƛ N †-by DN) · M †-by DM

_† : ∀ {Γ A} (M : Γ ⊢ A) {TDM : True (†-domain M)} → Γ ⊢ A
_† M {TDM} = M †-by toWitness TDM
infix 5 _†

†→~ : ∀ {Γ A} (M : Γ ⊢ A) {TDM : True (†-domain M)}
  → ∀ {N : Γ ⊢ A} → _† M {TDM = TDM} ≡ N → M ~ N
†→~ M {TDM} M†≡N = helper M (toWitness TDM) M†≡N
  where
    helper : ∀ {Γ A} (M : Γ ⊢ A) (DM : †-Domain M)
      → ∀ {N : Γ ⊢ A} → M †-by DM ≡ N → M ~ N
    helper (` x)      †-`           refl = ~`
    helper (ƛ M)      (†-ƛ DM)      refl = ~ƛ helper M DM refl
    helper (L · M)    (†- DL · DM)  refl = helper L DL refl ~· helper M DM refl
    helper (`let L M) (†-let DL DM) refl = ~let (helper L DL refl) (helper M DM refl)

~→†-Domain : ∀ {Γ A} {M : Γ ⊢ A}
  → ∀ {N : Γ ⊢ A} → M ~ N → †-Domain M
~→†-Domain ~`           = †-`
~→†-Domain (~ƛ ~M)      = †-ƛ (~→†-Domain ~M)
~→†-Domain (~M ~· ~N)   = †- ~→†-Domain ~M · ~→†-Domain ~N
~→†-Domain (~let ~M ~N) = †-let (~→†-Domain ~M) (~→†-Domain ~N)

~→†-by : ∀ {Γ A} {M N : Γ ⊢ A} (DM : †-Domain M)
  → M ~ N
  → M †-by DM ≡ N
~→†-by †-`           ~`           = refl
~→†-by (†-ƛ DM)      (~ƛ ~M)      = cong ƛ_ (~→†-by DM ~M)
~→†-by (†- DM · DN)  (~M ~· ~N)   = cong₂ _·_ (~→†-by DM ~M) (~→†-by DN ~N)
~→†-by (†-let DM DN) (~let ~M ~N) = cong₂ _·_ (cong ƛ_ (~→†-by DN ~N)) (~→†-by DM ~M)

~→† : ∀ {Γ A} {M N : Γ ⊢ A} 
  → (~M : M ~ N)
  → _† M {TDM = fromWitness (~→†-Domain ~M)} ≡ N
~→† M~N = helper M~N
  where
    helper : ∀ {Γ A} {M N : Γ ⊢ A} {TDM : True (†-domain M)}
      → M ~ N
      → _† M {TDM = TDM} ≡ N
    helper {TDM = TDM} = ~→†-by (toWitness TDM)
```


## Simulation commutes with values

We need a number of technical results. The first is that simulation
commutes with values.  That is, if `M ~ M†` and `M` is a value then
`M†` is also a value:
```
~val : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M
    --------
  → Value M†
~val ~`           ()
~val (~ƛ ~N)      V-ƛ  =  V-ƛ
~val (~L ~· ~M)   ()
~val (~let ~M ~N) ()
```
It is a straightforward case analysis, where here the only value
of interest is a lambda abstraction.

#### Exercise `~val⁻¹` (practice)

Show that this also holds in the reverse direction: if `M ~ M†`
and `Value M†` then `Value M`.

```
~val⁻¹ : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M†
    ---------
  → Value M
~val⁻¹ (~ƛ ~M) V-ƛ = V-ƛ
```


## Simulation commutes with renaming

The next technical result is that simulation commutes with renaming.
That is, if `ρ` maps any judgment `Γ ∋ A` to a judgment `Δ ∋ A`,
and if `M ~ M†` then `rename ρ M ~ rename ρ M†`:

```
~rename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
    ----------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → rename ρ M ~ rename ρ M†)
~rename ρ (~`)          =  ~`
~rename ρ (~ƛ ~N)       =  ~ƛ (~rename (ext ρ) ~N)
~rename ρ (~L ~· ~M)    =  (~rename ρ ~L) ~· (~rename ρ ~M)
~rename ρ (~let ~M ~N)  =  ~let (~rename ρ ~M) (~rename (ext ρ) ~N)
```
The structure of the proof is similar to the structure of renaming itself:
reconstruct each term with recursive invocation, extending the environment
where appropriate (in this case, only for the body of an abstraction).


## Simulation commutes with substitution

The third technical result is that simulation commutes with substitution.
It is more complex than renaming, because where we had one renaming map
`ρ` here we need two substitution maps, `σ` and `σ†`.

The proof first requires we establish an analogue of extension.
If `σ` and `σ†` both map any judgment `Γ ∋ A` to a judgment `Δ ⊢ A`,
such that for every `x` in `Γ ∋ A` we have `σ x ~ σ† x`,
then for any `x` in `Γ , B ∋ A` we have `exts σ x ~ exts σ† x`:
```
~exts : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    --------------------------------------------------
  → (∀ {A B} → (x : Γ , B ∋ A) → exts σ x ~ exts σ† x)
~exts ~σ Z      =  ~`
~exts ~σ (S x)  =  ~rename S_ (~σ x)
```
The structure of the proof is similar to the structure of extension itself.
The newly introduced variable trivially relates to itself, and otherwise
we apply renaming to the hypothesis.

With extension under our belts, it is straightforward to show
substitution commutes.  If `σ` and `σ†` both map any judgment `Γ ∋ A`
to a judgment `Δ ⊢ A`, such that for every `x` in `Γ ∋ A` we have `σ
x ~ σ† x`, and if `M ~ M†`, then `subst σ M ~ subst σ† M†`:
```
~subst : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    ---------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → subst σ M ~ subst σ† M†)
~subst ~σ (~` {x = x})  =  ~σ x
~subst ~σ (~ƛ ~N)       =  ~ƛ (~subst (~exts ~σ) ~N)
~subst ~σ (~L ~· ~M)    =  (~subst ~σ ~L) ~· (~subst ~σ ~M)
~subst ~σ (~let ~M ~N)  =  ~let (~subst ~σ ~M) (~subst (~exts ~σ) ~N)
```
Again, the structure of the proof is similar to the structure of
substitution itself: reconstruct each term with recursive invocation,
extending the environment where appropriate (in this case, only for
the body of an abstraction).

From the general case of substitution, it is also easy to derive
the required special case.  If `N ~ N†` and `M ~ M†`, then
`N [ M ] ~ N† [ M† ]`:
```
~sub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {M M† : Γ ⊢ B}
  → N ~ N†
  → M ~ M†
    -----------------------
  → (N [ M ]) ~ (N† [ M† ])
~sub {Γ} {A} {B} ~N ~M = ~subst {Γ , B} {Γ} ~σ {A} ~N
  where
  ~σ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ _
  ~σ Z      =  ~M
  ~σ (S x)  =  ~`
```
Once more, the structure of the proof resembles the original.


## The relation is a simulation

Finally, we can show that the relation actually is a simulation.
In fact, we will show the stronger condition of a lock-step simulation.
What we wish to show is:

_Lock-step simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —→ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

We first formulate a concept corresponding to the lower leg
of the diagram, that is, its right and bottom edges:
```
data Leg {Γ A} (M† N : Γ ⊢ A) : Set where

  leg : ∀ {N† : Γ ⊢ A}
    → N ~ N†
    → M† —→ N†
      --------
    → Leg M† N
```
For our formalisation, in this case, we can use a stronger
relation than `—↠`, replacing it by `—→`.

We can now state and prove that the relation is a simulation.
Again, in this case, we can use a stronger relation than
`—↠`, replacing it by `—→`:
```
sim : ∀ {Γ A} {M M† N : Γ ⊢ A}
  → M ~ M†
  → M —→ N
    ---------
  → Leg  M† N
sim ~`              ()
sim (~ƛ ~N)         ()
sim (~L ~· ~M)      (ξ-·₁ L—→)
  with sim ~L L—→
...  | leg ~L′ L†—→                 =  leg (~L′ ~· ~M)   (ξ-·₁ L†—→)
sim (~V ~· ~M)      (ξ-·₂ VV M—→)
  with sim ~M M—→
...  | leg ~M′ M†—→                 =  leg (~V ~· ~M′)   (ξ-·₂ (~val ~V VV) M†—→)
sim ((~ƛ ~N) ~· ~V) (β-ƛ VV)        =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))
sim (~let ~M ~N)    (ξ-let M—→)
  with sim ~M M—→
...  | leg ~M′ M†—→                 =  leg (~let ~M′ ~N) (ξ-·₂ V-ƛ M†—→)
sim (~let ~V ~N)    (β-let VV)      =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))
```
The proof is by case analysis, examining each possible instance of `M ~ M†`
and each possible instance of `M —→ M†`, using recursive invocation whenever
the reduction is by a `ξ` rule, and hence contains another reduction.
In its structure, it looks a little bit like a proof of progress:

* If the related terms are variables, no reduction applies.
* If the related terms are abstractions, no reduction applies.
* If the related terms are applications, there are three subcases:
  - The source term reduces via `ξ-·₁`, in which case the target term does as well.
    Recursive invocation gives us

        L  --- —→ ---  L′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        L† --- —→ --- L′†

    from which follows:

         L · M  --- —→ ---  L′ · M
           |                   |
           |                   |
           ~                   ~
           |                   |
           |                   |
        L† · M† --- —→ --- L′† · M†

  - The source term reduces via `ξ-·₂`, in which case the target term does as well.
    Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

         V · M  --- —→ ---  V · M′
           |                  |
           |                  |
           ~                  ~
           |                  |
           |                  |
        V† · M† --- —→ --- V† · M′†

    Since simulation commutes with values and `V` is a value, `V†` is also a value.

  - The source term reduces via `β-ƛ`, in which case the target term does as well:

         (ƛ x ⇒ N) · V  --- —→ ---  N [ x := V ]
              |                           |
              |                           |
              ~                           ~
              |                           |
              |                           |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x :=  V† ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V ] ~ N† [ x := V† ]`.

* If the related terms are a let and an application of an abstraction,
  there are two subcases:

  - The source term reduces via `ξ-let`, in which case the target term
    reduces via `ξ-·₂`.  Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

        let x = M in N --- —→ --- let x = M′ in N
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N) · M  --- —→ --- (ƛ x ⇒ N) · M′

  - The source term reduces via `β-let`, in which case the target
    term reduces via `β-ƛ`:

        let x = V in N  --- —→ ---  N [ x := V ]
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x := V† ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V ] ~ N† [ x := V† ]`.


#### Exercise `sim⁻¹` (practice)

Show that we also have a simulation in the other direction, and hence that we have
a bisimulation.

```
data Leg⁻¹ {Γ A} (M N† : Γ ⊢ A) : Set where
  leg⁻¹ : ∀ {N : Γ ⊢ A}
    → M —→ N
    → N ~ N†
      --------
    → Leg⁻¹ M N†

sim⁻¹ : ∀ {Γ A} {M M† N† : Γ ⊢ A}
  → M ~ M†
  → M† —→ N†
    ---------
  → Leg⁻¹ M N†
sim⁻¹ (~L ~· ~M)      (ξ-·₁ L—→)    with sim⁻¹ ~L L—→
...                                    | leg⁻¹ N—→ ~L′ = leg⁻¹ (ξ-·₁ N—→) (~L′ ~· ~M)
sim⁻¹ (~L ~· ~M)      (ξ-·₂ VL M—→) with sim⁻¹ ~M M—→
...                                    | leg⁻¹ N—→ ~M′ = leg⁻¹ (ξ-·₂ (~val⁻¹ ~L VL) N—→) (~L ~· ~M′)
sim⁻¹ ((~ƛ ~L) ~· ~M) (β-ƛ VM)                         = leg⁻¹ (β-ƛ (~val⁻¹ ~M VM)) (~sub ~L ~M)
sim⁻¹ (~let ~M ~L)    (ξ-·₂ VL M—→) with sim⁻¹ ~M M—→
...                                    | leg⁻¹ N—→ ~M′ = leg⁻¹ (ξ-let N—→) (~let ~M′ ~L)
sim⁻¹ (~let ~M ~L)    (β-ƛ VM)                         = leg⁻¹ (β-let (~val⁻¹ ~M VM)) (~sub ~L ~M)
```

#### Exercise `products` (practice)

Show that the two formulations of products in
Chapter [More](/More/)
are in bisimulation.  The only constructs you need to include are
variables, and those connected to functions and products.
In this case, the simulation is _not_ lock-step.

```
infix  4 _~ˣ_
infix  5 ~ˣƛ_
infix  7 _~ˣ·_

data _~ˣ_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ~ˣ` : ∀ {Γ A} {x : Γ ∋ A}
     ---------
   → ` x ~ˣ ` x

  ~ˣƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ˣ N†
      ----------
    → ƛ N ~ˣ ƛ N†

  _~ˣ·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ˣ L†
    → M ~ˣ M†
      ---------------
    → L · M ~ˣ L† · M†

  ~ˣ⟨_,_⟩ : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ ⊢ B}
    → M ~ˣ M†
    → N ~ˣ N†
      ----------------------
    → `⟨ M , N ⟩ ~ˣ `⟨ M† , N† ⟩

  ~ˣproj₁ : ∀ {Γ A B} {L L† : Γ ⊢ A `× B}
    → L ~ˣ L†
      ----------------------
    → `proj₁ L ~ˣ case× L† (# 1)

  ~ˣproj₂ : ∀ {Γ A B} {L L† : Γ ⊢ A `× B}
    → L ~ˣ L†
      ----------------------
    → `proj₂ L ~ˣ case× L† (# 0)

~ˣval : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ˣ M†
  → Value M
    --------
  → Value M†
~ˣval ~ˣ`            ()
~ˣval (~ˣƛ ~M)       V-ƛ            = V-ƛ
~ˣval (~M ~ˣ· ~M₁)   ()
~ˣval ~ˣ⟨ ~M , ~M₁ ⟩ V-⟨ VM , VM₁ ⟩ = V-⟨ ~ˣval ~M VM , ~ˣval ~M₁ VM₁ ⟩
~ˣval (~ˣproj₁ ~M)   ()
~ˣval (~ˣproj₂ ~M)   ()

~ˣval⁻¹ : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ˣ M†
  → Value M†
    --------
  → Value M
~ˣval⁻¹ ~ˣ`            ()
~ˣval⁻¹ (~ˣƛ ~M)       V-ƛ              = V-ƛ
~ˣval⁻¹ (~M ~ˣ· ~M₁)   ()
~ˣval⁻¹ ~ˣ⟨ ~M , ~M₁ ⟩ V-⟨ VM† , VM†₁ ⟩ = V-⟨ ~ˣval⁻¹ ~M VM† , ~ˣval⁻¹ ~M₁ VM†₁ ⟩
~ˣval⁻¹ (~ˣproj₁ ~M)   ()
~ˣval⁻¹ (~ˣproj₂ ~M)   ()

~ˣrename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
    ----------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ˣ M† → rename ρ M ~ˣ rename ρ M†)
~ˣrename ρ ~ˣ`            = ~ˣ`
~ˣrename ρ (~ˣƛ ~M)       = ~ˣƛ ~ˣrename (ext ρ) ~M
~ˣrename ρ (~L ~ˣ· ~M)   = ~ˣrename ρ ~L ~ˣ· ~ˣrename ρ ~M
~ˣrename ρ ~ˣ⟨ ~M , ~N ⟩ = ~ˣ⟨ ~ˣrename ρ ~M , ~ˣrename ρ ~N ⟩
~ˣrename ρ (~ˣproj₁ ~L)   = ~ˣproj₁ (~ˣrename ρ ~L)
~ˣrename ρ (~ˣproj₂ ~L)   = ~ˣproj₂ (~ˣrename ρ ~L)

~ˣexts : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ˣ σ† x)
    --------------------------------------------------
  → (∀ {A B} → (x : Γ , B ∋ A) → exts σ x ~ˣ exts σ† x)
~ˣexts ~σ Z      = ~ˣ`
~ˣexts ~σ (S ∋x) = ~ˣrename S_ (~σ ∋x)

~ˣsubst : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ˣ σ† x)
    ---------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ˣ M† → subst σ M ~ˣ subst σ† M†)
~ˣsubst ~σ (~ˣ` {x = x}) = ~σ x
~ˣsubst ~σ (~ˣƛ ~M)      = ~ˣƛ ~ˣsubst (~ˣexts ~σ) ~M
~ˣsubst ~σ (~L ~ˣ· ~M)   = ~ˣsubst ~σ ~L ~ˣ· ~ˣsubst ~σ ~M
~ˣsubst ~σ ~ˣ⟨ ~M , ~N ⟩ = ~ˣ⟨ ~ˣsubst ~σ ~M , ~ˣsubst ~σ ~N ⟩
~ˣsubst ~σ (~ˣproj₁ ~L)  = ~ˣproj₁ (~ˣsubst ~σ ~L)
~ˣsubst ~σ (~ˣproj₂ ~L)  = ~ˣproj₂ (~ˣsubst ~σ ~L)

~ˣsub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {M M† : Γ ⊢ B}
  → N ~ˣ N†
  → M ~ˣ M†
    -----------------------
  → (N [ M ]) ~ˣ (N† [ M† ])
~ˣsub {Γ} {A} {B} ~N ~M = ~ˣsubst ~σ ~N
  where
    ~σ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ˣ _
    ~σ Z     = ~M
    ~σ (S x) = ~ˣ`

~ˣsub₂ : ∀ {Γ A B C} {N N† : Γ , C , B ⊢ A} {L L† : Γ ⊢ B} {M M† : Γ ⊢ C}
  → N ~ˣ N†
  → L ~ˣ L†
  → M ~ˣ M†
    -----------------------
  → (N [ M ][ L ]) ~ˣ (N† [ M† ][ L† ])
~ˣsub₂ {Γ} {A} {B} {C} ~N ~L ~M = ~ˣsubst ~σ ~N
  where
    ~σ : ∀ {A} → (x : Γ , C , B ∋ A) → _ ~ˣ _
    ~σ Z         = ~L
    ~σ (S Z)     = ~M
    ~σ (S (S x)) = ~ˣ`

data Legˣ {Γ A} (M† N : Γ ⊢ A) : Set where
  legˣ : ∀ {N† : Γ ⊢ A}
    → N ~ˣ N†
    → M† —→ N†
      ----------
    → Legˣ M† N

simˣ : ∀ {Γ A} {M M† N : Γ ⊢ A}
  → M ~ˣ M†
  → M —→ N
    ----------
  → Legˣ M† N
simˣ ~ˣ`               ()
simˣ (~ˣƛ ~M)          ()
simˣ (~L ~ˣ· ~M)       (ξ-·₁ L—→)
  with simˣ ~L L—→
... | legˣ ~N L†—→                           = legˣ (~N ~ˣ· ~M) (ξ-·₁ L†—→)
simˣ (~L ~ˣ· ~M)       (ξ-·₂ VL M—→)
  with simˣ ~M M—→
... | legˣ ~N M†—→                           = legˣ (~L ~ˣ· ~N) (ξ-·₂ (~ˣval ~L VL) M†—→)
simˣ ((~ˣƛ ~L) ~ˣ· ~M) (β-ƛ VM)              = legˣ (~ˣsub ~L ~M) (β-ƛ (~ˣval ~M VM))
simˣ ~ˣ⟨ ~L , ~M ⟩     (ξ-⟨,⟩₁ L—→)
  with simˣ ~L L—→
...  | legˣ ~N L†—→                          = legˣ ~ˣ⟨ ~N , ~M ⟩ (ξ-⟨,⟩₁ L†—→)
simˣ ~ˣ⟨ ~L , ~M ⟩     (ξ-⟨,⟩₂ VL M—→)
  with simˣ ~M M—→
...  | legˣ ~N M†—→                          = legˣ ~ˣ⟨ ~L , ~N ⟩ (ξ-⟨,⟩₂ (~ˣval ~L VL) M†—→)
simˣ (~ˣproj₁ ~L)      (ξ-proj₁ L—→)
  with simˣ ~L L—→
...  | legˣ ~N L†—→                          = legˣ (~ˣproj₁ ~N) (ξ-case× L†—→)
simˣ (~ˣproj₁ ~ˣ⟨ ~M , ~N ⟩) (β-proj₁ VV VW) = legˣ ~M (β-case× (~ˣval ~M VV) (~ˣval ~N VW))
simˣ (~ˣproj₂ ~L)      (ξ-proj₂ L—→)
  with simˣ ~L L—→
...  | legˣ ~N L†—→                          = legˣ (~ˣproj₂ ~N) (ξ-case× L†—→)
simˣ (~ˣproj₂ ~ˣ⟨ ~M , ~N ⟩) (β-proj₂ VV VW) = legˣ ~N (β-case× (~ˣval ~M VV) (~ˣval ~N VW))

data Legˣ⁻¹ {Γ A} (M N† : Γ ⊢ A) : Set where
  legˣ⁻¹ : ∀ {N : Γ ⊢ A}
    → M —→ N
    → N ~ˣ N†
      ----------
    → Legˣ⁻¹ M N†

simˣ⁻¹ : ∀ {Γ A} {M M† N† : Γ ⊢ A}
  → M ~ˣ M†
  → M† —→ N†
    -----------
  → Legˣ⁻¹ M N†
simˣ⁻¹ ~ˣ`          ()
simˣ⁻¹ (~ˣƛ ~M)     ()
simˣ⁻¹ (~L ~ˣ· ~M) (ξ-·₁ L†—→)
  with simˣ⁻¹ ~L L†—→
...  | legˣ⁻¹ L—→ ~N                           = legˣ⁻¹ (ξ-·₁ L—→) (~N ~ˣ· ~M)
simˣ⁻¹ (~L ~ˣ· ~M) (ξ-·₂ VL M†—→)
  with simˣ⁻¹ ~M M†—→
...  | legˣ⁻¹ M—→ ~N                           = legˣ⁻¹ (ξ-·₂ (~ˣval⁻¹ ~L VL) M—→) (~L ~ˣ· ~N)
simˣ⁻¹ ((~ˣƛ ~L) ~ˣ· ~M) (β-ƛ VM)              = legˣ⁻¹ (β-ƛ (~ˣval⁻¹ ~M VM)) (~ˣsub ~L ~M)
simˣ⁻¹ ~ˣ⟨ ~L , ~M ⟩ (ξ-⟨,⟩₁ L†—→)
  with simˣ⁻¹ ~L L†—→
...  | legˣ⁻¹ L—→ ~N                           = legˣ⁻¹ (ξ-⟨,⟩₁ L—→) ~ˣ⟨ ~N , ~M ⟩
simˣ⁻¹ ~ˣ⟨ ~L , ~M ⟩ (ξ-⟨,⟩₂ VL M†—→)
  with simˣ⁻¹ ~M M†—→
...  | legˣ⁻¹ M—→ ~N                           = legˣ⁻¹ (ξ-⟨,⟩₂ (~ˣval⁻¹ ~L VL) M—→) ~ˣ⟨ ~L , ~N ⟩
simˣ⁻¹ (~ˣproj₁ ~L) (ξ-case× L†—→)
  with simˣ⁻¹ ~L L†—→
...  | legˣ⁻¹ L—→ ~N                           = legˣ⁻¹ (ξ-proj₁ L—→) (~ˣproj₁ ~N)
simˣ⁻¹ (~ˣproj₁ ~ˣ⟨ ~V , ~W ⟩) (β-case× VV VW) = legˣ⁻¹ (β-proj₁ (~ˣval⁻¹ ~V VV) (~ˣval⁻¹ ~W VW)) ~V
simˣ⁻¹ (~ˣproj₂ ~L) (ξ-case× L†—→)
  with simˣ⁻¹ ~L L†—→
...  | legˣ⁻¹ L—→ ~N                           = legˣ⁻¹ (ξ-proj₂ L—→) (~ˣproj₂ ~N)
simˣ⁻¹ (~ˣproj₂ ~ˣ⟨ ~V , ~W ⟩) (β-case× VV VW) = legˣ⁻¹ (β-proj₂ (~ˣval⁻¹ ~V VV) (~ˣval⁻¹ ~W VW)) ~W
```

## Unicode

This chapter uses the following unicode:

    †  U+2020  DAGGER (\dag)
    ⁻  U+207B  SUPERSCRIPT MINUS (\^-)
    ¹  U+00B9  SUPERSCRIPT ONE (\^1)
