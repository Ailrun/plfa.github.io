---
title     : "Inference: Bidirectional type inference"
layout    : page
prev      : /Bisimulation/
permalink : /Inference/
next      : /Untyped/
---

```
module plfa.part2.Inference where
```

So far in our development, type derivations for the corresponding
term have been provided by fiat.
In Chapter [Lambda](/Lambda/)
type derivations are extrinsic to the term, while
in Chapter [DeBruijn](/DeBruijn/)
type derivations are intrinsic to the term,
but in both we have written out the type derivations in full.

In practice, one often writes down a term with a few decorations and
applies an algorithm to _infer_ the corresponding type derivation.
Indeed, this is exactly what happens in Agda: we specify the types for
top-level function declarations, and type information for everything
else is inferred from what has been given.  The style of inference
Agda uses is based on a technique called _bidirectional_ type
inference, which will be presented in this chapter.

This chapter ties our previous developments together. We begin with
a term with some type annotations, close to the raw terms of
Chapter [Lambda](/Lambda/),
and from it we compute an intrinsically-typed term, in the style of
Chapter [DeBruijn](/DeBruijn/).

## Introduction: Inference rules as algorithms {name=algorithms}

In the calculus we have considered so far, a term may have more than
one type.  For example,

    (ƛ x ⇒ x) ⦂ (A ⇒ A)

holds for _every_ type `A`.  We start by considering a small language for
lambda terms where every term has a unique type.  All we need do
is decorate each abstraction term with the type of its argument.
This gives us the grammar:

    L, M, N ::=                         decorated terms
      x                                   variable
      ƛ x ⦂ A ⇒ N                         abstraction (decorated)
      L · M                               application

Each of the associated type rules can be read as an algorithm for
type checking.  For each typing judgment, we label each position
as either an _input_ or an _output_.

For the judgment

    Γ ∋ x ⦂ A

we take the context `Γ` and the variable `x` as inputs, and the
type `A` as output.  Consider the rules:

    ----------------- Z
    Γ , x ⦂ A ∋ x ⦂ A

    Γ ∋ x ⦂ A
    ----------------- S
    Γ , y ⦂ B ∋ x ⦂ A

From the inputs we can determine which rule applies: if the last
variable in the context matches the given variable then the first
rule applies, else the second.  (For de Bruijn indices, it is even
easier: zero matches the first rule and successor the second.)
For the first rule, the output type can be read off as the last
type in the input context. For the second rule, the inputs of the
conclusion determine the inputs of the hypothesis, and the output
of the hypothesis determines the output of the conclusion.

For the judgment

    Γ ⊢ M ⦂ A

we take the context `Γ` and term `M` as inputs, and the type `A`
as output. Consider the rules:

    Γ ∋ x ⦂ A
    -----------
    Γ ⊢ ` x ⦂ A

    Γ , x ⦂ A ⊢ N ⦂ B
    ---------------------------
    Γ ⊢ (ƛ x ⦂ A ⇒ N) ⦂ (A ⇒ B)

    Γ ⊢ L ⦂ A ⇒ B
    Γ ⊢ M ⦂ A′
    A ≡ A′
    -------------
    Γ ⊢ L · M ⦂ B

The input term determines which rule applies: variables use the first
rule, abstractions the second, and applications the third.  We say
such rules are _syntax directed_.  For the variable rule, the inputs
of the conclusion determine the inputs of the hypothesis, and the
output of the hypothesis determines the output of the conclusion.
Same for the abstraction rule — the bound variable and argument are
carried from the term of the conclusion into the context of the
hypothesis; this works because we added the argument type to the
abstraction.  For the application rule, we add a third hypothesis to
check whether the domain of the function matches the type of the
argument; this judgment is decidable when both types are given as
inputs. The inputs of the conclusion determine the inputs of the first
two hypotheses, the outputs of the first two hypotheses determine the
inputs of the third hypothesis, and the output of the first hypothesis
determines the output of the conclusion.

Converting the above to an algorithm is straightforward, as is adding
naturals and fixpoint.  We omit the details.  Instead, we consider a
detailed description of an approach that requires less obtrusive
decoration.  The idea is to break the normal typing judgment into two
judgments, one that produces the type as an output (as above), and
another that takes it as an input.


## Synthesising and inheriting types

In addition to the lookup judgment for variables, which will remain
as before, we now have two judgments for the type of the term:

    Γ ⊢ M ↑ A
    Γ ⊢ M ↓ A

The first of these _synthesises_ the type of a term, as before,
while the second _inherits_ the type.  In the first, the context
and term are inputs and the type is an output; while in the
second, all three of the context, term, and type are inputs.

Which terms use synthesis and which inheritance?  Our approach will be
that the main term in a _deconstructor_ is typed via synthesis while
_constructors_ are typed via inheritance.  For instance, the function in
an application is typed via synthesis, but an abstraction is typed via
inheritance.  The inherited type in an abstraction term serves the
same purpose as the argument type decoration of the previous section.

Terms that deconstruct a value of a type always have a main term
(supplying an argument of the required type) and often have
side-terms.  For application, the main term supplies the function and
the side term supplies the argument.  For case terms, the main term
supplies a natural and the side terms are the two branches.  In a
deconstructor, the main term will be typed using synthesis but the
side terms will be typed using inheritance.  As we will see, this
leads naturally to an application as a whole being typed by synthesis,
while a case term as a whole will be typed by inheritance.
Variables are naturally typed by synthesis, since we can look up
the type in the input context.  Fixed points will be naturally
typed by inheritance.

In order to get a syntax-directed type system we break terms into two
kinds, `Term⁺` and `Term⁻`, which are typed by synthesis and
inheritance, respectively.  A subterm that is typed
by synthesis may appear in a context where it is typed by inheritance,
or vice-versa, and this gives rise to two new term forms.

For instance, we said above that the argument of an application is
typed by inheritance and that variables are typed by synthesis, giving
a mismatch if the argument of an application is a variable.  Hence, we
need a way to treat a synthesized term as if it is inherited.  We
introduce a new term form, `M ↑` for this purpose.  The typing judgment
checks that the inherited and synthesised types match.

Similarly, we said above that the function of an application is typed
by synthesis and that abstractions are typed by inheritance, giving a
mismatch if the function of an application is an abstraction.  Hence, we
need a way to treat an inherited term as if it is synthesised.  We
introduce a new term form `M ↓ A` for this purpose.  The typing
judgment returns `A` as the synthesized type of the term as a whole,
as well as using it as the inherited type for `M`.

The term form `M ↓ A` represents the only place terms need to be
decorated with types.  It only appears when switching from synthesis
to inheritance, that is, when a term that _deconstructs_ a value of a
type contains as its main term a term that _constructs_ a value of a
type, in other words, a place where a `β`-reduction will occur.
Typically, we will find that decorations are only required on top
level declarations.

We can extract the grammar for terms from the above:

    L⁺, M⁺, N⁺ ::=                      terms with synthesized type
      x                                   variable
      L⁺ · M⁻                             application
      M⁻ ↓ A                              switch to inherited

    L⁻, M⁻, N⁻ ::=                      terms with inherited type
      ƛ x ⇒ N⁻                            abstraction
      `zero                               zero
      `suc M⁻                             successor
      case L⁺ [zero⇒ M⁻ |suc x ⇒ N⁻ ]     case
      μ x ⇒ N⁻                            fixpoint
      M⁺ ↑                                switch to synthesized

We will formalise the above shortly.


## Soundness and completeness

What we intend to show is that the typing judgments are
_decidable_:

    synthesize : ∀ (Γ : Context) (M : Term⁺)
        -----------------------
      → Dec (∃[ A ](Γ ⊢ M ↑ A))

    inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type)
        ---------------
      → Dec (Γ ⊢ M ↓ A)

Given context `Γ` and synthesised term `M`, we must decide whether
there exists a type `A` such that `Γ ⊢ M ↑ A` holds, or its negation.
Similarly, given context `Γ`, inherited term `M`, and type `A`, we
must decide whether `Γ ⊢ M ↓ A` holds, or its negation.

Our proof is constructive. In the synthesised case, it will either
deliver a pair of a type `A` and evidence that `Γ ⊢ M ↓ A`, or a function
that given such a pair produces evidence of a contradiction. In the inherited
case, it will either deliver evidence that `Γ ⊢ M ↑ A`, or a function
that given such evidence produces evidence of a contradiction.
The positive case is referred to as _soundness_ --- synthesis and inheritance
succeed only if the corresponding relation holds.  The negative case is
referred to as _completeness_ --- synthesis and inheritance fail only when
they cannot possibly succeed.

Another approach might be to return a derivation if synthesis or
inheritance succeeds, and an error message otherwise --- for instance,
see the section of the Agda user manual discussing
[syntactic sugar](https://agda.readthedocs.io/en/latest/language/syntactic-sugar.html#example).
Such an approach demonstrates soundness, but not completeness.  If it
returns a derivation, we know it is correct; but there is nothing to
prevent us from writing a function that _always_ returns an error,
even when there exists a correct derivation.  Demonstrating both
soundness and completeness is significantly stronger than
demonstrating soundness alone.  The negative proof can be thought of
as a semantically verified error message, although in practice it
may be less readable than a well-crafted error message.

We are now ready to begin the formal development.


## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.String using (String; _≟_)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
```

Once we have a type derivation, it will be easy to construct
from it the intrinsically-typed representation.  In order that we
can compare with our previous development, we import
module `plfa.part2.More`:

```
import plfa.part2.More as DB
```

The phrase `as DB` allows us to refer to definitions
from that module as, for instance, `DB._⊢_`, which is
invoked as `Γ DB.⊢ A`, where `Γ` has type
`DB.Context` and `A` has type `DB.Type`.


## Syntax

First, we get all our infix declarations out of the way.
We list separately operators for judgments and terms:

```
infix   4  _∋_⦂_
infix   4  _⊢_↑_
infix   4  _⊢_↓_
infixl  5  _,_⦂_

infixr  7  _⇒_

infix   5  ƛ_⇒_
infix   5  μ_⇒_
infix   6  _↑
infix   6  _↓_
infixl  7  _·_
infix   8  `suc_
infix   9  `_
```

Identifiers, types, and contexts are as before:
```
Id : Set
Id = String

data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context
```

The syntax of terms is defined by mutual recursion.
We use `Term⁺` and `Term⁻`
for terms with synthesized and inherited types, respectively.
Note the inclusion of the switching forms,
`M ↓ A` and `M ↑`:
```
data Term⁺ : Set
data Term⁻ : Set

data Term⁺ where
  `_                        : Id → Term⁺
  _·_                       : Term⁺ → Term⁻ → Term⁺
  _↓_                       : Term⁻ → Type → Term⁺

data Term⁻ where
  ƛ_⇒_                     : Id → Term⁻ → Term⁻
  `zero                    : Term⁻
  `suc_                    : Term⁻ → Term⁻
  `case_[zero⇒_|suc_⇒_]    : Term⁺ → Term⁻ → Id → Term⁻ → Term⁻
  μ_⇒_                     : Id → Term⁻ → Term⁻
  _↑                       : Term⁺ → Term⁻
```
The choice as to whether each term is synthesized or
inherited follows the discussion above, and can be read
off from the informal grammar presented earlier.  Main terms in
deconstructors synthesise, constructors and side terms
in deconstructors inherit.

## Example terms

We can recreate the examples from preceding chapters.
First, computing two plus two on naturals:
```
two : Term⁻
two = `suc (`suc `zero)

plus : Term⁺
plus = (μ "p" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
          `case (` "m") [zero⇒ ` "n" ↑
                        |suc "m" ⇒ `suc (` "p" · (` "m" ↑) · (` "n" ↑) ↑) ])
            ↓ (`ℕ ⇒ `ℕ ⇒ `ℕ)

2+2 : Term⁺
2+2 = plus · two · two
```
The only change is to decorate with down and up arrows as required.
The only type decoration required is for `plus`.

Next, computing two plus two with Church numerals:
```
Ch : Type
Ch = (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ

twoᶜ : Term⁻
twoᶜ = (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · (` "z" ↑) ↑) ↑)

plusᶜ : Term⁺
plusᶜ = (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
           ` "m" · (` "s" ↑) · (` "n" · (` "s" ↑) · (` "z" ↑) ↑) ↑)
             ↓ (Ch ⇒ Ch ⇒ Ch)

sucᶜ : Term⁻
sucᶜ = ƛ "x" ⇒ `suc (` "x" ↑)

2+2ᶜ : Term⁺
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
```
The only type decoration required is for `plusᶜ`.  One is not even
required for `sucᶜ`, which inherits its type as an argument of `plusᶜ`.

## Bidirectional type checking

The typing rules for variables are as in
[Lambda](/Lambda/):
```
data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      --------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      -----------------
    → Γ , y ⦂ B ∋ x ⦂ A
```

As with syntax, the judgments for synthesizing
and inheriting types are mutually recursive:
```
data _⊢_↑_ : Context → Term⁺ → Type → Set
data _⊢_↓_ : Context → Term⁻ → Type → Set

data _⊢_↑_ where

  ⊢` : ∀ {Γ A x}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ↑ A

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ↑ A ⇒ B
    → Γ ⊢ M ↓ A
      -------------
    → Γ ⊢ L · M ↑ B

  ⊢↓ : ∀ {Γ M A}
    → Γ ⊢ M ↓ A
      ---------------
    → Γ ⊢ (M ↓ A) ↑ A

data _⊢_↓_ where

  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ↓ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ↓ A ⇒ B

  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ↓ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ↓ `ℕ
      ---------------
    → Γ ⊢ `suc M ↓ `ℕ

  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ↑ `ℕ
    → Γ ⊢ M ↓ A
    → Γ , x ⦂ `ℕ ⊢ N ↓ A
      -------------------------------------
    → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ↓ A

  ⊢μ : ∀ {Γ x N A}
    → Γ , x ⦂ A ⊢ N ↓ A
      -----------------
    → Γ ⊢ μ x ⇒ N ↓ A

  ⊢↑ : ∀ {Γ M A B}
    → Γ ⊢ M ↑ A
    → A ≡ B
      -------------
    → Γ ⊢ (M ↑) ↓ B
```
We follow the same convention as
Chapter [Lambda](/Lambda/),
prefacing the constructor with `⊢` to derive the name of the
corresponding type rule.

The rules are similar to those in
Chapter [Lambda](/Lambda/),
modified to support synthesised and inherited types.
The two new rules are those for `⊢↓` and `⊢↑`.
The former both passes the type decoration as the inherited type and returns
it as the synthesised type.  The latter takes the synthesised type and the
inherited type and confirms they are identical --- it should remind you of
the equality test in the application rule in the first
[section](/Inference/#algorithms).


#### Exercise `bidirectional-mul` (recommended) {name=bidirectional-mul}

Rewrite your definition of multiplication from
Chapter [Lambda](/Lambda/), decorated to support inference.

```
mul : Term⁺
mul = (μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         `case (` "m") [zero⇒ `zero
                       |suc "m" ⇒ plus · (` "n" ↑) · (` "*" · (` "m" ↑) · (` "n" ↑) ↑) ↑ ])
           ↓ (`ℕ ⇒ `ℕ ⇒ `ℕ)
```


#### Exercise `bidirectional-products` (recommended) {name=bidirectional-products}

Extend the bidirectional type rules to include products from
Chapter [More](/More/).

```
infix  4  _∋_⦂′_
infix  4  _⊢_↑′_
infix  4  _⊢_↓′_

infixr 7  _⇒′_
infixl 8 _`×′_

data Type′ : Set where
  `ℕ   : Type′
  _⇒′_ : Type′ → Type′ → Type′
  _`×′_ : Type′ → Type′ → Type′

data Context′ : Set where
  ∅     : Context′
  _,_⦂_ : Context′ → Id → Type′ → Context′

data _∋_⦂′_ : Context′ → Id → Type′ → Set where
  Z : ∀ {Γ x A}
      --------------------
    → Γ , x ⦂ A ∋ x ⦂′ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂′ A
      -----------------
    → Γ , y ⦂ B ∋ x ⦂′ A

data Term⁺′ : Set
data Term⁻′ : Set

data Term⁺′ where
  `_     : Id → Term⁺′
  _·_    : Term⁺′ → Term⁻′ → Term⁺′
  `proj₁ : Term⁺′ → Term⁺′
  `proj₂ : Term⁺′ → Term⁺′
  _↓_    : Term⁻′ → Type′ → Term⁺′

data Term⁻′ where
  ƛ_⇒_                  : Id → Term⁻′ → Term⁻′
  `zero                 : Term⁻′
  `suc_                 : Term⁻′ → Term⁻′
  `case_[zero⇒_|suc_⇒_] : Term⁺′ → Term⁻′ → Id → Term⁻′ → Term⁻′
  μ_⇒_                  : Id → Term⁻′ → Term⁻′
  `⟨_,_⟩                : Term⁻′ → Term⁻′ → Term⁻′
  `case×_[⟨_,_⟩⇒_]      : Term⁺′ → Id → Id → Term⁻′ → Term⁻′
  _↑                    : Term⁺′ → Term⁻′

data _⊢_↑′_ : Context′ → Term⁺′ → Type′ → Set
data _⊢_↓′_ : Context′ → Term⁻′ → Type′ → Set

data _⊢_↑′_ where
  ⊢` : ∀ {Γ A x}
    → Γ ∋ x ⦂′ A
      -----------
    → Γ ⊢ ` x ↑′ A

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ↑′ A ⇒′ B
    → Γ ⊢ M ↓′ A
      -------------
    → Γ ⊢ L · M ↑′ B

  ⊢proj₁ : ∀ {Γ L A B}
    → Γ ⊢ L ↑′ A `×′ B
      -------------
    → Γ ⊢ `proj₁ L ↑′ A

  ⊢proj₂ : ∀ {Γ L A B}
    → Γ ⊢ L ↑′ A `×′ B
      -------------
    → Γ ⊢ `proj₂ L ↑′ B

  ⊢↓ : ∀ {Γ M A}
    → Γ ⊢ M ↓′ A
      ---------------
    → Γ ⊢ (M ↓ A) ↑′ A

data _⊢_↓′_ where
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ↓′ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ↓′ A ⇒′ B

  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ↓′ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ↓′ `ℕ
      ---------------
    → Γ ⊢ `suc M ↓′ `ℕ

  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ↑′ `ℕ
    → Γ ⊢ M ↓′ A
    → Γ , x ⦂ `ℕ ⊢ N ↓′ A
      -------------------------------------
    → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ↓′ A

  ⊢μ : ∀ {Γ x N A}
    → Γ , x ⦂ A ⊢ N ↓′ A
      -----------------
    → Γ ⊢ μ x ⇒ N ↓′ A

  `⟨_,_⟩ : ∀ {Γ M N A B}
    → Γ ⊢ M ↓′ A
    → Γ ⊢ N ↓′ B
      -------------------------
    → Γ ⊢ `⟨ M , N ⟩ ↓′ A `×′ B

  ⊢case× : ∀ {Γ L x y M A B C}
    → Γ ⊢ L ↑′ A `×′ B
    → Γ , x ⦂ A , y ⦂ B ⊢ M ↓′ C
      ----------------------------------
    → Γ ⊢ `case× L [⟨ x , y ⟩⇒ M ] ↓′ C

  ⊢↑ : ∀ {Γ M A B}
    → Γ ⊢ M ↑′ A
    → A ≡ B
      -------------
    → Γ ⊢ (M ↑) ↓′ B
```


#### Exercise `bidirectional-rest` (stretch)

Extend the bidirectional type rules to include the rest of the constructs from
Chapter [More](/More/).

```
infix  4  _∋_⦂′′_
infix  4  _⊢_↑′′_
infix  4  _⊢_↓′′_

infixr 7  _⇒′′_
infixl 8 _`×′′_
infixr 8  _`⊎_

data Type′′ : Set where
  `ℕ     : Type′′
  _⇒′′_  : Type′′ → Type′′ → Type′′
  _`×′′_ : Type′′ → Type′′ → Type′′
  _`⊎_   : Type′′ → Type′′ → Type′′
  `⊤     : Type′′
  `⊥     : Type′′
  `List  : Type′′ → Type′′

data Context′′ : Set where
  ∅     : Context′′
  _,_⦂_ : Context′′ → Id → Type′′ → Context′′

data _∋_⦂′′_ : Context′′ → Id → Type′′ → Set where
  Z : ∀ {Γ x A}
      --------------------
    → Γ , x ⦂ A ∋ x ⦂′′ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂′′ A
      -----------------
    → Γ , y ⦂ B ∋ x ⦂′′ A

data Term⁺′′ : Set
data Term⁻′′ : Set

data Term⁺′′ where
  `_     : Id → Term⁺′′
  _·_    : Term⁺′′ → Term⁻′′ → Term⁺′′
  `proj₁ : Term⁺′′ → Term⁺′′
  `proj₂ : Term⁺′′ → Term⁺′′
  _↓_    : Term⁻′′ → Type′′ → Term⁺′′

data Term⁻′′ where
  ƛ_⇒_                     : Id → Term⁻′′ → Term⁻′′
  `zero                    : Term⁻′′
  `suc_                    : Term⁻′′ → Term⁻′′
  `case_[zero⇒_|suc_⇒_]    : Term⁺′′ → Term⁻′′ → Id → Term⁻′′ → Term⁻′′
  μ_⇒_                     : Id → Term⁻′′ → Term⁻′′
  `⟨_,_⟩                   : Term⁻′′ → Term⁻′′ → Term⁻′′
  `case×_[⟨_,_⟩⇒_]         : Term⁺′′ → Id → Id → Term⁻′′ → Term⁻′′
  `inj₁                    : Term⁻′′ → Term⁻′′
  `inj₂                    : Term⁻′′ → Term⁻′′
  `case⊎_[inj₁_⇒_|inj₂_⇒_] : Term⁺′′ → Id → Term⁻′′ → Id → Term⁻′′ → Term⁻′′
  `tt                      : Term⁻′′
  `case⊤_[tt⇒_]            : Term⁺′′ → Term⁻′′ → Term⁻′′
  `case⊥_[]                : Term⁺′′ → Term⁻′′
  `[]                      : Term⁻′′
  _`∷_                     : Term⁻′′ → Term⁻′′ → Term⁻′′
  `caseL_[[]⇒_|`_∷_⇒_]     : Term⁺′′ → Term⁻′′ → Id → Id → Term⁻′′ → Term⁻′′
  _↑                       : Term⁺′′ → Term⁻′′

data _⊢_↑′′_ : Context′′ → Term⁺′′ → Type′′ → Set
data _⊢_↓′′_ : Context′′ → Term⁻′′ → Type′′ → Set

data _⊢_↑′′_ where
  ⊢` : ∀ {Γ A x}
    → Γ ∋ x ⦂′′ A
      -----------
    → Γ ⊢ ` x ↑′′ A

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ↑′′ A ⇒′′ B
    → Γ ⊢ M ↓′′ A
      -------------
    → Γ ⊢ L · M ↑′′ B

  ⊢proj₁ : ∀ {Γ L A B}
    → Γ ⊢ L ↑′′ A `×′′ B
      -------------
    → Γ ⊢ `proj₁ L ↑′′ A

  ⊢proj₂ : ∀ {Γ L A B}
    → Γ ⊢ L ↑′′ A `×′′ B
      -------------
    → Γ ⊢ `proj₂ L ↑′′ B

  ⊢↓ : ∀ {Γ M A}
    → Γ ⊢ M ↓′′ A
      ---------------
    → Γ ⊢ (M ↓ A) ↑′′ A

data _⊢_↓′′_ where
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ↓′′ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ↓′′ A ⇒′′ B

  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ↓′′ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ↓′′ `ℕ
      ---------------
    → Γ ⊢ `suc M ↓′′ `ℕ

  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ↑′′ `ℕ
    → Γ ⊢ M ↓′′ A
    → Γ , x ⦂ `ℕ ⊢ N ↓′′ A
      -------------------------------------
    → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ↓′′ A

  ⊢μ : ∀ {Γ x N A}
    → Γ , x ⦂ A ⊢ N ↓′′ A
      -----------------
    → Γ ⊢ μ x ⇒ N ↓′′ A

  `⟨_,_⟩ : ∀ {Γ M N A B}
    → Γ ⊢ M ↓′′ A
    → Γ ⊢ N ↓′′ B
      --------------------------
    → Γ ⊢ `⟨ M , N ⟩ ↓′′ A `×′′ B

  ⊢case× : ∀ {Γ L x y M A B C}
    → Γ ⊢ L ↑′′ A `×′′ B
    → Γ , x ⦂ A , y ⦂ B ⊢ M ↓′′ C
      -----------------------------------
    → Γ ⊢ `case× L [⟨ x , y ⟩⇒ M ] ↓′′ C

  ⊢inj₁ : ∀ {Γ M A B}
    → Γ ⊢ M ↓′′ A
      -----------------------
    → Γ ⊢ `inj₁ M ↓′′ A `⊎ B

  ⊢inj₂ : ∀ {Γ N A B}
    → Γ ⊢ N ↓′′ B
      -----------------------
    → Γ ⊢ `inj₂ N ↓′′ A `⊎ B

  ⊢case⊎ : ∀ {Γ L x M y N A B C}
    → Γ ⊢ L ↑′′ A `⊎ B
    → Γ , x ⦂ A ⊢ M ↓′′ C
    → Γ , y ⦂ B ⊢ N ↓′′ C
      ---------------------------------------------
    → Γ ⊢ `case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ] ↓′′ C

  ⊢tt : ∀ {Γ}
      ---------------
    → Γ ⊢ `tt ↓′′ `⊤

  ⊢case⊤ : ∀ {Γ L M A}
    → Γ ⊢ L ↑′′ `⊤
    → Γ ⊢ M ↓′′ A
      ----------------------------
    → Γ ⊢ `case⊤ L [tt⇒ M ] ↓′′ A

  ⊢case⊥ : ∀ {Γ L A}
    → Γ ⊢ L ↑′′ `⊥
      ----------------------
    → Γ ⊢ `case⊥ L [] ↓′′ A

  ⊢[] : ∀ {Γ A}
      --------------------
    → Γ ⊢ `[] ↓′′ `List A

  _`∷_ : ∀ {Γ M N A}
    → Γ ⊢ M ↓′′ A
    → Γ ⊢ N ↓′′ `List A
      -----------------------
    → Γ ⊢ M `∷ N ↓′′ `List A

  ⊢caseL : ∀ {Γ L M x y N A B}
    → Γ ⊢ L ↑′′ `List A
    → Γ ⊢ M ↓′′ B
    → Γ , x ⦂ A , y ⦂ `List A ⊢ N ↓′′ B
      -----------------------------------------
    → Γ ⊢ `caseL L [[]⇒ M |` x ∷ y ⇒ N ] ↓′′ B

  ⊢↑ : ∀ {Γ M A B}
    → Γ ⊢ M ↑′′ A
    → A ≡ B
      -------------
    → Γ ⊢ (M ↑) ↓′′ B
```


## Prerequisites

The rule for `M ↑` requires the ability to decide whether two types
are equal.  It is straightforward to code:
```
_≟Tp_ : (A B : Type) → Dec (A ≡ B)
`ℕ      ≟Tp `ℕ              =  yes refl
`ℕ      ≟Tp (A ⇒ B)         =  no λ()
(A ⇒ B) ≟Tp `ℕ              =  no λ()
(A ⇒ B) ≟Tp (A′ ⇒ B′)
  with A ≟Tp A′ | B ≟Tp B′
...  | no A≢    | _         =  no λ{refl → A≢ refl}
...  | yes _    | no B≢     =  no λ{refl → B≢ refl}
...  | yes refl | yes refl  =  yes refl
```

We will also need a couple of obvious lemmas; the domain
and range of equal function types are equal:
```
dom≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
dom≡ refl = refl

rng≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
rng≡ refl = refl
```

We will also need to know that the types `` `ℕ ``
and `A ⇒ B` are not equal:
```
ℕ≢⇒ : ∀ {A B} → `ℕ ≢ A ⇒ B
ℕ≢⇒ ()
```


## Unique types

Looking up a type in the context is unique.  Given two derivations,
one showing `Γ ∋ x ⦂ A` and one showing `Γ ∋ x ⦂ B`, it follows that
`A` and `B` must be identical:
```
uniq-∋ : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
uniq-∋ Z Z                 =  refl
uniq-∋ Z (S x≢y _)         =  ⊥-elim (x≢y refl)
uniq-∋ (S x≢y _) Z         =  ⊥-elim (x≢y refl)
uniq-∋ (S _ ∋x) (S _ ∋x′)  =  uniq-∋ ∋x ∋x′
```
If both derivations are by rule `Z` then uniqueness
follows immediately, while if both derivations are
by rule `S` then uniqueness follows by induction.
It is a contradiction if one derivation is by
rule `Z` and one by rule `S`, since rule `Z`
requires the variable we are looking for is the
final one in the context, while rule `S` requires
it is not.

Synthesizing a type is also unique.  Given two derivations,
one showing `Γ ⊢ M ↑ A` and one showing `Γ ⊢ M ↑ B`, it follows
that `A` and `B` must be identical:
```
uniq-↑ : ∀ {Γ M A B} → Γ ⊢ M ↑ A → Γ ⊢ M ↑ B → A ≡ B
uniq-↑ (⊢` ∋x) (⊢` ∋x′)       =  uniq-∋ ∋x ∋x′
uniq-↑ (⊢L · ⊢M) (⊢L′ · ⊢M′)  =  rng≡ (uniq-↑ ⊢L ⊢L′)
uniq-↑ (⊢↓ ⊢M) (⊢↓ ⊢M′)       =  refl
```
There are three possibilities for the term. If it is a variable,
uniqueness of synthesis follows from uniqueness of lookup.
If it is an application, uniqueness follows by induction on
the function in the application, since the range of equal
types are equal.  If it is a switch expression, uniqueness
follows since both terms are decorated with the same type.


## Lookup type of a variable in the context

Given `Γ` and two distinct variables `x` and `y`, if there is no type `A`
such that `Γ ∋ x ⦂ A` holds, then there is also no type `A` such that
`Γ , y ⦂ B ∋ x ⦂ A` holds:
```
ext∋ : ∀ {Γ B x y}
  → x ≢ y
  → ¬ ∃[ A ]( Γ ∋ x ⦂ A )
    -----------------------------
  → ¬ ∃[ A ]( Γ , y ⦂ B ∋ x ⦂ A )
ext∋ x≢y _  ⟨ A , Z ⟩       =  x≢y refl
ext∋ _   ¬∃ ⟨ A , S _ ∋x ⟩  =  ¬∃ ⟨ A , ∋x ⟩
```
Given a type `A` and evidence that `Γ , y ⦂ B ∋ x ⦂ A` holds, we must
demonstrate a contradiction.  If the judgment holds by `Z`, then we
must have that `x` and `y` are the same, which contradicts the first
assumption. If the judgment holds by `S _ ⊢x` then `⊢x` provides
evidence that `Γ ∋ x ⦂ A`, which contradicts the second assumption.

Given a context `Γ` and a variable `x`, we decide whether
there exists a type `A` such that `Γ ∋ x ⦂ A` holds, or its
negation:
```
lookup : ∀ (Γ : Context) (x : Id)
    -----------------------
  → Dec (∃[ A ](Γ ∋ x ⦂ A))
lookup ∅ x                        =  no  (λ ())
lookup (Γ , y ⦂ B) x with x ≟ y
... | yes refl                    =  yes ⟨ B , Z ⟩
... | no x≢y with lookup Γ x
...             | no  ¬∃          =  no  (ext∋ x≢y ¬∃)
...             | yes ⟨ A , ∋x ⟩  =  yes ⟨ A , S x≢y ∋x ⟩
```
Consider the context:

* If it is empty, then trivially there is no possible derivation.

* If it is non-empty, compare the given variable to the most
  recent binding:

  + If they are identical, we have succeeded, with `Z` as
    the appropriate derivation.

  + If they differ, we recurse:

    - If lookup fails, we apply `ext∋` to convert the proof
      there is no derivation from the contained context
      to the extended context.

    - If lookup succeeds, we extend the derivation with `S`.


## Promoting negations

For each possible term form, we need to show that if one of its
components fails to type, then the whole fails to type.  Most of
these results are easy to demonstrate inline, but we provide
auxiliary functions for a couple of the trickier cases.

If `Γ ⊢ L ↑ A ⇒ B` holds but `Γ ⊢ M ↓ A` does not hold, then
there is no term `B′` such that `Γ ⊢ L · M ↑ B′` holds:
```
¬arg : ∀ {Γ A B L M}
  → Γ ⊢ L ↑ A ⇒ B
  → ¬ Γ ⊢ M ↓ A
    -------------------------
  → ¬ ∃[ B′ ](Γ ⊢ L · M ↑ B′)
¬arg ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom≡ (uniq-↑ ⊢L ⊢L′) = ¬⊢M ⊢M′
```
Let `⊢L` be evidence that `Γ ⊢ L ↑ A ⇒ B` holds and `¬⊢M` be evidence
that `Γ ⊢ M ↓ A` does not hold.  Given a type `B′` and evidence that
`Γ ⊢ L · M ↑ B′` holds, we must demonstrate a contradiction.  The
evidence must take the form `⊢L′ · ⊢M′`, where `⊢L′` is evidence that
`Γ ⊢ L ↑ A′ ⇒ B′` and `⊢M′` is evidence that `Γ ⊢ M ↓ A′`.  By
`uniq-↑` applied to `⊢L` and `⊢L′`, we know that `A ⇒ B ≡ A′ ⇒ B′`,
and hence that `A ≡ A′`, which means that `¬⊢M` and `⊢M′` yield a
contradiction.  Without the `rewrite` clause, Agda would not allow us
to derive a contradiction between `¬⊢M` and `⊢M′`, since one concerns
type `A` and the other type `A′`.


If `Γ ⊢ M ↑ A` holds and `A ≢ B`, then `Γ ⊢ (M ↑) ↓ B` does not hold:
```
¬switch : ∀ {Γ M A B}
  → Γ ⊢ M ↑ A
  → A ≢ B
    ---------------
  → ¬ Γ ⊢ (M ↑) ↓ B
¬switch ⊢M A≢B (⊢↑ ⊢M′ A′≡B) rewrite uniq-↑ ⊢M ⊢M′ = A≢B A′≡B
```
Let `⊢M` be evidence that `Γ ⊢ M ↑ A` holds, and `A≢B` be evidence
that `A ≢ B`.  Given evidence that `Γ ⊢ (M ↑) ↓ B` holds, we must
demonstrate a contradiction.  The evidence must take the form `⊢↑ ⊢M′
A′≡B`, where `⊢M′` is evidence that `Γ ⊢ M ↑ A′` and `A′≡B` is
evidence that `A′≡B`.  By `uniq-↑` applied to `⊢M` and `⊢M′` we know
that `A ≡ A′`, which means that `A≢B` and `A′≡B` yield a
contradiction.  Without the `rewrite` clause, Agda would not allow us
to derive a contradiction between `A≢B` and `A′≡B`, since one concerns
type `A` and the other type `A′`.


## Synthesize and inherit types

The table has been set and we are ready for the main course.
We define two mutually recursive functions,
one for synthesis and one for inheritance.  Synthesis is given
a context `Γ` and a synthesis term `M` and either
returns a type `A` and evidence that `Γ ⊢ M ↑ A`, or its negation.
Inheritance is given a context `Γ`, an inheritance term `M`,
and a type `A` and either returns evidence that `Γ ⊢ M ↓ A`,
or its negation:
```
synthesize : ∀ (Γ : Context) (M : Term⁺)
    -----------------------
  → Dec (∃[ A ](Γ ⊢ M ↑ A))

inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type)
    ---------------
  → Dec (Γ ⊢ M ↓ A)
```

We first consider the code for synthesis:
```
synthesize Γ (` x) with lookup Γ x
... | no  ¬∃              =  no  (λ{ ⟨ A , ⊢` ∋x ⟩ → ¬∃ ⟨ A , ∋x ⟩ })
... | yes ⟨ A , ∋x ⟩      =  yes ⟨ A , ⊢` ∋x ⟩
synthesize Γ (L · M) with synthesize Γ L
... | no  ¬∃              =  no  (λ{ ⟨ _ , ⊢L  · _  ⟩  →  ¬∃ ⟨ _ , ⊢L ⟩ })
... | yes ⟨ `ℕ ,    ⊢L ⟩  =  no  (λ{ ⟨ _ , ⊢L′ · _  ⟩  →  ℕ≢⇒ (uniq-↑ ⊢L ⊢L′) })
... | yes ⟨ A ⇒ B , ⊢L ⟩ with inherit Γ M A
...    | no  ¬⊢M          =  no  (¬arg ⊢L ¬⊢M)
...    | yes ⊢M           =  yes ⟨ B , ⊢L · ⊢M ⟩
synthesize Γ (M ↓ A) with inherit Γ M A
... | no  ¬⊢M             =  no  (λ{ ⟨ _ , ⊢↓ ⊢M ⟩  →  ¬⊢M ⊢M })
... | yes ⊢M              =  yes ⟨ A , ⊢↓ ⊢M ⟩
```
There are three cases:

* If the term is a variable `` ` x ``, we use lookup as defined above:

  + If it fails, then `¬∃` is evidence that there is no `A` such
    that `Γ ∋ x ⦂ A` holds.  Evidence that `` Γ ⊢ ` x ↑ A `` holds must
    have the form `` ⊢` ∋x ``, where `∋x` is evidence that `Γ ∋ x ⦂ A`,
    which yields a contradiction.

  + If it succeeds, then `∋x` is evidence that `Γ ∋ x ⦂ A`, and
    hence `` ⊢′ ∋x `` is evidence that `` Γ ⊢ ` x ↑ A ``.

* If the term is an application `L · M`, we recurse on the function `L`:

  + If it fails, then `¬∃` is evidence that there is no type such
    that `Γ ⊢ L ↑ _` holds.  Evidence that `Γ ⊢ L · M ↑ _` holds
    must have the form `⊢L · _`, where `⊢L` is evidence that
    `Γ ⊢ L ↑ _`, which yields a contradiction.

  + If it succeeds, there are two possibilities:

    - One is that `⊢L` is evidence that `` Γ ⊢ L ⦂ `ℕ ``.  Evidence
      that `Γ ⊢ L · M ↑ _` holds must have the form `⊢L′ · _` where
      `⊢L′` is evidence that `Γ ⊢ L ↑ A ⇒ B` for some types `A` and
      `B`.  Applying `uniq-↑` to `⊢L` and `⊢L′` yields a
      contradiction, since `` `ℕ `` cannot equal `A ⇒ B`.

    - The other is that `⊢L` is evidence that `Γ ⊢ L ↑ A ⇒ B`, in
      which case we recurse on the argument `M`:

      * If it fails, then `¬⊢M` is evidence that `Γ ⊢ M ↓ A` does
        not hold.  By `¬arg` applied to `⊢L` and `¬⊢M`, it follows
        that `Γ ⊢ L · M ↑ B` cannot hold.

      * If it succeeds, then `⊢M` is evidence that `Γ ⊢ M ↓ A`,
        and `⊢L · ⊢M` provides evidence that `Γ ⊢ L · M ↑ B`.

* If the term is a switch `M ↓ A` from synthesised to inherited,
  we recurse on the subterm `M`, supplying type `A` by inheritance:

  + If it fails, then `¬⊢M` is evidence that `Γ ⊢ M ↓ A` does not
    hold.  Evidence that `Γ ⊢ (M ↓ A) ↑ A` holds must have the
    form `⊢↓ ⊢M` where `⊢M` is evidence that `Γ ⊢ M ↓ A` holds,
    which yields a contradiction.

  + If it succeeds, then `⊢M` is evidence that `Γ ⊢ M ↓ A`,
    and `⊢↓ ⊢M` provides evidence that `Γ ⊢ (M ↓ A) ↑ A`.

We next consider the code for inheritance:
```
inherit Γ (ƛ x ⇒ N) `ℕ      =  no  (λ())
inherit Γ (ƛ x ⇒ N) (A ⇒ B) with inherit (Γ , x ⦂ A) N B
... | no ¬⊢N                =  no  (λ{ (⊢ƛ ⊢N)  →  ¬⊢N ⊢N })
... | yes ⊢N                =  yes (⊢ƛ ⊢N)
inherit Γ `zero `ℕ          =  yes ⊢zero
inherit Γ `zero (A ⇒ B)     =  no  (λ())
inherit Γ (`suc M) `ℕ with inherit Γ M `ℕ
... | no ¬⊢M                =  no  (λ{ (⊢suc ⊢M)  →  ¬⊢M ⊢M })
... | yes ⊢M                =  yes (⊢suc ⊢M)
inherit Γ (`suc M) (A ⇒ B)  =  no  (λ())
inherit Γ (`case L [zero⇒ M |suc x ⇒ N ]) A with synthesize Γ L
... | no ¬∃                 =  no  (λ{ (⊢case ⊢L  _ _) → ¬∃ ⟨ `ℕ , ⊢L ⟩})
... | yes ⟨ _ ⇒ _ , ⊢L ⟩    =  no  (λ{ (⊢case ⊢L′ _ _) → ℕ≢⇒ (uniq-↑ ⊢L′ ⊢L) })
... | yes ⟨ `ℕ ,    ⊢L ⟩ with inherit Γ M A
...    | no ¬⊢M             =  no  (λ{ (⊢case _ ⊢M _) → ¬⊢M ⊢M })
...    | yes ⊢M with inherit (Γ , x ⦂ `ℕ) N A
...       | no ¬⊢N          =  no  (λ{ (⊢case _ _ ⊢N) → ¬⊢N ⊢N })
...       | yes ⊢N          =  yes (⊢case ⊢L ⊢M ⊢N)
inherit Γ (μ x ⇒ N) A with inherit (Γ , x ⦂ A) N A
... | no ¬⊢N                =  no  (λ{ (⊢μ ⊢N) → ¬⊢N ⊢N })
... | yes ⊢N                =  yes (⊢μ ⊢N)
inherit Γ (M ↑) B with synthesize Γ M
... | no  ¬∃                =  no  (λ{ (⊢↑ ⊢M _) → ¬∃ ⟨ _ , ⊢M ⟩ })
... | yes ⟨ A , ⊢M ⟩ with A ≟Tp B
...   | no  A≢B             =  no  (¬switch ⊢M A≢B)
...   | yes A≡B             =  yes (⊢↑ ⊢M A≡B)
```
We consider only the cases for abstraction and
and for switching from inherited to synthesized:

* If the term is an abstraction `ƛ x ⇒ N` and the inherited type
  is `` `ℕ ``, then it is trivial that `` Γ ⊢ (ƛ x ⇒ N) ↓ `ℕ ``
  cannot hold.

* If the term is an abstraction `ƛ x ⇒ N` and the inherited type
  is `A ⇒ B`, then we recurse with context `Γ , x ⦂ A` on subterm
  `N` inheriting type `B`:

  + If it fails, then `¬⊢N` is evidence that `Γ , x ⦂ A ⊢ N ↓ B`
    does not hold.  Evidence that `Γ ⊢ (ƛ x ⇒ N) ↓ A ⇒ B` holds
    must have the form `⊢ƛ ⊢N` where `⊢N` is evidence that
    `Γ , x ⦂ A ⊢ N ↓ B`, which yields a contradiction.

  + If it succeeds, then `⊢N` is evidence that `Γ , x ⦂ A ⊢ N ↓ B`
    holds, and `⊢ƛ ⊢N` provides evidence that `Γ ⊢ (ƛ x ⇒ N) ↓ A ⇒ B`.

* If the term is a switch `M ↑` from inherited to synthesised,
  we recurse on the subterm `M`:

  + If it fails, then `¬∃` is evidence there is no `A` such
    that `Γ ⊢ M ↑ A` holds.  Evidence that `Γ ⊢ (M ↑) ↓ B` holds
    must have the form `⊢↑ ⊢M _` where `⊢M` is evidence that
    `Γ ⊢ M ↑ _`, which yields a contradiction.

  + If it succeeds, then `⊢M` is evidence that `Γ ⊢ M ↑ A` holds.
    We apply `_≟Tp_` do decide whether `A` and `B` are equal:

    - If it fails, then `A≢B` is evidence that `A ≢ B`.
      By `¬switch` applied to `⊢M` and `A≢B` it follow that
      `Γ ⊢ (M ↑) ↓ B` cannot hold.

    - If it succeeds, then `A≡B` is evidence that `A ≡ B`,
      and `⊢↑ ⊢M A≡B` provides evidence that `Γ ⊢ (M ↑) ↓ B`.

The remaining cases are similar, and their code can pretty much be
read directly from the corresponding typing rules.

## Testing the example terms

First, we copy a function introduced earlier that makes it easy to
compute the evidence that two variable names are distinct:
```
_≠_ : ∀ (x y : Id) → x ≢ y
x ≠ y  with x ≟ y
...       | no  x≢y  =  x≢y
...       | yes _    =  ⊥-elim impossible
  where postulate impossible : ⊥
```

Here is the result of typing two plus two on naturals:
```
⊢2+2 : ∅ ⊢ 2+2 ↑ `ℕ
⊢2+2 =
  (⊢↓
   (⊢μ
    (⊢ƛ
     (⊢ƛ
      (⊢case (⊢` (S ("m" ≠ "n") Z)) (⊢↑ (⊢` Z) refl)
       (⊢suc
        (⊢↑
         (⊢`
          (S ("p" ≠ "m")
           (S ("p" ≠ "n")
            (S ("p" ≠ "m") Z)))
          · ⊢↑ (⊢` Z) refl
          · ⊢↑ (⊢` (S ("n" ≠ "m") Z)) refl)
         refl))))))
   · ⊢suc (⊢suc ⊢zero)
   · ⊢suc (⊢suc ⊢zero))
```
We confirm that synthesis on the relevant term returns
natural as the type and the above derivation:
```
_ : synthesize ∅ 2+2 ≡ yes ⟨ `ℕ , ⊢2+2 ⟩
_ = refl
```
Indeed, the above derivation was computed by evaluating the term on
the left, with minor editing of the result.  The only editing required
was to replace Agda's representation of the evidence that two strings
are unequal (which it cannot print nor read) by equivalent calls to
`_≠_`.

Here is the result of typing two plus two with Church numerals:
```
⊢2+2ᶜ : ∅ ⊢ 2+2ᶜ ↑ `ℕ
⊢2+2ᶜ =
  ⊢↓
  (⊢ƛ
   (⊢ƛ
    (⊢ƛ
     (⊢ƛ
      (⊢↑
       (⊢`
        (S ("m" ≠ "z")
         (S ("m" ≠ "s")
          (S ("m" ≠ "n") Z)))
        · ⊢↑ (⊢` (S ("s" ≠ "z") Z)) refl
        ·
        ⊢↑
        (⊢`
         (S ("n" ≠ "z")
          (S ("n" ≠ "s") Z))
         · ⊢↑ (⊢` (S ("s" ≠ "z") Z)) refl
         · ⊢↑ (⊢` Z) refl)
        refl)
       refl)))))
  ·
  ⊢ƛ
  (⊢ƛ
   (⊢↑
    (⊢` (S ("s" ≠ "z") Z) ·
     ⊢↑ (⊢` (S ("s" ≠ "z") Z) · ⊢↑ (⊢` Z) refl)
     refl)
    refl))
  ·
  ⊢ƛ
  (⊢ƛ
   (⊢↑
    (⊢` (S ("s" ≠ "z") Z) ·
     ⊢↑ (⊢` (S ("s" ≠ "z") Z) · ⊢↑ (⊢` Z) refl)
     refl)
    refl))
  · ⊢ƛ (⊢suc (⊢↑ (⊢` Z) refl))
  · ⊢zero
```
We confirm that synthesis on the relevant term returns
natural as the type and the above derivation:
```
_ : synthesize ∅ 2+2ᶜ ≡ yes ⟨ `ℕ , ⊢2+2ᶜ ⟩
_ = refl
```
Again, the above derivation was computed by evaluating the
term on the left and editing.

## Testing the error cases

It is important not just to check that code works as intended,
but also that it fails as intended.  Here are checks for
several possible errors:

Unbound variable:
```
_ : synthesize ∅ ((ƛ "x" ⇒ ` "y" ↑) ↓ (`ℕ ⇒ `ℕ)) ≡ no _
_ = refl
```

Argument in application is ill typed:
```
_ : synthesize ∅ (plus · sucᶜ) ≡ no _
_ = refl
```

Function in application is ill typed:
```
_ : synthesize ∅ (plus · sucᶜ · two) ≡ no _
_ = refl
```

Function in application has type natural:
```
_ : synthesize ∅ ((two ↓ `ℕ) · two) ≡ no _
_ = refl
```

Abstraction inherits type natural:
```
_ : synthesize ∅ (twoᶜ ↓ `ℕ) ≡ no _
_ = refl
```

Zero inherits a function type:
```
_ : synthesize ∅ (`zero ↓ `ℕ ⇒ `ℕ) ≡ no _
_ = refl
```

Successor inherits a function type:
```
_ : synthesize ∅ (two ↓ `ℕ ⇒ `ℕ) ≡ no _
_ = refl
```

Successor of an ill-typed term:
```
_ : synthesize ∅ (`suc twoᶜ ↓ `ℕ) ≡ no _
_ = refl
```

Case of a term with a function type:
```
_ : synthesize ∅
      ((`case (twoᶜ ↓ Ch) [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ] ↓ `ℕ) ) ≡ no _
_ = refl
```

Case of an ill-typed term:
```
_ : synthesize ∅
      ((`case (twoᶜ ↓ `ℕ) [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ] ↓ `ℕ) ) ≡ no _
_ = refl
```

Inherited and synthesised types disagree in a switch:
```
_ : synthesize ∅ (((ƛ "x" ⇒ ` "x" ↑) ↓ `ℕ ⇒ (`ℕ ⇒ `ℕ))) ≡ no _
_ = refl
```


## Erasure

From the evidence that a decorated term has the correct type it is
easy to extract the corresponding intrinsically-typed term.  We use the
name `DB` to refer to the code in
Chapter [DeBruijn](/DeBruijn/).
It is easy to define an _erasure_ function that takes an extrinsic
type judgment into the corresponding intrinsically-typed term.

First, we give code to erase a type:
```
∥_∥Tp : Type → DB.Type
∥ `ℕ ∥Tp             =  DB.`ℕ
∥ A ⇒ B ∥Tp          =  ∥ A ∥Tp DB.⇒ ∥ B ∥Tp
```
It simply renames to the corresponding constructors in module `DB`.

Next, we give the code to erase a context:
```
∥_∥Cx : Context → DB.Context
∥ ∅ ∥Cx              =  DB.∅
∥ Γ , x ⦂ A ∥Cx      =  ∥ Γ ∥Cx DB., ∥ A ∥Tp
```
It simply drops the variable names.

Next, we give the code to erase a lookup judgment:
```
∥_∥∋ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ∥ Γ ∥Cx DB.∋ ∥ A ∥Tp
∥ Z ∥∋               =  DB.Z
∥ S x≢ ∋x ∥∋         =  DB.S ∥ ∋x ∥∋
```
It simply drops the evidence that variable names are distinct.

Finally, we give the code to erase a typing judgment.
Just as there are two mutually recursive typing judgments,
there are two mutually recursive erasure functions:
```
∥_∥⁺ : ∀ {Γ M A} → Γ ⊢ M ↑ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp
∥_∥⁻ : ∀ {Γ M A} → Γ ⊢ M ↓ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp

∥ ⊢` ⊢x ∥⁺           =  DB.` ∥ ⊢x ∥∋
∥ ⊢L · ⊢M ∥⁺         =  ∥ ⊢L ∥⁺ DB.· ∥ ⊢M ∥⁻
∥ ⊢↓ ⊢M ∥⁺           =  ∥ ⊢M ∥⁻

∥ ⊢ƛ ⊢N ∥⁻           =  DB.ƛ ∥ ⊢N ∥⁻
∥ ⊢zero ∥⁻           =  DB.`zero
∥ ⊢suc ⊢M ∥⁻         =  DB.`suc ∥ ⊢M ∥⁻
∥ ⊢case ⊢L ⊢M ⊢N ∥⁻  =  DB.case ∥ ⊢L ∥⁺ ∥ ⊢M ∥⁻ ∥ ⊢N ∥⁻
∥ ⊢μ ⊢M ∥⁻           =  DB.μ ∥ ⊢M ∥⁻
∥ ⊢↑ ⊢M refl ∥⁻      =  ∥ ⊢M ∥⁺
```
Erasure replaces constructors for each typing judgment
by the corresponding term constructor from `DB`.  The
constructors that correspond to switching from synthesized
to inherited or vice versa are dropped.

We confirm that the erasure of the type derivations in
this chapter yield the corresponding intrinsically-typed terms
from the earlier chapter:
```
_ : ∥ ⊢2+2 ∥⁺ ≡ DB.2+2
_ = refl

_ : ∥ ⊢2+2ᶜ ∥⁺ ≡ DB.2+2ᶜ
_ = refl
```
Thus, we have confirmed that bidirectional type inference
converts decorated versions of the lambda terms from
Chapter [Lambda](/Lambda/)
to the intrinsically-typed terms of
Chapter [DeBruijn](/DeBruijn/).


#### Exercise `inference-multiplication` (recommended)

Apply inference to your decorated definition of multiplication from
exercise [`bidirectional-mul`](/Inference/#bidirectional-mul), and show that
erasure of the inferred typing yields your definition of
multiplication from Chapter [DeBruijn](/DeBruijn/).

```
open import Data.Product using (proj₂)
open import Relation.Nullary.Decidable using (from-yes)

dbmul : ∀ {Γ} → Γ DB.⊢ DB.`ℕ DB.⇒ DB.`ℕ DB.⇒ DB.`ℕ
dbmul = μ ƛ ƛ case (# 1) `zero (DB.plus · # 1 · (# 3 · # 0 · # 1))
  where
    open DB

_ : ∥ proj₂ (from-yes (synthesize ∅ mul)) ∥⁺ ≡ dbmul
_ = refl
```

#### Exercise `inference-products` (recommended)

Using your rules from exercise
[`bidirectional-products`](/Inference/#bidirectional-products), extend
bidirectional inference to include products.

```
_≟Tp′_ : (A B : Type′) → Dec (A ≡ B)
`ℕ        ≟Tp′ `ℕ          = yes refl
`ℕ        ≟Tp′ (A   ⇒′ B)  = no λ()
`ℕ        ≟Tp′ (A  `×′ B)  = no (λ ())
(A  ⇒′ B) ≟Tp′ `ℕ          = no λ()
(A  ⇒′ B) ≟Tp′ (A′  ⇒′ B′)
  with A ≟Tp′ A′ | B ≟Tp′ B′
...  | no  A≢   | _        = no λ{refl → A≢ refl}
...  | yes _    | no  B≢   = no λ{refl → B≢ refl}
...  | yes refl | yes refl = yes refl
(A  ⇒′ B) ≟Tp′ (A′ `×′ B′) = no (λ ())
(A `×′ B) ≟Tp′ `ℕ          = no (λ ())
(A `×′ B) ≟Tp′ (A′  ⇒′ B′) = no (λ ())
(A `×′ B) ≟Tp′ (A′ `×′ B′)
  with A ≟Tp′ A′ | B ≟Tp′ B′
...  | no  A≢   | _        = no λ{refl → A≢ refl}
...  | yes _    | no  B≢   = no λ{refl → B≢ refl}
...  | yes refl | yes refl = yes refl

dom′≡ : ∀ {A A′ B B′} → A ⇒′ B ≡ A′ ⇒′ B′ → A ≡ A′
dom′≡ refl = refl

rng′≡ : ∀ {A A′ B B′} → A ⇒′ B ≡ A′ ⇒′ B′ → B ≡ B′
rng′≡ refl = refl

fst′≡ : ∀ {A A′ B B′} → A `×′ B ≡ A′ `×′ B′ → A ≡ A′
fst′≡ refl = refl

snd′≡ : ∀ {A A′ B B′} → A `×′ B ≡ A′ `×′ B′ → B ≡ B′
snd′≡ refl = refl

ℕ≢⇒′ : ∀ {A B} → `ℕ ≢ A ⇒′ B
ℕ≢⇒′ ()

ℕ≢*′ : ∀ {A B} → `ℕ ≢ A `×′ B
ℕ≢*′ ()

⇒′≢*′ : ∀ {A B C D} → A ⇒′ B ≢ C `×′ D
⇒′≢*′ ()

uniq-∋′ : ∀ {Γ x A B} → Γ ∋ x ⦂′ A → Γ ∋ x ⦂′ B → A ≡ B
uniq-∋′ Z          Z           = refl
uniq-∋′ Z          (S x≢y _)   = ⊥-elim (x≢y refl)
uniq-∋′ (S x≢y _)  Z           = ⊥-elim (x≢y refl)
uniq-∋′ (S _   ∋x) (S _   ∋x′) = uniq-∋′ ∋x ∋x′

uniq-↑′ : ∀ {Γ M A B} → Γ ⊢ M ↑′ A → Γ ⊢ M ↑′ B → A ≡ B
uniq-↑′ (⊢` ∋x)     (⊢` ∋x′)     = uniq-∋′ ∋x ∋x′
uniq-↑′ (⊢L · ⊢M)   (⊢L′ · ⊢M′)  = rng′≡ (uniq-↑′ ⊢L ⊢L′)
uniq-↑′ (⊢↓ ⊢M)     (⊢↓ ⊢M′)     = refl
uniq-↑′ (⊢proj₁ ⊢M) (⊢proj₁ ⊢M′) = fst′≡ (uniq-↑′ ⊢M ⊢M′)
uniq-↑′ (⊢proj₂ ⊢M) (⊢proj₂ ⊢M′) = snd′≡ (uniq-↑′ ⊢M ⊢M′)

ext∋′ : ∀ {Γ B x y}
  → x ≢ y
  → ¬ ∃[ A ]( Γ ∋ x ⦂′ A )
    -----------------------------
  → ¬ ∃[ A ]( Γ , y ⦂ B ∋ x ⦂′ A )
ext∋′ x≢y _  ⟨ A , Z ⟩      = x≢y refl
ext∋′ _   ¬∃ ⟨ A , S _ ∋x ⟩ = ¬∃ ⟨ A , ∋x ⟩

lookup′ : ∀ (Γ : Context′) (x : Id)
    -----------------------
  → Dec (∃[ A ](Γ ∋ x ⦂′ A))
lookup′ ∅ x                      = no  (λ ())
lookup′ (Γ , y ⦂ B) x with x ≟ y
... | yes refl                   = yes ⟨ B , Z ⟩
... | no x≢y with lookup′ Γ x
...             | no  ¬∃         = no  (ext∋′ x≢y ¬∃)
...             | yes ⟨ A , ∋x ⟩ = yes ⟨ A , S x≢y ∋x ⟩

¬arg′ : ∀ {Γ A B L M}
  → Γ ⊢ L ↑′ A ⇒′ B
  → ¬ Γ ⊢ M ↓′ A
    -------------------------
  → ¬ ∃[ B′ ](Γ ⊢ L · M ↑′ B′)
¬arg′ ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom′≡ (uniq-↑′ ⊢L ⊢L′) = ¬⊢M ⊢M′

¬body′ : ∀ {Γ A B C L x y M}
  → Γ ⊢ L ↑′ A `×′ B
  → ¬ Γ , x ⦂ A , y ⦂ B ⊢ M ↓′ C
    -------------------------
  → ¬ (Γ ⊢ `case× L [⟨ x , y ⟩⇒ M ] ↓′ C)
¬body′ ⊢L ¬⊢M (⊢case× ⊢L′ ⊢M′) rewrite fst′≡ (uniq-↑′ ⊢L ⊢L′) | snd′≡ (uniq-↑′ ⊢L ⊢L′) = ¬⊢M ⊢M′

synthesize′ : ∀ (Γ : Context′) (M : Term⁺′)
    -----------------------
  → Dec (∃[ A ](Γ ⊢ M ↑′ A))

inherit′ : ∀ (Γ : Context′) (M : Term⁻′) (A : Type′)
    ---------------
  → Dec (Γ ⊢ M ↓′ A)

synthesize′ Γ (` x)      with lookup′ Γ x
... | yes ⟨ _ , ∋x ⟩       = yes ⟨ _ , ⊢` ∋x ⟩
... | no  ¬∃               = no (λ{ ⟨ _ , ⊢` ∋x ⟩ → ¬∃ ⟨ _ , ∋x ⟩ })
synthesize′ Γ (M · N)    with synthesize′ Γ M
... | no  ¬∃               = no (λ{ ⟨ _ , ⊢M′ · _ ⟩ → ¬∃ ⟨ _ , ⊢M′ ⟩ })
... | yes ⟨ `ℕ      , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢M′ · _ ⟩ → ℕ≢⇒′ (uniq-↑′ ⊢M ⊢M′) })
... | yes ⟨ A `×′ B , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢M′ · _ ⟩ → ⇒′≢*′ (uniq-↑′ ⊢M′ ⊢M) })
... | yes ⟨ A  ⇒′ B , ⊢M ⟩ with inherit′ Γ N A
...   | no  ¬∃             = no (λ{ ⟨ _ , ⊢M′ ⟩ → ¬arg′ ⊢M ¬∃ ⟨ _ , ⊢M′ ⟩ })
...   | yes ⊢N             = yes ⟨ B , ⊢M · ⊢N ⟩
synthesize′ Γ (`proj₁ M) with synthesize′ Γ M
... | no  ¬∃               = no (λ{ ⟨ _ , ⊢proj₁ ⊢M′ ⟩ → ¬∃ ⟨ _ , ⊢M′ ⟩ })
... | yes ⟨ `ℕ      , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₁ ⊢M′ ⟩ → ℕ≢*′ (uniq-↑′ ⊢M ⊢M′) })
... | yes ⟨ A  ⇒′ B , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₁ ⊢M′ ⟩ → ⇒′≢*′ (uniq-↑′ ⊢M ⊢M′) })
... | yes ⟨ A `×′ B , ⊢M ⟩ = yes ⟨ A , ⊢proj₁ ⊢M ⟩
synthesize′ Γ (`proj₂ M) with synthesize′ Γ M
... | no  ¬∃               = no (λ{ ⟨ _ , ⊢proj₂ ⊢M′ ⟩ → ¬∃ ⟨ _ , ⊢M′ ⟩ })
... | yes ⟨ `ℕ      , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₂ ⊢M′ ⟩ → ℕ≢*′ (uniq-↑′ ⊢M ⊢M′) })
... | yes ⟨ A  ⇒′ B , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₂ ⊢M′ ⟩ → ⇒′≢*′ (uniq-↑′ ⊢M ⊢M′) })
... | yes ⟨ A `×′ B , ⊢M ⟩ = yes ⟨ B , ⊢proj₂ ⊢M ⟩
synthesize′ Γ (M ↓ A)    with inherit′ Γ M A
... | no ¬⊢M               = no (λ{ ⟨ _ , ⊢↓ ⊢M ⟩ → ¬⊢M ⊢M })
... | yes ⊢M               = yes ⟨ A , ⊢↓ ⊢M ⟩

inherit′ Γ (ƛ x ⇒ M)                     `ℕ        = no (λ ())
inherit′ Γ (ƛ x ⇒ M)                     (A  ⇒′ B) with inherit′ (Γ , x ⦂ A) M B
... | no ¬⊢M                                       = no (λ{ (⊢ƛ ⊢M) → ¬⊢M ⊢M })
... | yes ⊢M                                       = yes (⊢ƛ ⊢M)
inherit′ Γ (ƛ x ⇒ M)                     (A `×′ B) = no (λ ())
inherit′ Γ `zero                         `ℕ        = yes ⊢zero
inherit′ Γ `zero                         (A  ⇒′ B) = no (λ ())
inherit′ Γ `zero                         (A `×′ B) = no (λ ())
inherit′ Γ (`suc M)                      `ℕ        with inherit′ Γ M `ℕ
... | no ¬⊢M                                       = no (λ{ (⊢suc ⊢M) → ¬⊢M ⊢M })
... | yes ⊢M                                       = yes (⊢suc ⊢M)
inherit′ Γ (`suc M)                      (A  ⇒′ B) = no (λ ())
inherit′ Γ (`suc M)                      (A `×′ B) = no (λ ())
inherit′ Γ `case L [zero⇒ M |suc x ⇒ N ] C         with synthesize′ Γ L
... | no  ¬∃                                       = no (λ{ (⊢case ⊢L _ _) → ¬∃ ⟨ _ , ⊢L ⟩ })
... | yes ⟨ A  ⇒′ B , ⊢L ⟩                         = no (λ{ (⊢case ⊢L′ _ _) → ℕ≢⇒′ (uniq-↑′ ⊢L′ ⊢L) })
... | yes ⟨ A `×′ B , ⊢L ⟩                         = no (λ{ (⊢case ⊢L′ _ _) → ℕ≢*′ (uniq-↑′ ⊢L′ ⊢L) })
... | yes ⟨ `ℕ      , ⊢L ⟩ with inherit′ Γ M C | inherit′ (Γ , x ⦂ `ℕ) N C
...   | no ¬⊢M | _                                 = no (λ{ (⊢case _ ⊢M _) → ¬⊢M ⊢M })
...   | _      | no ¬⊢N                            = no (λ{ (⊢case _ _ ⊢N) → ¬⊢N ⊢N })
...   | yes ⊢M | yes ⊢N                            = yes (⊢case ⊢L ⊢M ⊢N)
inherit′ Γ (μ x ⇒ M)                     C         with inherit′ (Γ , x ⦂ C) M C
... | no ¬⊢M                                       = no (λ{ (⊢μ ⊢M) → ¬⊢M ⊢M })
... | yes ⊢M                                       = yes (⊢μ ⊢M)
inherit′ Γ `⟨ M , N ⟩                    `ℕ        = no (λ ())
inherit′ Γ `⟨ M , N ⟩                    (A  ⇒′ B) = no (λ ())
inherit′ Γ `⟨ M , N ⟩                    (A `×′ B) with inherit′ Γ M A | inherit′ Γ N B
... | no ¬⊢M | _                                   = no (λ{ `⟨ ⊢M , _ ⟩ → ¬⊢M ⊢M })
... | _      | no ¬⊢N                              = no (λ{ `⟨ _ , ⊢N ⟩ → ¬⊢N ⊢N })
... | yes ⊢M | yes ⊢N                              = yes `⟨ ⊢M , ⊢N ⟩
inherit′ Γ `case× L [⟨ x , y ⟩⇒ M ]      C         with synthesize′ Γ L
... | no  ¬∃                                       = no (λ{ (⊢case× ⊢L _) → ¬∃ ⟨ _ , ⊢L ⟩ })
... | yes ⟨ `ℕ      , ⊢L ⟩                         = no (λ{ (⊢case× ⊢L′ _) → ℕ≢*′ (uniq-↑′ ⊢L ⊢L′) })
... | yes ⟨ A  ⇒′ B , ⊢L ⟩                         = no (λ{ (⊢case× ⊢L′ _) → ⇒′≢*′ (uniq-↑′ ⊢L ⊢L′) })
... | yes ⟨ A `×′ B , ⊢L ⟩ with inherit′ (Γ , x ⦂ A , y ⦂ B) M C
...   | no ¬⊢M                                     = no (λ{ ⊢K → ¬body′ ⊢L ¬⊢M ⊢K })
...   | yes ⊢M                                     = yes (⊢case× ⊢L ⊢M)
inherit′ Γ (M ↑)                         A         with synthesize′ Γ M
... | no  ¬∃                                       = no (λ{ (⊢↑ ⊢M′ _) → ¬∃ ⟨ _ , ⊢M′ ⟩ })
... | yes ⟨ B , ⊢M ⟩ with A ≟Tp′ B
...   | no  A≢B                                    = no (λ{ (⊢↑ ⊢M′ refl) → A≢B (uniq-↑′ ⊢M′ ⊢M) })
...   | yes refl                                   = yes (⊢↑ ⊢M refl)
```

#### Exercise `inference-rest` (stretch)

Extend the bidirectional type rules to include the rest of the constructs from
Chapter [More](/More/).

```
_≟Tp′′_ : (A B : Type′′) → Dec (A ≡ B)
`ℕ         ≟Tp′′ `ℕ           = yes refl
`ℕ         ≟Tp′′ (A   ⇒′′ B)  = no λ()
`ℕ         ≟Tp′′ (A  `×′′ B)  = no (λ ())
`ℕ         ≟Tp′′ (A  `⊎   B)  = no (λ ())
`ℕ         ≟Tp′′ `⊤           = no (λ ())
`ℕ         ≟Tp′′ `⊥           = no (λ ())
`ℕ         ≟Tp′′ `List A′     = no (λ ())
(A  ⇒′′ B) ≟Tp′′ `ℕ           = no λ()
(A  ⇒′′ B) ≟Tp′′ (A′  ⇒′′ B′)
  with A ≟Tp′′ A′ | B ≟Tp′′ B′
...  | no  A≢   | _           = no λ{refl → A≢ refl}
...  | yes _    | no  B≢      = no λ{refl → B≢ refl}
...  | yes refl | yes refl    = yes refl
(A  ⇒′′ B) ≟Tp′′ (A′ `×′′ B′) = no (λ ())
(A  ⇒′′ B) ≟Tp′′ (A′ `⊎   B′) = no (λ ())
(A  ⇒′′ B) ≟Tp′′ `⊤           = no (λ ())
(A  ⇒′′ B) ≟Tp′′ `⊥           = no (λ ())
(A  ⇒′′ B) ≟Tp′′ `List A′     = no (λ ())
(A `×′′ B) ≟Tp′′ `ℕ           = no (λ ())
(A `×′′ B) ≟Tp′′ (A′  ⇒′′ B′) = no (λ ())
(A `×′′ B) ≟Tp′′ (A′ `×′′ B′)
  with A ≟Tp′′ A′ | B ≟Tp′′ B′
...  | no  A≢   | _           = no λ{refl → A≢ refl}
...  | yes _    | no  B≢      = no λ{refl → B≢ refl}
...  | yes refl | yes refl    = yes refl
(A `×′′ B) ≟Tp′′ (A′ `⊎   B′) = no (λ ())
(A `×′′ B) ≟Tp′′ `⊤           = no (λ ())
(A `×′′ B) ≟Tp′′ `⊥           = no (λ ())
(A `×′′ B) ≟Tp′′ `List A′     = no (λ ())
(A `⊎   B) ≟Tp′′ `ℕ           = no (λ ())
(A `⊎   B) ≟Tp′′ (A′  ⇒′′ B′) = no (λ ())
(A `⊎   B) ≟Tp′′ (A′ `×′′ B′) = no (λ ())
(A `⊎   B) ≟Tp′′ (A′ `⊎   B′)
  with A ≟Tp′′ A′ | B ≟Tp′′ B′
...  | no  A≢   | _           = no λ{refl → A≢ refl}
...  | yes _    | no  B≢      = no λ{refl → B≢ refl}
...  | yes refl | yes refl    = yes refl
(A `⊎   B) ≟Tp′′ `⊤           = no (λ ())
(A `⊎   B) ≟Tp′′ `⊥           = no (λ ())
(A `⊎   B) ≟Tp′′ `List A′     = no (λ ())
`⊤         ≟Tp′′ `ℕ           = no (λ ())
`⊤         ≟Tp′′ (A′  ⇒′′ B′) = no (λ ())
`⊤         ≟Tp′′ (A′ `×′′ B′) = no (λ ())
`⊤         ≟Tp′′ (A′ `⊎   B′) = no (λ ())
`⊤         ≟Tp′′ `⊤           = yes refl
`⊤         ≟Tp′′ `⊥           = no (λ ())
`⊤         ≟Tp′′ `List A′     = no (λ ())
`⊥         ≟Tp′′ `ℕ           = no (λ ())
`⊥         ≟Tp′′ (A′  ⇒′′ B′) = no (λ ())
`⊥         ≟Tp′′ (A′ `×′′ B′) = no (λ ())
`⊥         ≟Tp′′ (A′ `⊎   B′) = no (λ ())
`⊥         ≟Tp′′ `⊤           = no (λ ())
`⊥         ≟Tp′′ `⊥           = yes refl
`⊥         ≟Tp′′ `List A′     = no (λ ())
`List A    ≟Tp′′ `ℕ           = no (λ ())
`List A    ≟Tp′′ (A′  ⇒′′ B′) = no (λ ())
`List A    ≟Tp′′ (A′ `×′′ B′) = no (λ ())
`List A    ≟Tp′′ (A′ `⊎   B′) = no (λ ())
`List A    ≟Tp′′ `⊤           = no (λ ())
`List A    ≟Tp′′ `⊥           = no (λ ())
`List A    ≟Tp′′ `List A′
  with A ≟Tp′′ A′
...  | no  A≢   = no λ{ refl → A≢ refl }
...  | yes refl = yes refl

dom′′≡ : ∀ {A A′ B B′} → A ⇒′′ B ≡ A′ ⇒′′ B′ → A ≡ A′
dom′′≡ refl = refl

rng′′≡ : ∀ {A A′ B B′} → A ⇒′′ B ≡ A′ ⇒′′ B′ → B ≡ B′
rng′′≡ refl = refl

fst′′≡ : ∀ {A A′ B B′} → A `×′′ B ≡ A′ `×′′ B′ → A ≡ A′
fst′′≡ refl = refl

snd′′≡ : ∀ {A A′ B B′} → A `×′′ B ≡ A′ `×′′ B′ → B ≡ B′
snd′′≡ refl = refl

left′′≡ : ∀ {A A′ B B′} → A `⊎ B ≡ A′ `⊎ B′ → A ≡ A′
left′′≡ refl = refl

right′′≡ : ∀ {A A′ B B′} → A `⊎ B ≡ A′ `⊎ B′ → B ≡ B′
right′′≡ refl = refl

item′′≡ : ∀ {A A′} → `List A ≡ `List A′ → A ≡ A′
item′′≡ refl = refl

ℕ≢⇒′′ : ∀ {A B} → `ℕ ≢ A ⇒′′ B
ℕ≢⇒′′ ()

ℕ≢*′′ : ∀ {A B} → `ℕ ≢ A `×′′ B
ℕ≢*′′ ()

ℕ≢⊎ : ∀ {A B} → `ℕ ≢ A `⊎ B
ℕ≢⊎ ()

ℕ≢⊤ : `ℕ ≢ `⊤
ℕ≢⊤ ()

ℕ≢⊥ : `ℕ ≢ `⊥
ℕ≢⊥ ()

ℕ≢List : ∀ {A} → `ℕ ≢ `List A
ℕ≢List ()

⇒′′≢*′′ : ∀ {A B C D} → A ⇒′′ B ≢ C `×′′ D
⇒′′≢*′′ ()

⇒′′≢⊎ : ∀ {A B C D} → A ⇒′′ B ≢ C `⊎ D
⇒′′≢⊎ ()

⇒′′≢⊤ : ∀ {A B} → A ⇒′′ B ≢ `⊤
⇒′′≢⊤ ()

⇒′′≢⊥ : ∀ {A B} → A ⇒′′ B ≢ `⊥
⇒′′≢⊥ ()

⇒′′≢List : ∀ {A B C} → A ⇒′′ B ≢ `List C
⇒′′≢List ()

*′′≢⊎ : ∀ {A B C D} → A `×′′ B ≢ C `⊎ D
*′′≢⊎ ()

*′′≢⊤ : ∀ {A B} → A `×′′ B ≢ `⊤
*′′≢⊤ ()

*′′≢⊥ : ∀ {A B} → A `×′′ B ≢ `⊥
*′′≢⊥ ()

*′′≢List : ∀ {A B C} → A `×′′ B ≢ `List C
*′′≢List ()

⊎≢⊤ : ∀ {A B} → A `⊎ B ≢ `⊤
⊎≢⊤ ()

⊎≢⊥ : ∀ {A B} → A `⊎ B ≢ `⊥
⊎≢⊥ ()

⊎≢List : ∀ {A B C} → A `⊎ B ≢ `List C
⊎≢List ()

⊤≢⊥ : `⊤ ≢ `⊥
⊤≢⊥ ()

⊤≢List : ∀ {A} → `⊤ ≢ `List A
⊤≢List ()

⊥≢List : ∀ {A} → `⊥ ≢ `List A
⊥≢List ()

uniq-∋′′ : ∀ {Γ x A B} → Γ ∋ x ⦂′′ A → Γ ∋ x ⦂′′ B → A ≡ B
uniq-∋′′ Z          Z           = refl
uniq-∋′′ Z          (S x≢y _)   = ⊥-elim (x≢y refl)
uniq-∋′′ (S x≢y _)  Z           = ⊥-elim (x≢y refl)
uniq-∋′′ (S _   ∋x) (S _   ∋x′) = uniq-∋′′ ∋x ∋x′

uniq-↑′′ : ∀ {Γ M A B} → Γ ⊢ M ↑′′ A → Γ ⊢ M ↑′′ B → A ≡ B
uniq-↑′′ (⊢` ∋x)     (⊢` ∋x′)     = uniq-∋′′ ∋x ∋x′
uniq-↑′′ (⊢L · ⊢M)   (⊢L′ · ⊢M′)  = rng′′≡ (uniq-↑′′ ⊢L ⊢L′)
uniq-↑′′ (⊢↓ ⊢M)     (⊢↓ ⊢M′)     = refl
uniq-↑′′ (⊢proj₁ ⊢M) (⊢proj₁ ⊢M′) = fst′′≡ (uniq-↑′′ ⊢M ⊢M′)
uniq-↑′′ (⊢proj₂ ⊢M) (⊢proj₂ ⊢M′) = snd′′≡ (uniq-↑′′ ⊢M ⊢M′)

ext∋′′ : ∀ {Γ B x y}
  → x ≢ y
  → ¬ ∃[ A ]( Γ ∋ x ⦂′′ A )
    -----------------------------
  → ¬ ∃[ A ]( Γ , y ⦂ B ∋ x ⦂′′ A )
ext∋′′ x≢y _  ⟨ A , Z ⟩      = x≢y refl
ext∋′′ _   ¬∃ ⟨ A , S _ ∋x ⟩ = ¬∃ ⟨ A , ∋x ⟩

lookup′′ : ∀ (Γ : Context′′) (x : Id)
    -----------------------
  → Dec (∃[ A ](Γ ∋ x ⦂′′ A))
lookup′′ ∅ x                     = no  (λ ())
lookup′′ (Γ , y ⦂ B) x with x ≟ y
... | yes refl                   = yes ⟨ B , Z ⟩
... | no x≢y with lookup′′ Γ x
...             | no  ¬∃         = no  (ext∋′′ x≢y ¬∃)
...             | yes ⟨ A , ∋x ⟩ = yes ⟨ A , S x≢y ∋x ⟩

¬arg′′ : ∀ {Γ A B L M}
  → Γ ⊢ L ↑′′ A ⇒′′ B
  → ¬ Γ ⊢ M ↓′′ A
    -------------------------
  → ¬ ∃[ B′ ](Γ ⊢ L · M ↑′′ B′)
¬arg′′ ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom′′≡ (uniq-↑′′ ⊢L ⊢L′) = ¬⊢M ⊢M′

¬case×-body′′ : ∀ {Γ A B C L x y M}
  → Γ ⊢ L ↑′′ A `×′′ B
  → ¬ Γ , x ⦂ A , y ⦂ B ⊢ M ↓′′ C
    -------------------------
  → ¬ (Γ ⊢ `case× L [⟨ x , y ⟩⇒ M ] ↓′′ C)
¬case×-body′′ ⊢L ¬⊢M (⊢case× ⊢L′ ⊢M′) rewrite fst′′≡ (uniq-↑′′ ⊢L ⊢L′) | snd′′≡ (uniq-↑′′ ⊢L ⊢L′) = ¬⊢M ⊢M′

¬case⊎-body₁′′ : ∀ {Γ A B C L x M y N}
  → Γ ⊢ L ↑′′ A `⊎ B
  → ¬ Γ , x ⦂ A ⊢ M ↓′′ C
    -------------------------
  → ¬ (Γ ⊢ `case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ] ↓′′ C)
¬case⊎-body₁′′ ⊢L ¬⊢M (⊢case⊎ ⊢L′ ⊢M′ ⊢N′) rewrite left′′≡ (uniq-↑′′ ⊢L ⊢L′) = ¬⊢M ⊢M′

¬case⊎-body₂′′ : ∀ {Γ A B C L x M y N}
  → Γ ⊢ L ↑′′ A `⊎ B
  → ¬ Γ , y ⦂ B ⊢ N ↓′′ C
    -------------------------
  → ¬ (Γ ⊢ `case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ] ↓′′ C)
¬case⊎-body₂′′ ⊢L ¬⊢N (⊢case⊎ ⊢L′ ⊢M′ ⊢N′) rewrite right′′≡ (uniq-↑′′ ⊢L ⊢L′) = ¬⊢N ⊢N′

¬caseL-body′′ : ∀ {Γ A B L M x y N}
  → Γ ⊢ L ↑′′ `List A
  → ¬ Γ , x ⦂ A , y ⦂ `List A ⊢ N ↓′′ B
    -------------------------
  → ¬ (Γ ⊢ `caseL L [[]⇒ M |` x ∷ y ⇒ N ] ↓′′ B)
¬caseL-body′′ ⊢L ¬⊢N (⊢caseL ⊢L′ ⊢M′ ⊢N′) rewrite item′′≡ (uniq-↑′′ ⊢L ⊢L′) = ¬⊢N ⊢N′

synthesize′′ : ∀ (Γ : Context′′) (M : Term⁺′′)
    -----------------------
  → Dec (∃[ A ](Γ ⊢ M ↑′′ A))

inherit′′ : ∀ (Γ : Context′′) (M : Term⁻′′) (A : Type′′)
    ---------------
  → Dec (Γ ⊢ M ↓′′ A)

synthesize′′ Γ (` x)      with lookup′′ Γ x
... | yes ⟨ _ , ∋x ⟩        = yes ⟨ _ , ⊢` ∋x ⟩
... | no  ¬∃                = no (λ{ ⟨ _ , ⊢` ∋x ⟩ → ¬∃ ⟨ _ , ∋x ⟩ })
synthesize′′ Γ (M · N)    with synthesize′′ Γ M
... | no  ¬∃                = no (λ{ ⟨ _ , ⊢M′ · _ ⟩ → ¬∃ ⟨ _ , ⊢M′ ⟩ })
... | yes ⟨ `ℕ       , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢M′ · _ ⟩ → ℕ≢⇒′′ (uniq-↑′′ ⊢M ⊢M′) })
... | yes ⟨ A `×′′ B , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢M′ · _ ⟩ → ⇒′′≢*′′ (uniq-↑′′ ⊢M′ ⊢M) })
... | yes ⟨ A `⊎ A₁  , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢M′ · _ ⟩ → ⇒′′≢⊎ (uniq-↑′′ ⊢M′ ⊢M) })
... | yes ⟨ `⊤       , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢M′ · _ ⟩ → ⇒′′≢⊤ (uniq-↑′′ ⊢M′ ⊢M) })
... | yes ⟨ `⊥       , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢M′ · _ ⟩ → ⇒′′≢⊥ (uniq-↑′′ ⊢M′ ⊢M) })
... | yes ⟨ `List A  , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢M′ · _ ⟩ → ⇒′′≢List (uniq-↑′′ ⊢M′ ⊢M) })
... | yes ⟨ A  ⇒′′ B , ⊢M ⟩ with inherit′′ Γ N A
...   | no  ¬∃              = no (λ{ ⟨ _ , ⊢M′ ⟩ → ¬arg′′ ⊢M ¬∃ ⟨ _ , ⊢M′ ⟩ })
...   | yes ⊢N              = yes ⟨ B , ⊢M · ⊢N ⟩
synthesize′′ Γ (`proj₁ M) with synthesize′′ Γ M
... | no  ¬∃                = no (λ{ ⟨ _ , ⊢proj₁ ⊢M′ ⟩ → ¬∃ ⟨ _ , ⊢M′ ⟩ })
... | yes ⟨ `ℕ       , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₁ ⊢M′ ⟩ → ℕ≢*′′ (uniq-↑′′ ⊢M ⊢M′) })
... | yes ⟨ A  ⇒′′ B , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₁ ⊢M′ ⟩ → ⇒′′≢*′′ (uniq-↑′′ ⊢M ⊢M′) })
... | yes ⟨ A `⊎   B , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₁ ⊢M′ ⟩ → *′′≢⊎ (uniq-↑′′ ⊢M′ ⊢M) })
... | yes ⟨ `⊤       , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₁ ⊢M′ ⟩ → *′′≢⊤ (uniq-↑′′ ⊢M′ ⊢M) })
... | yes ⟨ `⊥       , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₁ ⊢M′ ⟩ → *′′≢⊥ (uniq-↑′′ ⊢M′ ⊢M) })
... | yes ⟨ `List A  , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₁ ⊢M′ ⟩ → *′′≢List (uniq-↑′′ ⊢M′ ⊢M) })
... | yes ⟨ A `×′′ B , ⊢M ⟩ = yes ⟨ A , ⊢proj₁ ⊢M ⟩
synthesize′′ Γ (`proj₂ M) with synthesize′′ Γ M
... | no  ¬∃                = no (λ{ ⟨ _ , ⊢proj₂ ⊢M′ ⟩ → ¬∃ ⟨ _ , ⊢M′ ⟩ })
... | yes ⟨ `ℕ       , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₂ ⊢M′ ⟩ → ℕ≢*′′ (uniq-↑′′ ⊢M ⊢M′) })
... | yes ⟨ A  ⇒′′ B , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₂ ⊢M′ ⟩ → ⇒′′≢*′′ (uniq-↑′′ ⊢M ⊢M′) })
... | yes ⟨ A `⊎   B , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₂ ⊢M′ ⟩ → *′′≢⊎ (uniq-↑′′ ⊢M′ ⊢M) })
... | yes ⟨ `⊤       , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₂ ⊢M′ ⟩ → *′′≢⊤ (uniq-↑′′ ⊢M′ ⊢M) })
... | yes ⟨ `⊥       , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₂ ⊢M′ ⟩ → *′′≢⊥ (uniq-↑′′ ⊢M′ ⊢M) })
... | yes ⟨ `List A  , ⊢M ⟩ = no (λ{ ⟨ _ , ⊢proj₂ ⊢M′ ⟩ → *′′≢List (uniq-↑′′ ⊢M′ ⊢M) })
... | yes ⟨ A `×′′ B , ⊢M ⟩ = yes ⟨ B , ⊢proj₂ ⊢M ⟩
synthesize′′ Γ (M ↓ A)    with inherit′′ Γ M A
... | no ¬⊢M                = no (λ{ ⟨ _ , ⊢↓ ⊢M ⟩ → ¬⊢M ⊢M })
... | yes ⊢M                = yes ⟨ A , ⊢↓ ⊢M ⟩


inherit′′ Γ (ƛ x ⇒ M)                          `ℕ         = no (λ ())
inherit′′ Γ (ƛ x ⇒ M)                          (A  ⇒′′ B) with inherit′′ (Γ , x ⦂ A) M B
... | no ¬⊢M = no (λ{ (⊢ƛ ⊢M) → ¬⊢M ⊢M })
... | yes ⊢M = yes (⊢ƛ ⊢M)
inherit′′ Γ (ƛ x ⇒ M)                          (A `×′′ B) = no (λ ())
inherit′′ Γ (ƛ x ⇒ M)                          (A `⊎   B) = no (λ ())
inherit′′ Γ (ƛ x ⇒ M)                          `⊤         = no (λ ())
inherit′′ Γ (ƛ x ⇒ M)                          `⊥         = no (λ ())
inherit′′ Γ (ƛ x ⇒ M)                          (`List A)  = no (λ ())
inherit′′ Γ `zero                              `ℕ         = yes ⊢zero
inherit′′ Γ `zero                              (A  ⇒′′ B) = no (λ ())
inherit′′ Γ `zero                              (A `×′′ B) = no (λ ())
inherit′′ Γ `zero                              (A `⊎   B) = no (λ ())
inherit′′ Γ `zero                              `⊤         = no (λ ())
inherit′′ Γ `zero                              `⊥         = no (λ ())
inherit′′ Γ `zero                              (`List A)  = no (λ ())
inherit′′ Γ (`suc M)                           `ℕ         with inherit′′ Γ M `ℕ
... | no ¬⊢M = no (λ{ (⊢suc ⊢M) → ¬⊢M ⊢M })
... | yes ⊢M = yes (⊢suc ⊢M)
inherit′′ Γ (`suc M)                           (A  ⇒′′ B) = no (λ ())
inherit′′ Γ (`suc M)                           (A `×′′ B) = no (λ ())
inherit′′ Γ (`suc M)                           (A `⊎   B) = no (λ ())
inherit′′ Γ (`suc M)                           `⊤         = no (λ ())
inherit′′ Γ (`suc M)                           `⊥         = no (λ ())
inherit′′ Γ (`suc M)                           (`List A)  = no (λ ())
inherit′′ Γ `case L [zero⇒ M |suc x ⇒ N ]      C          with synthesize′′ Γ L
... | no  ¬∃                                              = no (λ{ (⊢case ⊢L _ _) → ¬∃ ⟨ _ , ⊢L ⟩ })
... | yes ⟨ A  ⇒′′ B , ⊢L ⟩                               = no (λ{ (⊢case ⊢L′ _ _) → ℕ≢⇒′′ (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ A `×′′ B , ⊢L ⟩                               = no (λ{ (⊢case ⊢L′ _ _) → ℕ≢*′′ (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ A `⊎   B , ⊢L ⟩                               = no (λ{ (⊢case ⊢L′ _ _) → ℕ≢⊎ (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ `⊤       , ⊢L ⟩                               = no (λ{ (⊢case ⊢L′ _ _) → ℕ≢⊤ (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ `⊥       , ⊢L ⟩                               = no (λ{ (⊢case ⊢L′ _ _) → ℕ≢⊥ (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ `List A  , ⊢L ⟩                               = no (λ{ (⊢case ⊢L′ _ _) → ℕ≢List (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ `ℕ       , ⊢L ⟩ with inherit′′ Γ M C | inherit′′ (Γ , x ⦂ `ℕ) N C
...   | no ¬⊢M | _                                        = no (λ{ (⊢case _ ⊢M _) → ¬⊢M ⊢M })
...   | _      | no ¬⊢N                                   = no (λ{ (⊢case _ _ ⊢N) → ¬⊢N ⊢N })
...   | yes ⊢M | yes ⊢N                                   = yes (⊢case ⊢L ⊢M ⊢N)
inherit′′ Γ (μ x ⇒ M)                          C          with inherit′′ (Γ , x ⦂ C) M C
... | no ¬⊢M = no (λ{ (⊢μ ⊢M) → ¬⊢M ⊢M })
... | yes ⊢M = yes (⊢μ ⊢M)
inherit′′ Γ `⟨ M , N ⟩                         `ℕ         = no (λ ())
inherit′′ Γ `⟨ M , N ⟩                         (A  ⇒′′ B) = no (λ ())
inherit′′ Γ `⟨ M , N ⟩                         (A `×′′ B) with inherit′′ Γ M A | inherit′′ Γ N B
... | no ¬⊢M | _      = no (λ{ `⟨ ⊢M , _ ⟩ → ¬⊢M ⊢M })
... | _      | no ¬⊢N = no (λ{ `⟨ _ , ⊢N ⟩ → ¬⊢N ⊢N })
... | yes ⊢M | yes ⊢N = yes `⟨ ⊢M , ⊢N ⟩
inherit′′ Γ `⟨ M , N ⟩                         (A `⊎   B) = no (λ ())
inherit′′ Γ `⟨ M , N ⟩                         `⊤         = no (λ ())
inherit′′ Γ `⟨ M , N ⟩                         `⊥         = no (λ ())
inherit′′ Γ `⟨ M , N ⟩                         (`List A)  = no (λ ())
inherit′′ Γ `case× L [⟨ x , y ⟩⇒ M ]           C          with synthesize′′ Γ L
... | no  ¬∃                                              = no (λ{ (⊢case× ⊢L _) → ¬∃ ⟨ _ , ⊢L ⟩ })
... | yes ⟨ `ℕ       , ⊢L ⟩                               = no (λ{ (⊢case× ⊢L′ _) → ℕ≢*′′ (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ A  ⇒′′ B , ⊢L ⟩                               = no (λ{ (⊢case× ⊢L′ _) → ⇒′′≢*′′ (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ A `⊎   B , ⊢L ⟩                               = no (λ{ (⊢case× ⊢L′ _) → *′′≢⊎ (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ `⊤       , ⊢L ⟩                               = no (λ{ (⊢case× ⊢L′ _) → *′′≢⊤ (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ `⊥       , ⊢L ⟩                               = no (λ{ (⊢case× ⊢L′ _) → *′′≢⊥ (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ `List A  , ⊢L ⟩                               = no (λ{ (⊢case× ⊢L′ _) → *′′≢List (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ A `×′′ B , ⊢L ⟩ with inherit′′ (Γ , x ⦂ A , y ⦂ B) M C
...   | no ¬⊢M                                            = no (λ{ ⊢K → ¬case×-body′′ ⊢L ¬⊢M ⊢K })
...   | yes ⊢M                                            = yes (⊢case× ⊢L ⊢M)
inherit′′ Γ (`inj₁ M)                          `ℕ         = no (λ ())
inherit′′ Γ (`inj₁ M)                          (A  ⇒′′ B) = no (λ ())
inherit′′ Γ (`inj₁ M)                          (A `×′′ B) = no (λ ())
inherit′′ Γ (`inj₁ M)                          (A `⊎   B) with inherit′′ Γ M A
... | no ¬⊢M = no (λ{ (⊢inj₁ ⊢M) → ¬⊢M ⊢M })
... | yes ⊢M = yes (⊢inj₁ ⊢M)
inherit′′ Γ (`inj₁ M)                          `⊤         = no (λ ())
inherit′′ Γ (`inj₁ M)                          `⊥         = no (λ ())
inherit′′ Γ (`inj₁ M)                          (`List A)  = no (λ ())
inherit′′ Γ (`inj₂ N)                          `ℕ         = no (λ ())
inherit′′ Γ (`inj₂ N)                          (A  ⇒′′ B) = no (λ ())
inherit′′ Γ (`inj₂ N)                          (A `×′′ B) = no (λ ())
inherit′′ Γ (`inj₂ N)                          (A `⊎   B) with inherit′′ Γ N B
... | no ¬⊢N = no (λ{ (⊢inj₂ ⊢N) → ¬⊢N ⊢N })
... | yes ⊢N = yes (⊢inj₂ ⊢N)
inherit′′ Γ (`inj₂ N)                          `⊤         = no (λ ())
inherit′′ Γ (`inj₂ N)                          `⊥         = no (λ ())
inherit′′ Γ (`inj₂ N)                          (`List A)  = no (λ ())
inherit′′ Γ `case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ] C          with synthesize′′ Γ L
... | no ¬∃ = no (λ{ (⊢case⊎ ⊢L _ _) → ¬∃ ⟨ _ , ⊢L ⟩ })
... | yes ⟨ `ℕ       , ⊢L ⟩                               = no (λ{ (⊢case⊎ ⊢L′ _ _) → ℕ≢⊎ (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ A  ⇒′′ B , ⊢L ⟩                               = no (λ{ (⊢case⊎ ⊢L′ _ _) → ⇒′′≢⊎ (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ A `×′′ B , ⊢L ⟩                               = no (λ{ (⊢case⊎ ⊢L′ _ _) → *′′≢⊎ (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ `⊤       , ⊢L ⟩                               = no (λ{ (⊢case⊎ ⊢L′ _ _) → ⊎≢⊤ (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ `⊥       , ⊢L ⟩                               = no (λ{ (⊢case⊎ ⊢L′ _ _) → ⊎≢⊥ (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ `List A  , ⊢L ⟩                               = no (λ{ (⊢case⊎ ⊢L′ _ _) → ⊎≢List (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ A `⊎   B , ⊢L ⟩ with inherit′′ (Γ , x ⦂ A) M C | inherit′′ (Γ , y ⦂ B) N C
...   | no ¬⊢M | _      = no (λ{ ⊢K → ¬case⊎-body₁′′ ⊢L ¬⊢M ⊢K })
...   | _      | no ¬⊢N = no (λ{ ⊢K → ¬case⊎-body₂′′ ⊢L ¬⊢N ⊢K })
...   | yes ⊢M | yes ⊢N = yes (⊢case⊎ ⊢L ⊢M ⊢N)
inherit′′ Γ `tt                                `ℕ         = no (λ ())
inherit′′ Γ `tt                                (A  ⇒′′ B) = no (λ ())
inherit′′ Γ `tt                                (A `×′′ B) = no (λ ())
inherit′′ Γ `tt                                (A `⊎   B) = no (λ ())
inherit′′ Γ `tt                                `⊤         = yes ⊢tt
inherit′′ Γ `tt                                `⊥         = no (λ ())
inherit′′ Γ `tt                                (`List A)  = no (λ ())
inherit′′ Γ `case⊤ L [tt⇒ M ]                  C          with synthesize′′ Γ L
... | no ¬∃                                               = no (λ{ (⊢case⊤ ⊢L _) → ¬∃ ⟨ _ , ⊢L ⟩ })
... | yes ⟨ `ℕ       , ⊢L ⟩                               = no (λ{ (⊢case⊤ ⊢L′ _) → ℕ≢⊤ (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ A  ⇒′′ B , ⊢L ⟩                               = no (λ{ (⊢case⊤ ⊢L′ _) → ⇒′′≢⊤ (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ A `×′′ B , ⊢L ⟩                               = no (λ{ (⊢case⊤ ⊢L′ _) → *′′≢⊤ (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ A `⊎   B , ⊢L ⟩                               = no (λ{ (⊢case⊤ ⊢L′ _) → ⊎≢⊤ (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ `⊥       , ⊢L ⟩                               = no (λ{ (⊢case⊤ ⊢L′ _) → ⊤≢⊥ (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ `List A  , ⊢L ⟩                               = no (λ{ (⊢case⊤ ⊢L′ _) → ⊤≢List (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ `⊤       , ⊢L ⟩ with inherit′′ Γ M C
...   | no ¬⊢M                                            = no (λ{ (⊢case⊤ _ ⊢M) → ¬⊢M ⊢M })
...   | yes ⊢M                                            = yes (⊢case⊤ ⊢L ⊢M)
inherit′′ Γ `case⊥ L []                        C          with synthesize′′ Γ L
... | no ¬∃                                               = no (λ{ (⊢case⊥ ⊢L) → ¬∃ ⟨ _ , ⊢L ⟩ })
... | yes ⟨ `ℕ       , ⊢L ⟩                               = no (λ{ (⊢case⊥ ⊢L′) → ℕ≢⊥ (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ A  ⇒′′ B , ⊢L ⟩                               = no (λ{ (⊢case⊥ ⊢L′) → ⇒′′≢⊥ (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ A `×′′ B , ⊢L ⟩                               = no (λ{ (⊢case⊥ ⊢L′) → *′′≢⊥ (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ A `⊎   B , ⊢L ⟩                               = no (λ{ (⊢case⊥ ⊢L′) → ⊎≢⊥ (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ `⊤       , ⊢L ⟩                               = no (λ{ (⊢case⊥ ⊢L′) → ⊤≢⊥ (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ `List A  , ⊢L ⟩                               = no (λ{ (⊢case⊥ ⊢L′) → ⊥≢List (uniq-↑′′ ⊢L′ ⊢L) })
... | yes ⟨ `⊥       , ⊢L ⟩                               = yes (⊢case⊥ ⊢L)
inherit′′ Γ `[]                                `ℕ         = no (λ ())
inherit′′ Γ `[]                                (A  ⇒′′ B) = no (λ ())
inherit′′ Γ `[]                                (A `×′′ B) = no (λ ())
inherit′′ Γ `[]                                (A `⊎   B) = no (λ ())
inherit′′ Γ `[]                                `⊤         = no (λ ())
inherit′′ Γ `[]                                `⊥         = no (λ ())
inherit′′ Γ `[]                                (`List A)  = yes ⊢[]
inherit′′ Γ (M `∷ N)                           `ℕ         = no (λ ())
inherit′′ Γ (M `∷ N)                           (A  ⇒′′ B) = no (λ ())
inherit′′ Γ (M `∷ N)                           (A `×′′ B) = no (λ ())
inherit′′ Γ (M `∷ N)                           (A `⊎   B) = no (λ ())
inherit′′ Γ (M `∷ N)                           `⊤         = no (λ ())
inherit′′ Γ (M `∷ N)                           `⊥         = no (λ ())
inherit′′ Γ (M `∷ N)                           (`List A)  with inherit′′ Γ M A | inherit′′ Γ N (`List A)
... | no ¬⊢M | _                                          = no (λ{ (⊢M `∷ _) → ¬⊢M ⊢M })
... | _      | no ¬⊢N                                     = no (λ{ (_ `∷ ⊢N) → ¬⊢N ⊢N })
... | yes ⊢M | yes ⊢N                                     = yes (⊢M `∷ ⊢N)
inherit′′ Γ `caseL L [[]⇒ M |` x ∷ y ⇒ N ]     C          with synthesize′′ Γ L
... | no ¬∃                                               = no (λ{ (⊢caseL ⊢L _ _) → ¬∃ ⟨ _ , ⊢L ⟩ })
... | yes ⟨ `ℕ       , ⊢L ⟩                               = no (λ{ (⊢caseL ⊢L′ _ _) → ℕ≢List (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ A  ⇒′′ B , ⊢L ⟩                               = no (λ{ (⊢caseL ⊢L′ _ _) → ⇒′′≢List (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ A `×′′ B , ⊢L ⟩                               = no (λ{ (⊢caseL ⊢L′ _ _) → *′′≢List (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ A `⊎   B , ⊢L ⟩                               = no (λ{ (⊢caseL ⊢L′ _ _) → ⊎≢List (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ `⊤       , ⊢L ⟩                               = no (λ{ (⊢caseL ⊢L′ _ _) → ⊤≢List (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ `⊥       , ⊢L ⟩                               = no (λ{ (⊢caseL ⊢L′ _ _) → ⊥≢List (uniq-↑′′ ⊢L ⊢L′) })
... | yes ⟨ `List A  , ⊢L ⟩ with inherit′′ Γ M C | inherit′′ (Γ , x ⦂ A , y ⦂ `List A) N C
...   | no ¬⊢M | _      = no (λ{ (⊢caseL _ ⊢M _) → ¬⊢M ⊢M })
...   | _      | no ¬⊢N = no (λ{ ⊢K → ¬caseL-body′′ ⊢L ¬⊢N ⊢K })
...   | yes ⊢M | yes ⊢N = yes (⊢caseL ⊢L ⊢M ⊢N)
inherit′′ Γ (M ↑)                              A          with synthesize′′ Γ M
... | no  ¬∃                                              = no (λ{ (⊢↑ ⊢M′ _) → ¬∃ ⟨ _ , ⊢M′ ⟩ })
... | yes ⟨ B , ⊢M ⟩ with A ≟Tp′′ B
...   | no  A≢B                                           = no (λ{ (⊢↑ ⊢M′ refl) → A≢B (uniq-↑′′ ⊢M′ ⊢M) })
...   | yes refl                                          = yes (⊢↑ ⊢M refl)
```


## Bidirectional inference in Agda

Agda itself uses bidirectional inference.  This explains why
constructors can be overloaded while other defined names cannot ---
here by _overloaded_ we mean that the same name can be used for
constructors of different types.  Constructors are typed by
inheritance, and so the name is available when resolving the
constructor, whereas variables are typed by synthesis, and so each
variable must have a unique type.

Most top-level definitions in Agda are of functions, which are typed
by inheritance, which is why Agda requires a type declaration for
those definitions.  A definition with a right-hand side that is a term
typed by synthesis, such as an application, does not require a type
declaration.
```
answer = 6 * 7
```


## Unicode

This chapter uses the following unicode:

    ↓  U+2193:  DOWNWARDS ARROW (\d)
    ↑  U+2191:  UPWARDS ARROW (\u)
    ∥  U+2225:  PARALLEL TO (\||)
