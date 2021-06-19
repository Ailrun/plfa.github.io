---
title     : "More: Additional constructs of simply-typed lambda calculus"
layout    : page
prev      : /DeBruijn/
permalink : /More/
next      : /Bisimulation/
---

```
module plfa.part2.More where
```

So far, we have focussed on a relatively minimal language, based on
Plotkin's PCF, which supports functions, naturals, and fixpoints.  In
this chapter we extend our calculus to support the following:

  * primitive numbers
  * _let_ bindings
  * products
  * an alternative formulation of products
  * sums
  * unit type
  * an alternative formulation of unit type
  * empty type
  * lists

All of the data types should be familiar from Part I of this textbook.
For _let_ and the alternative formulations we show how they translate
to other constructs in the calculus.  Most of the description will be
informal. We show how to formalise the first four constructs and leave
the rest as an exercise for the reader.

Our informal descriptions will be in the style of
Chapter [Lambda](/Lambda/),
using extrinsically-typed terms,
while our formalisation will be in the style of
Chapter [DeBruijn](/DeBruijn/),
using intrinsically-typed terms.

By now, explaining with symbols should be more concise, more precise,
and easier to follow than explaining in prose.
For each construct, we give syntax, typing, reductions, and an example.
We also give translations where relevant; formally establishing the
correctness of translations will be the subject of the next chapter.

## Primitive numbers

We define a `Nat` type equivalent to the built-in natural number type
with multiplication as a primitive operation on numbers:

### Syntax

    A, B, C ::= ...                     Types
      Nat                                 primitive natural numbers

    L, M, N ::= ...                     Terms
      con c                               constant
      L `* M                              multiplication

    V, W ::= ...                        Values
      con c                               constant

### Typing

The hypothesis of the `con` rule is unusual, in that
it refers to a typing judgment of Agda rather than a
typing judgment of the defined calculus:

    c : ℕ
    --------------- con
    Γ ⊢ con c : Nat

    Γ ⊢ L : Nat
    Γ ⊢ M : Nat
    ---------------- _`*_
    Γ ⊢ L `* M : Nat

### Reduction

A rule that defines a primitive directly, such as the last rule below,
is called a δ rule.  Here the δ rule defines multiplication of
primitive numbers in terms of multiplication of naturals as given
by the Agda standard prelude:

    L —→ L′
    ----------------- ξ-*₁
    L `* M —→ L′ `* M

    M —→ M′
    ----------------- ξ-*₂
    V `* M —→ V `* M′

    ----------------------------- δ-*
    con c `* con d —→ con (c * d)

### Example

Here is a function to cube a primitive number:

    cube : ∅ ⊢ Nat ⇒ Nat
    cube = ƛ x ⇒ x `* x `* x


## Let bindings

Let bindings affect only the syntax of terms; they introduce no new
types or values:

### Syntax

    L, M, N ::= ...                     Terms
      `let x `= M `in N                   let

### Typing

    Γ ⊢ M ⦂ A
    Γ , x ⦂ A ⊢ N ⦂ B
    ------------------------- `let
    Γ ⊢ `let x `= M `in N ⦂ B

### Reduction

    M —→ M′
    --------------------------------------- ξ-let
    `let x `= M `in N —→ `let x `= M′ `in N

    --------------------------------- β-let
    `let x `= V `in N —→ N [ x := V ]

### Example

Here is a function to raise a primitive number to the tenth power:

    exp10 : ∅ ⊢ Nat ⇒ Nat
    exp10 = ƛ x ⇒ `let x2  `= x  `* x  `in
                  `let x4  `= x2 `* x2 `in
                  `let x5  `= x4 `* x  `in
                  x5 `* x5

### Translation

We can translate each _let_ term into an application of an abstraction:

    (`let x `= M `in N) †  =  (ƛ x ⇒ (N †)) · (M †)

Here `M †` is the translation of term `M` from a calculus with the
construct to a calculus without the construct.


## Products {name=products}

### Syntax

    A, B, C ::= ...                     Types
      A `× B                              product type

    L, M, N ::= ...                     Terms
      `⟨ M , N ⟩                          pair
      `proj₁ L                            project first component
      `proj₂ L                            project second component

    V, W ::= ...                        Values
      `⟨ V , W ⟩                          pair

### Typing

    Γ ⊢ M ⦂ A
    Γ ⊢ N ⦂ B
    ----------------------- `⟨_,_⟩ or `×-I
    Γ ⊢ `⟨ M , N ⟩ ⦂ A `× B

    Γ ⊢ L ⦂ A `× B
    ---------------- `proj₁ or `×-E₁
    Γ ⊢ `proj₁ L ⦂ A

    Γ ⊢ L ⦂ A `× B
    ---------------- `proj₂ or `×-E₂
    Γ ⊢ `proj₂ L ⦂ B

### Reduction

    M —→ M′
    ------------------------- ξ-⟨,⟩₁
    `⟨ M , N ⟩ —→ `⟨ M′ , N ⟩

    N —→ N′
    ------------------------- ξ-⟨,⟩₂
    `⟨ V , N ⟩ —→ `⟨ V , N′ ⟩

    L —→ L′
    --------------------- ξ-proj₁
    `proj₁ L —→ `proj₁ L′

    L —→ L′
    --------------------- ξ-proj₂
    `proj₂ L —→ `proj₂ L′

    ---------------------- β-proj₁
    `proj₁ `⟨ V , W ⟩ —→ V

    ---------------------- β-proj₂
    `proj₂ `⟨ V , W ⟩ —→ W

### Example

Here is a function to swap the components of a pair:

    swap× : ∅ ⊢ A `× B ⇒ B `× A
    swap× = ƛ z ⇒ `⟨ `proj₂ z , `proj₁ z ⟩


## Alternative formulation of products

There is an alternative formulation of products, where in place of two
ways to eliminate the type we have a case term that binds two
variables.  We repeat the syntax in full, but only give the new type
and reduction rules:

### Syntax

    A, B, C ::= ...                     Types
      A `× B                              product type

    L, M, N ::= ...                     Terms
      `⟨ M , N ⟩                          pair
      case× L [⟨ x , y ⟩⇒ M ]             case

    V, W ::=                            Values
      `⟨ V , W ⟩                          pair

### Typing

    Γ ⊢ L ⦂ A `× B
    Γ , x ⦂ A , y ⦂ B ⊢ N ⦂ C
    ------------------------------- case× or ×-E
    Γ ⊢ case× L [⟨ x , y ⟩⇒ N ] ⦂ C

### Reduction

    L —→ L′
    --------------------------------------------------- ξ-case×
    case× L [⟨ x , y ⟩⇒ N ] —→ case× L′ [⟨ x , y ⟩⇒ N ]

    --------------------------------------------------------- β-case×
    case× `⟨ V , W ⟩ [⟨ x , y ⟩⇒ N ] —→ N [ x := V ][ y := W ]

### Example

Here is a function to swap the components of a pair rewritten in the new notation:

    swap×-case : ∅ ⊢ A `× B ⇒ B `× A
    swap×-case = ƛ z ⇒ case× z
                         [⟨ x , y ⟩⇒ `⟨ y , x ⟩ ]

### Translation

We can translate the alternative formulation into the one with projections:

      (case× L [⟨ x , y ⟩⇒ N ]) †
    =
      `let z `= (L †) `in
      `let x `= `proj₁ z `in
      `let y `= `proj₂ z `in
      (N †)

Here `z` is a variable that does not appear free in `N`.  We refer
to such a variable as _fresh_.

One might think that we could instead use a more compact translation:

    -- WRONG
      (case× L [⟨ x , y ⟩⇒ N ]) †
    =
      (N †) [ x := `proj₁ (L †) ] [ y := `proj₂ (L †) ]

But this behaves differently.  The first term always reduces `L`
before `N`, and it computes ```proj₁`` and ```proj₂`` exactly once.  The
second term does not reduce `L` to a value before reducing `N`, and
depending on how many times and where `x` and `y` appear in `N`, it
may reduce `L` many times or not at all, and it may compute ```proj₁``
and ```proj₂`` many times or not at all.

We can also translate back the other way:

    (`proj₁ L) ‡  =  case× (L ‡) [⟨ x , y ⟩⇒ x ]
    (`proj₂ L) ‡  =  case× (L ‡) [⟨ x , y ⟩⇒ y ]

## Sums {name=sums}

### Syntax

    A, B, C ::= ...                     Types
      A `⊎ B                              sum type

    L, M, N ::= ...                     Terms
      `inj₁ M                             inject first component
      `inj₂ N                             inject second component
      case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ]    case

    V, W ::= ...                        Values
      `inj₁ V                             inject first component
      `inj₂ W                             inject second component

### Typing

    Γ ⊢ M ⦂ A
    -------------------- `inj₁ or ⊎-I₁
    Γ ⊢ `inj₁ M ⦂ A `⊎ B

    Γ ⊢ N ⦂ B
    -------------------- `inj₂ or ⊎-I₂
    Γ ⊢ `inj₂ N ⦂ A `⊎ B

    Γ ⊢ L ⦂ A `⊎ B
    Γ , x ⦂ A ⊢ M ⦂ C
    Γ , y ⦂ B ⊢ N ⦂ C
    ----------------------------------------- case⊎ or ⊎-E
    Γ ⊢ case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ] ⦂ C

### Reduction

    M —→ M′
    ------------------- ξ-inj₁
    `inj₁ M —→ `inj₁ M′

    N —→ N′
    ------------------- ξ-inj₂
    `inj₂ N —→ `inj₂ N′

    L —→ L′
    ---------------------------------------------------------------------- ξ-case⊎
    case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ] —→ case⊎ L′ [inj₁ x ⇒ M |inj₂ y ⇒ N ]

    --------------------------------------------------------- β-inj₁
    case⊎ (`inj₁ V) [inj₁ x ⇒ M |inj₂ y ⇒ N ] —→ M [ x := V ]

    --------------------------------------------------------- β-inj₂
    case⊎ (`inj₂ W) [inj₁ x ⇒ M |inj₂ y ⇒ N ] —→ N [ y := W ]

### Example

Here is a function to swap the components of a sum:

    swap⊎ : ∅ ⊢ A `⊎ B ⇒ B `⊎ A
    swap⊎ = ƛ z ⇒ case⊎ z
                    [inj₁ x ⇒ `inj₂ x
                    |inj₂ y ⇒ `inj₁ y ]


## Unit type

For the unit type, there is a way to introduce
values of the type but no way to eliminate values of the type.
There are no reduction rules.

### Syntax

    A, B, C ::= ...                     Types
      `⊤                                  unit type

    L, M, N ::= ...                     Terms
      `tt                                 unit value

    V, W ::= ...                        Values
      `tt                                 unit value

### Typing

    ------------ `tt or ⊤-I
    Γ ⊢ `tt ⦂ `⊤

### Reduction

(none)

### Example

Here is the isomorphism between `A` and ``A `× `⊤``:

    to×⊤ : ∅ ⊢ A ⇒ A `× `⊤
    to×⊤ = ƛ x ⇒ `⟨ x , `tt ⟩

    from×⊤ : ∅ ⊢ A `× `⊤ ⇒ A
    from×⊤ = ƛ z ⇒ `proj₁ z


## Alternative formulation of unit type

There is an alternative formulation of the unit type, where in place of
no way to eliminate the type we have a case term that binds zero variables.
We repeat the syntax in full, but only give the new type and reduction rules:

### Syntax

    A, B, C ::= ...                     Types
      `⊤                                  unit type

    L, M, N ::= ...                     Terms
      `tt                                 unit value
      `case⊤ L [tt⇒ N ]                   case

    V, W ::= ...                        Values
      `tt                                 unit value

### Typing

    Γ ⊢ L ⦂ `⊤
    Γ ⊢ M ⦂ A
    ------------------------ case⊤ or ⊤-E
    Γ ⊢ case⊤ L [tt⇒ M ] ⦂ A

### Reduction

    L —→ L′
    ------------------------------------- ξ-case⊤
    case⊤ L [tt⇒ M ] —→ case⊤ L′ [tt⇒ M ]

    ----------------------- β-case⊤
    case⊤ `tt [tt⇒ M ] —→ M

### Example

Here is half the isomorphism between `A` and ``A `× `⊤`` rewritten in the new notation:

    from×⊤-case : ∅ ⊢ A `× `⊤ ⇒ A
    from×⊤-case = ƛ z ⇒ case× z
                          [⟨ x , y ⟩⇒ case⊤ y
                                        [tt⇒ x ] ]


### Translation

We can translate the alternative formulation into one without case:

    (case⊤ L [tt⇒ M ]) †  =  `let z `= (L †) `in (M †)

Here `z` is a variable that does not appear free in `M`.


## Empty type

For the empty type, there is a way to eliminate values of
the type but no way to introduce values of the type.  There are no
values of the type and no β rule, but there is a ξ rule.  The `case⊥`
construct plays a role similar to `⊥-elim` in Agda:

### Syntax

    A, B, C ::= ...                     Types
      `⊥                                  empty type

    L, M, N ::= ...                     Terms
      case⊥ L []                          case

### Typing

    Γ ⊢ L ⦂ `⊥
    ------------------ case⊥ or ⊥-E
    Γ ⊢ case⊥ L [] ⦂ A

### Reduction

    L —→ L′
    ------------------------- ξ-case⊥
    case⊥ L [] —→ case⊥ L′ []

### Example

Here is the isomorphism between `A` and ``A `⊎ `⊥``:

    to⊎⊥ : ∅ ⊢ A ⇒ A `⊎ `⊥
    to⊎⊥ = ƛ x ⇒ `inj₁ x

    from⊎⊥ : ∅ ⊢ A `⊎ `⊥ ⇒ A
    from⊎⊥ = ƛ z ⇒ case⊎ z
                     [inj₁ x ⇒ x
                     |inj₂ y ⇒ case⊥ y
                                 [] ]

## Lists

### Syntax

    A, B, C ::= ...                     Types
      `List A                             list type

    L, M, N ::= ...                     Terms
      `[]                                 nil
      M `∷ N                              cons
      caseL L [[]⇒ M | x ∷ y ⇒ N ]        case

    V, W ::= ...                        Values
      `[]                                 nil
      V `∷ W                              cons

### Typing

    ----------------- `[] or List-I₁
    Γ ⊢ `[] ⦂ `List A

    Γ ⊢ M ⦂ A
    Γ ⊢ N ⦂ `List A
    -------------------- _`∷_ or List-I₂
    Γ ⊢ M `∷ N ⦂ `List A

    Γ ⊢ L ⦂ `List A
    Γ ⊢ M ⦂ B
    Γ , x ⦂ A , xs ⦂ `List A ⊢ N ⦂ B
    -------------------------------------- caseL or List-E
    Γ ⊢ caseL L [[]⇒ M | x ∷ xs ⇒ N ] ⦂ B

### Reduction

    M —→ M′
    ----------------- ξ-∷₁
    M `∷ N —→ M′ `∷ N

    N —→ N′
    ----------------- ξ-∷₂
    V `∷ N —→ V `∷ N′

    L —→ L′
    --------------------------------------------------------------- ξ-caseL
    caseL L [[]⇒ M | x ∷ xs ⇒ N ] —→ caseL L′ [[]⇒ M | x ∷ xs ⇒ N ]

    ------------------------------------ β-[]
    caseL `[] [[]⇒ M | x ∷ xs ⇒ N ] —→ M

    --------------------------------------------------------------- β-∷
    caseL (V `∷ W) [[]⇒ M | x ∷ xs ⇒ N ] —→ N [ x := V ][ xs := W ]

### Example

Here is the map function for lists:

    mapL : ∅ ⊢ (A ⇒ B) ⇒ `List A ⇒ `List B
    mapL = μ mL ⇒ ƛ f ⇒ ƛ xs ⇒
             caseL xs
               [[]⇒ `[]
               | x ∷ xs ⇒ f · x `∷ mL · f · xs ]


## Formalisation

We now show how to formalise

  * primitive numbers
  * _let_ bindings
  * products
  * an alternative formulation of products

and leave formalisation of the remaining constructs as an exercise.


### Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
```


### Syntax

```
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_
infixr 9 _`×_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infixl 8 _`*_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_
```

### Types

```
data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type
  Nat   : Type
  _`×_  : Type → Type → Type
-- begin
  _`⊎_  : Type → Type → Type
  `⊤    : Type
  `⊥    : Type
  `List : Type → Type
-- end
```

### Contexts

```
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```

### Variables and the lookup judgment

```
data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ B
      ---------
    → Γ , A ∋ B
```

### Terms and the typing judgment

```
data _⊢_ : Context → Type → Set where

  -- variables

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  -- functions

  ƛ_  :  ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  -- naturals

  `zero : ∀ {Γ}
      ------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      -----
    → Γ ⊢ A

  -- fixpoint

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ----------
    → Γ ⊢ A

  -- primitive numbers

  con : ∀ {Γ}
    → ℕ
      -------
    → Γ ⊢ Nat

  _`*_ : ∀ {Γ}
    → Γ ⊢ Nat
    → Γ ⊢ Nat
      -------
    → Γ ⊢ Nat

  -- let

  `let : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ , A ⊢ B
      ----------
    → Γ ⊢ B

  -- products

  `⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ B
      -----------
    → Γ ⊢ A `× B

  `proj₁ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      -----------
    → Γ ⊢ A

  `proj₂ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      -----------
    → Γ ⊢ B

  -- alternative formulation of products

  case× : ∀ {Γ A B C}
    → Γ ⊢ A `× B
    → Γ , A , B ⊢ C
      --------------
    → Γ ⊢ C

-- begin
  -- sums

  `inj₁ : ∀ {Γ A B}
    → Γ ⊢ A
      -----------
    → Γ ⊢ A `⊎ B

  `inj₂ : ∀ {Γ A B}
    → Γ ⊢ B
      -----------
    → Γ ⊢ A `⊎ B

  case⊎ : ∀ {Γ A B C}
    → Γ ⊢ A `⊎ B
    → Γ , A ⊢ C
    → Γ , B ⊢ C
      -----------
    → Γ ⊢ C

  -- unit type

  `tt : ∀ {Γ}
      -------
    → Γ ⊢ `⊤

  -- alternative formulation of unit type

  case⊤ : ∀ {Γ A}
    → Γ ⊢ `⊤
    → Γ ⊢ A
      ------
    → Γ ⊢ A

  -- empty type

  case⊥ : ∀ {Γ A}
    → Γ ⊢ `⊥
      -------
    → Γ ⊢ A

  -- lists

  `[] : ∀ {Γ A}
      ------------
    → Γ ⊢ `List A

  _`∷_ : ∀ {Γ A}
    → Γ ⊢ A
    → Γ ⊢ `List A
      ------------
    → Γ ⊢ `List A

  caseL : ∀ {Γ A B}
    → Γ ⊢ `List A
    → Γ ⊢ B
    → Γ , A , `List A ⊢ B
      --------------------
    → Γ ⊢ B
-- end
```

### Abbreviating de Bruijn indices

```
length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
lookup {(Γ , _)} {(suc n)} (s≤s p)    =  lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero}    (s≤s z≤n)  =  Z
count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ}  =  ` count (toWitness n∈Γ)
```

## Renaming

```
ext : ∀ {Γ Δ}
  → (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , A ∋ B → Δ , A ∋ B)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
rename ρ (`suc M)       =  `suc (rename ρ M)
rename ρ (case L M N)   =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ N)          =  μ (rename (ext ρ) N)
rename ρ (con n)        =  con n
rename ρ (M `* N)       =  rename ρ M `* rename ρ N
rename ρ (`let M N)     =  `let (rename ρ M) (rename (ext ρ) N)
rename ρ `⟨ M , N ⟩     =  `⟨ rename ρ M , rename ρ N ⟩
rename ρ (`proj₁ L)     =  `proj₁ (rename ρ L)
rename ρ (`proj₂ L)     =  `proj₂ (rename ρ L)
rename ρ (case× L M)    =  case× (rename ρ L) (rename (ext (ext ρ)) M)
-- begin
rename ρ (`inj₁ M)      =  `inj₁ (rename ρ M)
rename ρ (`inj₂ N)      =  `inj₂ (rename ρ N)
rename ρ (case⊎ L M N)  =  case⊎ (rename ρ L) (rename (ext ρ) M) (rename (ext ρ) N)
rename ρ `tt            =  `tt
rename ρ (case⊤ L M)    =  case⊤ (rename ρ L) (rename ρ M)
rename ρ (case⊥ L)      =  case⊥ (rename ρ L)
rename ρ `[]            =  `[]
rename ρ (M `∷ N)       =  rename ρ M `∷ rename ρ N
rename ρ (caseL L M N)  =  caseL (rename ρ L) (rename ρ M) (rename (ext (ext ρ)) N)
-- end
```

## Simultaneous Substitution

```
exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A B} → Γ , A ∋ B → Δ , A ⊢ B)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ} → (∀ {C} → Γ ∋ C → Δ ⊢ C) → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`zero)        =  `zero
subst σ (`suc M)       =  `suc (subst σ M)
subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N)          =  μ (subst (exts σ) N)
subst σ (con n)        =  con n
subst σ (M `* N)       =  subst σ M `* subst σ N
subst σ (`let M N)     =  `let (subst σ M) (subst (exts σ) N)
subst σ `⟨ M , N ⟩     =  `⟨ subst σ M , subst σ N ⟩
subst σ (`proj₁ L)     =  `proj₁ (subst σ L)
subst σ (`proj₂ L)     =  `proj₂ (subst σ L)
subst σ (case× L M)    =  case× (subst σ L) (subst (exts (exts σ)) M)
-- begin
subst σ (`inj₁ M)      =  `inj₁ (subst σ M)
subst σ (`inj₂ N)      =  `inj₂ (subst σ N)
subst σ (case⊎ L M N)  =  case⊎ (subst σ L) (subst (exts σ) M) (subst (exts σ) N)
subst σ `tt            =  `tt
subst σ (case⊤ L M)    =  case⊤ (subst σ L) (subst σ M)
subst σ (case⊥ L)      =  case⊥ (subst σ L)
subst σ `[]            =  `[]
subst σ (M `∷ N)       =  subst σ M `∷ subst σ N
subst σ (caseL L M N)  =  caseL (subst σ L) (subst σ M) (subst (exts (exts σ)) N)
-- end
```

## Single and double substitution

```
substZero : ∀ {Γ}{A B} → Γ ⊢ A → Γ , A ∋ B → Γ ⊢ B
substZero V Z      =  V
substZero V (S x)  =  ` x

_[_] : ∀ {Γ A B}
  → Γ , A ⊢ B
  → Γ ⊢ A
    ---------
  → Γ ⊢ B
_[_] {Γ} {A} N V =  subst {Γ , A} {Γ} (substZero V) N

_[_][_] : ∀ {Γ A B C}
  → Γ , A , B ⊢ C
  → Γ ⊢ A
  → Γ ⊢ B
    -------------
  → Γ ⊢ C
_[_][_] {Γ} {A} {B} N V W =  subst {Γ , A , B} {Γ} σ N
  where
  σ : ∀ {C} → Γ , A , B ∋ C → Γ ⊢ C
  σ Z          =  W
  σ (S Z)      =  V
  σ (S (S x))  =  ` x
```

## Values

```
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  -- functions

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  -- naturals

  V-zero : ∀ {Γ}
      -----------------
    → Value (`zero {Γ})

  V-suc_ : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)

  -- primitives

  V-con : ∀ {Γ n}
      -----------------
    → Value (con {Γ} n)

  -- products

  V-⟨_,_⟩ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------
    → Value `⟨ V , W ⟩

-- begin
  -- sums

  V-inj₁ : ∀ {Γ A B} {V : Γ ⊢ A}
    → Value V
      ----------------
    → Value (`inj₁ {B = B} V)

  V-inj₂ : ∀ {Γ A B} {W : Γ ⊢ B}
    → Value W
      ----------------
    → Value (`inj₂ {A = A} W)

  -- unit type

  V-tt : ∀ {Γ}
      ----------
    → Value (`tt {Γ = Γ})

  -- lists

  V-[] : ∀ {Γ A}
      ---------
    → Value (`[] {Γ = Γ} {A = A})

  V-∷ : ∀ {Γ A} {V : Γ ⊢ A} {W : Γ ⊢ `List A}
    → Value V
    → Value W
      ---------------
    → Value (V `∷ W)
-- end
```

Implicit arguments need to be supplied when they are
not fixed by the given arguments.

## Reduction

```
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  -- functions

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
    → Value V
      --------------------
    → (ƛ N) · V —→ N [ V ]

  -- naturals

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]

  -- fixpoint

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
      ----------------
    → μ N —→ N [ μ N ]

  -- primitive numbers

  ξ-*₁ : ∀ {Γ} {L L′ M : Γ ⊢ Nat}
    → L —→ L′
      -----------------
    → L `* M —→ L′ `* M

  ξ-*₂ : ∀ {Γ} {V M M′ : Γ ⊢ Nat}
    → Value V
    → M —→ M′
      -----------------
    → V `* M —→ V `* M′

  δ-* : ∀ {Γ c d}
      ---------------------------------
    → con {Γ} c `* con d —→ con (c * d)

  -- let

  ξ-let : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ , A ⊢ B}
    → M —→ M′
      ---------------------
    → `let M N —→ `let M′ N

  β-let : ∀ {Γ A B} {V : Γ ⊢ A} {N : Γ , A ⊢ B}
    → Value V
      -------------------
    → `let V N —→ N [ V ]

  -- products

  ξ-⟨,⟩₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ ⊢ B}
    → M —→ M′
      -------------------------
    → `⟨ M , N ⟩ —→ `⟨ M′ , N ⟩

  ξ-⟨,⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {N N′ : Γ ⊢ B}
    → Value V
    → N —→ N′
      -------------------------
    → `⟨ V , N ⟩ —→ `⟨ V , N′ ⟩

  ξ-proj₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
    → L —→ L′
      ---------------------
    → `proj₁ L —→ `proj₁ L′

  ξ-proj₂ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
    → L —→ L′
      ---------------------
    → `proj₂ L —→ `proj₂ L′

  β-proj₁ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------------
    → `proj₁ `⟨ V , W ⟩ —→ V

  β-proj₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------------
    → `proj₂ `⟨ V , W ⟩ —→ W

  -- alternative formulation of products

  ξ-case× : ∀ {Γ A B C} {L L′ : Γ ⊢ A `× B} {M : Γ , A , B ⊢ C}
    → L —→ L′
      -----------------------
    → case× L M —→ case× L′ M

  β-case× : ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {M : Γ , A , B ⊢ C}
    → Value V
    → Value W
      ----------------------------------
    → case× `⟨ V , W ⟩ M —→ M [ V ][ W ]

-- begin
  -- sums

  ξ-inj₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A}
    → M —→ M′
      ------------------------------------
    → `inj₁ {B = B} M —→ `inj₁ {B = B} M′

  ξ-inj₂ : ∀ {Γ A B} {N N′ : Γ ⊢ B}
    → N —→ N′
      ------------------------------------
    → `inj₂ {A = A} N —→ `inj₂ {A = A} N′

  ξ-case⊎ : ∀ {Γ A B C} {L L′ : Γ ⊢ A `⊎ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → L —→ L′
      ----------------------------
    → case⊎ L M N —→ case⊎ L′ M N

  β-inj₁ : ∀ {Γ A B C} {V : Γ ⊢ A} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → Value V
      ----------------------------
    → case⊎ (`inj₁ V) M N —→ M [ V ]

  β-inj₂ : ∀ {Γ A B C} {W : Γ ⊢ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → Value W
      ----------------------------
    → case⊎ (`inj₂ W) M N —→ N [ W ]

  -- alternative formulation of unit type

  ξ-case⊤ : ∀ {Γ A} {L L′ : Γ ⊢ `⊤} {M : Γ ⊢ A}
    → L —→ L′
      ----------------------------
    → case⊤ L M —→ case⊤ L′ M

  β-case⊤ : ∀ {Γ A} {M : Γ ⊢ A}
      ----------------------------
    → case⊤ `tt M —→ M

  -- empty type

  ξ-case⊥ : ∀ {Γ A} {L L′ : Γ ⊢ `⊥}
    → L —→ L′
      ----------------------------
    → case⊥ {A = A} L —→ case⊥ {A = A} L′

  -- lists

  ξ-∷₁ : ∀ {Γ A} {M M′ : Γ ⊢ A} {N : Γ ⊢ `List A}
    → M —→ M′
      ----------------------------
    → M `∷ N —→ M′ `∷ N

  ξ-∷₂ : ∀ {Γ A} {V : Γ ⊢ A} {N N′ : Γ ⊢ `List A}
    → Value V
    → N —→ N′
      ----------------------------
    → V `∷ N —→ V `∷ N′

  ξ-caseL : ∀ {Γ A B} {L L′ : Γ ⊢ `List A} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
    → L —→ L′
      ----------------------------
    → caseL L M N —→ caseL L′ M N

  β-[] : ∀ {Γ A B} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
      ----------------------------
    → caseL `[] M N —→ M

  β-∷ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ `List A} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
    → Value V
    → Value W
      ----------------------------
    → caseL (V `∷ W) M N —→ N [ V ][ W ]
-- end
```

## Reflexive and transitive closure

```
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M —↠ M

  _—→⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```


## Values do not reduce

```
V¬—→ : ∀ {Γ A} {M N : Γ ⊢ A}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ V-ƛ          ()
V¬—→ V-zero       ()
V¬—→ (V-suc VM)   (ξ-suc M—→M′)     =  V¬—→ VM M—→M′
V¬—→ V-con        ()
V¬—→ V-⟨ VM , _ ⟩ (ξ-⟨,⟩₁ M—→M′)    =  V¬—→ VM M—→M′
V¬—→ V-⟨ _ , VN ⟩ (ξ-⟨,⟩₂ _ N—→N′)  =  V¬—→ VN N—→N′
-- begin
V¬—→ (V-inj₁ VM)  (ξ-inj₁ M—→M′)    =  V¬—→ VM M—→M′
V¬—→ (V-inj₂ VN)  (ξ-inj₂ N—→N′)    =  V¬—→ VN N—→N′
V¬—→ V-tt         ()
V¬—→ V-[]         ()
V¬—→ (V-∷ VM VN)  (ξ-∷₁ M—→M′)      =  V¬—→ VM M—→M′
V¬—→ (V-∷ VM VN)  (ξ-∷₂ _ N—→N′)    =  V¬—→ VN N—→N′
-- end
```


## Progress

```
data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {A}
  → (M : ∅ ⊢ A)
    -----------
  → Progress M
progress (` ())
progress (ƛ N)                              =  done V-ƛ
progress (L · M) with progress L
...    | step L—→L′                         =  step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M
...        | step M—→M′                     =  step (ξ-·₂ V-ƛ M—→M′)
...        | done VM                        =  step (β-ƛ VM)
progress (`zero)                            =  done V-zero
progress (`suc M) with progress M
...    | step M—→M′                         =  step (ξ-suc M—→M′)
...    | done VM                            =  done (V-suc VM)
progress (case L M N) with progress L
...    | step L—→L′                         =  step (ξ-case L—→L′)
...    | done V-zero                        =  step β-zero
...    | done (V-suc VL)                    =  step (β-suc VL)
progress (μ N)                              =  step β-μ
progress (con n)                            =  done V-con
progress (L `* M) with progress L
...    | step L—→L′                         =  step (ξ-*₁ L—→L′)
...    | done V-con with progress M
...        | step M—→M′                     =  step (ξ-*₂ V-con M—→M′)
...        | done V-con                     =  step δ-*
progress (`let M N) with progress M
...    | step M—→M′                         =  step (ξ-let M—→M′)
...    | done VM                            =  step (β-let VM)
progress `⟨ M , N ⟩ with progress M
...    | step M—→M′                         =  step (ξ-⟨,⟩₁ M—→M′)
...    | done VM with progress N
...        | step N—→N′                     =  step (ξ-⟨,⟩₂ VM N—→N′)
...        | done VN                        =  done (V-⟨ VM , VN ⟩)
progress (`proj₁ L) with progress L
...    | step L—→L′                         =  step (ξ-proj₁ L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₁ VM VN)
progress (`proj₂ L) with progress L
...    | step L—→L′                         =  step (ξ-proj₂ L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₂ VM VN)
progress (case× L M) with progress L
...    | step L—→L′                         =  step (ξ-case× L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-case× VM VN)
-- begin
progress (`inj₁ M) with progress M
...    | step M—→M′                         =  step (ξ-inj₁ M—→M′)
...    | done VM                            =  done (V-inj₁ VM)
progress (`inj₂ N) with progress N
... | step N—→N′                            =  step (ξ-inj₂ N—→N′)
... | done VN                               =  done (V-inj₂ VN)
progress (case⊎ L M N) with progress L
... | step L—→L′                            =  step (ξ-case⊎ L—→L′)
... | done (V-inj₁ VV)                      =  step (β-inj₁ VV)
... | done (V-inj₂ VW)                      =  step (β-inj₂ VW)
progress `tt                                =  done V-tt
progress (case⊤ L N)  with progress L
... | step L—→L′                            =  step (ξ-case⊤ L—→L′)
... | done V-tt                             =  step β-case⊤
progress (case⊥ L) with progress L
... | step L—→L′                            =  step (ξ-case⊥ L—→L′)
progress `[]                                =  done V-[]
progress (M `∷ N) with progress M
... | step M—→M′                            =  step (ξ-∷₁ M—→M′)
... | done VM with progress N
...   | step N—→N′                          =  step (ξ-∷₂ VM N—→N′)
...   | done VN                             =  done (V-∷ VM VN)
progress (caseL L M N) with progress L
... | step L—→L′                            =  step (ξ-caseL L—→L′)
... | done V-[]                             =  step β-[]
... | done (V-∷ VV VW)                      =  step (β-∷ VV VW)
-- end
```


## Evaluation

```
record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N

data Steps {A} : ∅ ⊢ A → Set where

  steps : {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```


## Examples

```
cube : ∅ ⊢ Nat ⇒ Nat
cube = ƛ (# 0 `* # 0 `* # 0)

_ : cube · con 2 —↠ con 8
_ =
  begin
    cube · con 2
  —→⟨ β-ƛ V-con ⟩
    con 2 `* con 2 `* con 2
  —→⟨ ξ-*₁ δ-* ⟩
    con 4 `* con 2
  —→⟨ δ-* ⟩
    con 8
  ∎

exp10 : ∅ ⊢ Nat ⇒ Nat
exp10 = ƛ (`let (# 0 `* # 0)
            (`let (# 0 `* # 0)
              (`let (# 0 `* # 2)
                (# 0 `* # 0))))

_ : exp10 · con 2 —↠ con 1024
_ =
  begin
    exp10 · con 2
  —→⟨ β-ƛ V-con ⟩
    `let (con 2 `* con 2) (`let (# 0 `* # 0) (`let (# 0 `* con 2) (# 0 `* # 0)))
  —→⟨ ξ-let δ-* ⟩
    `let (con 4) (`let (# 0 `* # 0) (`let (# 0 `* con 2) (# 0 `* # 0)))
  —→⟨ β-let V-con ⟩
    `let (con 4 `* con 4) (`let (# 0 `* con 2) (# 0 `* # 0))
  —→⟨ ξ-let δ-* ⟩
    `let (con 16) (`let (# 0 `* con 2) (# 0 `* # 0))
  —→⟨ β-let V-con ⟩
    `let (con 16 `* con 2) (# 0 `* # 0)
  —→⟨ ξ-let δ-* ⟩
    `let (con 32) (# 0 `* # 0)
  —→⟨ β-let V-con ⟩
    con 32 `* con 32
  —→⟨ δ-* ⟩
    con 1024
  ∎

swap× : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
swap× = ƛ `⟨ `proj₂ (# 0) , `proj₁ (# 0) ⟩

_ : swap× · `⟨ con 42 , `zero ⟩ —↠ `⟨ `zero , con 42 ⟩
_ =
  begin
    swap× · `⟨ con 42 , `zero ⟩
  —→⟨ β-ƛ V-⟨ V-con , V-zero ⟩ ⟩
    `⟨ `proj₂ `⟨ con 42 , `zero ⟩ , `proj₁ `⟨ con 42 , `zero ⟩ ⟩
  —→⟨ ξ-⟨,⟩₁ (β-proj₂ V-con V-zero) ⟩
    `⟨ `zero , `proj₁ `⟨ con 42 , `zero ⟩ ⟩
  —→⟨ ξ-⟨,⟩₂ V-zero (β-proj₁ V-con V-zero) ⟩
    `⟨ `zero , con 42 ⟩
  ∎

swap×-case : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
swap×-case = ƛ case× (# 0) `⟨ # 0 , # 1 ⟩

_ : swap×-case · `⟨ con 42 , `zero ⟩ —↠ `⟨ `zero , con 42 ⟩
_ =
  begin
     swap×-case · `⟨ con 42 , `zero ⟩
   —→⟨ β-ƛ V-⟨ V-con , V-zero ⟩ ⟩
     case× `⟨ con 42 , `zero ⟩ `⟨ # 0 , # 1 ⟩
   —→⟨ β-case× V-con V-zero ⟩
     `⟨ `zero , con 42 ⟩
   ∎
```

#### Exercise `More` (recommended and practice)

Formalise the remaining constructs defined in this chapter.
Make your changes in this file.
Evaluate each example, applied to data as needed,
to confirm it returns the expected answer:

  * sums (recommended)
  * unit type (practice)
  * an alternative formulation of unit type (practice)
  * empty type (recommended)
  * lists (practice)

Please delimit any code you add as follows:

    -- begin
    -- end


#### Exercise `double-subst` (stretch)

Show that a double substitution is equivalent to two single
substitutions.
```
-- postulate
--   double-subst :
--     ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {N : Γ , A , B ⊢ C} →
--       N [ V ][ W ] ≡ (N [ rename S_ W ]) [ V ]
```
Note the arguments need to be swapped and `W` needs to have
its context adjusted via renaming in order for the right-hand
side to be well typed.

```
open import Function using (_∘_)
open Eq using (cong; cong₂; cong-app; sym; trans)
open import plfa.part1.Isomorphism using (extensionality; ∀-extensionality)
module EqR = Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

implicit-extensionality : ∀ {A : Set} {B : A → Set} {f g : {x : A} → B x} →
  (∀ {x} → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
implicit-extensionality = helper ∀-extensionality
  where
    open import Axiom.Extensionality.Propositional
      using ()
      renaming (implicit-extensionality to helper)

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v w z}
  → x ≡ y
  → u ≡ v
  → w ≡ z
  → f x u w ≡ f y v z
cong₃ f refl refl refl = refl

cong-ext : ∀ {Γ₁ Γ₂} {f : ∀ {C} → Γ₁ ∋ C → Γ₂ ∋ C} {g : ∀ {D} → Γ₁ ∋ D → Γ₂ ∋ D}
  → (∀ {A} → f {A} ≡ g {A})
  → (∀ {A B} → ext f {A} {B} ≡ ext g)
cong-ext f≡g = cong (λ s → ext (λ {A} → s {A})) (implicit-extensionality f≡g)

cong-rename : ∀ {Γ₁ Γ₂} {f : ∀ {C} → Γ₁ ∋ C → Γ₂ ∋ C} {g : ∀ {D} → Γ₁ ∋ D → Γ₂ ∋ D}
  → (∀ {A} → f {A} ≡ g {A})
  → (∀ {A} → rename f {A} ≡ rename g)
cong-rename f≡g = cong (λ s → rename (λ {A} → s {A})) (implicit-extensionality f≡g)

cong-exts : ∀ {Γ₁ Γ₂} {f : ∀ {C} → Γ₁ ∋ C → Γ₂ ⊢ C} {g : ∀ {D} → Γ₁ ∋ D → Γ₂ ⊢ D}
  → (∀ {A} → f {A} ≡ g {A})
  → (∀ {A B} → exts f {A} {B} ≡ exts g)
cong-exts f≡g = cong (λ s → exts (λ {A} → s {A})) (implicit-extensionality f≡g)

cong-subst : ∀ {Γ₁ Γ₂} {f : ∀ {C} → Γ₁ ∋ C → Γ₂ ⊢ C} {g : ∀ {D} → Γ₁ ∋ D → Γ₂ ⊢ D}
  → (∀ {A} → f {A} ≡ g {A})
  → (∀ {A} → subst f {A} ≡ subst g)
cong-subst f≡g = cong (λ s → subst (λ {A} → s {A})) (implicit-extensionality f≡g)

ext-ext-compose : ∀ {Γ₁ Γ₂ Γ₃}
  → (ρ₁ : ∀ {C} → Γ₁ ∋ C → Γ₂ ∋ C)
  → (ρ₂ : ∀ {D} → Γ₂ ∋ D → Γ₃ ∋ D)
  → (∀ {A B} → ext ρ₂ ∘ ext ρ₁ {A} {B} ≡ ext (ρ₂ ∘ ρ₁))
ext-ext-compose {Γ₁ = Γ₁} ρ₁ ρ₂ = extensionality helper
  where
    helper : ∀ {A B} (X : Γ₁ , A ∋ B)
      → (ext ρ₂ ∘ ext ρ₁) X ≡ ext (ρ₂ ∘ ρ₁) X
    helper Z     = refl
    helper (S X) = refl

rename-compose : ∀ {Γ₁ Γ₂ Γ₃}
  → (ρ₁ : ∀ {B} → Γ₁ ∋ B → Γ₂ ∋ B)
  → (ρ₂ : ∀ {C} → Γ₂ ∋ C → Γ₃ ∋ C)
  → (∀ {A} → rename ρ₂ ∘ rename ρ₁ {A} ≡ rename (ρ₂ ∘ ρ₁))
rename-compose ρ₁ ρ₂ = extensionality (helper ρ₁ ρ₂)
  where
    helper : ∀ {Γ₁ Γ₂ Γ₃}
      → (ρ₁ : ∀ {B} → Γ₁ ∋ B → Γ₂ ∋ B)
      → (ρ₂ : ∀ {C} → Γ₂ ∋ C → Γ₃ ∋ C)
      → (∀ {A} (X : Γ₁ ⊢ A) → (rename ρ₂ ∘ rename ρ₁) X ≡ rename (ρ₂ ∘ ρ₁) X)
    ext-helper : ∀ {Γ₁ Γ₂ Γ₃}
      → (ρ₁ : ∀ {C} → Γ₁ ∋ C → Γ₂ ∋ C)
      → (ρ₂ : ∀ {D} → Γ₂ ∋ D → Γ₃ ∋ D)
      → (∀ {A B} (X : Γ₁ , A ⊢ B) → (rename (ext ρ₂) ∘ rename (ext ρ₁)) X ≡ rename (ext (ρ₂ ∘ ρ₁)) X)
    extext-helper : ∀ {Γ₁ Γ₂ Γ₃}
      → (ρ₁ : ∀ {D} → Γ₁ ∋ D → Γ₂ ∋ D)
      → (ρ₂ : ∀ {E} → Γ₂ ∋ E → Γ₃ ∋ E)
      → (∀ {A B C} (X : Γ₁ , A , B ⊢ C) → (rename (ext (ext ρ₂)) ∘ rename (ext (ext ρ₁))) X ≡ rename (ext (ext (ρ₂ ∘ ρ₁))) X)

    helper ρ₁ ρ₂ (` x)           = refl
    helper ρ₁ ρ₂ (ƛ X)           = cong ƛ_ (ext-helper ρ₁ ρ₂ X)
    helper ρ₁ ρ₂ (X · X₁)        = cong₂ _·_ (helper ρ₁ ρ₂ X) (helper ρ₁ ρ₂ X₁)
    helper ρ₁ ρ₂ `zero           = refl
    helper ρ₁ ρ₂ (`suc X)        = cong `suc_ (helper ρ₁ ρ₂ X)
    helper ρ₁ ρ₂ (case X X₁ X₂)  = cong₃ case (helper ρ₁ ρ₂ X) (helper ρ₁ ρ₂ X₁) (ext-helper ρ₁ ρ₂ X₂)
    helper ρ₁ ρ₂ (μ X)           = cong μ_ (ext-helper ρ₁ ρ₂ X)
    helper ρ₁ ρ₂ (con x)         = refl
    helper ρ₁ ρ₂ (X `* X₁)       = cong₂ _`*_ (helper ρ₁ ρ₂ X) (helper ρ₁ ρ₂ X₁)
    helper ρ₁ ρ₂ (`let X X₁)     = cong₂ `let (helper ρ₁ ρ₂ X) (ext-helper ρ₁ ρ₂ X₁)
    helper ρ₁ ρ₂ `⟨ X , X₁ ⟩     = cong₂ `⟨_,_⟩ (helper ρ₁ ρ₂ X) (helper ρ₁ ρ₂ X₁)
    helper ρ₁ ρ₂ (`proj₁ X)      = cong `proj₁ (helper ρ₁ ρ₂ X)
    helper ρ₁ ρ₂ (`proj₂ X)      = cong `proj₂ (helper ρ₁ ρ₂ X)
    helper ρ₁ ρ₂ (case× X X₁)    = cong₂ case× (helper ρ₁ ρ₂ X) (extext-helper ρ₁ ρ₂ X₁)
    helper ρ₁ ρ₂ (`inj₁ X)       = cong `inj₁ (helper ρ₁ ρ₂ X)
    helper ρ₁ ρ₂ (`inj₂ X)       = cong `inj₂ (helper ρ₁ ρ₂ X)
    helper ρ₁ ρ₂ (case⊎ X X₁ X₂) = cong₃ case⊎ (helper ρ₁ ρ₂ X) (ext-helper ρ₁ ρ₂ X₁) (ext-helper ρ₁ ρ₂ X₂)
    helper ρ₁ ρ₂ `tt             = refl
    helper ρ₁ ρ₂ (case⊤ X X₁)    = cong₂ case⊤ (helper ρ₁ ρ₂ X) (helper ρ₁ ρ₂ X₁)
    helper ρ₁ ρ₂ (case⊥ X)       = cong case⊥ (helper ρ₁ ρ₂ X)
    helper ρ₁ ρ₂ `[]             = refl
    helper ρ₁ ρ₂ (X `∷ X₁)       = cong₂ _`∷_ (helper ρ₁ ρ₂ X) (helper ρ₁ ρ₂ X₁)
    helper ρ₁ ρ₂ (caseL X X₁ X₂) = cong₃ caseL (helper ρ₁ ρ₂ X) (helper ρ₁ ρ₂ X₁) (extext-helper ρ₁ ρ₂ X₂)

    ext-helper ρ₁ ρ₂ X =
      EqR.begin
        (rename (ext ρ₂) ∘ rename (ext ρ₁)) X
      EqR.≡⟨ helper (ext ρ₁) (ext ρ₂) X ⟩
        rename (ext ρ₂ ∘ ext ρ₁) X
      EqR.≡⟨ cong-app (cong-rename (ext-ext-compose ρ₁ ρ₂)) X ⟩
        rename (ext (ρ₂ ∘ ρ₁)) X
      EqR.∎

    extext-helper ρ₁ ρ₂ X =
      EqR.begin
        (rename (ext (ext ρ₂)) ∘ rename (ext (ext ρ₁))) X
      EqR.≡⟨ ext-helper (ext ρ₁) (ext ρ₂) X ⟩
        rename (ext (ext ρ₂ ∘ ext ρ₁)) X
      EqR.≡⟨ cong-app (cong-rename (cong-ext (ext-ext-compose ρ₁ ρ₂))) X ⟩
        rename (ext (ext (ρ₂ ∘ ρ₁))) X
      EqR.∎

rename-ext-compose : ∀ {Γ₁ Γ₂ Γ₃}
  → (σ : ∀ {C} → Γ₁ ∋ C → Γ₂ ⊢ C)
  → (ρ : ∀ {D} → Γ₂ ∋ D → Γ₃ ∋ D)
  → (∀ {A B} → rename (ext ρ) ∘ exts σ {A} {B} ≡ exts (rename ρ ∘ σ))
rename-ext-compose {Γ₁ = Γ₁} σ ρ = extensionality helper
  where
    helper : ∀ {A B} (X : Γ₁ , A ∋ B)
      → (rename (ext ρ) ∘ exts σ) X ≡ exts (rename ρ ∘ σ) X
    helper Z     = refl
    helper (S X) =
      EqR.begin
        (rename (ext ρ) ∘ exts σ) (S X)
      EqR.≡⟨⟩
        (rename (ext ρ) ∘ rename S_ ∘ σ) X
      EqR.≡⟨ cong-app (cong (_∘ σ) (rename-compose S_ (ext ρ))) X ⟩
        (rename (ext ρ ∘ S_) ∘ σ) X
      EqR.≡⟨⟩
        (rename (S_ ∘ ρ) ∘ σ) X
      EqR.≡⟨ cong-app (cong (_∘ σ) (sym (rename-compose ρ S_))) X ⟩
        (rename S_ ∘ rename ρ ∘ σ) X
      EqR.≡⟨⟩
        exts (rename ρ ∘ σ) (S X)
      EqR.∎

exts-ext-compose : ∀ {Γ₁ Γ₂ Γ₃}
  → (ρ : ∀ {C} → Γ₁ ∋ C → Γ₂ ∋ C)
  → (σ : ∀ {D} → Γ₂ ∋ D → Γ₃ ⊢ D)
  → (∀ {A B} → exts σ ∘ ext ρ {A} {B} ≡ exts (σ ∘ ρ))
exts-ext-compose {Γ₁ = Γ₁} ρ σ = extensionality helper
  where
    helper : ∀ {A B} (X : Γ₁ , A ∋ B)
      → (exts σ ∘ ext ρ) X ≡ exts (σ ∘ ρ) X
    helper Z     = refl
    helper (S X) = refl

subst-rename-compose : ∀ {Γ₁ Γ₂ Γ₃}
  → (ρ : ∀ {B} → Γ₁ ∋ B → Γ₂ ∋ B)
  → (σ : ∀ {C} → Γ₂ ∋ C → Γ₃ ⊢ C)
  → (∀ {A} → subst σ ∘ rename ρ ≡ subst (σ ∘ ρ))
subst-rename-compose ρ σ {A = A} = extensionality (helper ρ σ {A})
  where
    helper : ∀ {Γ₁ Γ₂ Γ₃}
      → (ρ : ∀ {B} → Γ₁ ∋ B → Γ₂ ∋ B)
      → (σ : ∀ {C} → Γ₂ ∋ C → Γ₃ ⊢ C)
      → (∀ {A} (X : Γ₁ ⊢ A) → (subst σ ∘ rename ρ) X ≡ subst (σ ∘ ρ) X)
    exts-helper : ∀ {Γ₁ Γ₂ Γ₃}
      → (ρ : ∀ {C} → Γ₁ ∋ C → Γ₂ ∋ C)
      → (σ : ∀ {D} → Γ₂ ∋ D → Γ₃ ⊢ D)
      → (∀ {A B} (X : Γ₁ , A ⊢ B) → (subst (exts σ) ∘ rename (ext ρ)) X ≡ subst (exts (σ ∘ ρ)) X)
    extsexts-helper : ∀ {Γ₁ Γ₂ Γ₃}
      → (ρ : ∀ {D} → Γ₁ ∋ D → Γ₂ ∋ D)
      → (σ : ∀ {E} → Γ₂ ∋ E → Γ₃ ⊢ E)
      → (∀ {A B C} (X : Γ₁ , A , B ⊢ C) → (subst (exts (exts σ)) ∘ rename (ext (ext ρ))) X ≡ subst (exts (exts (σ ∘ ρ))) X)

    helper ρ σ (` x)           = refl
    helper ρ σ (ƛ X)           = cong ƛ_ (exts-helper ρ σ X)
    helper ρ σ (X · X₁)        = cong₂ _·_ (helper ρ σ X) (helper ρ σ X₁)
    helper ρ σ (`zero)         = refl
    helper ρ σ (`suc X)        = cong `suc_ (helper ρ σ X)
    helper ρ σ (case X X₁ X₂)  = cong₃ case (helper ρ σ X) (helper ρ σ X₁) (exts-helper ρ σ X₂)
    helper ρ σ (μ X)           = cong μ_ (exts-helper ρ σ X)
    helper ρ σ (con x)         = refl
    helper ρ σ (X `* X₁)       = cong₂ _`*_ (helper ρ σ X) (helper ρ σ X₁)
    helper ρ σ (`let X X₁)     = cong₂ `let (helper ρ σ X) (exts-helper ρ σ X₁)
    helper ρ σ `⟨ X , X₁ ⟩     = cong₂ `⟨_,_⟩ (helper ρ σ X) (helper ρ σ X₁)
    helper ρ σ (`proj₁ X)      = cong `proj₁ (helper ρ σ X)
    helper ρ σ (`proj₂ X)      = cong `proj₂ (helper ρ σ X)
    helper ρ σ (case× X X₁)    = cong₂ case× (helper ρ σ X) (extsexts-helper ρ σ X₁)
    helper ρ σ (`inj₁ X)       = cong `inj₁ (helper ρ σ X)
    helper ρ σ (`inj₂ X)       = cong `inj₂ (helper ρ σ X)
    helper ρ σ (case⊎ X X₁ X₂) = cong₃ case⊎ (helper ρ σ X) (exts-helper ρ σ X₁) (exts-helper ρ σ X₂)
    helper ρ σ `tt             = refl
    helper ρ σ (case⊤ X X₁)    = cong₂ case⊤ (helper ρ σ X) (helper ρ σ X₁)
    helper ρ σ (case⊥ X)       = cong case⊥ (helper ρ σ X)
    helper ρ σ `[]             = refl
    helper ρ σ (X `∷ X₁)       = cong₂ _`∷_ (helper ρ σ X) (helper ρ σ X₁)
    helper ρ σ (caseL X X₁ X₂) = cong₃ caseL (helper ρ σ X) (helper ρ σ X₁) (extsexts-helper ρ σ X₂)

    exts-helper ρ σ X =
      EqR.begin
        (subst (exts σ) ∘ rename (ext ρ)) X
      EqR.≡⟨ helper (ext ρ) (exts σ) X ⟩
        subst (exts σ ∘ ext ρ) X
      EqR.≡⟨ cong-app (cong-subst (exts-ext-compose ρ σ)) X ⟩
        subst (exts (σ ∘ ρ)) X
      EqR.∎

    extsexts-helper ρ σ X =
      EqR.begin
        (subst (exts (exts σ)) ∘ rename (ext (ext ρ))) X
      EqR.≡⟨ exts-helper (ext ρ) (exts σ) X ⟩
        subst (exts (exts σ ∘ ext ρ)) X
      EqR.≡⟨ cong-app (cong-subst (cong-exts (exts-ext-compose ρ σ))) X ⟩
        subst (exts (exts (σ ∘ ρ))) X
      EqR.∎

rename-subst-compose : ∀ {Γ₁ Γ₂ Γ₃}
  → (σ : ∀ {B} → Γ₁ ∋ B → Γ₂ ⊢ B)
  → (ρ : ∀ {C} → Γ₂ ∋ C → Γ₃ ∋ C)
  → (∀ {A} → rename ρ ∘ subst σ ≡ subst (rename ρ ∘ σ))
rename-subst-compose ρ σ {A = A} = extensionality (helper ρ σ {A})
  where
    helper : ∀ {Γ₁ Γ₂ Γ₃}
      → (σ : ∀ {B} → Γ₁ ∋ B → Γ₂ ⊢ B)
      → (ρ : ∀ {C} → Γ₂ ∋ C → Γ₃ ∋ C)
      → (∀ {A} (X : Γ₁ ⊢ A) → (rename ρ ∘ subst σ) X ≡ subst (rename ρ ∘ σ) X)
    exts-helper : ∀ {Γ₁ Γ₂ Γ₃}
      → (σ : ∀ {C} → Γ₁ ∋ C → Γ₂ ⊢ C)
      → (ρ : ∀ {D} → Γ₂ ∋ D → Γ₃ ∋ D)
      → (∀ {A B} (X : Γ₁ , A ⊢ B) → (rename (ext ρ) ∘ subst (exts σ)) X ≡ subst (exts (rename ρ ∘ σ)) X)
    extsexts-helper : ∀ {Γ₁ Γ₂ Γ₃}
      → (σ : ∀ {D} → Γ₁ ∋ D → Γ₂ ⊢ D)
      → (ρ : ∀ {E} → Γ₂ ∋ E → Γ₃ ∋ E)
      → (∀ {A B C} (X : Γ₁ , A , B ⊢ C) → (rename (ext (ext ρ)) ∘ subst (exts (exts σ))) X ≡ subst (exts (exts (rename ρ ∘ σ))) X)

    helper σ ρ (` x)           = refl
    helper σ ρ (ƛ X)           = cong ƛ_ (exts-helper σ ρ X)
    helper σ ρ (X · X₁)        = cong₂ _·_ (helper σ ρ X) (helper σ ρ X₁)
    helper σ ρ `zero           = refl
    helper σ ρ (`suc X)        = cong `suc_ (helper σ ρ X)
    helper σ ρ (case X X₁ X₂)  = cong₃ case (helper σ ρ X) (helper σ ρ X₁) (exts-helper σ ρ X₂)
    helper σ ρ (μ X)           = cong μ_ (exts-helper σ ρ X)
    helper σ ρ (con x)         = refl
    helper σ ρ (X `* X₁)       = cong₂ _`*_ (helper σ ρ X) (helper σ ρ X₁)
    helper σ ρ (`let X X₁)     = cong₂ `let (helper σ ρ X) (exts-helper σ ρ X₁)
    helper σ ρ `⟨ X , X₁ ⟩     = cong₂ `⟨_,_⟩ (helper σ ρ X) (helper σ ρ X₁)
    helper σ ρ (`proj₁ X)      = cong `proj₁ (helper σ ρ X)
    helper σ ρ (`proj₂ X)      = cong `proj₂ (helper σ ρ X)
    helper σ ρ (case× X X₁)    = cong₂ case× (helper σ ρ X) (extsexts-helper σ ρ X₁)
    helper σ ρ (`inj₁ X)       = cong `inj₁ (helper σ ρ X)
    helper σ ρ (`inj₂ X)       = cong `inj₂ (helper σ ρ X)
    helper σ ρ (case⊎ X X₁ X₂) = cong₃ case⊎ (helper σ ρ X) (exts-helper σ ρ X₁) (exts-helper σ ρ X₂)
    helper σ ρ `tt             = refl
    helper σ ρ (case⊤ X X₁)    = cong₂ case⊤ (helper σ ρ X) (helper σ ρ X₁)
    helper σ ρ (case⊥ X)       = cong case⊥ (helper σ ρ X)
    helper σ ρ `[]             = refl
    helper σ ρ (X `∷ X₁)       = cong₂ _`∷_ (helper σ ρ X) (helper σ ρ X₁)
    helper σ ρ (caseL X X₁ X₂) = cong₃ caseL (helper σ ρ X) (helper σ ρ X₁) (extsexts-helper σ ρ X₂)

    exts-helper σ ρ X =
      EqR.begin
        (rename (ext ρ) ∘ subst (exts σ)) X
      EqR.≡⟨ helper (exts σ) (ext ρ) X ⟩
        subst (rename (ext ρ) ∘ exts σ) X
      EqR.≡⟨ cong-app (cong-subst (rename-ext-compose σ ρ)) X ⟩
        subst (exts (rename ρ ∘ σ)) X
      EqR.∎

    extsexts-helper σ ρ X =
      EqR.begin
        (rename (ext (ext ρ)) ∘ subst (exts (exts σ))) X
      EqR.≡⟨ exts-helper (exts σ) (ext ρ) X ⟩
        subst (exts (rename (ext ρ) ∘ exts σ)) X
      EqR.≡⟨ cong-app (cong-subst (cong-exts (rename-ext-compose σ ρ))) X ⟩
        subst (exts (exts (rename ρ ∘ σ))) X
      EqR.∎

subst-exts-commute : ∀ {Γ₁ Γ₂ Γ₃}
  → (σ₁ : ∀ {C} → Γ₁ ∋ C → Γ₂ ⊢ C)
  → (σ₂ : ∀ {D} → Γ₂ ∋ D → Γ₃ ⊢ D)
  → (∀ {A B} → subst (exts σ₂) ∘ exts σ₁ {A} {B} ≡ exts (subst σ₂ ∘ σ₁))
subst-exts-commute {Γ₁ = Γ₁} σ₁ σ₂ = extensionality helper
  where
    helper : ∀ {A B} (X : Γ₁ , B ∋ A)
      → (subst (exts σ₂) ∘ exts σ₁) X ≡ exts (subst σ₂ ∘ σ₁) X
    helper Z     = refl
    helper (S X) =
      EqR.begin
        (subst (exts σ₂) ∘ exts σ₁) (S X)
      EqR.≡⟨⟩
        (subst (exts σ₂) ∘ rename S_ ∘ σ₁) X
      EqR.≡⟨ cong-app (subst-rename-compose S_ (exts σ₂)) (σ₁ X) ⟩
        (subst (exts σ₂ ∘ S_) ∘ σ₁) X
      EqR.≡⟨⟩
        (subst (rename S_ ∘ σ₂) ∘ σ₁) X
      EqR.≡⟨ cong-app (cong (_∘ σ₁) (sym (rename-subst-compose σ₂ S_))) X ⟩
        (rename S_ ∘ (subst σ₂ ∘ σ₁)) X
      EqR.≡⟨⟩
        exts (subst σ₂ ∘ σ₁) (S X)
      EqR.∎

subst-compose : ∀ {Γ₁ Γ₂ Γ₃}
  → (σ₁ : ∀ {B} → Γ₁ ∋ B → Γ₂ ⊢ B)
  → (σ₂ : ∀ {C} → Γ₂ ∋ C → Γ₃ ⊢ C)
  → (∀ {A} → subst σ₂ ∘ subst σ₁ {A} ≡ subst (subst σ₂ ∘ σ₁))
subst-compose σ₁ σ₂ = extensionality (helper σ₁ σ₂)
  where
    helper : ∀ {Γ₁ Γ₂ Γ₃}
      → (σ₁ : ∀ {B} → Γ₁ ∋ B → Γ₂ ⊢ B)
      → (σ₂ : ∀ {C} → Γ₂ ∋ C → Γ₃ ⊢ C)
      → (∀ {A} (M : Γ₁ ⊢ A) → (subst σ₂ ∘ subst σ₁) M ≡ subst (subst σ₂ ∘ σ₁) M)
    exts-helper : ∀ {Γ₁ Γ₂ Γ₃}
      → (σ₁ : ∀ {C} → Γ₁ ∋ C → Γ₂ ⊢ C)
      → (σ₂ : ∀ {D} → Γ₂ ∋ D → Γ₃ ⊢ D)
      → (∀ {A B} (M : Γ₁ , A ⊢ B) → (subst (exts σ₂) ∘ subst (exts σ₁)) M ≡ subst (exts (subst σ₂ ∘ σ₁)) M)
    extsexts-helper : ∀ {Γ₁ Γ₂ Γ₃}
      → (σ₁ : ∀ {D} → Γ₁ ∋ D → Γ₂ ⊢ D)
      → (σ₂ : ∀ {E} → Γ₂ ∋ E → Γ₃ ⊢ E)
      → (∀ {A B C} (M : Γ₁ , A , B ⊢ C) → (subst (exts (exts σ₂)) ∘ subst (exts (exts σ₁))) M ≡ subst (exts (exts (subst σ₂ ∘ σ₁))) M)

    helper σ₁ σ₂ (` x)           = refl
    helper σ₁ σ₂ (ƛ M)           = cong ƛ_ (exts-helper σ₁ σ₂ M)
    helper σ₁ σ₂ (M · M₁)        = cong₂ _·_ (helper σ₁ σ₂ M) (helper σ₁ σ₂ M₁)
    helper σ₁ σ₂ (`zero)         = refl
    helper σ₁ σ₂ (`suc M)        = cong `suc_ (helper σ₁ σ₂ M)
    helper σ₁ σ₂ (case M M₁ M₂)  = cong₃ case (helper σ₁ σ₂ M) (helper σ₁ σ₂ M₁) (exts-helper σ₁ σ₂ M₂)
    helper σ₁ σ₂ (μ M)           = cong μ_ (exts-helper σ₁ σ₂ M)
    helper σ₁ σ₂ (con x)         = refl
    helper σ₁ σ₂ (M `* M₁)       = cong₂ _`*_ (helper σ₁ σ₂ M) (helper σ₁ σ₂ M₁)
    helper σ₁ σ₂ (`let M M₁)     = cong₂ `let (helper σ₁ σ₂ M) (exts-helper σ₁ σ₂ M₁)
    helper σ₁ σ₂ (`⟨ M , M₁ ⟩)   = cong₂ `⟨_,_⟩ (helper σ₁ σ₂ M) (helper σ₁ σ₂ M₁)
    helper σ₁ σ₂ (`proj₁ M)      = cong `proj₁ (helper σ₁ σ₂ M)
    helper σ₁ σ₂ (`proj₂ M)      = cong `proj₂ (helper σ₁ σ₂ M)
    helper σ₁ σ₂ (case× M M₁)    = cong₂ case× (helper σ₁ σ₂ M) (extsexts-helper σ₁ σ₂ M₁)
    helper σ₁ σ₂ (`inj₁ X)       = cong `inj₁ (helper σ₁ σ₂ X)
    helper σ₁ σ₂ (`inj₂ X)       = cong `inj₂ (helper σ₁ σ₂ X)
    helper σ₁ σ₂ (case⊎ X X₁ X₂) = cong₃ case⊎ (helper σ₁ σ₂ X) (exts-helper σ₁ σ₂ X₁) (exts-helper σ₁ σ₂ X₂)
    helper σ₁ σ₂ `tt             = refl
    helper σ₁ σ₂ (case⊤ X X₁)    = cong₂ case⊤ (helper σ₁ σ₂ X) (helper σ₁ σ₂ X₁)
    helper σ₁ σ₂ (case⊥ X)       = cong case⊥ (helper σ₁ σ₂ X)
    helper σ₁ σ₂ `[]             = refl
    helper σ₁ σ₂ (X `∷ X₁)       = cong₂ _`∷_ (helper σ₁ σ₂ X) (helper σ₁ σ₂ X₁)
    helper σ₁ σ₂ (caseL X X₁ X₂) = cong₃ caseL (helper σ₁ σ₂ X) (helper σ₁ σ₂ X₁) (extsexts-helper σ₁ σ₂ X₂)

    exts-helper σ₁ σ₂ M =
      EqR.begin
        subst (exts σ₂) (subst (exts σ₁) M)
      EqR.≡⟨ helper (exts σ₁) (exts σ₂) M ⟩
        subst (subst (exts σ₂) ∘ exts σ₁) M
      EqR.≡⟨ cong-app (cong-subst (subst-exts-commute σ₁ σ₂)) M ⟩
        subst (exts (subst σ₂ ∘ σ₁)) M
      EqR.∎

    extsexts-helper σ₁ σ₂ M =
      EqR.begin
        subst (exts (exts σ₂)) (subst (exts (exts σ₁)) M)
      EqR.≡⟨ exts-helper (exts σ₁) (exts σ₂) M ⟩
        subst (exts (subst (exts σ₂) ∘ exts σ₁)) M
      EqR.≡⟨ cong-app (cong-subst (cong-exts (subst-exts-commute σ₁ σ₂))) M ⟩
        subst (exts (exts (subst σ₂ ∘ σ₁))) M
      EqR.∎

double-subst : ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {N : Γ , A , B ⊢ C}
  → N [ V ][ W ] ≡ (N [ rename S_ W ]) [ V ]
double-subst {V = V} {W = W} {N = N} =
  EqR.begin
    N [ V ][ W ]
  EqR.≡⟨ cong-app (cong-subst (extensionality λ{ Z → helper ; (S Z) → refl ; (S (S x)) → refl})) N ⟩
    subst (_[ V ] ∘ substZero (rename S_ W)) N
  EqR.≡⟨ sym (cong-app (subst-compose (substZero (rename S_ W)) (substZero V)) N) ⟩
    (N [ rename S_ W ]) [ V ]
  EqR.∎
  where
    exts-` : ∀ {Γ A B}
      → exts {Γ = Γ} `_ {A = A} {B = B} ≡ λ x → ` x
    exts-` = extensionality helper
      where
        helper : ∀ {Γ A B} (X : Γ , A ∋ B)
          → exts {Γ = Γ} `_ {A = A} {B = B} X ≡ ` X
        helper Z     = refl
        helper (S X) = refl

    subst-` : ∀ {Γ A}
      → subst {Γ = Γ} `_ {C = A} ≡ λ X → X
    subst-` = extensionality helper
      where
        helper : ∀ {Γ A} (X : Γ ⊢ A)
          → subst `_ X ≡ X
        exts-helper : ∀ {Γ A B} (X : Γ , A ⊢ B)
          → subst (exts `_) X ≡ X
        extsexts-helper : ∀ {Γ A B C} (X : Γ , A , B ⊢ C)
          → subst (exts (exts `_)) X ≡ X

        helper (` x)           = refl
        helper (ƛ X)           = cong ƛ_ (exts-helper X)
        helper (X · X₁)        = cong₂ _·_ (helper X) (helper X₁)
        helper `zero           = refl
        helper (`suc X)        = cong `suc_ (helper X)
        helper (case X X₁ X₂)  = cong₃ case (helper X) (helper X₁) (exts-helper X₂)
        helper (μ X)           = cong μ_ (exts-helper X)
        helper (con x)         = refl
        helper (X `* X₁)       = cong₂ _`*_ (helper X) (helper X₁)
        helper (`let X X₁)     = cong₂ `let (helper X) (exts-helper X₁)
        helper `⟨ X , X₁ ⟩     = cong₂ `⟨_,_⟩ (helper X) (helper X₁)
        helper (`proj₁ X)      = cong `proj₁ (helper X)
        helper (`proj₂ X)      = cong `proj₂ (helper X)
        helper (case× X X₁)    = cong₂ case× (helper X) (extsexts-helper X₁)
        helper (`inj₁ X)       = cong `inj₁ (helper X)
        helper (`inj₂ X)       = cong `inj₂ (helper X)
        helper (case⊎ X X₁ X₂) = cong₃ case⊎ (helper X) (exts-helper X₁) (exts-helper X₂)
        helper `tt             = refl
        helper (case⊤ X X₁)    = cong₂ case⊤ (helper X) (helper X₁)
        helper (case⊥ X)       = cong case⊥ (helper X)
        helper `[]             = refl
        helper (X `∷ X₁)       = cong₂ _`∷_ (helper X) (helper X₁)
        helper (caseL X X₁ X₂) = cong₃ caseL (helper X) (helper X₁) (extsexts-helper X₂)

        exts-helper X =
          EqR.begin
            subst (exts `_) X
          EqR.≡⟨ cong-app (cong-subst exts-`) X ⟩
            subst `_ X
          EqR.≡⟨ helper X ⟩
            X
          EqR.∎

        extsexts-helper X =
          EqR.begin
            subst (exts (exts `_)) X
          EqR.≡⟨ cong-app (cong-subst (cong-exts exts-`)) X ⟩
            subst (exts `_) X
          EqR.≡⟨ exts-helper X ⟩
            X
          EqR.∎

    helper : W ≡ (rename S_ W) [ V ]
    helper =
      EqR.begin
        W
      EqR.≡⟨ sym (cong-app subst-` W) ⟩
        subst `_ W
      EqR.≡⟨⟩
        subst (substZero V ∘ S_) W
      EqR.≡⟨ sym (cong-app (subst-rename-compose S_ (substZero V)) W) ⟩
        (rename S_ W) [ V ]
      EqR.∎
```


## Test examples

We repeat the [test examples](/DeBruijn/#examples) from Chapter [DeBruijn](/DeBruijn/),
in order to make sure we have not broken anything in the process of extending our base calculus.
```
two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

2+2 : ∀ {Γ} → Γ ⊢ `ℕ
2+2 = plus · two · two

Ch : Type → Type
Ch A  =  (A ⇒ A) ⇒ A ⇒ A

twoᶜ : ∀ {Γ A} → Γ ⊢ Ch A
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

plusᶜ : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

sucᶜ : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ `suc (# 0)

2+2ᶜ : ∀ {Γ} → Γ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
```

## Unicode

This chapter uses the following unicode:

    σ  U+03C3  GREEK SMALL LETTER SIGMA (\Gs or \sigma)
    †  U+2020  DAGGER (\dag)
    ‡  U+2021  DOUBLE DAGGER (\ddag)
