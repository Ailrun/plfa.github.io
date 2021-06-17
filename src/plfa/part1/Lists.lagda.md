---
title     : "Lists: Lists and higher-order functions"
layout    : page
prev      : /Decidable/
permalink : /Lists/
next      : /Lambda/
---

```
module plfa.part1.Lists where
```

This chapter discusses the list data type.  It gives further examples
of many of the techniques we have developed so far, and provides
examples of polymorphic types and higher-order functions.

## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_)
```


## Lists

Lists are defined in Agda as follows:
```
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_
```
Let's unpack this definition. If `A` is a set, then `List A` is a set.
The next two lines tell us that `[]` (pronounced _nil_) is a list of
type `A` (often called the _empty_ list), and that `_∷_` (pronounced
_cons_, short for _constructor_) takes a value of type `A` and a value
of type `List A` and returns a value of type `List A`.  Operator `_∷_`
has precedence level 5 and associates to the right.

For example,
```
_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []
```
denotes the list of the first three natural numbers.  Since `_∷_`
associates to the right, the term parses as `0 ∷ (1 ∷ (2 ∷ []))`.
Here `0` is the first element of the list, called the _head_,
and `1 ∷ (2 ∷ [])` is a list of the remaining elements, called the
_tail_. A list is a strange beast: it has a head and a tail,
nothing in between, and the tail is itself another list!

As we've seen, parameterised types can be translated to
indexed types. The definition above is equivalent to the following:
```
data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A
```
Each constructor takes the parameter as an implicit argument.
Thus, our example list could also be written:
```
_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))
```
where here we have provided the implicit parameters explicitly.

Including the pragma:

    {-# BUILTIN LIST List #-}

tells Agda that the type `List` corresponds to the Haskell type
list, and the constructors `[]` and `_∷_` correspond to nil and
cons respectively, allowing a more efficient representation of lists.


## List syntax

We can write lists more conveniently by introducing the following definitions:
```
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
```
This is our first use of pattern declarations.  For instance,
the third line tells us that `[ x , y , z ]` is equivalent to
`x ∷ y ∷ z ∷ []`, and permits the former to appear either in
a pattern on the left-hand side of an equation, or a term
on the right-hand side of an equation.


## Append

Our first function on lists is written `_++_` and pronounced
_append_:

```
infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)
```
The type `A` is an implicit argument to append, making it a _polymorphic_
function (one that can be used at many types). A list appended to the empty list
yields the list itself. A list appended to a non-empty list yields a list with
the head the same as the head of the non-empty list, and a tail the same as the
other list appended to tail of the non-empty list.

Here is an example, showing how to compute the result
of appending two lists:
```
_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎
```
Appending two lists requires time linear in the
number of elements in the first list.


## Reasoning about append

We can reason about lists in much the same way that we reason
about numbers.  Here is the proof that append is associative:
```
++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎
```
The proof is by induction on the first argument. The base case instantiates
to `[]`, and follows by straightforward computation.
The inductive case instantiates to `x ∷ xs`,
and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated by a recursive
invocation of the proof, in this case `++-assoc xs ys zs`.

Recall that Agda supports [sections](/Induction/#sections).
Applying `cong (x ∷_)` promotes the inductive hypothesis:

    (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

to the equality:

    x ∷ ((xs ++ ys) ++ zs) ≡ x ∷ (xs ++ (ys ++ zs))

which is needed in the proof.

It is also easy to show that `[]` is a left and right identity for `_++_`.
That it is a left identity is immediate from the definition:
```
++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎
```
That it is a right identity follows by simple induction:
```
++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎
```
As we will see later,
these three properties establish that `_++_` and `[]` form
a _monoid_ over lists.

## Length

Our next function finds the length of a list:
```
length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  suc (length xs)
```
Again, it takes an implicit parameter `A`.
The length of the empty list is zero.
The length of a non-empty list
is one greater than the length of the tail of the list.

Here is an example showing how to compute the length of a list:
```
_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎
```
Computing the length of a list requires time
linear in the number of elements in the list.

In the second-to-last line, we cannot write simply `length []` but
must instead write `length {ℕ} []`.  Since `[]` has no elements, Agda
has insufficient information to infer the implicit parameter.


## Reasoning about length

The length of one list appended to another is the
sum of the lengths of the lists:
```
length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎
```
The proof is by induction on the first argument. The base case
instantiates to `[]`, and follows by straightforward computation.  As
before, Agda cannot infer the implicit type parameter to `length`, and
it must be given explicitly.  The inductive case instantiates to
`x ∷ xs`, and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated
by a recursive invocation of the proof, in this case `length-++ xs ys`,
and it is promoted by the congruence `cong suc`.


## Reverse

Using append, it is easy to formulate a function to reverse a list:
```
reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]
```
The reverse of the empty list is the empty list.
The reverse of a non-empty list
is the reverse of its tail appended to a unit list
containing its head.

Here is an example showing how to reverse a list:
```
_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎
```
Reversing a list in this way takes time _quadratic_ in the length of
the list. This is because reverse ends up appending lists of lengths
`1`, `2`, up to `n - 1`, where `n` is the length of the list being
reversed, append takes time linear in the length of the first
list, and the sum of the numbers up to `n - 1` is `n * (n - 1) / 2`.
(We will validate that last fact in an exercise later in this chapter.)

#### Exercise `reverse-++-distrib` (recommended)

Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first:

    reverse (xs ++ ys) ≡ reverse ys ++ reverse xs

```
reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib []       ys = sym (++-identityʳ (reverse ys))
reverse-++-distrib (x ∷ xs) ys =
  begin
    reverse ((x ∷ xs) ++ ys)
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ (reverse xs ++ [ x ])
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎
```

#### Exercise `reverse-involutive` (recommended)

A function is an _involution_ if when applied twice it acts
as the identity function.  Show that reverse is an involution:

    reverse (reverse xs) ≡ xs

```
reverse-involutive : ∀ {A : Set} (xs : List A)
  → reverse (reverse xs) ≡ xs
reverse-involutive []       = refl
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
    [ x ] ++ reverse (reverse xs)
  ≡⟨⟩
    x ∷ reverse (reverse xs)
  ≡⟨ cong (x ∷_) (reverse-involutive xs) ⟩
    x ∷ xs
  ∎
```


## Faster reverse

The definition above, while easy to reason about, is less efficient than
one might expect since it takes time quadratic in the length of the list.
The idea is that we generalise reverse to take an additional argument:
```
shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)
```
The definition is by recursion on the first argument. The second argument
actually becomes _larger_, but this is not a problem because the argument
on which we recurse becomes _smaller_.

Shunt is related to reverse as follows:
```
shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎
```
The proof is by induction on the first argument.
The base case instantiates to `[]`, and follows by straightforward computation.
The inductive case instantiates to `x ∷ xs` and follows by the inductive
hypothesis and associativity of append.  When we invoke the inductive hypothesis,
the second argument actually becomes *larger*, but this is not a problem because
the argument on which we induct becomes *smaller*.

Generalising on an auxiliary argument, which becomes larger as the argument on
which we recurse or induct becomes smaller, is a common trick. It belongs in
your quiver of arrows, ready to slay the right problem.

Having defined shunt be generalisation, it is now easy to respecialise to
give a more efficient definition of reverse:
```
reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []
```

Given our previous lemma, it is straightforward to show
the two definitions equivalent:
```
reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎
```

Here is an example showing fast reverse of the list `[ 0 , 1 , 2 ]`:
```
_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎
```
Now the time to reverse a list is linear in the length of the list.

## Map {name=Map}

Map applies a function to every element of a list to generate a corresponding list.
Map is an example of a _higher-order function_, one which takes a function as an
argument or returns a function as a result:
```
map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs
```
Map of the empty list is the empty list.
Map of a non-empty list yields a list
with head the same as the function applied to the head of the given list,
and tail the same as map of the function applied to the tail of the given list.

Here is an example showing how to use map to increment every element of a list:
```
_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ map suc (1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ≡⟨⟩
    1 ∷ 2 ∷ 3 ∷ []
  ∎
```
Map requires time linear in the length of the list.

It is often convenient to exploit currying by applying
map to a function to yield a new function, and at a later
point applying the resulting function:
```
sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎
```

Any type that is parameterised on another type, such as lists, has a
corresponding map, which accepts a function and returns a function
from the type parameterised on the domain of the function to the type
parameterised on the range of the function. Further, a type that is
parameterised on _n_ types will have a map that is parameterised on
_n_ functions.


#### Exercise `map-compose` (practice)

Prove that the map of a composition is equal to the composition of two maps:

    map (g ∘ f) ≡ map g ∘ map f

The last step of the proof requires extensionality.

```
open plfa.part1.Isomorphism using (extensionality)

map-compose-val : ∀ {A B C : Set} (f : A → B) (g : B → C)
  → (∀ (xs : List A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs)
map-compose-val f g []       = refl
map-compose-val f g (x ∷ xs) = cong ((g ∘ f) x ∷_) (map-compose-val f g xs)

map-compose : ∀ {A B C : Set} (f : A → B) (g : B → C)
  → map (g ∘ f) ≡ (map g ∘ map f)
map-compose f g = extensionality (map-compose-val f g)
```

#### Exercise `map-++-distribute` (practice)

Prove the following relationship between map and append:

    map f (xs ++ ys) ≡ map f xs ++ map f ys

```
map-++-distribute : ∀ {A B : Set} (f : A → B) (xs ys : List A)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f []       ys = refl
map-++-distribute f (x ∷ xs) ys =
  begin
    map f ((x ∷ xs) ++ ys)
  ≡⟨⟩
    f x ∷ map f (xs ++ ys)
  ≡⟨ cong (f x ∷_) (map-++-distribute f xs ys) ⟩
    f x ∷ (map f xs ++ map f ys)
  ≡⟨⟩
    map f (x ∷ xs) ++ map f ys
  ∎
```

#### Exercise `map-Tree` (practice)

Define a type of trees with leaves of type `A` and internal
nodes of type `B`:
```
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B
```
Define a suitable map operator over trees:

    map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D

```
map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf v)     = leaf (f v)
map-Tree f g (node l v r) = node (map-Tree f g l) (g v) (map-Tree f g r)
```

## Fold {name=Fold}

Fold takes an operator and a value, and uses the operator to combine
each of the elements of the list, taking the given value as the result
for the empty list:
```
foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs
```
Fold of the empty list is the given value.
Fold of a non-empty list uses the operator to combine
the head of the list and the fold of the tail of the list.

Here is an example showing how to use fold to find the sum of a list:
```
_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎
```
Here we have an instance of `foldr` where `A` and `B` are both `ℕ`.
Fold requires time linear in the length of the list.

It is often convenient to exploit currying by applying
fold to an operator and a value to yield a new function,
and at a later point applying the resulting function:
```
sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎
```

Just as the list type has two constructors, `[]` and `_∷_`,
so the fold function takes two arguments, `e` and `_⊗_`
(in addition to the list argument).
In general, a data type with _n_ constructors will have
a corresponding fold function that takes _n_ arguments.

As another example, observe that

    foldr _∷_ [] xs ≡ xs

Here, if `xs` is of type `List A`, then we see we have an instance of
`foldr` where `A` is `A` and `B` is `List A`.  It follows that

    xs ++ ys ≡ foldr _∷_ ys xs

Demonstrating both these equations is left as an exercise.


#### Exercise `product` (recommended)

Use fold to define a function to find the product of a list of numbers.
For example:

    product [ 1 , 2 , 3 , 4 ] ≡ 24

```
product : List ℕ → ℕ
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ =
  begin
    product [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _*_ 1 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    24
  ∎
```

#### Exercise `foldr-++` (recommended)

Show that fold and append are related as follows:

    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs

```
foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A)
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e []       ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys = cong (x ⊗_) (foldr-++ _⊗_ e xs ys)
```

#### Exercise `foldr-∷` (practice)

Show

    foldr _∷_ [] xs ≡ xs

Show as a consequence of `foldr-++` above that

    xs ++ ys ≡ foldr _∷_ ys xs

```
foldr-∷ : ∀ {A : Set} (xs : List A)
  → foldr _∷_ [] xs ≡ xs
foldr-∷ []       = refl
foldr-∷ (x ∷ xs) = cong (x ∷_) (foldr-∷ xs)

foldr-∷-general : ∀ {A : Set} (xs ys : List A)
  → xs ++ ys ≡ foldr _∷_ ys xs
foldr-∷-general xs ys =
  begin
    xs ++ ys
  ≡⟨ sym (foldr-∷ (xs ++ ys)) ⟩
    foldr _∷_ [] (xs ++ ys)
  ≡⟨ foldr-++ _∷_ [] xs ys ⟩
    foldr _∷_ (foldr _∷_ [] ys) xs
  ≡⟨ cong (λ zs → foldr _∷_ zs xs) (foldr-∷ ys) ⟩
    foldr _∷_ ys xs
  ∎
```

#### Exercise `map-is-foldr` (practice)

Show that map can be defined using fold:

    map f ≡ foldr (λ x xs → f x ∷ xs) []

The proof requires extensionality.

```
map-is-foldr-val : ∀ {A B : Set} (f : A → B)
  → (∀ (xs : List A) → map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs)
map-is-foldr-val f []       = refl
map-is-foldr-val f (x ∷ xs) = cong (f x ∷_) (map-is-foldr-val f xs)

map-is-foldr : ∀ {A B : Set} (f : A → B)
  → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality (map-is-foldr-val f)
```

#### Exercise `fold-Tree` (practice)

Define a suitable fold function for the type of trees given earlier:

    fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C

```
fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f _⦉_⦊_ (leaf v)     = f v
fold-Tree f _⦉_⦊_ (node l v r) = fold-Tree f _⦉_⦊_ l ⦉ v ⦊ fold-Tree f _⦉_⦊_ r
```

#### Exercise `map-is-fold-Tree` (practice)

Demonstrate an analogue of `map-is-foldr` for the type of trees.

```
map-from-fold-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-from-fold-Tree f g = fold-Tree (λ v → leaf (f v)) (λ l v r → node l (g v) r)

map-is-fold-Tree-val : ∀ {A B C D : Set} (f : A → C) (g : B → D)
  → (∀ (t : Tree A B) → map-Tree f g t ≡ map-from-fold-Tree f g t)
map-is-fold-Tree-val f g (leaf v)     = refl
map-is-fold-Tree-val f g (node l v r) =
  begin
    map-Tree f g (node l v r)
  ≡⟨⟩
    node (map-Tree f g l) (g v) (map-Tree f g r)
  ≡⟨ cong (λ t → node t (g v) (map-Tree f g r)) (map-is-fold-Tree-val f g l) ⟩
    node (map-from-fold-Tree f g l) (g v) (map-Tree f g r)
  ≡⟨ cong (node (map-from-fold-Tree f g l) (g v)) (map-is-fold-Tree-val f g r) ⟩
    node (map-from-fold-Tree f g l) (g v) (map-from-fold-Tree f g r)
  ≡⟨⟩
    map-from-fold-Tree f g (node l v r)
  ∎

map-is-fold-Tree : ∀ {A B C D : Set} (f : A → C) (g : B → D)
  → map-Tree f g ≡ map-from-fold-Tree f g
map-is-fold-Tree f g = extensionality (map-is-fold-Tree-val f g)
```

#### Exercise `sum-downFrom` (stretch)

Define a function that counts down as follows:
```
downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n
```
For example:
```
_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl
```
Prove that the sum of the numbers `(n - 1) + ⋯ + 0` is
equal to `n * (n ∸ 1) / 2`:

    sum (downFrom n) * 2 ≡ n * (n ∸ 1)

```
open Data.Nat.Properties using (*-comm; *-distribʳ-+; *-distribˡ-+)

sum-downFrom : ∀ (n : ℕ)
  → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero          = refl
sum-downFrom (suc zero)    = refl
sum-downFrom (suc (suc n)) =
  begin
    sum (downFrom (suc (suc n))) * 2
  ≡⟨⟩
    (suc n + sum (downFrom (suc n))) * 2
  ≡⟨ *-distribʳ-+ 2 (suc n) (sum (downFrom (suc n))) ⟩
    suc n * 2 + sum (downFrom (suc n)) * 2
  ≡⟨ cong (suc n * 2 +_) (sum-downFrom (suc n)) ⟩
    suc n * 2 + suc n * n
  ≡⟨ sym (*-distribˡ-+ (suc n) 2 n) ⟩
    suc n * (2 + n)
  ≡⟨ *-comm (suc n) (2 + n) ⟩
    (2 + n) * suc n
  ≡⟨⟩
    suc n + suc n * suc n
  ≡⟨⟩
    suc (suc n) * (suc (suc n) ∸ 1)
  ∎
```


## Monoids

Typically when we use a fold the operator is associative and the
value is a left and right identity for the operator, meaning that the
operator and the value form a _monoid_.

We can define a monoid as a suitable record type:
```
record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid
```

As examples, sum and zero, multiplication and one, and append and the empty
list, are all examples of monoids:
```
+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }
```

If `_⊗_` and `e` form a monoid, then we can re-express fold on the
same operator and an arbitrary value:
```
foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎
```

In a previous exercise we showed the following.
```
-- postulate
--   foldr-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) (xs ys : List A) →
--     foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
```

As a consequence, using a previous exercise, we have the following:
```
foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎
```

#### Exercise `foldl` (practice)

Define a function `foldl` which is analogous to `foldr`, but where
operations associate to the left rather than the right.  For example:

    foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
    foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z

```
foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e []       = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

-- Or using foldr
foldl′ : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl′ _⊗_ e xs = foldr (λ x f v → f (v ⊗ x)) (λ v → v) xs e

foldl≡foldl′-val : ∀ {A B : Set} → (_⊗_ : B → A → B) → (e : B)
  → (∀ (xs : List A) → foldl _⊗_ e xs ≡ foldl′ _⊗_ e xs)
foldl≡foldl′-val _⊗_ e []       = refl
foldl≡foldl′-val _⊗_ e (x ∷ xs) =
  begin
    foldl _⊗_ e (x ∷ xs)
  ≡⟨⟩
    foldl _⊗_ (e ⊗ x) xs
  ≡⟨ foldl≡foldl′-val _⊗_ (e ⊗ x) xs ⟩
    foldl′ _⊗_ (e ⊗ x) xs
  ≡⟨⟩
    foldr (λ x f v → f (v ⊗ x)) (λ v → v) xs (e ⊗ x)
  ≡⟨⟩
    foldr (λ x f v → f (v ⊗ x)) (λ v → v) (x ∷ xs) e
  ≡⟨⟩
    foldl′ _⊗_ e (x ∷ xs)
  ∎

foldl≡foldl′ : ∀ {A B : Set} → (_⊗_ : B → A → B) → (e : B)
  → foldl _⊗_ e ≡ foldl′ _⊗_ e
foldl≡foldl′ _⊗_ e = extensionality (foldl≡foldl′-val _⊗_ e)
```


#### Exercise `foldr-monoid-foldl` (practice)

Show that if `_⊗_` and `e` form a monoid, then `foldr _⊗_ e` and
`foldl _⊗_ e` always compute the same result.

```
foldl-monoid : ∀ {A : Set} →  (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → (∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ y ⊗ foldl _⊗_ e xs)
foldl-monoid _⊗_ e monoid-⊗ []      y =
  begin
    foldl _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityʳ monoid-⊗ y) ⟩
    y ⊗ e
  ≡⟨⟩
    y ⊗ foldl _⊗_ e []
  ∎
foldl-monoid _⊗_ e monoid-⊗ (x ∷ xs) y =
  begin
    foldl _⊗_ y (x ∷ xs)
  ≡⟨⟩
    foldl _⊗_ (y ⊗ x) xs
  ≡⟨ foldl-monoid _⊗_ e monoid-⊗ xs (y ⊗ x) ⟩
    (y ⊗ x) ⊗ foldl _⊗_ e xs
  ≡⟨ assoc monoid-⊗ y x (foldl _⊗_ e xs) ⟩
    y ⊗ (x ⊗ foldl _⊗_ e xs)
  ≡⟨ cong (y ⊗_) (sym (foldl-monoid _⊗_ e monoid-⊗ xs x)) ⟩
    y ⊗ foldl _⊗_ x xs
  ≡⟨ cong (λ z → y ⊗ foldl _⊗_ z xs) (sym (identityˡ monoid-⊗ x)) ⟩
    y ⊗ foldl _⊗_ (e ⊗ x) xs
  ∎

foldr-monoid-foldl : ∀ {A : Set} →  (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → (∀ (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs)
foldr-monoid-foldl _⊗_ e monoid-⊗ []       = refl
foldr-monoid-foldl _⊗_ e monoid-⊗ (x ∷ xs) =
  begin
    foldr _⊗_ e (x ∷ xs)
  ≡⟨⟩
    x ⊗ foldr _⊗_ e xs
  ≡⟨ cong (x ⊗_) (foldr-monoid-foldl _⊗_ e monoid-⊗ xs) ⟩
    x ⊗ foldl _⊗_ e xs
  ≡⟨ cong (_⊗ foldl _⊗_ e xs) (sym (identityˡ monoid-⊗ x)) ⟩
    (e ⊗ x) ⊗ foldl _⊗_ e xs
  ≡⟨ sym (foldl-monoid _⊗_ e monoid-⊗ xs (e ⊗ x)) ⟩
    foldl _⊗_ (e ⊗ x) xs
  ≡⟨⟩
    foldl _⊗_ e (x ∷ xs)
  ∎
```


## All {name=All}

We can also define predicates over lists. Two of the most important
are `All` and `Any`.

Predicate `All P` holds if predicate `P` is satisfied by every element of a list:
```
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)
```
The type has two constructors, reusing the names of the same constructors for lists.
The first asserts that `P` holds for every element of the empty list.
The second asserts that if `P` holds of the head of a list and for every
element of the tail of a list, then `P` holds for every element of the list.
Agda uses types to disambiguate whether the constructor is building
a list or evidence that `All P` holds.

For example, `All (_≤ 2)` holds of a list where every element is less
than or equal to two.  Recall that `z≤n` proves `zero ≤ n` for any
`n`, and that if `m≤n` proves `m ≤ n` then `s≤s m≤n` proves `suc m ≤
suc n`, for any `m` and `n`:
```
_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []
```
Here `_∷_` and `[]` are the constructors of `All P` rather than of `List A`.
The three items are proofs of `0 ≤ 2`, `1 ≤ 2`, and `2 ≤ 2`, respectively.

(One might wonder whether a pattern such as `[_,_,_]` can be used to
construct values of type `All` as well as type `List`, since both use
the same constructors. Indeed it can, so long as both types are in
scope when the pattern is declared.  That's not the case here, since
`List` is defined before `[_,_,_]`, but `All` is defined later.)


## Any

Predicate `Any P` holds if predicate `P` is satisfied by some element of a list:
```
data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)
```
The first constructor provides evidence that the head of the list
satisfies `P`, while the second provides evidence that some element of
the tail of the list satisfies `P`.  For example, we can define list
membership as follows:
```
infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)
```
For example, zero is an element of the list `[ 0 , 1 , 0 , 2 ]`.  Indeed, we can demonstrate
this fact in two different ways, corresponding to the two different
occurrences of zero in the list, as the first element and as the third element:
```
_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))
```
Further, we can demonstrate that three is not in the list, because
any possible proof that it is in the list leads to contradiction:
```
not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))
```
The five occurrences of `()` attest to the fact that there is no
possible evidence for `3 ≡ 0`, `3 ≡ 1`, `3 ≡ 0`, `3 ≡ 2`, and
`3 ∈ []`, respectively.

## All and append

A predicate holds for every element of one list appended to another if and
only if it holds for every element of both lists:
```
All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩
```

#### Exercise `Any-++-⇔` (recommended)

Prove a result similar to `All-++-⇔`, but with `Any` in place of `All`, and a suitable
replacement for `_×_`.  As a consequence, demonstrate an equivalence relating
`_∈_` and `_++_`.

```
open import Data.Sum using (_⊎_; inj₁; inj₂)

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A)
  → Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
    { to   = to xs ys
    ; from = from xs ys
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A)
      → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
    to []       _  (here Py)   = inj₂ (here Py)
    to []       _  (there Pys) = inj₂ (there Pys)
    to (x ∷ xs) ys (here Px)   = inj₁ (here Px)
    to (x ∷ xs) ys (there Pxys) with to xs ys Pxys
    ...                            | inj₁ Pxs = inj₁ (there Pxs)
    ...                            | inj₂ Pys = inj₂ Pys

    from : ∀ {A : Set} {P : A → Set} (xs ys : List A)
      → Any P xs ⊎ Any P ys → Any P (xs ++ ys)
    from []       ys (inj₂ Pys)         = Pys
    from (x ∷ xs) ys (inj₁ (here Px))   = here Px
    from (x ∷ xs) ys (inj₁ (there Pxs)) = there (from xs ys (inj₁ Pxs))
    from (x ∷ xs) ys (inj₂ Pys)         = there (from xs ys (inj₂ Pys))

∈-++ : ∀ {A : Set} (x : A) (xs ys : List A)
  → (x ∈ (xs ++ ys)) ⇔ (x ∈ xs ⊎ x ∈ ys)
∈-++ x xs ys = Any-++-⇔ xs ys
```

#### Exercise `All-++-≃` (stretch)

Show that the equivalence `All-++-⇔` can be extended to an isomorphism.

```
All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A)
  → All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys =
  record
    { to   = to xs ys
    ; from = from xs ys
    ; from∘to = from∘to xs ys
    ; to∘from = to∘from xs ys
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A)
      → All P (xs ++ ys) → (All P xs × All P ys)
    to []       ys Pys            = ⟨ [] , Pys ⟩
    to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
    ...                              | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

    from : ∀ { A : Set} {P : A → Set} (xs ys : List A)
      → All P xs × All P ys → All P (xs ++ ys)
    from []       ys ⟨ []       , Pys ⟩ = Pys
    from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = Px ∷ from xs ys ⟨ Pxs , Pys ⟩

    from∘to : ∀ {A : Set} {P : A → Set} (xs ys : List A) (Pxs++ys : All P (xs ++ ys))
      → from xs ys (to xs ys Pxs++ys) ≡ Pxs++ys
    from∘to []       ys Pxs++ys        = refl
    from∘to (x ∷ xs) ys (Px ∷ Pxs++ys) = cong (Px ∷_) (from∘to xs ys Pxs++ys)

    to∘from : ∀ {A : Set} {P : A → Set} (xs ys : List A) (PxsPys : All P xs × All P ys)
      → to xs ys (from xs ys PxsPys) ≡ PxsPys
    to∘from []       ys ⟨ []       , Pys ⟩ = refl
    to∘from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩
      with to xs ys (from xs ys ⟨ Pxs , Pys ⟩) | to∘from xs ys ⟨ Pxs , Pys ⟩
    ...  | _                                   | refl = refl
```

#### Exercise `¬Any⇔All¬` (recommended)

Show that `Any` and `All` satisfy a version of De Morgan's Law:

    (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs

(Can you see why it is important that here `_∘_` is generalised
to arbitrary levels, as described in the section on
[universe polymorphism](/Equality/#unipoly)?)

Do we also have the following?

    (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs

If so, prove; if not, explain why.


```
¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ xs =
  record
    { to   = to xs
    ; from = from xs
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs : List A)
      → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
    to []       ¬P[]  = []
    to (x ∷ xs) ¬Pxxs = (¬Pxxs ∘ here) ∷ to xs (¬Pxxs ∘ there)

    from : ∀ {A : Set} {P : A → Set} (xs : List A)
      → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
    from (x ∷ xs) (¬Px ∷ All¬Pxs) (here Px)      = ¬Px Px
    from (x ∷ xs) (¬Px ∷ All¬Pxs) (there AnyPxs) = from xs All¬Pxs AnyPxs

-- Without universe-polymorphic `_∘_`, we cannot compose
-- `¬_ : Set → Set` with `Any P : List A → Set`,
-- as they are in `Set₁`.

-- We cannot prove `¬All⇔Any¬`. Even a weaker form, i.e,
-- `¬All→Any¬` is equivalent to weak law of excluded middle,
-- which is not provable in intuitionistic logic.
[¬All→Any¬]-weak-em :
  (∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ All P) xs → Any (¬_ ∘ P) xs)
  → (∀ {A : Set} → ¬ A ⊎ ¬ ¬ A)
[¬All→Any¬]-weak-em ¬All→Any¬ {A}
  with ¬All→Any¬ {P = λ{ true → A ; false → ¬ A }} [ true , false ] (λ{ (A ∷ ¬A ∷ []) → ¬A A })
...  | here  a          = inj₁ a
...  | there (here  b)  = inj₂ b
...  | there (there ())

weak-em-[¬All→Any¬] :
  (∀ {A : Set} → ¬ A ⊎ ¬ ¬ A)
  → (∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ All P) xs → Any (¬_ ∘ P) xs)
weak-em-[¬All→Any¬] weak-em         []       ¬AllP[]
  with ¬AllP[] []
...  | ()
weak-em-[¬All→Any¬] weak-em {P = P} (x ∷ xs) ¬AllPxxs
  with weak-em {A = P x}
...  | inj₁  ¬Px = here ¬Px
...  | inj₂ ¬¬Px = there (weak-em-[¬All→Any¬] weak-em xs (λ AllPxs → ¬¬Px (¬AllPxxs ∘ (_∷ AllPxs))))
```

#### Exercise `¬Any≃All¬` (stretch)

Show that the equivalence `¬Any⇔All¬` can be extended to an isomorphism.
You will need to use extensionality.

```
¬Any≃All¬ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → (¬_ ∘ Any P) xs ≃ All (¬_ ∘ P) xs
¬Any≃All¬ xs =
  record
    { to      = to xs
    ; from    = from xs
    ; from∘to = from∘to xs
    ; to∘from = to∘from xs
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs : List A)
      → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
    to []       ¬P[]  = []
    to (x ∷ xs) ¬Pxxs = (¬Pxxs ∘ here) ∷ to xs (¬Pxxs ∘ there)

    from : ∀ {A : Set} {P : A → Set} (xs : List A)
      → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
    from (x ∷ xs) (¬Px ∷ All¬Pxs) (here Px)      = ¬Px Px
    from (x ∷ xs) (¬Px ∷ All¬Pxs) (there AnyPxs) = from xs All¬Pxs AnyPxs

    from∘to-val : ∀ {A : Set} {P : A → Set} (xs : List A) (¬AnyPxs : (¬_ ∘ Any P) xs)
      → (∀ (AnyPxs : Any P xs) → from xs (to xs ¬AnyPxs) AnyPxs ≡ ¬AnyPxs AnyPxs)
    from∘to-val xs ¬AnyPxs AnyPxs with ¬AnyPxs AnyPxs
    ...                              | ()

    from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) (¬AnyPxs : (¬_ ∘ Any P) xs)
      → from xs (to xs ¬AnyPxs) ≡ ¬AnyPxs
    from∘to xs ¬AnyPxs = extensionality (from∘to-val xs ¬AnyPxs)

    to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) (All¬Pxs : All (¬_ ∘ P) xs)
      → to xs (from xs All¬Pxs) ≡ All¬Pxs
    to∘from []       []              = refl
    to∘from (x ∷ xs) (¬Px ∷ All¬Pxs) =
      begin
        from (x ∷ xs) (¬Px ∷ All¬Pxs) ∘ here ∷ to xs (from (x ∷ xs) (¬Px ∷ All¬Pxs) ∘ there)
      ≡⟨⟩
        ¬Px ∷ to xs (from xs All¬Pxs)
      ≡⟨ cong (¬Px ∷_) (to∘from xs All¬Pxs) ⟩
        ¬Px ∷ All¬Pxs
      ∎
```

#### Exercise `All-∀` (practice)

Show that `All P xs` is isomorphic to `∀ {x} → x ∈ xs → P x`.

```
open import plfa.part1.Isomorphism using (∀-extensionality)

All-∀ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → All P xs ≃ (∀ (x : A) → x ∈ xs → P x)
All-∀ xs =
  record
    { to      = to xs
    ; from    = from xs
    ; from∘to = from∘to xs
    ; to∘from = to∘from xs
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs : List A)
      → All P xs → (∀ (x : A) → x ∈ xs → P x)
    to (x ∷ xs) (Px ∷ Pxs) v (here refl)  = Px
    to (x ∷ xs) (Px ∷ Pxs) v (there v∈xs) = to xs Pxs v v∈xs

    from : ∀ {A : Set} {P : A → Set} (xs : List A)
      → (∀ (x : A) → x ∈ xs → P x) → All P xs
    from []       f = []
    from (x ∷ xs) f = f x (here refl) ∷ from xs (λ v v∈xs → f v (there v∈xs))

    from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) (Pxs : All P xs)
      → from xs (to xs Pxs) ≡ Pxs
    from∘to []       []         = refl
    from∘to (x ∷ xs) (Px ∷ Pxs) = cong (Px ∷_) (from∘to xs Pxs)

    to∘from-val : ∀ {A : Set} {P : A → Set} (xs : List A) (f : (∀ (x : A) → x ∈ xs → P x))
      → (∀ (x : A) (x∈xs : x ∈ xs) → to xs (from xs f) x x∈xs ≡ f x x∈xs)
    to∘from-val (x ∷ xs) f v (here refl)  = refl
    to∘from-val (x ∷ xs) f v (there v∈xs) = to∘from-val xs (λ z z∈xs → f z (there z∈xs)) v v∈xs

    to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) (f : (∀ (x : A) → x ∈ xs → P x))
      → to xs (from xs f) ≡ f
    to∘from xs f = ∀-extensionality (λ v → extensionality (to∘from-val xs f v))
```


#### Exercise `Any-∃` (practice)

Show that `Any P xs` is isomorphic to `∃[ x ] (x ∈ xs × P x)`.

```
Any-∃ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → Any P xs ≃ ∃[ x ] (x ∈ xs × P x)
Any-∃ xs =
  record
    { to      = to xs
    ; from    = from xs
    ; from∘to = from∘to xs
    ; to∘from = to∘from xs
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs : List A)
      → Any P xs → ∃[ x ] (x ∈ xs × P x)
    to (x ∷ xs) (here Px)   = ⟨ x , ⟨ here refl , Px ⟩ ⟩
    to (x ∷ xs) (there Pxs) with to xs Pxs
    ...                        | ⟨ v , ⟨ v∈xs , Pv ⟩ ⟩ = ⟨ v , ⟨ there v∈xs , Pv ⟩ ⟩

    from : ∀ {A : Set} {P : A → Set} (xs : List A)
      → ∃[ x ] (x ∈ xs × P x) → Any P xs
    from (x ∷ xs) ⟨ v , ⟨ here refl  , Pv ⟩ ⟩ = here Pv
    from (x ∷ xs) ⟨ v , ⟨ there v∈xs , Pv ⟩ ⟩ with from xs ⟨ v , ⟨ v∈xs , Pv ⟩ ⟩
    ...                                           | Pxs = there Pxs

    from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) (Pxs : Any P xs)
      → from xs (to xs Pxs) ≡ Pxs
    from∘to (x ∷ xs) (here Px)   = refl
    from∘to (x ∷ xs) (there Pxs) = cong there (from∘to xs Pxs)

    to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) (Pxs : ∃[ x ] (x ∈ xs × P x))
      → to xs (from xs Pxs) ≡ Pxs
    to∘from (x ∷ xs) ⟨ v , ⟨ here refl  , Pv ⟩ ⟩ = refl
    to∘from (x ∷ xs) ⟨ v , ⟨ there v∈xs , Pv ⟩ ⟩ =
      cong (λ{ ⟨ z , ⟨ z∈xs , Pz ⟩ ⟩ → ⟨ z , ⟨ there z∈xs , Pz ⟩ ⟩ }) (to∘from xs ⟨ v , ⟨ v∈xs , Pv ⟩ ⟩)
```


## Decidability of All

If we consider a predicate as a function that yields a boolean,
it is easy to define an analogue of `All`, which returns true if
a given predicate returns true for every element of a list:
```
all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p
```
The function can be written in a particularly compact style by
using the higher-order functions `map` and `foldr`.

As one would hope, if we replace booleans by decidables there is again
an analogue of `All`.  First, return to the notion of a predicate `P` as
a function of type `A → Set`, taking a value `x` of type `A` into evidence
`P x` that a property holds for `x`.  Say that a predicate `P` is _decidable_
if we have a function that for a given `x` can decide `P x`:
```
Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)
```
Then if predicate `P` is decidable, it is also decidable whether every
element of a list satisfies the predicate:
```
All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }
```
If the list is empty, then trivially `P` holds for every element of
the list.  Otherwise, the structure of the proof is similar to that
showing that the conjunction of two decidable propositions is itself
decidable, using `_∷_` rather than `⟨_,_⟩` to combine the evidence for
the head and tail of the list.


#### Exercise `Any?` (stretch)

Just as `All` has analogues `all` and `All?` which determine whether a
predicate holds for every element of a list, so does `Any` have
analogues `any` and `Any?` which determine whether a predicate holds
for some element of a list.  Give their definitions.

```
any : ∀ {A : Set} → (A → Bool) → List A → Bool
any p = foldr _∨_ false ∘ map p

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? []       = no (λ ())
Any? P? (x ∷ xs) with P? x   | Any? P? xs
...                 | no ¬Px | no ¬Pxs = no (λ{ (here Px) → ¬Px Px
                                              ; (there Pxs) → ¬Pxs Pxs
                                              }
                                            )
...                 | yes Px | _       = yes (here Px)
...                 | _      | yes Pxs = yes (there Pxs)
```


#### Exercise `split` (stretch)

The relation `merge` holds when two lists merge to give a third list.
```
data merge {A : Set} : (xs ys zs : List A) → Set where

  [] :
      --------------
      merge [] [] []

  left-∷ : ∀ {x xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge (x ∷ xs) ys (x ∷ zs)

  right-∷ : ∀ {y xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge xs (y ∷ ys) (y ∷ zs)
```

For example,
```
_ : merge [ 1 , 4 ] [ 2 , 3 ] [ 1 , 2 , 3 , 4 ]
_ = left-∷ (right-∷ (right-∷ (left-∷ [])))

```

Given a decidable predicate and a list, we can split the list
into two lists that merge to give the original list, where all
elements of one list satisfy the predicate, and all elements of
the other do not satisfy the predicate.

Define the following variant of the traditional `filter` function on
lists, which given a decidable predicate and a list returns a list of
elements that satisfy the predicate and a list of elements that don't,
with their corresponding proofs.

    split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
      → ∃[ xs ] ∃[ ys ] ( merge xs ys zs × All P xs × All (¬_ ∘ P) ys )

```
split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
  → ∃[ xs ] ∃[ ys ] ( merge xs ys zs × All P xs × All (¬_ ∘ P) ys )
split P? []       = ⟨ [] , ⟨ [] , ⟨ [] , ⟨ [] , [] ⟩ ⟩ ⟩ ⟩
split P? (z ∷ zs)
  with split P? zs
...  | ⟨ xs , ⟨ ys , ⟨ ms , ⟨ Pxs , ¬Pys ⟩ ⟩ ⟩ ⟩
     with P? z
...     | yes Pz = ⟨ z ∷ xs , ⟨ ys     , ⟨ left-∷  ms , ⟨ Pz ∷ Pxs , ¬Pys       ⟩ ⟩ ⟩ ⟩
...     | no ¬Pz = ⟨ xs     , ⟨ z ∷ ys , ⟨ right-∷ ms , ⟨ Pxs      , ¬Pz ∷ ¬Pys ⟩ ⟩ ⟩ ⟩
```

## Standard Library

Definitions similar to those in this chapter can be found in the standard library:
```
import Data.List using (List; _++_; length; reverse; map; foldr; downFrom)
import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Membership.Propositional using (_∈_)
import Data.List.Properties
  using (reverse-++-commute; map-compose; map-++-commute; foldr-++)
  renaming (mapIsFold to map-is-foldr)
import Algebra.Structures using (IsMonoid)
import Relation.Unary using (Decidable)
import Relation.Binary using (Decidable)
```
The standard library version of `IsMonoid` differs from the
one given here, in that it is also parameterised on an equivalence relation.

Both `Relation.Unary` and `Relation.Binary` define a version of `Decidable`,
one for unary relations (as used in this chapter where `P` ranges over
unary predicates) and one for binary relations (as used earlier, where `_≤_`
ranges over a binary relation).

## Unicode

This chapter uses the following unicode:

    ∷  U+2237  PROPORTION  (\::)
    ⊗  U+2297  CIRCLED TIMES  (\otimes, \ox)
    ∈  U+2208  ELEMENT OF  (\in)
    ∉  U+2209  NOT AN ELEMENT OF  (\inn, \notin)
