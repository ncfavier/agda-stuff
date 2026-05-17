```agda
open import 1Lab.Prelude
open import Data.Dec
open import Data.Fin as Fin
open import Data.Fin.Finite
open import Data.Int
open import Data.List
open import Data.List.NonEmpty
open import Data.List.Quantifiers
open import Data.Nat as Nat
open import Data.Rational.Base
open import Data.Rational.Order as Ratio

module FPClimate.OUU3 where

private variable
  A B : Type

SP : ∀ {ℓ} → Type ℓ → Type ℓ
SP A = List (A × Ratio)

open Listing ⦃ ... ⦄ using (univ) public
```

# OUU3

## Exercise 3.1

```agda
die : ∀ n → ⦃ _ : Nat.Positive n ⦄ → SP (Fin n)
die n@(suc _) = map (_, 1 / pos n) univ

all-equal : ⦃ Discrete A ⦄ → List A → Type
all-equal (x ∷ xs) = All (x ≡_) xs
all-equal []       = ⊥

-- Here and in prb we assume that there are no duplicate `A`s in the list.
uniform : SP A → Type
uniform sp = all-equal (map snd sp)

uniform? : ∀ (sp : SP A) → Dec (uniform sp)
uniform? (_ ∷ _) = auto
uniform? []      = auto

die-uniform : uniform (die 6)
die-uniform = decide!

sum : List Ratio → Ratio
sum = foldl _+ℚ_ 0

prb : SP A → (p : A → Type) → ⦃ ∀ {a} → Dec (p a) ⦄ → Ratio
prb sp p = sum (map snd (filter (λ (a , _) → Dec→Bool (holds? (p a))) sp))

_ : prb (die 6) (0 Fin.<_) ≡ 5 / 6
_ = decide!
```

## Exercise 3.2

```agda
Kolmogorov1 : All (λ (_ , p) → 0 Ratio.≤ p) (die 6)
Kolmogorov1 = decide!

Kolmogorov2 : prb (die 6) (λ _ → ⊤) ≡ 1
Kolmogorov2 = decide!
```

## Exercise 3.3

```agda
DetSys : Type → Type
DetSys A = A → A

detFlow : DetSys A → Nat → DetSys A
detFlow f zero    = id
detFlow f (suc n) = detFlow f n ∘ f

detTrj : DetSys A → Nat → A → List A
detTrj f zero    a = a ∷ []
detTrj f (suc n) a = a ∷ detTrj f n (f a)

detTrj-nonempty : ∀ (f : DetSys A) n a → is-nonempty (detTrj f n a)
detTrj-nonempty f zero    a = auto
detTrj-nonempty f (suc n) a = auto

last : (as : List A) .⦃ _ : is-nonempty as ⦄ → A
last (x ∷ [])     = x
last (x ∷ y ∷ as) = last (y ∷ as)

last-nonempty
  : (a : A) (as : List A) .⦃ _ : is-nonempty as ⦄
  → last (a ∷ as) ≡ last as
last-nonempty a (x ∷ as) = refl

last-detTrj
  : ∀ (f : DetSys A) n a
  → detFlow f n a ≡ last (detTrj f n a) ⦃ detTrj-nonempty _ _ _ ⦄
last-detTrj f zero    a = refl
last-detTrj f (suc n) a =
    last-detTrj f n (f a)
  ∙ sym (last-nonempty _ _ ⦃ detTrj-nonempty f n _ ⦄)
```

## Exercise 3.4

`nonDetFlow` is just `detFlow` in the Kleisli category for the list monad, and
similarly for `nonDetTrj`.

The types get a little confusing because we use lists both for the "non-determinism"
effect and for the return type of the trajectory function, so in the
following I define `NonDet` as a synonym for `List` for clarity.

- `f x : NonDet A`;
- `map (nonDetFlow f n) : NonDet A → NonDet (NonDet A)`;
- `map (nonDetTrj f n) : NonDet A → NonDet (NonDet (List A))`.

## Exercise 3.5

```agda
NonDet = List

NonDetSys : Type → Type
NonDetSys A = A → NonDet A

-- Kleisli composition
_<∘>_ : NonDetSys A → NonDetSys A → NonDetSys A
(f <∘> g) x = f =<< g x

nonDetFlow : NonDetSys A → Nat → NonDetSys A
nonDetFlow f zero    = pure
nonDetFlow f (suc n) = nonDetFlow f n <∘> f

nonDetTrj : NonDetSys A → Nat → A → NonDet (List A)
nonDetTrj f zero    a = (a ∷_) <$> pure []
nonDetTrj f (suc n) a = (a ∷_) <$> (nonDetTrj f n =<< f a)
```

## Exercise 3.6

```agda
walk : NonDetSys Int
walk n = n ∷ sucℤ n ∷ []

_ : nonDetTrj walk 3 0
  ≡ (0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
  ∷ (0 ∷ 0 ∷ 0 ∷ 1 ∷ [])
  ∷ (0 ∷ 0 ∷ 1 ∷ 1 ∷ [])
  ∷ (0 ∷ 0 ∷ 1 ∷ 2 ∷ [])
  ∷ (0 ∷ 1 ∷ 1 ∷ 1 ∷ [])
  ∷ (0 ∷ 1 ∷ 1 ∷ 2 ∷ [])
  ∷ (0 ∷ 1 ∷ 2 ∷ 2 ∷ [])
  ∷ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
  ∷ []
_ = refl
```

# MM1

## Exercise 4.1

Whether to do a or b in state GU might depend on:

- the relative probabilities of a staying in GU or going to B;
- "how bad" B is relative to BT;
- "how good" GS is relative to GU.

## Exercise 4.2

It suffices to ensure that the probabilities mentioned above add up to
1; for example, staying in GU with probability 9/10 and going to B with
probability 1/10.

## Exercise 4.3

In the following maze:

```plain
-----
|Y  |
| | |
 X|
-----
```

At the spot marked X, "go right" and "go down" are not feasible controls,
while at the spot marked Y they are both feasible.

A "feasible" predicate would have type State → Control → Prop.

## Exercise 4.4

At the spot marked X, the two-step plan "go up, then right" is not feasible.

## Exercise 4.5

The expected value measure represents a neutral attitude towards risk,
which is not always the right choice. I am struggling to come up with
an example.
