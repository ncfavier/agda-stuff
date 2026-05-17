```agda
open import 1Lab.Prelude
open import Data.Dec
open import Data.Fin.Finite
open import Data.List
open import Data.List.NonEmpty
open import Data.Rational.Base
open import Data.Rational.Solver
open import Order.Base
open import Order.Instances.Rational
open import Order.Total

open import FPClimate.OUU3
open import FPClimate.MM2 hiding (SDP)

module FPClimate.MM4 where
```

# MM4

Some background theory on SDPs:

```agda
module _ (M : Effect) ⦃ _ : Bind M ⦄ (let module M = Effect M) where
  record SDP : Type (lsuc (M.adj lzero)) where
    field
      X : Nat → Type
      Y : (t : Nat) → X t → Type
      next : (t : Nat) → (x : X t) → Y t x → M.₀ (X (suc t))

    Policy : (t : Nat) → Type
    Policy t = (x : X t) → Y t x

    field
      Val-poset : Poset lzero lzero
      Val-total : is-decidable-total-order Val-poset

    Val = ⌞ Val-poset ⌟
    open Poset Val-poset public

    field
      0Val : Val
      _⊕_ : Val → Val → Val

    _≤ₗ_ : ∀ {ℓ} {A : Type ℓ} → (A → Val) → (A → Val) → Type _
    v1 ≤ₗ v2 = ∀ x → v1 x ≤ v2 x

    _⊕ₗ_ : ∀ {ℓ} {A : Type ℓ} → (A → Val) → (A → Val) → (A → Val)
    v1 ⊕ₗ v2 = λ x → v1 x ⊕ v2 x

    field
      reward : ∀ t → (x : X t) → Y t x → X (suc t) → Val

    data PolicySeq : (t n : Nat) → Type where
      Nil : ∀ {t} → PolicySeq t zero
      _∷_ : ∀ {t n} → Policy t → PolicySeq (suc t) n → PolicySeq t (suc n)

    data XYSeq : (t n : Nat) → Type where
      Last : ∀ {t} → X t → XYSeq t (suc zero)
      _∷_ : ∀ {t n} → Σ (X t) (Y t) → XYSeq (suc t) (suc n) → XYSeq t (suc (suc n))

    trj : ∀ {t n} → PolicySeq t n → X t → M.₀ (XYSeq t (suc n))
    trj {t} Nil x = pure (Last x)
    trj {t} (p ∷ ps) x =
      let y = p x
          mx' = next t x y
      in map ((x , y) ∷_) (mx' >>= trj ps)

    headXY : ∀ {t n} → XYSeq t n → X t
    headXY (Last x) = x
    headXY ((x , y) ∷ ps) = x

    sumR : ∀ {t n} → XYSeq t n → Val
    sumR {t} (Last x) = 0Val
    sumR {t} ((x , y) ∷ xys) = reward t x y (headXY xys) ⊕ sumR xys

    module Measure (measure : M.₀ Val → Val) where
      val : ∀ {t n} → (ps : PolicySeq t n) → (x : X t) → Val
      val ps = measure ∘ map sumR ∘ trj ps

      cval : ∀ {t n} → PolicySeq (suc t) n → (x : X t) → Y t x → Val
      val' : ∀ {t n} → PolicySeq t n → X t → Val

      cval {t} ps x y =
        let mx' = next t x y
        in measure (map (reward t x y ⊕ₗ val' ps) mx')

      val' Nil x = 0Val
      val' (p ∷ ps) x = cval ps x (p x)

      -- We formulate optimality in terms of val' to make certain computations easier.

      OptPolicySeq : ∀ {t n} → PolicySeq t n → Type
      OptPolicySeq {t} {n} ps = ∀ (ps' : PolicySeq t n) → val' ps' ≤ₗ val' ps

      OptExt : ∀ {t n} → PolicySeq (suc t) n → Policy t → Type
      OptExt ps p = ∀ p' → val' (p' ∷ ps) ≤ₗ val' (p ∷ ps)
```

## Exercise 7.1

Let's define the example SDP:

```agda
private
  data X' : Nat → Type where
    x₀ : X' 0
    x₁⁰ x₁¹ : X' 1
    x₂⁰⁰ x₂⁰¹ x₂¹⁰ : X' 2

  data Y' : (t : Nat) → X' t → Type where
    y₀ : Y' 0 x₀
    y₁⁰ : Y' 1 x₁⁰
    y₁¹ : Y' 1 x₁¹

ev : SP Ratio → Ratio
ev sp = sum (map (uncurry _*ℚ_) sp)

module Example (α β : Ratio) (r₀⁰ r₀¹ r₁⁰⁰ r₁⁰¹ r₁¹⁰ : Ratio) where
  example : SDP (eff SP)
  example .SDP.X = X'
  example .SDP.Y = Y'
  example .SDP.next 0 x₀ y₀ = (x₁⁰ , α) ∷ (x₁¹ , 1 -ℚ α) ∷ []
  example .SDP.next 1 x₁⁰ y₁⁰ = (x₂⁰⁰ , β) ∷ (x₂⁰¹ , 1 -ℚ β) ∷ []
  example .SDP.next 1 x₁¹ y₁¹ = (x₂¹⁰ , 1) ∷ []
  example .SDP.Val-poset = Ratio-poset
  example .SDP.Val-total = Ratio-is-dec-total
  example .SDP.0Val = 0
  example .SDP._⊕_ = _+ℚ_
  example .SDP.reward t x₀ y₀ x₁⁰ = r₀⁰
  example .SDP.reward t x₀ y₀ x₁¹ = r₀¹
  example .SDP.reward t x₁⁰ y₁⁰ x₂⁰⁰ = r₁⁰⁰
  example .SDP.reward t x₁⁰ y₁⁰ x₂⁰¹ = r₁⁰¹
  example .SDP.reward t x₁⁰ y₁⁰ x₂¹⁰ = 0
  example .SDP.reward t x₁¹ y₁¹ x₂⁰⁰ = 0
  example .SDP.reward t x₁¹ y₁¹ x₂⁰¹ = 0
  example .SDP.reward t x₁¹ y₁¹ x₂¹⁰ = r₁¹⁰

  open SDP example
  open Measure ev
```

We define the policies `p₀` and `p₁` and check that there are **three**
possible trajectories for the policy sequence `[p₀, p₁]`:

```agda
  p₀ : (x : X' 0) → Y' 0 x
  p₀ x₀ = y₀

  p₁ : (x : X' 1) → Y' 1 x
  p₁ x₁⁰ = y₁⁰
  p₁ x₁¹ = y₁¹

  _ : length (trj (p₀ ∷ p₁ ∷ Nil) x₀) ≡ 3
  _ = refl
```

## Exercise 7.2

The `SP` monad was already defined correctly in `MM2`; we check that
the trajectories evaluate as expected.

```agda
  μSP : ∀ {A : Type} → SP (SP A) → SP A
  μSP x = x >>= id

  _ : trj (p₀ ∷ p₁ ∷ Nil) x₀
    ≡ ((x₀ , y₀) ∷ (x₁⁰ , y₁⁰) ∷ Last x₂⁰⁰ , α *ℚ (β *ℚ 1))
    ∷ ((x₀ , y₀) ∷ (x₁⁰ , y₁⁰) ∷ Last x₂⁰¹ , α *ℚ ((1 -ℚ β) *ℚ 1))
    ∷ ((x₀ , y₀) ∷ (x₁¹ , y₁¹) ∷ Last x₂¹⁰ , (1 -ℚ α) *ℚ 1)
    ∷ []
  _ = refl
```

## Exercise 7.5 (out of order)

The computation below consists entirely of definitional equalities and
applications of the rational solver. I ran out of patience in the middle,
as you can tell.

```agda
  computation =
    val (p₀ ∷ p₁ ∷ Nil) x₀
      ≡⟨⟩ -- step 1
    ev (map sumR (trj (p₀ ∷ p₁ ∷ Nil) x₀))
      ≡⟨⟩ -- steps 2 and 3
    ev ((r₀⁰ +ℚ (r₁⁰⁰ +ℚ 0) , α *ℚ (β *ℚ 1))
      ∷ (r₀⁰ +ℚ (r₁⁰¹ +ℚ 0) , α *ℚ ((1 -ℚ β) *ℚ 1))
      ∷ (r₀¹ +ℚ (r₁¹⁰ +ℚ 0) , (1 -ℚ α) *ℚ 1)
      ∷ [])
      ≡⟨ rational! ⟩ -- steps 4 and 5
       r₀⁰ *ℚ α
    +ℚ r₁⁰⁰ *ℚ β *ℚ α
    +ℚ r₁⁰¹ *ℚ (1 -ℚ β) *ℚ α
    +ℚ r₀¹ *ℚ (1 -ℚ α)
    +ℚ r₁¹⁰ *ℚ (1 -ℚ α)
      ≡⟨ rational! ⟩ -- steps 6 to 11...
    ev ((reward 0 x₀ y₀ x₁⁰ ⊕ val (p₁ ∷ Nil) x₁⁰ , α) ∷ (reward 0 x₀ y₀ x₁¹ ⊕ val (p₁ ∷ Nil) x₁¹ , 1 -ℚ α) ∷ [])
      ≡⟨⟩ -- step 12
    ev (map (reward 0 x₀ y₀ ⊕ₗ val (p₁ ∷ Nil)) ((x₁⁰ , α) ∷ (x₁¹ , 1 -ℚ α) ∷ []))
      ≡⟨⟩ -- step 13
    ev (map (reward 0 x₀ y₀ ⊕ₗ val (p₁ ∷ Nil)) (next 0 x₀ y₀))
      ∎
```

## Exercise 7.3

We formulate the law of total probability relative to an event E:

$$ P(E) = \sum_{a : A} P(E \mid a) P(a) $$

```agda
module _
  (A B : Type) ⦃ _ : Listing A ⦄ (sp : SP A) (f : A → SP B)
  (E : B → Type) ⦃ _ : ∀ {b} → Dec (E b) ⦄
  where
  private instance
    Discrete-A : Discrete A
    Discrete-A = Listing→Discrete auto

  total-probability =
    prb (sp >>= f) E ≡ sum (univ <&> λ a → prb (f a) E *ℚ prb sp (_≡ a))
```

## Exercise 7.4

Yes.

## Exercise 7.7

```agda
instance
  Map-id : Map (eff id)
  Map-id .Map.map f = f

  Idiom-id : Idiom (eff id)
  Idiom-id .Idiom.pure a = a
  Idiom-id .Idiom._<*>_ f a = f a

  Bind-id : Bind (eff id)
  Bind-id .Bind._>>=_ s f = f s

module Bellman (sdp : SDP (eff id)) (open SDP sdp) where
  measure = id
  open Measure measure
```

We prove the `Lemma` using the fact that the head of a trajectory is the
initial state. Bellman's equation follows immediately.

```agda
  head-trj : ∀ {t n} (ps : PolicySeq t n) (x : X t) → headXY (trj ps x) ≡ x
  head-trj Nil x = refl
  head-trj (p ∷ ps) x = refl

  Lemma
    : (t n : Nat) (p : Policy t) (ps : PolicySeq (suc t) n) (x : X t)
    → sumR (trj (p ∷ ps) x)
    ≡ reward t x (p x) (next t x (p x)) ⊕ val ps (next t x (p x))
  Lemma t n p ps x = ap (λ z → reward t x (p x) z ⊕ val ps _) (head-trj ps _)

  BellmanEq
    : (t n : Nat) (p : Policy t) (ps : PolicySeq (suc t) n) (x : X t)
    → val (p ∷ ps) x
    ≡ measure (map (reward t x (p x) ⊕ₗ val ps) (next t x (p x)))
  BellmanEq = Lemma
```

## Exercise 7.8

Instead of postulating `Finite` and `NonEmpty` we use our existing
definitions. Note that the postulates below would be inconsistent with
univalence if formulated with `Finite`, so we use `Listing` instead.

```agda
module BI
  {M} ⦃ _ : Bind M ⦄ (let module M = Effect M)
  (sdp : SDP M) (open SDP sdp)
  (measure : M.₀ Val → Val) (open Measure measure)
  where

  postulate
    univ-nonempty : {A : Type} → ⦃ _ : Listing A ⦄ → ∥ A ∥ → is-nonempty (univ {A = A})
    argmax : {A : Type} → (f : A → Val) → Σ (List A) is-nonempty → A
    instance
      fY : {t : Nat} → {x : X t} → Listing (Y t x)
    neY : {t : Nat} → (x : X t) → ∥ Y t x ∥

  optExt : {t n : Nat} → PolicySeq (suc t) n → Policy t
  optExt ps x = argmax (cval ps x) (univ , univ-nonempty (neY x))
```

## Exercise 7.9

`toList {A}` (here `univ {A}`) should return a list containing every element of `A` at least once (`Listing.has-member`).
`argmax` should obey the obvious specification for an argmax function.

```agda
  postulate
    optExtSpec : ∀ {t n} → (ps : PolicySeq (suc t) n) → OptExt ps (optExt ps)
```

## Exercise 7.10

```agda
  postulate
    measureMon
      : ∀ {A : Type} (f g : A → Val)
      → f ≤ₗ g
      → measure ∘ map f ≤ₗ measure ∘ map g
    plusMon : ∀ {a b c d} → a ≤ b → c ≤ d → (a ⊕ c) ≤ (b ⊕ d)

  Bellman
    : ∀ {t n} (p : Policy t) (ps : PolicySeq (suc t) n)
    → OptExt ps p → OptPolicySeq ps → OptPolicySeq (p ∷ ps)
  Bellman p ps p-opt ps-opt (p' ∷ ps') x = ≤-trans
    (measureMon _ _ (λ x' → plusMon ≤-refl (ps-opt ps' x')) _)
    (p-opt p' x)
```

## Exercise 7.11

```agda
  bi : ∀ t n → PolicySeq t n
  bi t zero = Nil
  bi t (suc n) =
    let ps = bi (suc t) n
    in optExt ps ∷ ps

  biOptVal : ∀ t n → OptPolicySeq (bi t n)
  biOptVal t zero Nil x = ≤-refl
  biOptVal t (suc n) =
    let ps = bi (suc t) n
    in Bellman (optExt ps) ps (optExtSpec ps) (biOptVal (suc t) n)
```

## Exercise 7.12

Formalising real-world decision problems in this simple framework might be challenging?
