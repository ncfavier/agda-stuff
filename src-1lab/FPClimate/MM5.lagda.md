```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import 1Lab.Prelude hiding (Singleton)
open import Data.List.NonEmpty
open import Data.Fin.Finite
open import Data.Dec.Base

open import FPClimate.OUU3
open import FPClimate.MM2 hiding (SDP; Generational-dilemma)
open import FPClimate.MM4

module FPClimate.MM5 where
```

# MM5

## Exercise 8.1

```agda
Singleton : ∀ {ℓ} → Type ℓ → Type ℓ
Singleton = is-contr
```

`mMeas` should more generally be 0 when all available controls lead
to the same outcome.

How much a decision matters also depends on how many decision steps
remain, since this might amplify the positive/negative outcomes.
(As in Pascal's wager.)

## Exercise 8.2

```agda
module BV
  {M} ⦃ _ : Bind M ⦄ (let module M = Effect M)
  (sdp : SDP M) (open SDP sdp)
  (measure : M.₀ Val → Val) (open Measure measure)
  ⦃ fY : ∀ {t x} → Listing (Y t x) ⦄
  ⦃ neY : ∀ {t x} → is-nonempty (univ {A = Y t x}) ⦄
  (open BI sdp measure)
  where

  bestVal : (t n : Nat) → X t → Val
  bestVal t n x = val (bi t n) x
```

# Examples

```agda
open import Data.Float.Base renaming
  ( _+,_ to infixl 30 _+,_
  ; _-,_ to infixl 30 _-,_
  ; _*,_ to infixl 31 _*,_
  ; _/,_ to infixl 31 _/,_
  )
open import Data.Int
open import Data.List
open import Data.Rational.Base
open import Order.Instances.Rational
open import 1Lab.Reflection.List

private
  data X : Type where
    GU GS B BT : X

  data Y : X → Type where
    a : ∀ {x} → Y x
    b : Y GU

instance
  Listing-Y : ∀ {x} → Listing (Y x)
  Listing-Y {GU} .Listing.univ = a ∷ b ∷ []
  Listing-Y {GS} .Listing.univ = a ∷ []
  Listing-Y {B} .Listing.univ = a ∷ []
  Listing-Y {BT} .Listing.univ = a ∷ []
  Listing-Y {GU} .Listing.has-member a = unique-member!
  Listing-Y {GU} .Listing.has-member b = unique-member!
  Listing-Y {GS} .Listing.has-member a = unique-member!
  Listing-Y {B} .Listing.has-member a = unique-member!
  Listing-Y {BT} .Listing.has-member a = unique-member!

  NonEmpty-Y : ∀ {x} → is-nonempty (Listing-Y {x} .Listing.univ)
  NonEmpty-Y {GU} = nonempty
  NonEmpty-Y {GS} = nonempty
  NonEmpty-Y {B} = nonempty
  NonEmpty-Y {BT} = nonempty

  Discrete-Y : ∀ {x} → Discrete (Y x)
  Discrete-Y = Listing→Discrete auto

Generational-dilemma : Ratio → SDP (eff SP)
Generational-dilemma pGU .SDP.X t = X
Generational-dilemma pGU .SDP.Y t = Y
Generational-dilemma pGU .SDP.next t GU a = (GU , pGU) ∷ (B , 1 -ℚ pGU) ∷ []
Generational-dilemma pGU .SDP.next t GU b = pure BT
Generational-dilemma pGU .SDP.next t GS _ = pure GS
Generational-dilemma pGU .SDP.next t BT _ = pure GS
Generational-dilemma pGU .SDP.next t B  _ = pure B
Generational-dilemma pGU .SDP.Val-poset = Ratio-poset
Generational-dilemma pGU .SDP.Val-total = Ratio-is-dec-total
Generational-dilemma pGU .SDP.0Val = 0
Generational-dilemma pGU .SDP._⊕_ = _+ℚ_
-- Generational-dilemma pGU .SDP._⊕_ x y = x +ℚ y /ℚ 2 -- generational discount (makes computations too slow)
Generational-dilemma pGU .SDP.reward _ _ _ x = reward x where
  reward : X → Ratio
  reward GU =   3
  reward BT =  -2
  reward GS =   5 / 2
  reward B  = -10

PolicySeq→ab : ∀ {pGU t n} → SDP.PolicySeq (Generational-dilemma pGU) t n → List (Y GU)
PolicySeq→ab SDP.Nil = []
PolicySeq→ab (x SDP.∷ xs) = x GU ∷ PolicySeq→ab xs

private
  data DUA : Nat → Type where
    tt : DUA zero
    D U A : ∀ {n} → DUA (suc n)

instance
  Listing-DUA : ∀ {x} → Listing (DUA x)
  Listing-DUA {zero} .Listing.univ = tt ∷ []
  Listing-DUA {suc x} .Listing.univ = D ∷ U ∷ A ∷ []
  Listing-DUA {zero} .Listing.has-member tt = unique-member!
  Listing-DUA {suc x} .Listing.has-member D = unique-member!
  Listing-DUA {suc x} .Listing.has-member U = unique-member!
  Listing-DUA {suc x} .Listing.has-member A = unique-member!

  NonEmpty-DUA : ∀ {x} → is-nonempty (Listing-DUA {x} .Listing.univ)
  NonEmpty-DUA {zero} = nonempty
  NonEmpty-DUA {suc _} = nonempty

Waterfall : SDP (eff List)
Waterfall .SDP.X _ = Nat
Waterfall .SDP.Y _ = DUA
Waterfall .SDP.next _ zero y = zero ∷ []
Waterfall .SDP.next _ (suc zero) D = zero ∷ []
Waterfall .SDP.next _ (suc zero) U = suc zero ∷ suc (suc zero) ∷ []
Waterfall .SDP.next _ (suc zero) A = zero ∷ suc zero ∷ []
Waterfall .SDP.next _ (suc (suc x)) D = x ∷ suc x ∷ []
Waterfall .SDP.next _ (suc (suc x)) U = suc (suc x) ∷ suc (suc (suc x)) ∷ []
Waterfall .SDP.next _ (suc (suc x)) A = suc x ∷ suc (suc x) ∷ []
Waterfall .SDP.Val-poset = Ratio-poset
Waterfall .SDP.Val-total = Ratio-is-dec-total
Waterfall .SDP.0Val = 0
Waterfall .SDP._⊕_ = _+ℚ_
Waterfall .SDP.reward t x y zero = -1
Waterfall .SDP.reward t x y (suc x') = 0

PolicySeq→DUA : ∀ {t n} → SDP.PolicySeq Waterfall t n → List (DUA 1)
PolicySeq→DUA SDP.Nil = []
PolicySeq→DUA (x SDP.∷ xs) = x 1 ∷ PolicySeq→DUA xs

runs : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Discrete A ⦄ → List A → List (A × Nat)
runs [] = []
runs (x ∷ xs) with runs xs
... | [] = (x , 1) ∷ []
... | (y , c) ∷ rs with holds? (x ≡ y)
...   | yes x≡y = (y , suc c) ∷ rs
...   | no x≠y = (x , 1) ∷ (y , c) ∷ rs

Ratio→Float : Ratio → Float
Ratio→Float x using n / d [ _ ] ← reduceℚ x = ratio→float n d

runGD : (pGU : Ratio) (n : Nat) → List (Y GU × Nat) × Float
runGD pGU n = runs (PolicySeq→ab best) , Ratio→Float (val best GU)
  where
    open SDP (Generational-dilemma pGU)
    open Measure ev
    open BI (Generational-dilemma pGU) ev
    best = bi 0 n

runW : (n : Nat) → List (DUA 1) × Float
runW n = PolicySeq→DUA best , Ratio→Float (val best 10)
  where
    open SDP Waterfall
    open Measure sum
    open BI Waterfall sum
    best = bi 0 n

_ = {! runW 3  !}
```

This takes a while: the asymptotic complexity of computing an optimal
policy is exponential in the number of steps. It could
probably be made quadratic by using maps instead of functions for
representing policies.

## DICE

From "DICE simplified" by Ikefuji et al.

```agda
ℝ = Float
postulate
  _^_ : Float → Float → Float
  log : Float → Float
infix 32 _^_

module DICE where
  private
    record State : Type where
      field
        H K M X₁ X₂ Z : ℝ
    record Control : Type where
      field
        I' μ C : ℝ
    record Exogenous : Type where
      field
        A' E⁰ F L ψ σ : Nat → ℝ

  a₀ = 0.128189
  a₁ = 0.533755
  a₂ = 0.008844
  a₃ = 0.025
  b₀ = 0.12
  b₁ = 0.196
  b₂ = 0.001465
  b₃ = 0.007
  γ = 0.3
  δ = 0.40951

  module _ (exogenous : Exogenous) (open Exogenous exogenous) where
    DICE : SDP (eff id)
    DICE .SDP.X t = State
    DICE .SDP.Y t _ = Control
    DICE .SDP.next t s c = record where
      open State s
      open Control c
      Y = A' t *, K ^ γ *, L t ^ (1 -, γ)
      K = (1 -, δ) *, K +, I'
      E = σ t *, (1 -, μ) *, Y +, E⁰ t
      M = (1 -, b₀) *, M +, b₁ *, X₁ +, E
      X₁ = b₀ *, M +, (1 -, b₁ -, b₃) *, X₁ +, b₂ *, X₂
      X₂ = b₃ *, X₁ +, (1 -, b₂) *, X₂
      Z = (1 -, a₃) *, Z +, a₃ *, H
      H = (1 -, a₀) *, H +, a₁ *, log M +, a₂ *, Z +, F t
    DICE .SDP.Val-poset = {! ℝ  !}
    DICE .SDP.Val-total = {!   !}
    DICE .SDP.0Val = {!   !}
    DICE .SDP._⊕_ = {!   !}
    DICE .SDP.reward = {!   !}

  initialState : State
  initialState .State.H = 0.85
  initialState .State.K = 223
  initialState .State.M = 851
  initialState .State.X₁ = 460
  initialState .State.X₂ = 1740
  initialState .State.Z = 0.0068
```
