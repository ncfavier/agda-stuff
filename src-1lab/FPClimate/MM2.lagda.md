# MM2

## Exercises 5.1, 5.2

I am already familiar with categories, functors and monads, so I will skip this.

## Exercise 5.3

Compared to `next`, we now have time-dependence, controls, and the uncertainty monad is generalised from lists to an arbitrary monad M.

To compute the flow and trajectories of `next`, we would need to know which control should be selected at each step and state: a policy sequence for n steps.

## Exercise 5.4

A non-deterministic system would have multiple edges for the same starting time, state and control, which this picture does not.

A non-deterministic decision network with a single control could look like:

```plain
Init (t = 0)
|-[A]-> S0 (t = 1)
\-[A]-> S1 (t = 1)
```

## Exercise 5.5

Informally, solving an SDP is finding the optimal policy across all possible outcomes.

Formally, what it means depends on how we measure reward under uncertainty: that is, how we compare values of type `M Val`.

## Exercise 5.6

```agda
open import 1Lab.Prelude
open import Meta.Idiom
open import Meta.Bind
open import Data.List
open import Data.Int
open import Data.Rational.Base

open import FPClimate.OUU3

module FPClimate.MM2 where

module _ (M : Effect) ⦃ _ : Bind M ⦄ where
  private module M = Effect M

  record SDP : Type (lsuc (M.adj lzero)) where
    field
      X : Nat → Type
      Y : (t : Nat) → X t → Type
      next : (t : Nat) → (x : X t) → Y t x → M.₀ (X (suc t))

-- The SP monad (note: _>>=_ breaks `uniform`'s invariant)

mutual instance
  Map-SP : Map (eff SP)
  Map-SP .Map.map f = map λ (a , p) → f a , p

  Idiom-SP : Idiom (eff SP)
  Idiom-SP .Idiom.pure a = (a , 1) ∷ []
  Idiom-SP .Idiom._<*>_ f a = f >>= λ f → a >>= λ a → pure (f a)

  Bind-SP : Bind (eff SP)
  Bind-SP .Bind._>>=_ s f = s >>= λ (a , p) → f a <&> λ (b , q) → b , p *ℚ q

-- The generational dilemma as an SDP, parametrised by the probability that
-- the control a will take us to state B.

private
  data X : Type where
    GU GS B BT : X

  data Y : Type where
    a b : Y

Generational-dilemma : Ratio → SDP (eff SP)
Generational-dilemma risk .SDP.X t = X
Generational-dilemma risk .SDP.Y t GU = Y
Generational-dilemma risk .SDP.Y t _ = ⊤
Generational-dilemma risk .SDP.next t GU a = (GU , 1 -ℚ risk) ∷ (B , risk) ∷ []
Generational-dilemma risk .SDP.next t GU b = pure BT
Generational-dilemma risk .SDP.next t GS _ = pure GS
Generational-dilemma risk .SDP.next t BT _ = pure GS
Generational-dilemma risk .SDP.next t B  _ = pure B
```

`Val` should be some way to measure the well-being (wealth?) of a society.
In any case, `reward` should assign "low" rewards to states `B` and `BT`
and "high" rewards to states `GU` and `GS`.

## Exercise 5.7

A `PolicySeq t n` specifies how to act for `n` steps starting at time `t`:
morally, it is a dependent function `(i : [t..t+n-1]) → Policy i`.

Policy sequences grow "backwards" via the `_∷_` constructor: if we have policies for `n` steps starting at time `suc t`, and we have a policy for time `t`, then we have policies for `suc n` steps starting at time `t`.
