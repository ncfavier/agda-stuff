```agda
open import 1Lab.Prelude hiding (Singleton)

open import FPClimate.OUU3
open import FPClimate.MM2 hiding (SDP)
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
module _
  {M} ⦃ _ : Bind M ⦄ (let module M = Effect M)
  (sdp : SDP M) (open SDP sdp)
  (measure : M.₀ Val → Val) (open Measure measure)
  (open BI sdp measure)
  where

  bestVal : (t n : Nat) → X t → Val
  bestVal t n x = val (bi t n) x
```
