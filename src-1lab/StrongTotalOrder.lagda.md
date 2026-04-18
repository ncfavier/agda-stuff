```agda
open import 1Lab.Prelude
open import Data.Bool
open import Data.Sum
open import Data.Dec
open import Order.Base
open import Homotopy.Space.Suspension
open import Homotopy.Space.Suspension.Properties

open Poset

module StrongTotalOrder where

is-right : ∀ {a b} {A : Type a} {B : Type b} → A ⊎ B → Bool
is-right (inl _) = false
is-right (inr _) = true
```

# strong total orders

The point of this module is to answer the following question:

> In the definition of a total order, why do we need to truncate the
> disjunction $\| (x ≤ y) + (y ≤ x) \|$?

One immediate answer is that we want totality to be a *property* of an
order, not a structure on it. However, we could be tempted to achieve
this by placing the truncation *outside* of the quantification, defining
totality of an order as $\| \forall x y. (x ≤ y) + (y ≤ x) \|$. To
avoid ambiguity, let us refer to this (stronger) definition as a
**strong total order**.
What follows is an example which separates the two notions: a total order
which is a strong total order if and only if excluded middle holds.

We assume given a proposition $P$ and consider its
[*suspension*](https://1lab.dev/Homotopy.Space.Suspension.html) $\Sigma P$:
a set with two points $\mathsf{north}$ and $\mathsf{south}$ and a unique path between them
if and only $P$ holds. This set has one element if $P$ and two
elements if $\neg P$, so deciding its cardinality amounts to
deciding $P$. This is a recurrent protagonist in constructive counterexamples:
it is also used e.g. to prove that [the axiom of choice implies excluded
middle](https://1lab.dev/1Lab.Classical.html#the-axiom-of-choice).

```agda
module _ {ℓ} (P : Type ℓ) (P-prop : is-prop P) where
  ΣP = Susp P

  ΣP-is-set : is-set ΣP
  ΣP-is-set = Susp-prop-is-set P-prop
```

We then define a total order on $\Sigma P$ by declaring that the north
pole is higher than the south pole (hence that it is *strictly*
higher if and only if $\neg P$).

```agda
  _≤'_ : ΣP → ΣP → Prop ℓ
  _≤'_ = Susp-elim _
    (Susp-elim _
      (el! (Lift _ ⊤)) -- N ≤ N
      (el P P-prop)    -- N ≤ S
      (λ p → n-ua (P→⊤≃P p)))
    (λ _ → el! (Lift _ ⊤)) -- S ≤ _
    (λ p → ext (Susp-elim-prop (λ _ → hlevel 1) refl (n-ua (P→⊤≃P p e⁻¹))))
    where
      P→⊤≃P : P → Lift _ ⊤ ≃ P
      P→⊤≃P p = is-contr→≃ (hlevel 0) (is-prop∙→is-contr P-prop p)
```

It is straightforward to show that this is a total partial order.

```agda
  ≤'-refl : ∀ x → ∣ x ≤' x ∣
  ≤'-refl = Susp-elim-prop (λ _ → hlevel 1) _ _

  ≤'-trans : ∀ x y z → ∣ x ≤' y ∣ → ∣ y ≤' z ∣ → ∣ x ≤' z ∣
  ≤'-trans = Susp-elim-prop (λ _ → hlevel 1)
    (Susp-elim-prop (λ _ → hlevel 1)
      (λ _ _ p → p)
      (Susp-elim-prop (λ _ → hlevel 1)
        _
        (λ p _ → p)))
    _

  ≤'-antisym : ∀ x y → ∣ x ≤' y ∣ → ∣ y ≤' x ∣ → x ≡ y
  ≤'-antisym = Susp-elim-prop
    (λ _ → Π-is-hlevel 1 λ _ → Π-is-hlevel² 1 λ _ _ → ΣP-is-set _ _)
    (Susp-elim-prop (λ _ → Π-is-hlevel² 1 λ _ _ → ΣP-is-set _ _)
      (λ _ _ → refl)
      (λ p _ → merid p))
    (Susp-elim-prop (λ _ → Π-is-hlevel² 1 λ _ _ → ΣP-is-set _ _)
      (λ _ p → sym (merid p))
      (λ _ _ → refl))

  ΣP' : Poset ℓ ℓ
  ΣP' .Ob = ΣP
  ΣP' ._≤_ x y = ∣ x ≤' y ∣
  ΣP' .≤-thin {x} {y} = (x ≤' y) .is-tr
  ΣP' .≤-refl {x} = ≤'-refl x
  ΣP' .≤-trans {x} {y} {z} = ≤'-trans x y z
  ΣP' .≤-antisym {x} {y} = ≤'-antisym x y

  ΣP'-total : ∀ x y → ∥ ∣ x ≤' y ∣ ⊎ ∣ y ≤' x ∣ ∥
  ΣP'-total = Susp-elim-prop (λ _ → hlevel 1)
    (Susp-elim-prop (λ _ → hlevel 1)
      (inc (inl _))
      (inc (inr _)))
    (λ _ → inc (inl _))
```

However, assuming that $\Sigma P$ is *strongly* totally ordered allows
us to decide $P$. Letting $t(x, y)$ be the boolean-valued function that
returns false if $x ≤ y$ and true if $y ≤ x$, we reason by cases:

- If $t(\mathsf{south}, \mathsf{north})$ is true or $t(\mathsf{north}, \mathsf{south})$ is false, we have $\mathsf{north} ≤ \mathsf{south}$, hence $P$ holds.
- Otherwise, if $t(\mathsf{south}, \mathsf{north})$ is false and $t(\mathsf{north}, \mathsf{south})$ is true, then $P$ cannot hold, because then we would have $\mathsf{south} = \mathsf{north}$, hence $t$ should give the same result in both cases.

```agda
  not-strongly-total : (∀ x y → ∣ x ≤' y ∣ ⊎ ∣ y ≤' x ∣) → Dec P
  not-strongly-total t with t south north in e₁ | t north south in e₂
  ... | inr p | _     = yes p
  ... | inl _ | inl p = yes p
  ... | inl _ | inr _ = no λ p → false≠true $
       sym (ap is-right (Id≃path.to e₁))
    ∙∙ ap₂ (λ x y → is-right (t x y)) (sym (merid p)) (merid p)
    ∙∙ ap is-right (Id≃path.to e₂)
```
