```agda
open import 1Lab.Prelude
open import 1Lab.Reflection.Induction
open import 1Lab.HLevel.Universe
open import Data.Bool

module RPnHIT where
```

# $\mathbb{R}P^n$ as a higher inductive type

The real projective spaces have a convenient cubical cell structure,
which makes it easy to define $\mathbb{R}P^n$ (for a fixed *external* $n$)
as a HIT in cubical type theory with reversals:

```agda
data RPⁿ : Type where
  c0 : RPⁿ
  c1 : c0 ≡ c0
  c2 : RPⁿ.c1 ≡ (λ i → c1 (~ i))
  c3 : RPⁿ.c2 ≡ (λ i j → c2 (~ i) (~ j))
  c4 : RPⁿ.c3 ≡ (λ i j k → c3 (~ i) (~ j) (~ k))
  -- ... up to n
```

It doesn't seem possible to do this internally, so proving that this
yields the correct space would probably involve some sort of 2LTT or
reflection, but it is easy to see visually.

We derive an induction principle into groupoids automatically and define the
tautological two-element bundle.

```agda
unquoteDecl RPⁿ-elim = make-elim-n 3 RPⁿ-elim (quote RPⁿ)

RPⁿ-bundle : RPⁿ → Type
RPⁿ-bundle = ∣_∣ ∘ RPⁿ-elim (λ _ → n-Type-is-hlevel 2)
  (el! Bool)
  (n-ua not≃)
  (n-Type-square (transport-injective refl))
```

By adding an $(n-1)$-truncation constructor to $\mathbb{R}P^n$ (for $n ≥ 2$), we get
$\mathbb{R}P^∞ = \mathbf{B}\mathbb{Z}/2\mathbb{Z}$, so the eliminator
gives a convenient way to define coherent involutions in $n$-types.
