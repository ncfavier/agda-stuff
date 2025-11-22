```agda
open import Cat.Prelude
open import Cat.Strict
open import Cat.Skeletal
open import Cat.Gaunt
open import Cat.Functor.Equivalence
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Naturality
open import 1Lab.Function.Surjection

open is-precat-iso
open is-gaunt
open Functor

module SetsCover where
```

If $F : C \cong D$ is an equivalence of precategories where $C$ is
univalent and $D$ is strict, then $C$ is also strict.
If $D$ is furthermore skeletal, then $F$ is an isomorphism of
precategories (whence $C$ and $D$ are both gaunt).

While sets covering groupoids implies that every univalent category
is weakly equivalent to a strict one, this shows that we cannot
strengthen this to an equivalence (see also [Skeletons](/Skeletons)).

```agda
module _
  {oc ℓc od ℓd}
  (C : Precategory oc ℓc) (D : Precategory od ℓd)
  (F : Functor C D) (F-eqv : is-equivalence F)
  (C-cat : is-category C)
  where

  open is-equivalence F-eqv
  module C-cat = Univalent C-cat

  univalent≅strict : is-strict D → is-strict C
  univalent≅strict = retract→is-hlevel 2 (F⁻¹ .F₀) (F .F₀)
    λ c → sym $ C-cat.iso→path (isoⁿ→iso Id≅F⁻¹∘F c)

  univalent≅skeletal : is-skeletal D → is-precat-iso F
  univalent≅skeletal D-skeletal .has-is-ff = is-equivalence→is-ff F F-eqv
  univalent≅skeletal D-skeletal .has-is-iso = is-iso→is-equiv λ where
    .is-iso.from → F⁻¹ .F₀
    .is-iso.rinv d → D-skeletal.to-path (inc (isoⁿ→iso F∘F⁻¹≅Id d))
    .is-iso.linv c → sym $ C-cat.iso→path (isoⁿ→iso Id≅F⁻¹∘F c)
      where module D-skeletal = is-identity-system D-skeletal
```

$\mathrm{AC}_\infty$ implies that sets cover, in the strong sense that
every type is *equipped* with a set and a mere surjection.
I don't know if the fully untruncated version is consistent.

```agda
is-projective : ∀ {ℓ} (A : Type ℓ) → (κ : Level) → Type _
is-projective A κ =
  ∀ (P : A → Type κ)
  → (∀ a → ∥ P a ∥)
  → ∥ (∀ a → P a) ∥

AC∞ = ∀ {ℓ} (A : Type ℓ) κ → is-projective A κ

module _ (ac∞ : AC∞) where
  sets-cover
    : ∀ {ℓ} (A : Type ℓ)
    → Σ[ X ∈ Set ℓ ] ∥ ∣ X ∣ ↠ A ∥
  sets-cover A = el! ∥ A ∥₀ , do
    split ← ac∞ ∥ A ∥₀ _ (fibre inc) (elim! λ a → inc (a , refl))
    pure $ fst ⊙ split , λ a → do
      p ← ∥-∥₀-path.to (split (inc a) .snd)
      inc (inc a , p)
```
