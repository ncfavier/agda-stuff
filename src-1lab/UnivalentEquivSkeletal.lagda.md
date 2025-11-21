```agda
open import Cat.Prelude
open import Cat.Strict
open import Cat.Skeletal
open import Cat.Gaunt
open import Cat.Functor.Equivalence
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Naturality

open is-precat-iso
open is-gaunt
open Functor

module UnivalentEquivSkeletal where
```

If $F : C \cong D$ is an equivalence of precategories between a univalent
category and a skeletal category, then $F$ is an isomorphism of
precategories (whence $C$ and $D$ are both gaunt).

```agda

module _
  {o ℓ}
  (C : Precategory o ℓ) (D : Precategory o ℓ)
  (C-cat : is-category C) (D-skeletal : is-skeletal D)
  (F : Functor C D) (F-eqv : is-equivalence F)
  where

  open is-equivalence F-eqv
  module C-cat = Univalent C-cat
  module D-skeletal = is-identity-system D-skeletal

  F-is-iso : is-precat-iso F
  F-is-iso .has-is-ff = is-equivalence→is-ff F F-eqv
  F-is-iso .has-is-iso = is-iso→is-equiv λ where
    .is-iso.from → F⁻¹ .F₀
    .is-iso.rinv d → D-skeletal.to-path (inc (isoⁿ→iso F∘F⁻¹≅Id d))
    .is-iso.linv c → sym $ C-cat.iso→path (isoⁿ→iso Id≅F⁻¹∘F c)

  C≡D : C ≡ D
  C≡D = Precategory-path F F-is-iso

  C-gaunt : is-gaunt C
  D-gaunt : is-gaunt D

  C-gaunt .has-category = C-cat
  C-gaunt .has-strict = subst is-strict (sym C≡D) (D-gaunt .has-strict)
  D-gaunt .has-category = subst is-category C≡D C-cat
  D-gaunt .has-strict = skeletal→strict D D-skeletal
```
