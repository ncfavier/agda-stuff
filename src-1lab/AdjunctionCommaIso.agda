open import Cat.Functor.Adjoint
open import Cat.Functor.Equivalence
open import Cat.Instances.Comma
open import Cat.Prelude

import Cat.Reasoning

open ↓Hom
open ↓Obj
open Functor
open is-iso
open is-precat-iso

-- An adjunction F ⊣ G induces an isomorphism of comma categories F ↓ 1 ≅ 1 ↓ G
module AdjunctionCommaIso where

module _
  {oc ℓc od ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
  {F : Functor C D} {G : Functor D C} (F⊣G : F ⊣ G)
  where

  module C = Cat.Reasoning C
  module D = Cat.Reasoning D

  to : Functor (F ↓ Id) (Id ↓ G)
  to .F₀ o .dom = o .dom
  to .F₀ o .cod = o .cod
  to .F₀ o .map = L-adjunct F⊣G (o .map)
  to .F₁ f .top = f .top
  to .F₁ f .bot = f .bot
  to .F₁ {a} {b} f .com =
    L-adjunct F⊣G (b .map) C.∘ f .top         ≡˘⟨ L-adjunct-naturall F⊣G _ _ ⟩
    L-adjunct F⊣G (b .map D.∘ F .F₁ (f .top)) ≡⟨ ap (L-adjunct F⊣G) (f .com) ⟩
    L-adjunct F⊣G (f .bot D.∘ a .map)         ≡⟨ L-adjunct-naturalr F⊣G _ _ ⟩
    G .F₁ (f .bot) C.∘ L-adjunct F⊣G (a .map) ∎
  to .F-id = trivial!
  to .F-∘ _ _ = trivial!

  to-is-precat-iso : is-precat-iso to
  to-is-precat-iso .has-is-ff = is-iso→is-equiv is where
    is : ∀ {a b} → is-iso (to .F₁ {a} {b})
    is .from f .top = f .top
    is .from f .bot = f .bot
    is {a} {b} .from f .com = Equiv.injective (adjunct-hom-equiv F⊣G) $
      L-adjunct F⊣G (b .map D.∘ F .F₁ (f .top)) ≡⟨ L-adjunct-naturall F⊣G _ _ ⟩
      L-adjunct F⊣G (b .map) C.∘ f .top         ≡⟨ f .com ⟩
      G .F₁ (f .bot) C.∘ L-adjunct F⊣G (a .map) ≡˘⟨ L-adjunct-naturalr F⊣G _ _ ⟩
      L-adjunct F⊣G (f .bot D.∘ a .map)         ∎
    is .rinv f = trivial!
    is .linv f = trivial!
  to-is-precat-iso .has-is-iso = is-iso→is-equiv is where
    is : is-iso (to .F₀)
    is .from o .dom = o .dom
    is .from o .cod = o .cod
    is .from o .map = R-adjunct F⊣G (o .map)
    is .rinv o = ↓Obj-path _ _ refl refl (L-R-adjunct F⊣G _)
    is .linv o = ↓Obj-path _ _ refl refl (R-L-adjunct F⊣G _)
