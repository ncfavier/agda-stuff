<details>
<summary>Imports</summary>

```agda
open import Cat.Prelude hiding (J)
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Discrete
open import Cat.Instances.Shape.Join

open import Data.Sum

import Cat.Reasoning
import Cat.Functor.Reasoning

open Precategory
open Functor
open make-is-limit
```
</details>

This module formalises a very interesting result from Jem Lord's recent work on
[*Easy Parametricity*](https://hott-uf.github.io/2025/abstracts/HoTTUF_2025_paper_21.pdf),
presented at [HoTT/UF 2025](https://hott-uf.github.io/2025/).

```agda
module EasyParametricity {u} where

U = Type u
𝟘 = Lift u ⊥
𝟙 = Lift u ⊤

postulate
  -- An immediate consequence of Jem Lord's parametricity axiom: a function
  -- out of U into a U-small type cannot tell 0 and 1 apart; this is all we need here.
  -- If we think of functions f : U → A as "bridges" from f 0 to f 1, then this
  -- basically says that U-small types are "bridge-discrete".
  parametricity : ∀ {A : U} (f : U → A) → f 𝟘 ≡ f 𝟙

-- The type of formal composites r ∘ l : A → B in C. We want to think of this
-- as the type of factorisations of some morphism f : A → B, but it turns out
-- to be unnecessary to track f in the type.
record Factorisation {o ℓ} (C : Precategory o ℓ) (A B : C .Ob) : Type (o ⊔ ℓ) where
  constructor factor
  module C = Precategory C
  field
    X : C.Ob
    l : C.Hom A X
    r : C.Hom X B

-- We prove theorem 1.a from Easy Parametricity: if C is a U-complete univalent category
-- and D is a locally U-small category, then naturality of transformations between
-- functors C → D is free.
module _
  {o o' ℓ} {C : Precategory o ℓ} {D : Precategory o' u}
  (C-complete : is-complete u lzero C)
  (C-category : is-category C)
  (F G : Functor C D)
  (let module C = Cat.Reasoning C) (let module D = Cat.Reasoning D)
  (let module F = Cat.Functor.Reasoning F) (let module G = Cat.Functor.Reasoning G)
  (η : ∀ x → D.Hom (F.₀ x) (G.₀ x))
  where

  natural : is-natural-transformation F G η
  natural A B f = G.introl refl ∙ z0≡z1 ∙ (D.refl⟩∘⟨ F.elimr refl) where

    -- We define the two factorisations id ∘ f and f ∘ id.
    f,id : Factorisation C A B
    f,id = factor B f C.id
    id,f : Factorisation C A B
    id,f = factor A C.id f

    -- Given a factorisation A → X → B, we define the map
    --       F A
    --        ↓
    -- η X : F X → G X
    --              ↓
    --             G B
    -- which recovers the naturality square for f as the factorisation varies
    -- from id ∘ f to f ∘ id.
    z : Factorisation C A B → D.Hom (F.F₀ A) (G.F₀ B)
    z (factor X l r) = G.F₁ r D.∘ η X D.∘ F.F₁ l

    -- We define a "bridge" in the type of factorisations from id ∘ f to f ∘ id.
    b : U → Factorisation C A B
    b P = fac (C-complete diagram) module b where

      -- This is the interesting part: given a type P : U, we construct the
      -- wide pullback of P-many copies of f.
      -- Since we only care about the cases where P is a proposition, we
      -- can just take the discrete or codiscrete category on P and adjoin a
      -- terminal object to get our diagram shape.
      J : Precategory u lzero
      J = Codisc' P ▹

      diagram : Functor J C
      diagram .F₀ (inl _) = A
      diagram .F₀ (inr _) = B
      diagram .F₁ {inl _} {inl _} _ = C.id
      diagram .F₁ {inl _} {inr _} _ = f
      diagram .F₁ {inr _} {inr _} _ = C.id
      diagram .F-id {inl _} = refl
      diagram .F-id {inr _} = refl
      diagram .F-∘ {inl _} {inl _} {inl _} _ _ = sym (C.idl _)
      diagram .F-∘ {inl _} {inl _} {inr _} _ _ = sym (C.idr _)
      diagram .F-∘ {inl _} {inr _} {inr _} _ _ = sym (C.idl _)
      diagram .F-∘ {inr _} {inr _} {inr _} _ _ = sym (C.idl _)

      -- Given a limit of this diagram (which exists by the assumption of U-completeness),
      -- we get a factorisation of f as the universal map followed by the projection to B.
      fac : Limit diagram → Factorisation C A B
      fac lim = factor X l r where
        module lim = Limit lim
        X : C.Ob
        X = lim.apex
        l : C.Hom A X
        l = lim.universal (λ { (inl _) → C.id; (inr _) → f }) λ where
          {inl _} {inl _} _ → C.idl _
          {inl _} {inr _} _ → C.idr _
          {inr _} {inr _} _ → C.idl _
        r : C.Hom X B
        r = lim.cone ._=>_.η (inr tt)

    -- We check that the endpoints of the bridge are what we expect: when P
    -- is empty, we are taking the limit of the single-object diagram B, so
    -- our factorisation is A → B → B.
    b0 : b 𝟘 ≡ f,id
    b0 = ap (b.fac 𝟘) (Limit-is-prop C-category (C-complete _) (to-limit lim)) where
      lim : is-limit (b.diagram 𝟘) B _
      lim = to-is-limit λ where
        .ψ (inr _) → C.id
        .commutes {inr _} {inr _} _ → C.idl _
        .universal eps comm → eps (inr _)
        .factors {inr _} eps comm → C.idl _
        .unique eps comm other fac → sym (C.idl _) ∙ fac (inr _)

    -- When P is contractible, we are taking the limit of the arrow diagram
    -- A → B, so our factorisation is A → A → B.
    b1 : b 𝟙 ≡ id,f
    b1 = ap (b.fac 𝟙) (Limit-is-prop C-category (C-complete _) (to-limit lim)) where
      lim : is-limit (b.diagram 𝟙) A _
      lim = to-is-limit λ where
        .ψ (inl _) → C.id
        .ψ (inr _) → f
        .commutes {inl _} {inl _} _ → C.idl _
        .commutes {inl _} {inr _} _ → C.idr _
        .commutes {inr _} {inr _} _ → C.idl _
        .universal eps comm → eps (inl (lift tt))
        .factors {inl _} eps comm → C.idl _
        .factors {inr _} eps comm → comm {inl _} {inr _} _
        .unique eps comm other fac → sym (C.idl _) ∙ fac (inl _)

    -- As a result, we get a bridge from one side of the naturality square
    -- to the other; since D is locally U-small, the Hom-sets of D are bridge-discrete,
    -- so we get the desired equality.
    z0≡z1 : z f,id ≡ z id,f
    z0≡z1 = sym (ap z b0) ∙∙ parametricity (z ⊙ b) ∙∙ ap z b1
```
