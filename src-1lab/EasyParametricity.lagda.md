<details>
<summary>Imports</summary>

```agda
open import Cat.Prelude hiding (J)
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Discrete
open import Cat.Instances.Shape.Join
open import Cat.Instances.Product
open import Cat.Functor.Bifunctor

open import Data.Sum

import Cat.Reasoning
import Cat.Functor.Reasoning

open Precategory
open Functor
open make-is-limit
```
</details>

This module formalises a few very interesting results from Jem Lord's
"[Easy Parametricity](https://hott-uf.github.io/2025/abstracts/HoTTUF_2025_paper_21.pdf)".

```agda
module EasyParametricity {u} where

U = Type u
𝟘 = Lift u ⊥
𝟙 = Lift u ⊤

-- We think of functions f : U → A as "bridges" from f 𝟘 to f 𝟙.
record Bridge {ℓ} (A : Type ℓ) (x y : A) : Type (ℓ ⊔ lsuc u) where
  no-eta-equality
  constructor bridge
  pattern
  field
    app  : U → A
    app𝟘 : app 𝟘 ≡ x
    app𝟙 : app 𝟙 ≡ y

-- Every function preserves bridges.
ap-bridge
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) {x y : A}
  → Bridge A x y → Bridge B (f x) (f y)
ap-bridge f (bridge app app𝟘 app𝟙) = bridge (f ⊙ app) (ap f app𝟘) (ap f app𝟙)

postulate
  -- Jem Lord's parametricity axiom states that every type A : U is U-null,
  -- i.e. that every function U → A is constant.
  -- We postulate an immediate consequence: such functions cannot tell
  -- 𝟘 and 𝟙 apart, so any bridge in A is an equality; in other words,
  -- U-small types are bridge-discrete.
  parametricity : ∀ {A : U} {x y : A} → Bridge A x y → x ≡ y

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

module _
  {o ℓ} {C : Precategory o ℓ}
  (let module C = Precategory C)
  where

  module _ {A B : C.Ob} (f : C.Hom A B) where

    -- The two factorisations id ∘ f and f ∘ id.
    _∘id id∘_ : Factorisation C A B
    _∘id = factor A C.id f
    id∘_ = factor B f C.id

  module _
    (C-complete : is-complete u lzero C)
    (C-category : is-category C)
    {A B : C.Ob} (f : C.Hom A B)
    where

    -- In a U-complete univalent category, every type of factorisations is bridge-codiscrete.
    -- We define a bridge from id ∘ f to f ∘ id.

    factorisation-bridge : Bridge (Factorisation C A B) (id∘ f) (f ∘id)
    factorisation-bridge = bridge b b0 b1 where

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
      b0 : b 𝟘 ≡ id∘ f
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
      b1 : b 𝟙 ≡ f ∘id
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

-- Theorem 1: let C be a U-complete univalent category and D a locally
-- U-small category.
module _
  {o o' ℓ} {C : Precategory o ℓ} {D : Precategory o' u}
  (let module C = Cat.Reasoning C) (let module D = Cat.Reasoning D)
  (C-complete : is-complete u lzero C)
  (C-category : is-category C)
  where

  -- 1.a: naturality of transformations between functors C → D is free.
  -- (This is a special case of 1.b.)
  module _
    (F G : Functor C D)
    (let module F = Cat.Functor.Reasoning F) (let module G = Cat.Functor.Reasoning G)
    (η : ∀ x → D.Hom (F.₀ x) (G.₀ x))
    where

    natural : is-natural-transformation F G η
    natural A B f = G.introl refl ∙ z0≡z1 ∙ (D.refl⟩∘⟨ F.elimr refl) where

      -- Given a factorisation A → X → B, we define the map
      --       F A
      --        ↓
      -- η X : F X → G X
      --              ↓
      --             G B
      -- which recovers the naturality square for f as the factorisation varies
      -- from id ∘ f to f ∘ id.
      z : Factorisation C A B → D.Hom (F.₀ A) (G.₀ B)
      z (factor X l r) = G.₁ r D.∘ η X D.∘ F.₁ l

      -- As a result, we get a bridge from one side of the naturality square
      -- to the other; since D is locally U-small, the Hom-sets of D are bridge-discrete,
      -- so we get the desired equality.
      z0≡z1 : z (id∘ f) ≡ z (f ∘id)
      z0≡z1 = parametricity (ap-bridge z (factorisation-bridge C-complete C-category f))

  -- 1.b: dinaturality of transformations between bifunctors C^op × C → D is free.
  module _
    (F G : Bifunctor (C ^op) C D)
    (let module F = Bifunctor F) (let module G = Bifunctor G)
    (η : ∀ x → D.Hom (F.F₀ x x) (G.F₀ x x))
    where

    dinatural
      : ∀ A B (f : C.Hom A B)
      → (f G.◆ C.id) D.∘ η B D.∘ (C.id F.◆ f)
      ≡ (C.id G.◆ f) D.∘ η A D.∘ (f F.◆ C.id)
    dinatural A B f = z0≡z1 where

      -- Given a factorisation A → X → B, we define the map
      --   F B A → F X X → G X X → G A B
      -- which interpolates between the two sides of the dinaturality hexagon.
      z : Factorisation C A B → D.Hom (F.F₀ B A) (G.F₀ A B)
      z (factor X l r) = (l G.◆ r) D.∘ η X D.∘ (r F.◆ l)

      z0≡z1 : z (id∘ f) ≡ z (f ∘id)
      z0≡z1 = parametricity (ap-bridge z (factorisation-bridge C-complete C-category f))

-- Unfolding the ideas above, we get a short proof that any function with
-- the type (A : U) → A → A is the identity.
module _ (f : (A : U) → A → A) (A : U) (a : A) where
  f≡id : f A a ≡ a
  f≡id = parametricity record where
    -- A bridge from A to ⊤: the wide pullback of P-many copies of the map
    -- a : ⊤ → A.
    T : U → U
    T P = Σ[ x ∈ A ] (P → x ≡ a)

    T𝟘≃A : T 𝟘 ≃ A
    T𝟘≃A = Σ-contr-snd λ _ → Π-dom-empty-is-contr λ ()

    -- A dependent bridge from a to tt over T.
    t : (P : U) → T P
    t P = a , λ _ → refl

    -- A bridge from f A a to a.
    app : U → A
    app P = f (T P) (t P) .fst
    app𝟘  = ua-pathp→path T𝟘≃A (ap₂ f (ua T𝟘≃A) (path→ua-pathp T𝟘≃A refl))
    app𝟙  = f (T 𝟙) (t 𝟙) .snd _

id-is-unique : is-contr ((A : U) → A → A)
id-is-unique = contr (λ _ a → a) λ f → sym (ext (f≡id f))
```
