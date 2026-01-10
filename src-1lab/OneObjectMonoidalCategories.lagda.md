```agda
module OneObjectMonoidalCategories where
```

<details>
<summary>Imports and misc. definitions.</summary>

```agda
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Functor.Naturality.Reflection
open import Cat.Instances.Shape.Terminal
open import Cat.Instances.Delooping
open import Cat.Functor.Naturality
open import Cat.Monoidal.Functor
open import Cat.Monoidal.Base
open import Cat.Prelude hiding (_*_)

import Cat.Reasoning as Cat

open Lax-monoidal-functor-on
open Monoidal-category
open Functor
open is-iso
open _=>_

⊤ᵐ : Monoidal-category ⊤Cat
⊤ᵐ .-⊗- = !F
⊤ᵐ .Unit = _
⊤ᵐ .unitor-l = trivial-isoⁿ!
⊤ᵐ .unitor-r = trivial-isoⁿ!
⊤ᵐ .associator = trivial-isoⁿ!
⊤ᵐ .triangle = refl
⊤ᵐ .pentagon = refl
```
</details>

Given an abelian group $G$, there is a unique strict monoidal category
structure on the delooping $\mathbf{B}G$.

```agda
module _ {ℓ} (G : Abelian-group ℓ) where
  open Abelian-group-on (G .snd)
  private BG = B (underlying-monoid .snd)

  BGᵐ : Monoidal-category BG
  BGᵐ .-⊗- .F₀ = _
  BGᵐ .-⊗- .F₁ = uncurry _*_
  BGᵐ .-⊗- .F-id = idl
  BGᵐ .-⊗- .F-∘ (a , b) (c , d) = extendr (extendl commutes)
  BGᵐ .Unit = _
  BGᵐ .unitor-l = iso→isoⁿ (λ _ → Cat.id-iso _) (λ _ → idr)
  BGᵐ .unitor-r = iso→isoⁿ (λ _ → Cat.id-iso _) (λ _ → idr ∙∙ idr ∙∙ sym idl)
  BGᵐ .associator = iso→isoⁿ (λ _ → Cat.id-iso _) (λ _ → idr ∙ associative ∙ sym idl)
  BGᵐ .triangle = idr
  BGᵐ .pentagon = elimr (elimr idl)
```

Monoidal functors $\top \to \mathbf{B}G$ are in bijection with elements
of $G$ [@cheng:gurski, theorem 3.1].

```agda
  !Constᵐ≃G : Lax-monoidal-functor-on ⊤ᵐ BGᵐ (!Const _) ≃ ⌞ G ⌟
  !Constᵐ≃G .fst Fᵐ = Fᵐ .ε
  !Constᵐ≃G .snd = is-iso→is-equiv λ where
    .from g .ε → g
    .from g .F-mult .η _ → g ⁻¹
    .from g .F-mult .is-natural _ _ _ → elimr idl ∙ sym idl
    .from g .F-α→ → extendl id-comm-sym ∙ ap (g ⁻¹ *_) associative
    .from g .F-λ← → idl ∙ cancell inversel
    .from g .F-ρ← → idl ∙ ap (g ⁻¹ *_) idl ∙ inversel
    .rinv g → refl
    .linv Fᵐ → Lax-monoidal-functor-on-path _ _ refl $ ext λ _ →
      sym $ zero-diff $ ap (_ *_) (inv-inv ∙ sym idr) ∙ sym idl ∙ Fᵐ .F-λ←
```

-------------------
<div id=refs></div>
