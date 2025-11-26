```agda
open import Cat.Prelude
open import Cat.Strict
open import Cat.Instances.StrictCat
open import Cat.Skeletal
open import Cat.Gaunt
open import Cat.Functor.Equivalence
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Naturality
open import Cat.Groupoid
open import Cat.Univalent.Rezk
open import Cat.Univalent.Rezk.HIT hiding (C^-elim-set)

open import 1Lab.Path.Reasoning
open import 1Lab.Function.Surjection
open import 1Lab.Reflection.Induction

import Cat.Morphism
import Cat.Reasoning

open is-precat-iso
open is-gaunt
open Functor

module SetsCover where

private
  unquoteDecl C^-rec = make-rec-n 3 C^-rec (quote C^)
  unquoteDecl C^-elim-set = make-elim-n 2 C^-elim-set (quote C^)
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
  private
    module C-cat = Univalent C-cat

  univalent≅strict→strict : is-strict D → is-strict C
  univalent≅strict→strict = retract→is-hlevel 2 (F⁻¹ .F₀) (F .F₀)
    λ c → sym $ C-cat.iso→path (isoⁿ→iso Id≅F⁻¹∘F c)

  univalent≅skeletal→iso : is-skeletal D → is-precat-iso F
  univalent≅skeletal→iso D-skeletal .has-is-ff = is-equivalence→is-ff F F-eqv
  univalent≅skeletal→iso D-skeletal .has-is-iso = is-iso→is-equiv λ where
    .is-iso.from → F⁻¹ .F₀
    .is-iso.rinv d → D-skeletal.to-path (inc (isoⁿ→iso F∘F⁻¹≅Id d))
    .is-iso.linv c → sym $ C-cat.iso→path (isoⁿ→iso Id≅F⁻¹∘F c)
      where module D-skeletal = is-identity-system D-skeletal
```

$\mathrm{AC}_\infty$ implies that sets cover, in the strong sense that
every type is *equipped* with a set and a mere surjection.

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

On the other hand, the fully untruncated version is inconsistent: it
implies that the type of groupoids is a retract of the type of strict
pregroupoids, hence a groupoid itself, which is
[known to be false](https://doi.org/10.48550/arXiv.1311.4002).

```agda
StrictGrpd : ∀ ℓ → Type (lsuc ℓ)
StrictGrpd ℓ = Σ[ C ∈ Precategory ℓ ℓ ] (is-strict C × is-pregroupoid C)

StrictGrpd-is-groupoid : ∀ {ℓ} → is-groupoid (StrictGrpd ℓ)
StrictGrpd-is-groupoid = Equiv→is-hlevel 3 Σ-assoc
  (Σ-is-hlevel 3 Strict-cat-is-groupoid λ _ → hlevel 3)

module _
  (sets-cover!
    : ∀ {ℓ} (A : Type ℓ)
    → Σ[ X ∈ Set ℓ ] ∣ X ∣ ↠ A)
  where

  _↓ : ∀ {ℓ} → n-Type ℓ 3 → Precategory ℓ ℓ
  G ↓ using X , f , f-surj ← sets-cover! ∣ G ∣
    = record
      { Ob = ∣ X ∣
      ; Hom = λ x y → f x ≡ f y
      ; Hom-set = λ x y → hlevel 2
      ; id = refl
      ; _∘_ = flip _∙_
      ; idr = λ f → ∙-idl _
      ; idl = λ f → ∙-idr _
      ; assoc = λ f g h → sym $ ∙-assoc _ _ _
      }

  strictify : ∀ {ℓ} → n-Type ℓ 3 → StrictGrpd ℓ
  strictify G .fst = G ↓
  strictify G .snd .fst = hlevel 2
  strictify G .snd .snd p = make-invertible (sym p) (∙-invl _) (∙-invr _)
    where open Cat.Reasoning (G ↓)

  rezk : ∀ {ℓ} → StrictGrpd ℓ → n-Type ℓ 3
  rezk (G , G-grpd , G-strict) = el (C^ G) squash

  rezk-strictify : ∀ {ℓ} (G : n-Type ℓ 3) → rezk (strictify G) ≡ G
  rezk-strictify G using X , f , f-surj ← sets-cover! ∣ G ∣
    = n-ua (compare , compare-is-equiv)
    where
      open Cat.Reasoning (G ↓)
      open is-pregroupoid (strictify G .snd .snd)

      commutes→glueᵀ
        : ∀ {x y z} {p : x ≅ y} {q : x ≅ z} {r : y ≅ z}
        → to q ≡ to p ∙ to r
        → Triangle (glue p) (glue q) (glue r)
      commutes→glueᵀ {p = p} {q} {r} t = glueᵀ p r ▷ ap C^.glue (ext (sym t))

      compare : C^ (G ↓) → ∣ G ∣
      compare = C^-rec (hlevel 3) f to λ _ _ → ∙-filler _ _

      compare-is-equiv : is-equiv compare
      compare-is-equiv .is-eqv g = ∥-∥-out! do
        (x , p) ← f-surj g
        pure $ contr (inc x , p) $ uncurry $ C^-elim-set
          (λ _ → Π-is-hlevel 2 λ _ → fibre-is-hlevel 3 squash (hlevel 3) compare g _ _)
          (λ y q → glue (hom→iso (p ∙ sym q)) ,ₚ flip₂ (∙-filler'' p (sym q)))
          λ q → funext-dep-i0 λ r →
            Σ-set-square (λ _ → hlevel 2) $ commutes→glueᵀ $
              p ∙ sym ⌜ transport (λ z → to q z ≡ g) r ⌝ ≡⟨ ap! (subst-path-left r (to q)) ⟩
              p ∙ sym (sym (to q) ∙ r)                   ≡⟨ ap (p ∙_) (sym-∙ _ _) ⟩
              p ∙ sym r ∙ to q                           ≡⟨ ∙-assoc _ _ _ ⟩
              (p ∙ sym r) ∙ to q                         ∎

  groupoid-of-groupoids : ∀ {ℓ} → is-groupoid (n-Type ℓ 3)
  groupoid-of-groupoids = retract→is-hlevel 3 rezk strictify rezk-strictify
    StrictGrpd-is-groupoid
```
