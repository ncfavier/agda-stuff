<details>
<summary>Imports</summary>

```agda
open import Cat.Prelude
open import Cat.Strict
open import Cat.Instances.StrictCat
open import Cat.Skeletal
open import Cat.Gaunt
open import Cat.Functor.Properties
open import Cat.Functor.Equivalence
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Naturality
open import Cat.Groupoid
open import Cat.Univalent.Rezk
open import Cat.Univalent.Rezk.HIT hiding (C^-elim-set)
open import Cat.Instances.Discrete

open import 1Lab.Classical
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
</details>

# sets cover

We say that sets cover (types) if every type merely admits a surjection
from a set.

```agda
sets-cover : Typeω
sets-cover = ∀ {ℓ} (A : Type ℓ) → ∃[ X ∈ Set ℓ ] ∣ X ∣ ↠ A
```

## categories

If sets cover types, then strict categories cover categories in the sense
that every (pre)category is weakly equivalent to <small>(admits a fully faithful,
essentially surjective on objects functor from)</small> a strict one.

Given a category $C$ and a map $f : X \to C$ where $X$ is a set, we
think of $f$ as a functor from a discrete category and take its
[(bijective on objects, fully faithful) factorisation](https://ncatlab.org/nlab/show/%28bo%2C+ff%29+factorization+system):
when $f$ is surjective, the fully faithful part is also essentially surjective
on objects, so it is a weak equivalence from a strict category.

```agda
module _
  {o ℓ} (C : Precategory o ℓ)
  ((X , f) : Σ[ X ∈ Set o ] (∣ X ∣ → ⌞ C ⌟))
  where
  open Precategory C

  full-image : Precategory o ℓ
  full-image = record
    { Ob = ⌞ X ⌟
    ; Hom = λ x y → Hom (f x) (f y)
    ; Hom-set = λ x y → Hom-set (f x) (f y)
    ; id = id ; _∘_ = _∘_ ; idr = idr ; idl = idl ; assoc = assoc }

  forget : Functor full-image C
  forget .F₀ = f
  forget .F₁ x = x
  forget .F-id = refl
  forget .F-∘ _ _ = refl

module _
  (sc : sets-cover)
  {o ℓ} (C : Precategory o ℓ)
  where

  sets-cover→strict-cats-cover
    : ∃[ C' ∈ Precategory o ℓ ]
      is-strict C'
    × Σ[ F ∈ Functor C' C ]
      is-fully-faithful F × is-eso F
  sets-cover→strict-cats-cover = do
    X , f , f-surj ← sc ⌞ C ⌟
    let
      C' = full-image C (X , f)
      F = forget C (X , f)
      F-eso : is-eso F
      F-eso c = f-surj c <&> λ (x , p) → x , path→iso p
    pure (C' , hlevel 2 , F , (λ {x y} → id-equiv) , F-eso)
```

Note that we cannot strengthen this to an equivalence in general:
if $F : C \cong C'$ is an equivalence of precategories where $C$ is
univalent and $C'$ is strict, then $C$ is also strict.
If $C'$ is furthermore skeletal, then $F$ is an isomorphism of
precategories (thus $C$ and $C'$ are both gaunt).

```agda
module _
  {oc ℓc oc' ℓd'}
  (C : Precategory oc ℓc) (C' : Precategory oc' ℓd')
  (F : Functor C C') (F-eqv : is-equivalence F)
  (C-cat : is-category C)
  where

  open is-equivalence F-eqv
  private
    module C-cat = Univalent C-cat

  univalent≅strict→strict : is-strict C' → is-strict C
  univalent≅strict→strict = retract→is-hlevel 2 (F⁻¹ .F₀) (F .F₀)
    λ c → sym $ C-cat.iso→path (isoⁿ→iso Id≅F⁻¹∘F c)

  univalent≅skeletal→iso : is-skeletal C' → is-precat-iso F
  univalent≅skeletal→iso C'-skeletal .has-is-ff = is-equivalence→is-ff F F-eqv
  univalent≅skeletal→iso C'-skeletal .has-is-iso = is-iso→is-equiv λ where
    .is-iso.from → F⁻¹ .F₀
    .is-iso.rinv c' → C'-skeletal.to-path (inc (isoⁿ→iso F∘F⁻¹≅Id c'))
    .is-iso.linv c → sym $ C-cat.iso→path (isoⁿ→iso Id≅F⁻¹∘F c)
      where module C'-skeletal = is-identity-system C'-skeletal
```

## choice

If every set is projective ($\mathrm{AC}_\infty$), then every type is
covered by its set truncation.

```agda
is-projective : ∀ {ℓ} (A : Type ℓ) → (κ : Level) → Type _
is-projective A κ =
  ∀ (P : A → Type κ)
  → (∀ a → ∥ P a ∥)
  → ∥ (∀ a → P a) ∥

AC∞ = ∀ {ℓ} (A : Set ℓ) κ → is-projective ∣ A ∣ κ

AC∞→sets-cover
  : AC∞
  → ∀ {ℓ} (A : Type ℓ)
  → Σ[ X ∈ Set ℓ ] ∥ ∣ X ∣ ↠ A ∥
AC∞→sets-cover ac∞ A = el! ∥ A ∥₀ , do
  split ← ac∞ (el! ∥ A ∥₀) _ (fibre inc) (elim! λ a → inc (a , refl))
  pure $ fst ⊙ split , λ a → do
    p ← ∥-∥₀-path.to (split (inc a) .snd)
    inc (inc a , p)
```

In the other direction, if choice holds and sets cover, then
$\mathrm{AC}_\infty$ holds. We show that all surjections into a set
split: given a surjection $B \twoheadrightarrow A$ and assuming $X$
covers $B$, we get a composite surjection $X \twoheadrightarrow A$ where
$X$ and $A$ are both sets, hence a split surjection; this implies that
our original surjection splits.

```agda
surjections-split→AC∞
  : (∀ {ℓ κ} (A : Set ℓ) (B : Type κ) (f : B → ∣ A ∣)
    → is-surjective f
    → is-split-surjective f)
  → AC∞
surjections-split→AC∞ split A κ P h = do
  s ← split A (Σ _ P) fst λ a → h a <&> Equiv.from (Fibre-equiv P a)
  pure λ a → Equiv.to (Fibre-equiv P a) (s a)

AC+sets-cover→AC∞ : Axiom-of-choice → sets-cover → AC∞
AC+sets-cover→AC∞ ac sc = surjections-split→AC∞ λ A B f f-surj → do
  X , g , g-surj ← sc B
  s ← ac (hlevel 2) (λ _ → hlevel 2) (∘-is-surjective f-surj g-surj)
  pure λ a → let (x , p) = s a in g x , p
```

If sets cover, then every projective type is a set, by closure under
retracts.

```agda
module _
  (sc : sets-cover)
  where

  projective→is-set : ∀ {ℓ} (A : Type ℓ) → is-projective A ℓ → is-set A
  projective→is-set A A-proj = ∥-∥-out! do
    X , f , f-surj ← sc A
    s ← A-proj (fibre f) f-surj
    pure (retract→is-hlevel 2 f (fst ⊙ s) (snd ⊙ s) (hlevel 2))
```

## truncation

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
  (sc
    : ∀ {ℓ} (A : Type ℓ)
    → Σ[ X ∈ Set ℓ ] ∣ X ∣ ↠ A)
  where

  _↓ : ∀ {ℓ} → n-Type ℓ 3 → Precategory ℓ ℓ
  G ↓ using X , f , f-surj ← sc ∣ G ∣
    = full-image (Disc ∣ G ∣ (hlevel 3)) (X , f)

  strictify : ∀ {ℓ} → n-Type ℓ 3 → StrictGrpd ℓ
  strictify G .fst = G ↓
  strictify G .snd .fst = hlevel 2
  strictify G .snd .snd p = make-invertible (sym p) (∙-invl _) (∙-invr _)
    where open Cat.Reasoning (G ↓)

  rezk : ∀ {ℓ} → StrictGrpd ℓ → n-Type ℓ 3
  rezk (G , G-grpd , G-strict) = el (C^ G) squash

  rezk-strictify : ∀ {ℓ} (G : n-Type ℓ 3) → rezk (strictify G) ≡ G
  rezk-strictify G using X , f , f-surj ← sc ∣ G ∣
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
