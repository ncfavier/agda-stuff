```agda
{-# OPTIONS --erasure #-}
open import 1Lab.Prelude hiding (map)
open import 1Lab.Reflection.Induction
```

# erasure as an open modality

We show that Agda's erasure modality is an open modality and investigate some consequences.
Terminology is borrowed and some proofs are extracted from the paper
[Modalities in homotopy type theory](https://arxiv.org/abs/1706.07526)
by Rijke, Shulman and Spitters.
The erasure modality was previously investigated in
[Logical properties of a modality for erasure](https://www.cse.chalmers.se/~nad/publications/danielsson-erased.pdf)
by Danielsson.

```agda
module ErasureOpen where

private variable
  ℓ ℓ' : Level
  A B : Type ℓ
```

The `Erased` monadic modality, internalising the `@0` annotation:

```agda
record Erased (@0 A : Type ℓ) : Type ℓ where
  constructor [_]
  field
    @0 erased : A

open Erased

η : {@0 A : Type ℓ} → A → Erased A
η x = [ x ]

μ : {@0 A : Type ℓ} → Erased (Erased A) → Erased A
μ [ [ x ] ] = [ x ]
```

...is equivalent to the **open modality** `○` induced by the following proposition:

```agda
data Compiling : Type where
  @0 compiling : Compiling

Compiling-is-prop : is-prop Compiling
Compiling-is-prop compiling compiling = refl

○_ : Type ℓ → Type ℓ
○ A = Compiling → A

○'_ : ○ Type ℓ → Type ℓ
○' A = (c : Compiling) → A c

infix 30 ○_ ○'_

○→Erased : ○ A → Erased A
○→Erased a .erased = a compiling

-- Agda considers clauses that match on erased constructors as erased.
Erased→○ : Erased A → ○ A
Erased→○ a compiling = a .erased

○≃Erased : ○ A ≃ Erased A
○≃Erased = Iso→Equiv (○→Erased ,
  iso Erased→○ (λ _ → refl) (λ _ → funext λ where compiling → refl))

η○ : A → ○ A
η○ a _ = a
```

Since Agda allows erased matches for the empty type, the empty type is
modal; in other words, we are not not `Compiling`.

```agda
¬¬compiling : ¬ ¬ Compiling
¬¬compiling ¬c with ○→Erased ¬c
... | ()
```

## open and closed modalities

The corresponding **closed** modality `●` is given by the join with `Compiling`,
which is equivalent to the following higher inductive type.

```agda
data ●_ (A : Type ℓ) : Type ℓ where
  -- At runtime, we only have A.
  η● : A → ● A
  -- At compile time, we also have an erased "cone" that glues all of A together,
  -- so that ● A is contractible.
  @0 tip : ● A
  @0 cone : (a : A) → η● a ≡ tip

infix 30 ●_

unquoteDecl ●-elim = make-elim ●-elim (quote ●_)

@0 ●-contr : is-contr (● A)
●-contr {A = A} = contr tip λ a → sym (ps a) where
  ps : (a : ● A) → a ≡ tip
  ps = ●-elim cone refl λ a i j → cone a (i ∨ j)
```

The rest of this file investigates some general properties of open and closed
modalities, instantiated for `Compiling`.

<details>
<summary>Some common definitions about higher modalities</summary>

```agda
module Modality
  {○_ : ∀ {ℓ} → Type ℓ → Type ℓ}
  (η○ : ∀ {ℓ} {A : Type ℓ} → A → ○ A)
  (○-elim : ∀ {ℓ ℓ'} {A : Type ℓ} {P : ○ A → Type ℓ'}
          → ((a : A) → ○ P (η○ a)) → (a : ○ A) → ○ P a)
  (○-elim-β : ∀ {ℓ ℓ'} {A : Type ℓ} {P : ○ A → Type ℓ'} {pη : (a : A) → ○ P (η○ a)}
            → (a : A) → ○-elim {P = P} pη (η○ a) ≡ pη a)
  (○-≡-modal : ∀ {ℓ} {A : Type ℓ} {x y : ○ A} → is-equiv (η○ {A = x ≡ y}))
  where

  modal : Type ℓ → Type ℓ
  modal A = is-equiv (η○ {A = A})

  modal-map : (A → B) → Type _
  modal-map {B = B} f = (b : B) → modal (fibre f b)

  connected : Type ℓ → Type ℓ
  connected A = is-contr (○ A)

  connected-map : (A → B) → Type _
  connected-map {B = B} f = (b : B) → connected (fibre f b)

  modal+connected→contr : modal A → connected A → is-contr A
  modal+connected→contr A-mod A-conn = Equiv→is-hlevel 0 (η○ , A-mod) A-conn

  modal+connected→equiv : {f : A → B} → modal-map f → connected-map f → is-equiv f
  modal+connected→equiv f-mod f-conn .is-eqv b = modal+connected→contr (f-mod b) (f-conn b)

  elim-modal
    : ∀ {ℓ ℓ'} {A : Type ℓ} {P : ○ A → Type ℓ'}
    → (∀ a → modal (P a))
    → ((a : A) → P (η○ a)) → (a : ○ A) → P a
  elim-modal P-modal pη a = equiv→inverse (P-modal a) (○-elim (λ a → η○ (pη a)) a)

  elim-modal-β
    : ∀ {ℓ ℓ'} {A : Type ℓ} {P : ○ A → Type ℓ'} P-modal {pη : (a : A) → P (η○ a)}
    → (a : A) → elim-modal {P = P} P-modal pη (η○ a) ≡ pη a
  elim-modal-β P-modal {pη} a =
    ap (equiv→inverse (P-modal (η○ a))) (○-elim-β a)
    ∙ equiv→unit (P-modal (η○ a)) (pη a)

  map : (A → B) → ○ A → ○ B
  map f = ○-elim (η○ ∘ f)

  map-≃ : A ≃ B → (○ A) ≃ (○ B)
  map-≃ e = map (e .fst) , is-iso→is-equiv λ where
    .is-iso.from → map (Equiv.from e)
    .is-iso.rinv → elim-modal (λ _ → ○-≡-modal) λ b →
      ap (map (e .fst)) (○-elim-β b) ∙ ○-elim-β (Equiv.from e b) ∙ ap η○ (Equiv.ε e b)
    .is-iso.linv → elim-modal (λ _ → ○-≡-modal) λ a →
      ap (map (Equiv.from e)) (○-elim-β a) ∙ ○-elim-β (e .fst a) ∙ ap η○ (Equiv.η e a)

  retract-○→modal : (η⁻¹ : ○ A → A) → is-left-inverse η⁻¹ η○ → modal A
  retract-○→modal η⁻¹ ret = is-iso→is-equiv $
    iso η⁻¹ (elim-modal (λ _ → ○-≡-modal) λ a → ap η○ (ret a)) ret

  retract→modal
    : (f : A → B) (g : B → A)
    → is-left-inverse f g → modal A → modal B
  retract→modal {B = B} f g ret A-modal = retract-○→modal η⁻¹ linv where
    η⁻¹ : ○ B → B
    η⁻¹ = f ∘ elim-modal (λ _ → A-modal) g
    linv : is-left-inverse η⁻¹ η○
    linv b = ap f (elim-modal-β (λ _ → A-modal) b) ∙ ret b

  modal-≃ : B ≃ A → modal A → modal B
  modal-≃ e = retract→modal (Equiv.from e) (Equiv.to e) (Equiv.η e)

  connected-≃ : B ≃ A → connected A → connected B
  connected-≃ e A-conn = Equiv→is-hlevel 0 (map-≃ e) A-conn

  ≡-modal : modal A → ∀ {x y : A} → modal (x ≡ y)
  ≡-modal A-modal = modal-≃ (ap-equiv (η○ , A-modal)) ○-≡-modal

  PathP-modal : {A : I → Type ℓ} → modal (A i0) → ∀ {x y} → modal (PathP A x y)
  PathP-modal {A = A} A-modal {x} {y} = subst modal (sym (PathP≡Path⁻ A x y)) (≡-modal A-modal)

  reflection-modal : modal (○ A)
  reflection-modal = is-iso→is-equiv λ where
    .is-iso.from → ○-elim id
    .is-iso.rinv → elim-modal (λ _ → ○-≡-modal) λ a → ap η○ (○-elim-β a)
    .is-iso.linv → ○-elim-β

  Π-modal : {B : A → Type ℓ} → (∀ a → modal (B a)) → modal ((a : A) → B a)
  Π-modal B-modal = retract-○→modal
    (λ f a → elim-modal (λ _ → B-modal _) (_$ a) f)
    (λ f → funext λ a → elim-modal-β (λ _ → B-modal _) f)

  Σ-modal : {B : A → Type ℓ} → modal A → (∀ a → modal (B a)) → modal (Σ A B)
  Σ-modal {B = B} A-modal B-modal = retract-○→modal
    (Equiv.from Σ-Π-distrib
      ( elim-modal (λ _ → A-modal) fst
      , elim-modal (λ _ → B-modal _) λ (a , b) →
          subst B (sym (elim-modal-β (λ _ → A-modal) (a , b))) b))
    λ (a , b) →
         elim-modal-β (λ _ → A-modal) (a , b)
      ,ₚ elim-modal-β (λ _ → B-modal _) (a , b) ◁ to-pathp⁻ refl

  η-connected : connected-map (η○ {A = A})
  η-connected a = contr
    (○-elim {P = fibre η○} (λ a → η○ (a , refl)) a)
    (elim-modal (λ _ → ○-≡-modal) λ (a' , p) →
      J (λ a p → ○-elim (λ x → η○ (x , refl)) a ≡ η○ (a' , p)) (○-elim-β a') p)

  ○Σ○≃○Σ : {B : A → Type ℓ} → (○ (Σ A λ a → ○ B a)) ≃ (○ (Σ A B))
  ○Σ○≃○Σ .fst = ○-elim λ (a , b) → map (a ,_) b
  ○Σ○≃○Σ .snd = is-iso→is-equiv λ where
    .is-iso.from → map (Σ-map₂ η○)
    .is-iso.rinv → elim-modal (λ _ → ○-≡-modal) λ (a , b) →
      ap (○-elim _) (○-elim-β (a , b)) ∙ ○-elim-β (a , η○ b) ∙ ○-elim-β b
    .is-iso.linv → elim-modal (λ _ → ○-≡-modal) λ (a , b) →
      ap (map _) (○-elim-β (a , b)) ∙ elim-modal
        {P = λ b → ○-elim _ (○-elim _ b) ≡ η○ (a , b)} (λ _ → ○-≡-modal)
        (λ b → ap (○-elim _) (○-elim-β b) ∙ ○-elim-β (a , b)) b

  Σ-connected : {B : A → Type ℓ} → connected A → (∀ a → connected (B a)) → connected (Σ A B)
  Σ-connected A-conn B-conn = Equiv→is-hlevel 0 (○Σ○≃○Σ e⁻¹)
    (connected-≃ (Σ-contr-snd B-conn) A-conn)

  -- Additional properties of *lex* modalities

  module _ (○-lex : ∀ {ℓ} {A : Type ℓ} {a b : A} → (○ (a ≡ b)) ≃ (η○ a ≡ η○ b)) where
    ≡-connected : connected A → {x y : A} → connected (x ≡ y)
    ≡-connected A-conn = Equiv→is-hlevel 0 ○-lex (Path-is-hlevel 0 A-conn)

    PathP-connected : {A : I → Type ℓ} → connected (A i0) → ∀ {x y} → connected (PathP A x y)
    PathP-connected {A = A} A-conn {x} {y} =
      subst connected (sym (PathP≡Path⁻ A x y)) (≡-connected A-conn)
```
</details>

`○` and `●` are higher modalities, so we can instantiate this module
for both of them.

```agda
○-elim-○
  : ∀ {ℓ ℓ'} {A : Type ℓ} {P : ○ A → Type ℓ'}
  → ((a : A) → ○ P (η○ a)) → (a : ○ A) → ○ P a
○-elim-○ {P = P} pη a c =
  subst P (funext λ _ → ap a (Compiling-is-prop _ _)) (pη (a c) c)

○-≡-modal : {x y : ○ A} → is-equiv (η○ {A = x ≡ y})
○-≡-modal = is-iso→is-equiv λ where
  .is-iso.from p i compiling → p compiling i compiling
  .is-iso.rinv p i compiling j compiling → p compiling j compiling
  .is-iso.linv p i j compiling → p j compiling

●-elim-●
  : ∀ {ℓ ℓ'} {A : Type ℓ} {P : ● A → Type ℓ'}
  → ((a : A) → ● P (η● a)) → (a : ● A) → ● P a
●-elim-● pη = ●-elim pη tip λ _ → is-contr→pathp (λ _ → ●-contr) _ _

●-≡-modal : {x y : ● A} → is-equiv (η● {A = x ≡ y})
●-≡-modal = is-iso→is-equiv λ where
  .is-iso.from → ●-elim id (is-contr→is-prop ●-contr _ _)
    λ p → is-contr→is-set ●-contr _ _ _ _
  .is-iso.rinv → ●-elim (λ _ → refl) (sym (●-contr .paths _))
    λ p → is-set→squarep (λ _ _ → is-contr→is-set ●-contr) _ _ _ _
  .is-iso.linv _ → refl

module ○ = Modality η○ ○-elim-○ (λ _ → funext λ _ → transport-refl _) ○-≡-modal
module ● = Modality η● ●-elim-● (λ _ → refl) ●-≡-modal
```

Open and closed modalities are lex.

```agda
○-lex : {a b : A} → ○ (a ≡ b) ≃ (η○ a ≡ η○ b)
○-lex = funext≃

module ●-ids {A : Type ℓ} {a : A} where
  code : ● A → Type ℓ
  code = ●-elim (λ b → ● (a ≡ b)) (Lift _ ⊤) (λ b → ua (is-contr→≃ ●-contr (hlevel 0)))

  code-refl : code (η● a)
  code-refl = η● refl

  decode : ∀ b → code b → η● a ≡ b
  decode = ●.elim-modal (λ _ → ●.Π-modal λ _ → ●-≡-modal)
    λ a → ●.elim-modal (λ _ → ●-≡-modal) (ap η●)

  decode-over : ∀ b (c : code b) → PathP (λ i → code (decode b c i)) code-refl c
  decode-over = ●.elim-modal (λ _ → ●.Π-modal λ _ → ●.PathP-modal ●.reflection-modal)
    λ a → ●.elim-modal (λ _ → ●.PathP-modal ●.reflection-modal)
      λ p i → η● λ j → p (i ∧ j)

  ids : is-based-identity-system (η● a) code code-refl
  ids .to-path {b} = decode b
  ids .to-path-over {b} = decode-over b

●-lex : {a b : A} → ● (a ≡ b) ≃ (η● a ≡ η● b)
●-lex = based-identity-system-gives-path ●-ids.ids
```

Some equivalences specific to open and closed modalities:

<div style="text-align: center;">
`●-modal A ≃ ○ (is-contr A) ≃ is-contr (○ A) = ○-connected A`
</div>

```agda
@0 ●-modal→contr : ●.modal A → is-contr A
●-modal→contr A-modal = Equiv→is-hlevel 0 (η● , A-modal) ●-contr

contr→●-modal : @0 is-contr A → ●.modal A
contr→●-modal A-contr = ●.retract-○→modal
  (●-elim id (A-contr .centre) λ a → sym (A-contr .paths a))
  λ _ → refl

contr→○-connected : @0 is-contr A → ○.connected A
contr→○-connected A-contr = contr (Erased→○ [ A-contr .centre ]) λ a →
  funext λ where compiling → A-contr .paths _

@0 ○-connected→contr : ○.connected A → is-contr A
○-connected→contr A-conn = contr (A-conn .centre compiling) λ a →
  A-conn .paths (η○ a) $ₚ compiling

○-connected→●-modal : ○.connected A → ●.modal A
○-connected→●-modal A-conn = contr→●-modal (○-connected→contr A-conn)
```

## Artin gluing

We prove an **Artin gluing** theorem: every type `A` is equivalent to a
certain pullback of `○ A` and `● A` over `● ○ A`, which we call `Fracture A`.
Handwaving, this corresponds to decomposing a type into its "compile time"
part and its "runtime" part.

```agda
○→●○ : ○ A → ● ○ A
○→●○ = η●

●→●○ : ● A → ● ○ A
●→●○ = ●.map η○

Fracture : Type ℓ → Type ℓ
Fracture A = Σ (○ A × ● A) λ (o , c) → ○→●○ o ≡ ●→●○ c

module _ {A : Type ℓ} where
  fracture : A → Fracture A
  fracture a = (η○ a , η● a) , refl
```

The idea is to prove that the fibres of the `fracture` map are both
`●`-modal and `●`-connected, and hence contractible.

For the modal part, we observe that an element of the fibre of `fracture`
at a triple `(o : ○ A, c : ● A, p : ○→●○ o ≡ ●→●○ c)` can be rearranged into an element
of the fibre of `η○` at `o` (which is `○`-connected, hence `●`-modal) together with
a dependent path whose type is `●`-modal by standard results about higher modalities.

```agda
  fracture-modal : ●.modal-map fracture
  fracture-modal ((o , c) , p) = ●.modal-≃ e $
    ●.Σ-modal (○-connected→●-modal (○.η-connected _)) λ _ →
      ●.PathP-modal $ ●.Σ-modal ●.reflection-modal λ _ → ●-≡-modal
    where
      e : fibre fracture ((o , c) , p)
        ≃ Σ (fibre η○ o) λ (a , q) →
          PathP (λ i → Σ (● A) λ c → ○→●○ (q i) ≡ ●→●○ c) (η● a , refl) (c , p)
      e = Σ-ap-snd (λ _ → ap-equiv (Σ-assoc e⁻¹) ∙e Σ-pathp≃ e⁻¹) ∙e Σ-assoc
```

Almost symmetrically, for the connected part, we rearrange the fibre
into an element of the fibre of `η●` at `c` (which is `●`-connected) together
with a dependent path in the fibres of `○→●○`. Since the latter is
defined as `η●` its fibres are `●`-connected as well, hence the path type
is `●`-connected because `●` is lex.

```agda
  fracture-connected : ●.connected-map fracture
  fracture-connected ((o , c) , p) = ●.connected-≃ e $
    ●.Σ-connected (●.η-connected _) λ _ →
      ●.PathP-connected ●-lex (●.η-connected _)
    where
      e : fibre fracture ((o , c) , p)
        ≃ Σ (fibre η● c) λ (a , q) →
          PathP (λ i → Σ (○ A) λ o → ○→●○ o ≡ ●→●○ (q i)) (η○ a , refl) (o , p)
      e = Σ-ap-snd (λ _ → ap-equiv (Σ-ap-fst ×-swap ∙e Σ-assoc e⁻¹) ∙e Σ-pathp≃ e⁻¹) ∙e Σ-assoc

  fracture-is-equiv : is-equiv fracture
  fracture-is-equiv = ●.modal+connected→equiv fracture-modal fracture-connected

  Artin-gluing : A ≃ Fracture A
  Artin-gluing = fracture , fracture-is-equiv
```
