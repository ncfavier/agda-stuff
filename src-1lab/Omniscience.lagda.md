```agda
open import 1Lab.Prelude
open import Data.Bool
open import Data.Dec
open import Data.Fin hiding (_≤_; _<_)
open import Data.Nat
open import Meta.Invariant

module Omniscience where
```

# LPO ↔ IPP

This module shows that the limited principle of omniscience (LPO) is
equivalent to the infinite pigeonhole principle (IPP). The proof is not
difficult, and the idea can be found in [TypeTopology](https://martinescardo.github.io/pigeon/html/InfinitePigeon.html)
or in "[Constructive Reverse Mathematics](https://arxiv.org/abs/1804.05495)" (§ 1.2.1).
However, the two sources cited are not very frugal in their assumptions:
the former works in a continuation monad (thus essentially has access to
full excluded middle, as well as some form of choice), while the latter
seems to require countable or dependent choice. We show that the equivalence
follows from just unique choice, which is assumed implicitly by working in HoTT.

The ambient assumption of unique choice "collapses" the arithmetical hierarchy,
in the sense that from LPO (excluded middle for $Σ_1$ formulas) we are able to
decide e.g. whether $f : ℕ → \mathbb{2}$ has infinitely many ones, which is
a $Π_2$ statement, by using LPO in a nested manner. For more on this, see
"[Not choosing is still a choice](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2026.5)" (around fact 29).

```agda
-- "decidable subsets of ℕ are closed under ∃"
LPO : (ℓ : Level) → Type (lsuc ℓ)
LPO ℓ = (P : Nat → Type ℓ) ⦃ _ : ∀ {n} → H-Level (P n) 1 ⦄
      → (∀ n → Dec (P n))
      → Dec (∃[ n ∈ Nat ] P n)

_ : ∀ {ℓ} → is-prop (LPO ℓ)
_ = hlevel 1

-- "every infinite bit sequence has a constant infinite subsequence"
IPP = (f : Nat → Bool)
    → Σ[ b ∈ Bool ] Σ[ s ∈ (Nat → Nat) ]
      (∀ i → s i < s (suc i)) ×
      (∀ i → f (s i) ≡ b)
```

## LPO → IPP

```agda
Σℕ-split-support
  : ∀ {ℓ} {P : Nat → Type ℓ} ⦃ _ : ∀ {n} → H-Level (P n) 1 ⦄
  → (∀ n → Dec (P n))
  → ∃[ n ∈ Nat ] P n
  → Σ[ n ∈ Nat ] P n
Σℕ-split-support {P = P} P-dec w
  using n , p , _ ← ℕ-well-ordered {P = λ n → el! (P n)} P-dec w
  = n , p

module _ (lpo : ∀ {ℓ} → LPO ℓ) where
  lpoΣ
    : ∀ {ℓ} (P : Nat → Type ℓ) ⦃ _ : ∀ {n} → H-Level (P n) 1 ⦄
    → (∀ n → Dec (P n))
    → Dec (Σ[ n ∈ Nat ] P n)
  lpoΣ P P-dec = invmap (Σℕ-split-support P-dec) inc (lpo P P-dec)

  lpoΠ
    : ∀ {ℓ} (P : Nat → Type ℓ) ⦃ _ : ∀ {n} → H-Level (P n) 1 ⦄
    → (∀ n → Dec (P n))
    → Dec (∀ (n : Nat) → P n)
  lpoΠ P P-dec with lpoΣ (¬_ ∘ P) (λ n → Dec-→ ⦃ P-dec n ⦄)
  ... | yes (n , p) = no λ all → p (all n)
  ... | no ¬w = yes λ n → dec→dne ⦃ P-dec n ⦄ λ k → ¬w (n , k)

  LPO→IPP : IPP
  LPO→IPP f = Dec-rec if-Q if-¬Q (lpoΣ _ λ n → lpoΠ _ λ m → auto)
    where
      -- Is f eventually always true?
      Q = Σ[ n ∈ Nat ] ∀ (m : Nat) → f (n + m) ≡ true

      -- If so, there is trivially a constantly true subsequence.
      if-Q : Q → _
      if-Q (n , p) = true , n +_ , (λ i → +-preserves-<l i _ _ ≤-refl) , p

      -- If not, f is always eventually false (¬♢□ → □♢¬),
      -- so we can iterate LPO to extract a constantly false subsequence.
      if-¬Q : ¬ Q → _
      if-¬Q ¬a = false , s , (λ i → next (s i) .snd .fst) , s-false
        where
          next : ∀ (n : Nat) → Σ[ m ∈ Nat ] m > n × f m ≡ false
          next n with lpoΣ (λ m → f (suc n + m) ≡ false) (λ _ → auto)
          ... | yes (m , p) = suc n + m , +-≤l _ _ , p
          ... | no ¬w = absurd (¬a (suc n , λ m → dec→dne λ k → ¬w (m , ne→is-not k)))

          s : Nat → Nat
          s zero = next 0 .fst
          s (suc i) = next (s i) .fst

          s-false : (n : Nat) → f (s n) ≡ false
          s-false zero = next 0 .snd .snd
          s-false (suc n) = next (s n) .snd .snd
```

## LPO ← IPP

```agda
Dec→Bool-true
   : ∀ {ℓ} {A : Type ℓ} (d : Dec A)
   → Dec→Bool d ≡ true
   → A
Dec→Bool-true (yes a) _  = a
Dec→Bool-true (no ¬a) eq = absurd (false≠true eq)

Dec→Bool-false
   : ∀ {ℓ} {A : Type ℓ} (d : Dec A)
   → Dec→Bool d ≡ false
   → ¬ A
Dec→Bool-false (yes a) eq _ = true≠false eq
Dec→Bool-false (no ¬a) _    = ¬a

increasing→inflationary
  : (f : Nat → Nat)
  → (∀ i → f i < f (suc i))
  → ∀ i → i ≤ f i
increasing→inflationary f mono zero = 0≤x
increasing→inflationary f mono (suc i) =
  ≤-trans (s≤s (increasing→inflationary f mono i)) (mono i)

module _ (ipp : IPP) where
  IPP→LPO : ∀ {ℓ} → LPO ℓ
  IPP→LPO P P-dec = cases where
    instance
      _ : ∀ {n} → Dec (P n)
      _ = P-dec _

    -- f turns true as soon as P does, and stays that way.
    f : Nat → Bool
    f n = Dec→Bool (holds? (Σ[ i ∈ Fin (suc n) ] P (lower i)))

    -- If f is true infinitely often, P has to be true at least once.
    -- If f is false infinitely often, P can't ever be true.
    cases : _
    cases with ipp f
    ... | true , s , _ , s-true =
      yes (inc (Σ-map lower id (Dec→Bool-true _ (s-true 0))))
    ... | false , s , s-mono , s-false = no $
      rec! λ n p → Dec→Bool-false _ (s-false n)
        (fin n ⦃ s≤s (increasing→inflationary s s-mono n) ⦄ , p)
```
