```agda
open import 1Lab.Prelude
open import 1Lab.Reflection.Induction

open import Data.Bool

open import Homotopy.Space.Circle

module DoubleCoverOfTheCircle where
```

# double cover of the circle

We define the connected double cover of the circle in two ways, as a
higher inductive family and by recursion, and show that the two
definitions are equivalent.

~~~{.quiver}
% stolen from the Symmetry book https://github.com/UniMath/SymmetryBook
\begin{tikzpicture}
  \node at (2,-1) {$S^1$};
  \node at (2,0.5) {$\mathsf{Cover}$};
  \draw[line width=1pt] (0,-1) ellipse (1 and .3);
  \draw[line width=1pt] (-1,0)
  .. controls ++( 90:-.3) and ++(210: .4) .. (0,0.1)
  .. controls ++(210:-.4) and ++(270: .3) .. (1,1)
  .. controls ++(270:-.3) and ++(  0: .1) .. (0,1.3)
  .. controls ++(  0:-.1) and ++( 90: .3) .. (-1,1)
  .. controls ++( 90:-.3) and ++(150: .4) .. (0,0.1)
  .. controls ++(150:-.4) and ++(270: .3) .. (1,0)
  .. controls ++(270:-.3) and ++(  0: .1) .. (0,0.3)
  .. controls ++(  0:-.1) and ++( 90: .3) .. (-1,0);
  \node[fill,circle,inner sep=1.5pt] at (-1,-1) {};
  \node[fill,circle,inner sep=1.5pt] at (-1,0) {};
  \node[fill,circle,inner sep=1.5pt] at (-1,1) {};
\end{tikzpicture}
~~~

The higher inductive definition has two $n$-cells for every $n$-cell
in the circle: two points over $\mathsf{base}$ and two loops over
$\mathsf{loop}$.

```agda
data Cover : S¹ → Type where
  base0 base1 : Cover base
  loop0 : PathP (λ i → Cover (loop i)) base0 base1
  loop1 : PathP (λ i → Cover (loop i)) base1 base0

unquoteDecl Cover-elim =
  make-elim-with default-elim-visible Cover-elim (quote Cover)
```

The recursive definition defines a $2$-element set bundle directly by sending
$\mathsf{base}$ to the booleans and $\mathsf{loop}$ to the identification
that swaps the booleans, using univalence.

```agda
cover : S¹ → Type
cover = S¹-elim Bool (ua not≃)
```

We can then write functions in both directions and prove that they are
inverses using the introduction and elimination helpers for `ua`.

```agda
recover : ∀ s → Cover s → cover s
recover = Cover-elim _ true false
  (path→ua-pathp _ refl) (path→ua-pathp _ refl)

discover-base : cover base → Cover base
discover-base true = base0
discover-base false = base1

discover-loop
  : ∀ c → PathP (λ i → Cover (loop i)) (discover-base c) (discover-base (not c))
discover-loop true = loop0
discover-loop false = loop1

discover : ∀ s → cover s → Cover s
discover = S¹-elim discover-base (ua→ discover-loop)

rediscover : ∀ s c → recover s (discover s c) ≡ c
rediscover = S¹-elim (Bool-elim _ refl refl) hlevel!

disrecover : ∀ s c → discover s (recover s c) ≡ c
disrecover = Cover-elim _ refl refl
  (transposeP (ua→-β not≃ {f₁ = discover-base} discover-loop refl ∙ ▷-idr loop0))
  (transposeP (ua→-β not≃ {f₁ = discover-base} discover-loop refl ∙ ▷-idr loop1))

Cover≃cover : ∀ s → Cover s ≃ cover s
Cover≃cover s = recover s , is-iso→is-equiv λ where
  .is-iso.from → discover s
  .is-iso.rinv → rediscover s
  .is-iso.linv → disrecover s
```
