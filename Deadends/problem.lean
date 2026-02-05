import Mathlib

/-
# Problem Description

**Definition 1 (Square-free).** An integer $n \geq 1$ is *square-free* if $p^2 \nmid n$ for every
prime $p$. By convention, $0$ is not square-free.

**Definition 2 (Base-$b$ dead end).** Let $b \geq 2$ be an integer. A positive integer $N$ is a
*base-$b$ dead end* if:
1. $N$ is square-free, and
2. For every $d \in \{0, 1, \ldots, b-1\}$, the integer $bN + d$ is **not** square-free.

**Definition 3 (Asymptotic density of base-$b$ dead ends).** For $b \geq 2$, the asymptotic density
of base-$b$ dead ends is:
$$D_b := \lim_{X \to \infty} \frac{\#\{N \leq X : N \text{ is a base-}b\text{ dead end}\}}{X}$$

**Definition 4 (Local density factor).** For a prime $p$, an integer $b \geq 2$, and a subset
$T \subseteq \{0, 1, \ldots, b-1\}$, define the *local density factor* $\mu_p(b, T)$ as:
$$\mu_p(b, T) := \frac{1}{p^2} \cdot \#\{r \in \{0, 1, \ldots, p^2-1\} : p^2 \nmid r
                   \text{ and } p^2 \nmid br + d \text{ for all } d \in T\}$$

**Definition 5 (Joint square-free density).** For $b \geq 2$ and $T \subseteq \{0, 1, \ldots, b-1\}$,
define $\alpha(b, T)$ as:
$$\alpha(b, T) := \prod_{p \text{ prime}} \mu_p(b, T)$$

**Theorem (Explicit formula for $D_b$).** For each integer $b \geq 2$:
1. The limit $D_b$ exists.
2. $D_b$ is given by the inclusion-exclusion formula:
   $$D_b = \sum_{T \subseteq \{0, 1, \ldots, b-1\}} (-1)^{|T|} \cdot \alpha(b, T)$$
3. Each $\alpha(b, T)$ is the asymptotic density of positive integers $N$ such that $N$ is
   square-free and $bN + d$ is square-free for all $d \in T$. This density exists and equals
   the convergent Euler product $\prod_p \mu_p(b, T)$.
-/

-- Background: The term "base-$b$ dead end" arises from interpreting integers via their base-$b$
-- representations. If $N$ has base-$b$ representation, then "appending a digit $d$" to $N$
-- corresponds to computing $bN + d$. A dead end is a square-free number such that every possible
-- digit extension yields a non-square-free number.

-- Main Definition(s)

/-- A positive integer N is a base-b dead end if:
    1. N is square-free, and
    2. For every digit d in {0, 1, ..., b-1}, the integer bN + d is not square-free. -/
def IsBaseBDeadEnd (b : ℕ) (N : ℕ) : Prop :=
  0 < N ∧ Squarefree N ∧ ∀ d ∈ Finset.range b, ¬Squarefree (b * N + d)

instance (b N : ℕ) : Decidable (IsBaseBDeadEnd b N) := by
  unfold IsBaseBDeadEnd
  infer_instance

/-- The counting function for base-b dead ends up to X. -/
def countBaseBDeadEnds (b : ℕ) (X : ℕ) : ℕ :=
  (Finset.filter (fun N => IsBaseBDeadEnd b N) (Finset.Icc 1 X)).card

/-- The asymptotic density of base-b dead ends exists and equals some value D. -/
def HasAsymptoticDensity (b : ℕ) (D : ℝ) : Prop :=
  Filter.Tendsto (fun X : ℕ => (countBaseBDeadEnds b X : ℝ) / (X : ℝ))
    Filter.atTop (nhds D)

/-- The local density factor $\mu_p(b, T)$ from Definition 4.
    This counts the proportion of residue classes r in {0, ..., p^2 - 1} such that:
    - $p^2 \nmid r$ (ensuring N is square-free at p), and
    - $p^2 \nmid br + d$ for all $d \in T$ (ensuring $bN + d$ is square-free at p for all d in T).

    We compute it as: (1/p^2) * #{r : 0 <= r < p^2 | p^2 does not divide r and
                        for all d in T, p^2 does not divide br + d} -/
noncomputable def localDensityFactor (p : ℕ) (b : ℕ) (T : Finset ℕ) : ℝ :=
  let pSq := p ^ 2
  let validResidues := (Finset.range pSq).filter fun r =>
    ¬(pSq ∣ r) ∧ ∀ d ∈ T, ¬(pSq ∣ (b * r + d))
  (validResidues.card : ℝ) / (pSq : ℝ)

/-- The joint square-free density $\alpha(b, T)$ from Definition 5.
    This is the infinite product $\prod_p \mu_p(b, T)$ over all primes. -/
noncomputable def jointSquarefreeDensity (b : ℕ) (T : Finset ℕ) : ℝ :=
  ∏' p : Nat.Primes, localDensityFactor (p : ℕ) b T

/-- The explicit formula for $D_b$ using inclusion-exclusion.
    $D_b = \sum_{T \subseteq \{0, 1, \ldots, b-1\}} (-1)^{|T|} \cdot \alpha(b, T)$ -/
noncomputable def explicitDensityFormula (b : ℕ) : ℝ :=
  ∑ T ∈ (Finset.range b).powerset,
    ((-1 : ℝ) ^ T.card) * jointSquarefreeDensity b T

-- Main Statement(s)

/-- Part 1: For each base b >= 2, the asymptotic density of base-b dead ends exists. -/
theorem baseBDeadEnd_density_exists (b : ℕ) (hb : 2 ≤ b) :
    ∃ D : ℝ, HasAsymptoticDensity b D := by
  sorry

/-- Uniqueness of the asymptotic density (limits in Hausdorff spaces are unique). -/
theorem baseBDeadEnd_density_unique (b : ℕ) (D₁ D₂ : ℝ)
    (h₁ : HasAsymptoticDensity b D₁) (h₂ : HasAsymptoticDensity b D₂) :
    D₁ = D₂ := by
  sorry

/-- The density D_b, defined as the unique limit when b >= 2.
    We use Classical.choose on the existence result. -/
noncomputable def baseBDeadEndDensity (b : ℕ) (hb : 2 ≤ b) : ℝ :=
  Classical.choose (baseBDeadEnd_density_exists b hb)

/-- The density function satisfies the asymptotic density property. -/
theorem baseBDeadEndDensity_spec (b : ℕ) (hb : 2 ≤ b) :
    HasAsymptoticDensity b (baseBDeadEndDensity b hb) :=
  Classical.choose_spec (baseBDeadEnd_density_exists b hb)

/-- The Euler product $\prod_p \mu_p(b, T)$ converges for any valid b and T. -/
theorem jointSquarefreeDensity_convergent (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ)
    (hT : T ⊆ Finset.range b) :
    Multipliable (fun p : Nat.Primes => localDensityFactor (p : ℕ) b T) := by
  sorry

/-- Part 3: $\alpha(b, T)$ equals the asymptotic density of positive integers N such that
    N is square-free and bN + d is square-free for all d in T. -/
theorem jointSquarefreeDensity_is_asymptotic_density (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ)
    (hT : T ⊆ Finset.range b) :
    let countJoint (X : ℕ) : ℕ :=
      (Finset.Icc 1 X).filter (fun N =>
        Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d)) |>.card
    Filter.Tendsto (fun X : ℕ => (countJoint X : ℝ) / (X : ℝ))
      Filter.atTop (nhds (jointSquarefreeDensity b T)) := by
  sorry

/-- Part 2: The explicit formula for D_b via inclusion-exclusion.
    $D_b = \sum_{T \subseteq \{0, ..., b-1\}} (-1)^{|T|} \cdot \alpha(b, T)$ -/
theorem baseBDeadEnd_density_formula (b : ℕ) (hb : 2 ≤ b) :
    baseBDeadEndDensity b hb = explicitDensityFormula b := by
  sorry

/-- Correctness statement: The explicit formula computes the same value as the limit-based
    definition of the density. -/
theorem explicitDensityFormula_correct (b : ℕ) (hb : 2 ≤ b) :
    HasAsymptoticDensity b (explicitDensityFormula b) := by
  sorry
