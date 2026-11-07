import Mathlib

/-!
# Theorem 1 of the BIC paper (multiplier argument), and the fast-path bound of Theorem 4

Theorem 1 holds for any admissible sets `R i`. The paper's set (R),
`R_i = {0} ∪ [xmin, x_i^max]`, is the special case `paper_theorem1` below.
-/

open Finset

namespace BIC

variable {ι : Type*} [Fintype ι]

/-- **Theorem 1 (general form).** If every `x i` maximizes `f_i(y) - λ y` over `R i`, `λ ≥ 0`, and
the rates sum to `B`, then `x` maximizes `∑ f_i` over all `y` with `y i ∈ R i` and `∑ y_i ≤ B`. -/
theorem everett (R : ι → Set ℝ) (f : ι → ℝ → ℝ) (B lam : ℝ) (hlam : 0 ≤ lam)
    (x : ι → ℝ) (hmax : ∀ i, ∀ y ∈ R i, f i y - lam * y ≤ f i (x i) - lam * x i)
    (hS : ∑ i, x i = B) :
    ∀ y : ι → ℝ, (∀ i, y i ∈ R i) → ∑ i, y i ≤ B → ∑ i, f i (y i) ≤ ∑ i, f i (x i) := by
  intro y hyR hyB
  have h1 : ∑ i, (f i (y i) - lam * y i) ≤ ∑ i, (f i (x i) - lam * x i) :=
    sum_le_sum (fun i _ => hmax i (y i) (hyR i))
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hS] at h1
  have h2 := mul_le_mul_of_nonneg_left hyB hlam
  linarith

/-- The admissible set (R) of the paper. -/
def admissible (xmin xmaxi : ℝ) : Set ℝ := {0} ∪ Set.Icc xmin xmaxi

/-- **Theorem 1**, as stated in the paper: if `x(λ*)` is a pointwise maximizer (chi_argmax) and
`S(λ*) = B`, then `x(λ*)` is feasible for (P) and a global maximizer of (P). -/
theorem paper_theorem1 (xmin : ℝ) (xmax : ι → ℝ) (f : ι → ℝ → ℝ) (B lam : ℝ) (hlam : 0 ≤ lam)
    (x : ι → ℝ) (hxR : ∀ i, x i ∈ admissible xmin (xmax i))
    (hmax : ∀ i, ∀ y ∈ admissible xmin (xmax i), f i y - lam * y ≤ f i (x i) - lam * x i)
    (hS : ∑ i, x i = B) :
    ((∀ i, x i ∈ admissible xmin (xmax i)) ∧ ∑ i, x i ≤ B) ∧
    ∀ y : ι → ℝ, (∀ i, y i ∈ admissible xmin (xmax i)) → ∑ i, y i ≤ B →
      ∑ i, f i (y i) ≤ ∑ i, f i (x i) :=
  ⟨⟨hxR, hS.le⟩, everett _ f B lam hlam x hmax hS⟩

/-- **Fast-path bound in the proof of Theorem 4.** If `x(λ)` is a pointwise maximizer, `λ ≥ 0`
and `B - δ ≤ S(λ) ≤ B`, then the objective of `x(λ)` is at most `λ δ` below that of any feasible
allocation of (P). -/
theorem fast_path (R : ι → Set ℝ) (f : ι → ℝ → ℝ) (B lam δ : ℝ) (hlam : 0 ≤ lam)
    (x : ι → ℝ) (hmax : ∀ i, ∀ y ∈ R i, f i y - lam * y ≤ f i (x i) - lam * x i)
    (hlo : B - δ ≤ ∑ i, x i) :
    ∀ y : ι → ℝ, (∀ i, y i ∈ R i) → ∑ i, y i ≤ B →
      ∑ i, f i (y i) ≤ ∑ i, f i (x i) + lam * δ := by
  intro y hyR hyB
  have h1 : ∑ i, (f i (y i) - lam * y i) ≤ ∑ i, (f i (x i) - lam * x i) :=
    sum_le_sum (fun i _ => hmax i (y i) (hyR i))
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum] at h1
  have h2 := mul_le_mul_of_nonneg_left hyB hlam
  have h3 := mul_le_mul_of_nonneg_left (show B - ∑ i, x i ≤ δ by linarith) hlam
  nlinarith

end BIC
