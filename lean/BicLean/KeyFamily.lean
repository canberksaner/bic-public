import BicLean.Prefix

/-!
# Appendix A of the BIC paper: utility families with a key

The utilities of group `k` are `f_i(x) = h k x (key i)`, with `h k 0 κ = 0`. If the marginal
utility `∂h/∂x (x; κ)` is monotone in the key `κ` (same direction for every `x ∈ [0, x̄_k]`), then
sorting the EVs of each group by their keys gives Assumption 2 (priority order).
-/

open Set

namespace BIC

/-- Last step of Appendix A: `f - g` vanishes at `0` and has a nonnegative derivative on
`[0, b]`, hence `f ≥ g` on `[0, b]`. -/
theorem le_of_deriv_le {f g f' g' : ℝ → ℝ} {b : ℝ}
    (hf : ∀ x ∈ Icc 0 b, HasDerivAt f (f' x) x) (hg : ∀ x ∈ Icc 0 b, HasDerivAt g (g' x) x)
    (hle : ∀ x ∈ Icc 0 b, g' x ≤ f' x) (h0 : f 0 = g 0) :
    ∀ x ∈ Icc 0 b, g x ≤ f x := by
  have hmono : MonotoneOn (fun x => f x - g x) (Icc 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 b)
    · intro x hx
      exact ((hf x hx).sub (hg x hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact ((hf x (Ioo_subset_Icc_self hx)).sub
        (hg x (Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hd : HasDerivAt (fun x => f x - g x) (f' x - g' x) x :=
        (hf x (Ioo_subset_Icc_self hx)).sub (hg x (Ioo_subset_Icc_self hx))
      rw [hd.deriv]
      linarith [hle x (Ioo_subset_Icc_self hx)]
  intro x hx
  have h0mem : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hx.1.trans hx.2⟩
  have := hmono h0mem hx hx.1
  simp only [h0, sub_self] at this
  linarith

variable {ι κ : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq κ]

/-- **Appendix A, marginal utility increasing in the key:** sorting each group by descending
key gives Assumption 2. The conditions are asked only for the keys of the family's domain
`Kset k` (which may depend on the group, e.g. `a_i > b x̄_k` for the quadratic family). -/
theorem priority_of_key_increasing (grp : ι → κ) (xmax : κ → ℝ) (xmin : ℝ)
    (h h' : κ → ℝ → ℝ → ℝ) (Kset : κ → Set ℝ) (key : ι → ℝ)
    (hkey : ∀ i, key i ∈ Kset (grp i)) (hxmin : 0 ≤ xmin)
    (hderiv : ∀ k, ∀ κ' ∈ Kset k, ∀ x ∈ Icc 0 (xmax k),
      HasDerivAt (fun y => h k y κ') (h' k x κ') x)
    (hzero : ∀ k, ∀ κ' ∈ Kset k, h k 0 κ' = 0)
    (hmono : ∀ k, ∀ x ∈ Icc 0 (xmax k), MonotoneOn (h' k x) (Kset k))
    (hsorted : ∀ i j, grp i = grp j → i ≤ j → key j ≤ key i) :
    PriorityOrder grp xmax xmin (fun i y => h (grp i) y (key i)) := by
  intro i j hg hij y hy
  have hki := hkey i
  have hkj : key j ∈ Kset (grp i) := by rw [hg]; exact hkey j
  simp only [← hg]
  exact le_of_deriv_le (hderiv (grp i) (key i) hki) (hderiv (grp i) (key j) hkj)
    (fun x hx => hmono (grp i) x hx hkj hki (hsorted i j hg hij))
    (by rw [hzero _ _ hki, hzero _ _ hkj]) y ⟨hxmin.trans hy.1, hy.2⟩

/-- **Appendix A, marginal utility decreasing in the key:** sorting each group by ascending
key gives Assumption 2 (conditions on the keys of the domain `Kset k` only). -/
theorem priority_of_key_decreasing (grp : ι → κ) (xmax : κ → ℝ) (xmin : ℝ)
    (h h' : κ → ℝ → ℝ → ℝ) (Kset : κ → Set ℝ) (key : ι → ℝ)
    (hkey : ∀ i, key i ∈ Kset (grp i)) (hxmin : 0 ≤ xmin)
    (hderiv : ∀ k, ∀ κ' ∈ Kset k, ∀ x ∈ Icc 0 (xmax k),
      HasDerivAt (fun y => h k y κ') (h' k x κ') x)
    (hzero : ∀ k, ∀ κ' ∈ Kset k, h k 0 κ' = 0)
    (hanti : ∀ k, ∀ x ∈ Icc 0 (xmax k), AntitoneOn (h' k x) (Kset k))
    (hsorted : ∀ i j, grp i = grp j → i ≤ j → key i ≤ key j) :
    PriorityOrder grp xmax xmin (fun i y => h (grp i) y (key i)) := by
  intro i j hg hij y hy
  have hki := hkey i
  have hkj : key j ∈ Kset (grp i) := by rw [hg]; exact hkey j
  simp only [← hg]
  exact le_of_deriv_le (hderiv (grp i) (key i) hki) (hderiv (grp i) (key j) hkj)
    (fun x hx => hanti (grp i) x hx hki hkj (hsorted i j hg hij))
    (by rw [hzero _ _ hki, hzero _ _ hkj]) y ⟨hxmin.trans hy.1, hy.2⟩

end BIC
