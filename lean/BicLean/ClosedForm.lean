import Mathlib

/-!
# Appendix B of the BIC paper: the closed form (chi)

One EV, utility `f`, minimum rate `a = xmin`, maximum rate `b = x_i^max`, `0 < a ≤ b`.
`f` is concave on `[0, b]` with derivative `f'` there, and `f 0 = 0`.
-/

open Set

namespace BIC

variable {f f' : ℝ → ℝ} {a b : ℝ}

/-- First-order conditions give a maximizer of `f(y) - λ y` on `[a, b]` (concave `f`). -/
theorem foc_max (hconc : ConcaveOn ℝ (Icc 0 b) f) (ha : 0 ≤ a)
    (hderiv : ∀ x ∈ Icc 0 b, HasDerivAt f (f' x) x) {lam p : ℝ} (hp : p ∈ Icc a b)
    (hlo : p < b → f' p ≤ lam) (hhi : a < p → lam ≤ f' p) :
    ∀ y ∈ Icc a b, f y - lam * y ≤ f p - lam * p := by
  intro y hy
  have hpS : p ∈ Icc 0 b := ⟨ha.trans hp.1, hp.2⟩
  have hyS : y ∈ Icc 0 b := ⟨ha.trans hy.1, hy.2⟩
  rcases lt_trichotomy y p with hyp | rfl | hpy
  · have h1 := hconc.le_slope_of_hasDerivAt hyS hpS hyp (hderiv p hpS)
    have h2 := hhi (lt_of_le_of_lt hy.1 hyp)
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h1
    have h3 := mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 hyp.le)
    linarith
  · exact le_rfl
  · have h1 := hconc.slope_le_of_hasDerivAt hpS hyS hpy (hderiv p hpS)
    have h2 := hlo (lt_of_lt_of_le hpy hy.2)
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h1
    have h3 := mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 hpy.le)
    linarith

/-- The projection `[(f')⁻¹(λ)]_a^b` of (selector), for `λ` in the range `[f'(b), f'(0)]` where
the inverse is defined: if `f'(z) = λ` with `z ∈ [0, b]`, then `min (max z a) b` satisfies the
first-order conditions, hence maximizes `f(y) - λ y` on `[a, b]` by `foc_max`. -/
theorem clamp_foc (hconc : ConcaveOn ℝ (Icc 0 b) f) (ha : 0 ≤ a) (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc 0 b, HasDerivAt f (f' x) x) {lam z : ℝ} (hz : z ∈ Icc 0 b)
    (hfz : f' z = lam) :
    min (max z a) b ∈ Icc a b ∧ (min (max z a) b < b → f' (min (max z a) b) ≤ lam) ∧
      (a < min (max z a) b → lam ≤ f' (min (max z a) b)) := by
  have hanti : AntitoneOn f' (Icc 0 b) := by
    have := hconc.antitoneOn_deriv (fun x hx => (hderiv x hx).differentiableAt)
    intro x hx y hy hxy
    have h := this hx hy hxy
    rwa [(hderiv x hx).deriv, (hderiv y hy).deriv] at h
  rcases le_total z a with hza | haz
  · have hp : min (max z a) b = a := by rw [max_eq_right hza, min_eq_left hab]
    rw [hp]
    refine ⟨⟨le_rfl, hab⟩, fun _ => ?_, fun h => absurd h (lt_irrefl a)⟩
    rw [← hfz]
    exact hanti hz ⟨ha, hab⟩ hza
  · have hp : min (max z a) b = z := by rw [max_eq_left haz, min_eq_left hz.2]
    rw [hp]
    exact ⟨⟨haz, hz.2⟩, fun _ => hfz.le, fun _ => hfz.ge⟩

/-- For `λ > f'(0)` the projection is `a` (convention `(f')⁻¹(λ) ≤ 0`): `a` satisfies the
first-order conditions. -/
theorem foc_left (hconc : ConcaveOn ℝ (Icc 0 b) f) (ha : 0 ≤ a) (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc 0 b, HasDerivAt f (f' x) x) {lam : ℝ} (hlam : f' 0 < lam) :
    a ∈ Icc a b ∧ (a < b → f' a ≤ lam) ∧ (a < a → lam ≤ f' a) := by
  have hanti := hconc.antitoneOn_deriv (fun x hx => (hderiv x hx).differentiableAt)
  have h := hanti ⟨le_rfl, ha.trans hab⟩ ⟨ha, hab⟩ ha
  rw [(hderiv 0 ⟨le_rfl, ha.trans hab⟩).deriv, (hderiv a ⟨ha, hab⟩).deriv] at h
  exact ⟨⟨le_rfl, hab⟩, fun _ => by linarith, fun h' => absurd h' (lt_irrefl a)⟩

/-- For `λ < f'(b)` the projection is `b` (convention `(f')⁻¹(λ) ≥ b`): `b` satisfies the
first-order conditions. -/
theorem foc_right (hab : a ≤ b) {lam : ℝ} (hlam : lam < f' b) :
    b ∈ Icc a b ∧ (b < b → f' b ≤ lam) ∧ (a < b → lam ≤ f' b) :=
  ⟨⟨hab, le_rfl⟩, fun h => absurd h (lt_irrefl b), fun _ => hlam.le⟩

/-- Appendix B: strict concavity and `f 0 = 0` give `λ^th = f(a)/a > f'(a)`. -/
theorem lambda_th_gt (hsc : StrictConcaveOn ℝ (Icc 0 b) f) (hf0 : f 0 = 0) (ha : 0 < a)
    (hab : a ≤ b) (hderiv : HasDerivAt f (f' a) a) : f' a < f a / a := by
  have h := hsc.lt_slope_of_hasDerivAt (x := 0) (y := a) ⟨le_rfl, ha.le.trans hab⟩
    ⟨ha.le, hab⟩ ha hderiv
  rwa [slope_def_field, hf0, sub_zero, sub_zero] at h

/-- **Proposition 1, choosing bullet.** For `λ ≥ λ^th` (in particular `λ = L`), `a = xmin` is the
unique maximizer of `f(y) - λ y` on `[a, b]`. So at `λ = L` every EV of a restriction is at
`xmin`, its aggregate is `|I| xmin ≤ B`, and the multiplier of each restriction lies in `[0, L]`. -/
theorem xmin_unique_max (hsc : StrictConcaveOn ℝ (Icc 0 b) f) (hf0 : f 0 = 0) (ha : 0 < a)
    (hab : a ≤ b) (hderiv : HasDerivAt f (f' a) a) {lam : ℝ} (hlam : f a / a ≤ lam) :
    ∀ y ∈ Icc a b, y ≠ a → f y - lam * y < f a - lam * a := by
  intro y hy hya
  have hay : a < y := lt_of_le_of_ne hy.1 (Ne.symm hya)
  have h1 := hsc.slope_lt_of_hasDerivAt ⟨ha.le, hab⟩ ⟨ha.le.trans hy.1, hy.2⟩ hay hderiv
  have h2 := lambda_th_gt hsc hf0 ha hab hderiv
  rw [slope_def_field, div_lt_iff₀ (by linarith)] at h1
  have h3 := mul_le_mul_of_nonneg_right (h2.le.trans hlam) (sub_nonneg.2 hay.le)
  have h4 : f' a * (y - a) < lam * (y - a) := by
    have := mul_lt_mul_of_pos_right (h2.trans_le hlam) (sub_pos.2 hay)
    linarith
  linarith

/-- Concavity and `f 0 = 0`: `f(y) ≤ y λ^th` on `[a, b]`. -/
theorem le_mul_lambda_th (hconc : ConcaveOn ℝ (Icc 0 b) f) (hf0 : f 0 = 0) (ha : 0 < a)
    {y : ℝ} (hy : y ∈ Icc a b) : f y ≤ y * (f a / a) := by
  have hanti := hconc.slope_anti (x := 0) ⟨le_rfl, ha.le.trans hy.1 |>.trans hy.2⟩
  have hamem : a ∈ Icc 0 b \ {0} := ⟨⟨ha.le, hy.1.trans hy.2⟩, ne_of_gt ha⟩
  have hymem : y ∈ Icc 0 b \ {0} := ⟨⟨ha.le.trans hy.1, hy.2⟩, ne_of_gt (ha.trans_le hy.1)⟩
  have h := hanti hamem hymem hy.1
  rw [slope_def_field, slope_def_field, hf0, sub_zero, sub_zero, sub_zero, sub_zero] at h
  have hy0 : 0 < y := ha.trans_le hy.1
  rw [div_le_iff₀ hy0] at h
  linarith

/-- The closed form (chi): the maximizer `p` of the interval if `λ < λ^th`, and `0` otherwise. -/
noncomputable def chi (f : ℝ → ℝ) (a lam p : ℝ) : ℝ := if lam < f a / a then p else 0

/-- **Appendix B.** If `p` maximizes `f(y) - λ y` over `[a, b]` (the projection, see `foc_max`
and `clamp_foc`), then the closed form (chi) maximizes `f(y) - λ y` over `R = {0} ∪ [a, b]`. -/
theorem closed_form (hconc : ConcaveOn ℝ (Icc 0 b) f) (hf0 : f 0 = 0) (ha : 0 < a)
    {lam p : ℝ} (hp : p ∈ Icc a b) (hpmax : ∀ y ∈ Icc a b, f y - lam * y ≤ f p - lam * p) :
    (chi f a lam p = 0 ∨ chi f a lam p ∈ Icc a b) ∧
    ∀ y, (y = 0 ∨ y ∈ Icc a b) → f y - lam * y ≤ f (chi f a lam p) - lam * chi f a lam p := by
  unfold chi
  split_ifs with h
  · refine ⟨Or.inr hp, ?_⟩
    rintro y (rfl | hy)
    · have h1 := hpmax a ⟨le_rfl, hp.1.trans hp.2⟩
      have h2 : f a - lam * a = a * (f a / a - lam) := by field_simp
      have h3 : 0 < a * (f a / a - lam) := mul_pos ha (sub_pos.2 h)
      rw [hf0]
      linarith
    · exact hpmax y hy
  · refine ⟨Or.inl rfl, ?_⟩
    rintro y (rfl | hy)
    · exact le_rfl
    · have h1 := le_mul_lambda_th hconc hf0 ha hy
      have hy0 : 0 ≤ y := ha.le.trans hy.1
      have h2 := mul_le_mul_of_nonneg_left (not_lt.1 h) hy0
      rw [hf0]
      linarith

/-! ## The projection of (selector), and (chi) with it -/

/-- With `f'` continuous on `[0, b]` (Assumption 1: continuously differentiable), `(f')⁻¹(λ)`
exists for every `λ ∈ [f'(b), f'(0)]` (intermediate value theorem). -/
theorem exists_inv (hb : 0 ≤ b) (hcont : ContinuousOn f' (Icc 0 b)) {lam : ℝ}
    (hlam : lam ∈ Icc (f' b) (f' 0)) : ∃ z ∈ Icc 0 b, f' z = lam := by
  obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc' hb hcont hlam
  exact ⟨z, hz, hfz⟩

/-- `(f')⁻¹(λ)`: a point `z ∈ [0, b]` with `f'(z) = λ` when one exists; otherwise the convention
`0` for `λ > f'(0)` and `b` for `λ < f'(b)`. -/
noncomputable def invD (f' : ℝ → ℝ) (b lam : ℝ) : ℝ := by
  classical
  exact if h : ∃ z ∈ Icc 0 b, f' z = lam then h.choose else if f' 0 < lam then 0 else b

/-- The projection `[(f')⁻¹(λ)]_a^b = min{max{(f')⁻¹(λ), a}, b}` of (selector) and (chi). -/
noncomputable def proj (f' : ℝ → ℝ) (a b lam : ℝ) : ℝ := min (max (invD f' b lam) a) b

/-- The projection maximizes `f(y) - λ y` on `[a, b]`, for every `λ`. -/
theorem proj_max (hconc : ConcaveOn ℝ (Icc 0 b) f) (ha : 0 ≤ a) (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc 0 b, HasDerivAt f (f' x) x) (hcont : ContinuousOn f' (Icc 0 b))
    (lam : ℝ) :
    proj f' a b lam ∈ Icc a b ∧
      ∀ y ∈ Icc a b, f y - lam * y ≤ f (proj f' a b lam) - lam * proj f' a b lam := by
  have hb : 0 ≤ b := ha.trans hab
  have hfoc : proj f' a b lam ∈ Icc a b ∧ (proj f' a b lam < b → f' (proj f' a b lam) ≤ lam) ∧
      (a < proj f' a b lam → lam ≤ f' (proj f' a b lam)) := by
    unfold proj invD
    split_ifs with h hgt
    · exact clamp_foc hconc ha hab hderiv h.choose_spec.1 h.choose_spec.2
    · rw [max_eq_right ha, min_eq_left hab]
      exact foc_left hconc ha hab hderiv hgt
    · rw [max_eq_left hab, min_self]
      have hlt : lam < f' b := by
        by_contra hge
        push_neg at hge
        exact h (exists_inv hb hcont ⟨hge, not_lt.1 hgt⟩)
      exact foc_right hab hlt
  exact ⟨hfoc.1, foc_max hconc ha hderiv hfoc.1 hfoc.2.1 hfoc.2.2⟩

/-- **Appendix B, full form.** With the projection of (selector), the closed form (chi) is a
maximizer of `f(y) - λ y` over `R = {0} ∪ [a, b]`, for every `λ`. -/
theorem selector_max (hconc : ConcaveOn ℝ (Icc 0 b) f) (hf0 : f 0 = 0) (ha : 0 < a)
    (hab : a ≤ b) (hderiv : ∀ x ∈ Icc 0 b, HasDerivAt f (f' x) x)
    (hcont : ContinuousOn f' (Icc 0 b)) (lam : ℝ) :
    (chi f a lam (proj f' a b lam) = 0 ∨ chi f a lam (proj f' a b lam) ∈ Icc a b) ∧
    ∀ y, (y = 0 ∨ y ∈ Icc a b) →
      f y - lam * y ≤ f (chi f a lam (proj f' a b lam)) - lam * chi f a lam (proj f' a b lam) := by
  obtain ⟨hp, hpmax⟩ := proj_max hconc ha.le hab hderiv hcont lam
  exact closed_form hconc hf0 ha hp hpmax

end BIC
