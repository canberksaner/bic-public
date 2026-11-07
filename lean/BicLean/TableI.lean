import BicLean.KeyFamily

/-!
# Table I of the BIC paper: the four utility families satisfy Assumptions 1 and 2

For each family and every key in its domain, `Assumption1 b f f'` states: `f` has derivative
`f'` at every point of `[0, b]`, `f'` is continuous on `[0, b]`, `f` is strictly increasing and
strictly concave on `[0, b]`, and `f 0 = 0` (Assumption 1 and the normalization of Section II).
With each group sorted as in the last column of Table I, Assumption 2 holds (via Appendix A).
The sLLF utility is the normalized one of the footnote of Table I.
-/

open Set Real

namespace BIC

/-- Assumption 1 from the derivative: `f' > 0` and `f'` strictly decreasing on `[0, b]`. -/
lemma assumption1_of_deriv {f f' : ℝ → ℝ} {b : ℝ}
    (hd : ∀ x ∈ Icc 0 b, HasDerivAt f (f' x) x) (hpos : ∀ x ∈ Icc 0 b, 0 < f' x)
    (hanti : StrictAntiOn f' (Icc 0 b)) :
    StrictMonoOn f (Icc 0 b) ∧ StrictConcaveOn ℝ (Icc 0 b) f := by
  have hcont : ContinuousOn f (Icc 0 b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hderiv_eq : ∀ x ∈ interior (Icc 0 b), deriv f x = f' x := by
    intro x hx
    rw [interior_Icc] at hx
    exact (hd x (Ioo_subset_Icc_self hx)).deriv
  refine ⟨strictMonoOn_of_deriv_pos (convex_Icc 0 b) hcont (fun x hx => ?_),
    StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc 0 b) hcont ?_⟩
  · rw [hderiv_eq x hx]
    rw [interior_Icc] at hx
    exact hpos x (Ioo_subset_Icc_self hx)
  · intro x hx y hy hxy
    rw [hderiv_eq x hx, hderiv_eq y hy]
    rw [interior_Icc] at hx hy
    exact hanti (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hxy

/-- Assumption 1 (continuously differentiable, strictly increasing, strictly concave on
`[0, b]`) for one utility `f` with derivative `f'`, together with `f(0) = 0`. -/
def Assumption1 (b : ℝ) (f f' : ℝ → ℝ) : Prop :=
  (∀ x ∈ Icc 0 b, HasDerivAt f (f' x) x) ∧ ContinuousOn f' (Icc 0 b) ∧
    StrictMonoOn f (Icc 0 b) ∧ StrictConcaveOn ℝ (Icc 0 b) f ∧ f 0 = 0

lemma assumption1_mk {b : ℝ} {f f' : ℝ → ℝ} (hd : ∀ x ∈ Icc 0 b, HasDerivAt f (f' x) x)
    (hc : ContinuousOn f' (Icc 0 b)) (hpos : ∀ x ∈ Icc 0 b, 0 < f' x)
    (hanti : StrictAntiOn f' (Icc 0 b)) (h0 : f 0 = 0) : Assumption1 b f f' :=
  ⟨hd, hc, (assumption1_of_deriv hd hpos hanti).1, (assumption1_of_deriv hd hpos hanti).2, h0⟩

variable {ι κ : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq κ]

/-! ## sLLF: `x̄_k log(ℓ_i - 1 + x/x̄_k)`, normalized, `ℓ_i > 1`, ascending `ℓ_i` -/

/-- The sLLF utility, normalized: `x̄ (log(ℓ - 1 + x/x̄) - log(ℓ - 1))`. -/
noncomputable def sllf (xb ℓ x : ℝ) : ℝ := xb * (Real.log (ℓ - 1 + x / xb) - Real.log (ℓ - 1))

/-- Its derivative `1 / (ℓ - 1 + x/x̄)`. -/
noncomputable def sllf' (xb ℓ x : ℝ) : ℝ := 1 / (ℓ - 1 + x / xb)

lemma sllf_arg_pos {xb ℓ x : ℝ} (hxb : 0 < xb) (hℓ : 1 < ℓ) (hx : 0 ≤ x) :
    0 < ℓ - 1 + x / xb := by
  have := div_nonneg hx hxb.le
  linarith

lemma sllf_deriv {xb ℓ x : ℝ} (hxb : 0 < xb) (hℓ : 1 < ℓ) (hx : 0 ≤ x) :
    HasDerivAt (sllf xb ℓ) (sllf' xb ℓ x) x := by
  have hpos := sllf_arg_pos hxb hℓ hx
  have h1 : HasDerivAt (fun y => ℓ - 1 + y / xb) (1 / xb) x :=
    ((hasDerivAt_id' x).div_const xb).const_add (ℓ - 1)
  have h2 := ((h1.log hpos.ne').sub_const (Real.log (ℓ - 1))).const_mul xb
  have hxb' := hxb.ne'
  have hpos' := hpos.ne'
  unfold sllf sllf'
  convert h2 using 1
  field_simp

lemma sllf_assumption1 {xb ℓ : ℝ} (hxb : 0 < xb) (hℓ : 1 < ℓ) :
    Assumption1 xb (sllf xb ℓ) (sllf' xb ℓ) := by
  apply assumption1_mk
  · intro x hx
    exact sllf_deriv hxb hℓ hx.1
  · intro x hx
    have hne := (sllf_arg_pos hxb hℓ hx.1).ne'
    apply ContinuousAt.continuousWithinAt
    unfold sllf'
    fun_prop (disch := assumption)
  · intro x hx
    unfold sllf'
    exact one_div_pos.2 (sllf_arg_pos hxb hℓ hx.1)
  · intro x hx y hy hxy
    unfold sllf'
    apply one_div_lt_one_div_of_lt (sllf_arg_pos hxb hℓ hx.1)
    have := div_lt_div_of_pos_right hxy hxb
    linarith
  · simp [sllf]

/-- **Table I, sLLF row.** With `x̄_k > 0`, laxities `ℓ_i > 1` and each group sorted by
ascending `ℓ_i`, every utility satisfies Assumption 1 with `f_i(0) = 0`, and Assumption 2 holds. -/
theorem tableI_sllf (grp : ι → κ) (xmax : κ → ℝ) (xmin : ℝ) (hxb : ∀ k, 0 < xmax k)
    (hxmin : 0 ≤ xmin) (ell : ι → ℝ) (hell : ∀ i, 1 < ell i)
    (hsorted : ∀ i j, grp i = grp j → i ≤ j → ell i ≤ ell j) :
    (∀ i, Assumption1 (xmax (grp i)) (sllf (xmax (grp i)) (ell i)) (sllf' (xmax (grp i)) (ell i))) ∧
    PriorityOrder grp xmax xmin (fun i y => sllf (xmax (grp i)) (ell i) y) :=
  ⟨fun i => sllf_assumption1 (hxb (grp i)) (hell i),
   priority_of_key_decreasing grp xmax xmin (fun k y ℓ => sllf (xmax k) ℓ y)
     (fun k x ℓ => sllf' (xmax k) ℓ x) (fun _ => Ioi 1) ell (fun i => hell i) hxmin
     (fun k ℓ hℓ x hx => sllf_deriv (hxb k) hℓ hx.1)
     (fun k ℓ _ => by simp [sllf])
     (fun k x hx ℓ1 hℓ1 ℓ2 _ h12 => by
        simp only [sllf']
        exact one_div_le_one_div_of_le (sllf_arg_pos (hxb k) hℓ1 hx.1) (by linarith))
     hsorted⟩

/-! ## Quadratic: `a_i x - (b/2) x²`, `b > 0`, `a_i > b x̄_k`, descending `a_i` -/

/-- The quadratic utility `a x - (b/2) x²`. -/
noncomputable def quad (b a x : ℝ) : ℝ := a * x - b / 2 * x ^ 2

/-- Its derivative `a - b x`. -/
noncomputable def quad' (b a x : ℝ) : ℝ := a - b * x

lemma quad_deriv (b a x : ℝ) : HasDerivAt (quad b a) (quad' b a x) x := by
  have h := ((hasDerivAt_id' x).const_mul a).sub ((hasDerivAt_pow 2 x).const_mul (b / 2))
  unfold quad quad'
  convert h using 1
  norm_num
  ring

lemma quad_assumption1 {xb b a : ℝ} (hb : 0 < b) (ha : b * xb < a) :
    Assumption1 xb (quad b a) (quad' b a) := by
  apply assumption1_mk
  · intro x _
    exact quad_deriv b a x
  · unfold quad'
    fun_prop
  · intro x hx
    unfold quad'
    have := mul_le_mul_of_nonneg_left hx.2 hb.le
    linarith
  · intro x _ y _ hxy
    unfold quad'
    have := mul_lt_mul_of_pos_left hxy hb
    linarith
  · simp [quad]

/-- **Table I, quadratic row.** With `b > 0`, keys `a_i > b x̄_k` and each group sorted by
descending `a_i`, every utility satisfies Assumption 1 with `f_i(0) = 0`, and Assumption 2
holds. -/
theorem tableI_quad (grp : ι → κ) (xmax : κ → ℝ) (xmin : ℝ) (hxmin : 0 ≤ xmin) {b : ℝ}
    (hb : 0 < b) (a : ι → ℝ) (ha : ∀ i, b * xmax (grp i) < a i)
    (hsorted : ∀ i j, grp i = grp j → i ≤ j → a j ≤ a i) :
    (∀ i, Assumption1 (xmax (grp i)) (quad b (a i)) (quad' b (a i))) ∧
    PriorityOrder grp xmax xmin (fun i y => quad b (a i) y) :=
  ⟨fun i => quad_assumption1 hb (ha i),
   priority_of_key_increasing grp xmax xmin (fun _ y κ' => quad b κ' y)
     (fun _ x κ' => quad' b κ' x) (fun k => Ioi (b * xmax k)) a (fun i => ha i) hxmin
     (fun k κ' _ x _ => quad_deriv b κ' x)
     (fun k κ' _ => by simp [quad])
     (fun k x _ a1 _ a2 _ h12 => by
        simp only [quad']
        linarith)
     hsorted⟩

/-! ## Logarithmic: `a_i log(1 + x/b)`, `a_i, b > 0`, descending `a_i` -/

/-- The logarithmic utility `a log(1 + x/b)`. -/
noncomputable def logu (b a x : ℝ) : ℝ := a * Real.log (1 + x / b)

/-- Its derivative `a / (b + x)`. -/
noncomputable def logu' (b a x : ℝ) : ℝ := a / (b + x)

lemma logu_deriv {b a x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    HasDerivAt (logu b a) (logu' b a x) x := by
  have hpos : 0 < 1 + x / b := by
    have := div_nonneg hx hb.le
    linarith
  have h1 : HasDerivAt (fun y => 1 + y / b) (1 / b) x :=
    ((hasDerivAt_id' x).div_const b).const_add 1
  have h2 := (h1.log hpos.ne').const_mul a
  have hb' := hb.ne'
  have hpos' := hpos.ne'
  have hbx : b + x ≠ 0 := (show (0 : ℝ) < b + x by linarith).ne'
  unfold logu logu'
  convert h2 using 1
  field_simp

lemma logu_assumption1 {xb b a : ℝ} (hb : 0 < b) (ha : 0 < a) :
    Assumption1 xb (logu b a) (logu' b a) := by
  apply assumption1_mk
  · intro x hx
    exact logu_deriv hb hx.1
  · intro x hx
    have hne : b + x ≠ 0 := (show (0 : ℝ) < b + x by linarith [hx.1]).ne'
    apply ContinuousAt.continuousWithinAt
    unfold logu'
    fun_prop (disch := assumption)
  · intro x hx
    unfold logu'
    exact div_pos ha (by linarith [hx.1])
  · intro x hx y _ hxy
    unfold logu'
    exact div_lt_div_of_pos_left ha (by linarith [hx.1]) (by linarith)
  · simp [logu]

/-- **Table I, logarithmic row.** With `b > 0`, keys `a_i > 0` and each group sorted by
descending `a_i`, every utility satisfies Assumption 1 with `f_i(0) = 0`, and Assumption 2
holds. -/
theorem tableI_log (grp : ι → κ) (xmax : κ → ℝ) (xmin : ℝ) (hxmin : 0 ≤ xmin) {b : ℝ}
    (hb : 0 < b) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hsorted : ∀ i j, grp i = grp j → i ≤ j → a j ≤ a i) :
    (∀ i, Assumption1 (xmax (grp i)) (logu b (a i)) (logu' b (a i))) ∧
    PriorityOrder grp xmax xmin (fun i y => logu b (a i) y) :=
  ⟨fun i => logu_assumption1 hb (ha i),
   priority_of_key_increasing grp xmax xmin (fun _ y κ' => logu b κ' y)
     (fun _ x κ' => logu' b κ' x) (fun _ => Ioi 0) a (fun i => ha i) hxmin
     (fun k κ' _ x hx => logu_deriv hb hx.1)
     (fun k κ' _ => by simp [logu])
     (fun k x hx a1 _ a2 _ h12 => by
        simp only [logu']
        exact div_le_div_of_nonneg_right h12 (by linarith [hx.1]))
     hsorted⟩

/-! ## Exponential: `a_i (1 - e^{-b x})`, `a_i, b > 0`, descending `a_i` -/

/-- The exponential utility `a (1 - e^{-b x})`. -/
noncomputable def expu (b a x : ℝ) : ℝ := a * (1 - Real.exp (-(b * x)))

/-- Its derivative `a b e^{-b x}`. -/
noncomputable def expu' (b a x : ℝ) : ℝ := a * b * Real.exp (-(b * x))

lemma expu_deriv (b a x : ℝ) : HasDerivAt (expu b a) (expu' b a x) x := by
  have h1 : HasDerivAt (fun y => -(b * y)) (-(b * 1)) x := ((hasDerivAt_id' x).const_mul b).neg
  have h2 := (h1.exp.const_sub 1).const_mul a
  unfold expu expu'
  convert h2 using 1
  ring

lemma expu_assumption1 {xb b a : ℝ} (hb : 0 < b) (ha : 0 < a) :
    Assumption1 xb (expu b a) (expu' b a) := by
  apply assumption1_mk
  · intro x _
    exact expu_deriv b a x
  · unfold expu'
    fun_prop
  · intro x _
    unfold expu'
    exact mul_pos (mul_pos ha hb) (Real.exp_pos _)
  · intro x _ y _ hxy
    unfold expu'
    have h1 : -(b * y) < -(b * x) := by
      have := mul_lt_mul_of_pos_left hxy hb
      linarith
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 h1) (mul_pos ha hb)
  · simp [expu]

/-- **Table I, exponential row.** With `b > 0`, keys `a_i > 0` and each group sorted by
descending `a_i`, every utility satisfies Assumption 1 with `f_i(0) = 0`, and Assumption 2
holds. -/
theorem tableI_exp (grp : ι → κ) (xmax : κ → ℝ) (xmin : ℝ) (hxmin : 0 ≤ xmin) {b : ℝ}
    (hb : 0 < b) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hsorted : ∀ i j, grp i = grp j → i ≤ j → a j ≤ a i) :
    (∀ i, Assumption1 (xmax (grp i)) (expu b (a i)) (expu' b (a i))) ∧
    PriorityOrder grp xmax xmin (fun i y => expu b (a i) y) :=
  ⟨fun i => expu_assumption1 hb (ha i),
   priority_of_key_increasing grp xmax xmin (fun _ y κ' => expu b κ' y)
     (fun _ x κ' => expu' b κ' x) (fun _ => Ioi 0) a (fun i => ha i) hxmin
     (fun k κ' _ x _ => expu_deriv b κ' x)
     (fun k κ' _ => by simp [expu])
     (fun k x _ a1 _ a2 _ h12 => by
        simp only [expu']
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h12 hb.le)
          (Real.exp_pos _).le)
     hsorted⟩

end BIC
