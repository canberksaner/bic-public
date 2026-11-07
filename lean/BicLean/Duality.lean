import BicLean.Prefix
import BicLean.ClosedForm

/-!
# Lemma 1 of the BIC paper (lem:submod), with the strong duality it relies on

The paper's proof of Lemma 1 uses `V(I) = min_{λ ≥ 0} L_I(λ)` ("strong duality holds").
Mathlib has no Lagrangian duality for this problem, so it is proved here: an optimal allocation
of `(P_I)` exists (compactness), and an exchange argument between two EVs gives a multiplier
`λ ≥ 0` at which every EV of `I` maximizes `f_i(x) - λ x` on `[xmin, x_i^max]` and
`λ (B - ∑ x_i) = 0`.
-/

open Finset Set Filter Topology

namespace BIC

variable {ι κ : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq κ]
variable (grp : ι → κ) (xmax : κ → ℝ) (xmin B : ℝ) (f f' : ι → ℝ → ℝ)

/-- Assumption 1 (regularity) with the standing conditions `0 < xmin < x_i^max`.
`f' i` is the derivative of `f i`, asked as `HasDerivAt` at every point of `[0, x_i^max]`
(two-sided also at the end points). Continuity of `f'` is not needed. -/
structure Regular : Prop where
  xmin_pos : 0 < xmin
  xmin_lt : ∀ i, xmin < xmax (grp i)
  deriv : ∀ i, ∀ x ∈ Icc 0 (xmax (grp i)), HasDerivAt (f i) (f' i x) x
  mono : ∀ i, StrictMonoOn (f i) (Icc 0 (xmax (grp i)))
  conc : ∀ i, StrictConcaveOn ℝ (Icc 0 (xmax (grp i))) (f i)

/-- `φ_i(λ) = max_{x ∈ [xmin, x_i^max]} (f_i(x) - λ x)`. -/
noncomputable def phi (i : ι) (lam : ℝ) : ℝ :=
  sSup ((fun y => f i y - lam * y) '' Icc xmin (xmax (grp i)))

/-- `L_I(λ) = λ B + ∑_{i ∈ I} φ_i(λ)`. -/
noncomputable def Lag (I : Finset ι) (lam : ℝ) : ℝ :=
  lam * B + ∑ i ∈ I, phi grp xmax xmin f i lam

variable {grp xmax xmin B f f'}

lemma Regular.contOn (hR : Regular grp xmax xmin f f') (i : ι) :
    ContinuousOn (f i) (Icc xmin (xmax (grp i))) :=
  fun x hx => (hR.deriv i x ⟨hR.xmin_pos.le.trans hx.1, hx.2⟩).continuousAt.continuousWithinAt

lemma bdd_phi (hR : Regular grp xmax xmin f f') (i : ι) (lam : ℝ) :
    BddAbove ((fun y => f i y - lam * y) '' Icc xmin (xmax (grp i))) :=
  (isCompact_Icc.image_of_continuousOn
    ((hR.contOn i).sub (continuousOn_const.mul continuousOn_id))).bddAbove

lemma le_phi (hR : Regular grp xmax xmin f f') {i : ι} {lam y : ℝ}
    (hy : y ∈ Icc xmin (xmax (grp i))) : f i y - lam * y ≤ phi grp xmax xmin f i lam :=
  le_csSup (bdd_phi hR i lam) ⟨y, hy, rfl⟩

lemma phi_le (hR : Regular grp xmax xmin f f') {i : ι} {lam c : ℝ}
    (h : ∀ y ∈ Icc xmin (xmax (grp i)), f i y - lam * y ≤ c) :
    phi grp xmax xmin f i lam ≤ c :=
  csSup_le ((Set.nonempty_Icc.2 (hR.xmin_lt i).le).image _)
    (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)

/-- Each `φ_i` is non-increasing in `λ`. -/
lemma phi_anti (hR : Regular grp xmax xmin f f') (i : ι) {l1 l2 : ℝ} (h : l1 ≤ l2) :
    phi grp xmax xmin f i l2 ≤ phi grp xmax xmin f i l1 :=
  phi_le hR (fun y hy => by
    have h1 := le_phi hR (lam := l1) hy
    have hy0 : 0 ≤ y := hR.xmin_pos.le.trans hy.1
    have h2 := mul_le_mul_of_nonneg_right h hy0
    linarith)

/-- Weak duality for one allocation. -/
lemma value_le_Lag (hR : Regular grp xmax xmin f f') {I : Finset ι} {x : ι → ℝ}
    (hx : Feasible grp xmax xmin B I x) {lam : ℝ} (hlam : 0 ≤ lam) :
    value f I x ≤ Lag grp xmax xmin B f I lam := by
  unfold value Lag
  have h1 : ∑ i ∈ I, (f i (x i) - lam * x i) ≤ ∑ i ∈ I, phi grp xmax xmin f i lam :=
    sum_le_sum (fun i hi => le_phi hR (hx.1 i hi))
  rw [sum_sub_distrib, ← mul_sum] at h1
  have h2 := mul_le_mul_of_nonneg_left hx.2 hlam
  linarith

lemma bdd_V (hR : Regular grp xmax xmin f f') (I : Finset ι) :
    BddAbove {v | ∃ x, Feasible grp xmax xmin B I x ∧ value f I x = v} :=
  ⟨Lag grp xmax xmin B f I 0, by rintro v ⟨x, hx, rfl⟩; exact value_le_Lag hR hx le_rfl⟩

lemma le_V (hR : Regular grp xmax xmin f f') {I : Finset ι} {x : ι → ℝ}
    (hx : Feasible grp xmax xmin B I x) : value f I x ≤ V grp xmax xmin B f I :=
  le_csSup (bdd_V hR I) ⟨x, hx, rfl⟩

/-- Weak duality: `V(I) ≤ L_I(λ)` for every `λ ≥ 0`. -/
lemma V_le_Lag (hR : Regular grp xmax xmin f f') {I : Finset ι}
    (hI : ∃ x, Feasible grp xmax xmin B I x) {lam : ℝ} (hlam : 0 ≤ lam) :
    V grp xmax xmin B f I ≤ Lag grp xmax xmin B f I lam := by
  unfold V
  apply csSup_le
  · obtain ⟨x, hx⟩ := hI
    exact ⟨_, x, hx, rfl⟩
  · rintro v ⟨x, hx, rfl⟩
    exact value_le_Lag hR hx hlam

/-- `(P_I)` is feasible when `|I| xmin ≤ B`. -/
lemma feasible_of_card (hR : Regular grp xmax xmin f f') {I : Finset ι}
    (h : (I.card : ℝ) * xmin ≤ B) : ∃ x, Feasible grp xmax xmin B I x :=
  ⟨fun _ => xmin, fun i _ => ⟨le_rfl, (hR.xmin_lt i).le⟩, by
    simpa [sum_const, nsmul_eq_mul] using h⟩

/-- An optimal allocation of `(P_I)` exists. It is taken in the box `[xmin, x_i^max]` for all
EVs, which does not change the value or the budget on `I`. -/
lemma exists_opt (hR : Regular grp xmax xmin f f') {I : Finset ι}
    (hI : ∃ x, Feasible grp xmax xmin B I x) :
    ∃ x : ι → ℝ, (∀ i, x i ∈ Icc xmin (xmax (grp i))) ∧ ∑ i ∈ I, x i ≤ B ∧
      ∀ y : ι → ℝ, (∀ i, y i ∈ Icc xmin (xmax (grp i))) → ∑ i ∈ I, y i ≤ B →
        value f I y ≤ value f I x := by
  have hcomp : IsCompact {x : ι → ℝ | (∀ i, x i ∈ Icc xmin (xmax (grp i))) ∧
      ∑ i ∈ I, x i ≤ B} := by
    have h1 : IsCompact (Set.pi univ fun i => Icc xmin (xmax (grp i))) :=
      isCompact_univ_pi (fun i => isCompact_Icc)
    have h2 : IsClosed {x : ι → ℝ | ∑ i ∈ I, x i ≤ B} :=
      isClosed_le (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const
    have : {x : ι → ℝ | (∀ i, x i ∈ Icc xmin (xmax (grp i))) ∧ ∑ i ∈ I, x i ≤ B}
        = (Set.pi univ fun i => Icc xmin (xmax (grp i))) ∩ {x | ∑ i ∈ I, x i ≤ B} := by
      ext x
      exact ⟨fun h => ⟨fun i _ => h.1 i, h.2⟩, fun h => ⟨fun i => h.1 i (Set.mem_univ i), h.2⟩⟩
    rw [this]
    exact h1.inter_right h2
  have hne : {x : ι → ℝ | (∀ i, x i ∈ Icc xmin (xmax (grp i))) ∧
      ∑ i ∈ I, x i ≤ B}.Nonempty := by
    obtain ⟨x0, hx0⟩ := hI
    refine ⟨fun _ => xmin, fun i => ⟨le_rfl, (hR.xmin_lt i).le⟩, ?_⟩
    calc ∑ _i ∈ I, xmin ≤ ∑ i ∈ I, x0 i := sum_le_sum (fun i hi => (hx0.1 i hi).1)
      _ ≤ B := hx0.2
  have hcont : ContinuousOn (value f I) {x : ι → ℝ | (∀ i, x i ∈ Icc xmin (xmax (grp i))) ∧
      ∑ i ∈ I, x i ≤ B} := by
    unfold value
    apply continuousOn_finsetSum
    intro i _
    exact (hR.contOn i).comp (continuous_apply i).continuousOn (fun x hx => hx.1 i)
  obtain ⟨x, hxK, hxmax⟩ := hcomp.exists_isMaxOn hne hcont
  exact ⟨x, hxK.1, hxK.2, fun y hy1 hy2 => hxmax ⟨hy1, hy2⟩⟩

/-- Concavity: `f_i'` does not increase on `[0, x_i^max]`. -/
lemma Regular.deriv_antitone (hR : Regular grp xmax xmin f f') (i : ι) {y z : ℝ}
    (hy : y ∈ Icc 0 (xmax (grp i))) (hz : z ∈ Icc 0 (xmax (grp i))) (hyz : y ≤ z) :
    f' i z ≤ f' i y := by
  have hanti := (hR.conc i).concaveOn.antitoneOn_deriv
    (fun x hx => (hR.deriv i x hx).differentiableAt)
  have h := hanti hy hz hyz
  rwa [(hR.deriv i y hy).deriv, (hR.deriv i z hz).deriv] at h

/-- A strictly increasing differentiable function has a nonnegative derivative. -/
lemma Regular.deriv_nonneg (hR : Regular grp xmax xmin f f') {i : ι} {y : ℝ}
    (hy : y ∈ Ioc 0 (xmax (grp i))) : 0 ≤ f' i y := by
  have hd := (hR.deriv i y ⟨hy.1.le, hy.2⟩).tendsto_slope_zero_left
  apply ge_of_tendsto hd
  filter_upwards [Ioo_mem_nhdsLT (show -y < 0 by linarith [hy.1])] with t ht
  have hmem : y + t ∈ Icc 0 (xmax (grp i)) := ⟨by linarith [ht.1], by linarith [ht.2, hy.2]⟩
  have hle : f i (y + t) ≤ f i y :=
    (hR.mono i).monotoneOn hmem ⟨hy.1.le, hy.2⟩ (by linarith [ht.2])
  rw [smul_eq_mul]
  have h1 : t⁻¹ ≤ 0 := inv_nonpos.2 ht.2.le
  have h2 : f i (y + t) - f i y ≤ 0 := sub_nonpos.2 hle
  nlinarith

/-- Changing an allocation at two EVs changes a sum over `s` by the two differences. -/
lemma sum_two_point {s : Finset ι} {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (u v : ι → ℝ) (hrest : ∀ r, r ≠ i → r ≠ j → u r = v r) :
    ∑ r ∈ s, u r = ∑ r ∈ s, v r + (u i - v i) + (u j - v j) := by
  have h := sum_eq_add (s := s) (f := fun r => u r - v r) i j hij
    (fun r _ hr => by simp [hrest r hr.1 hr.2]) (fun h => absurd hi h) (fun h => absurd hj h)
  rw [sum_sub_distrib] at h
  linarith

/-- Changing an allocation at one EV changes a sum over `s` by the difference. -/
lemma sum_one_point {s : Finset ι} {i : ι} (hi : i ∈ s) (u v : ι → ℝ)
    (hrest : ∀ r, r ≠ i → u r = v r) :
    ∑ r ∈ s, u r = ∑ r ∈ s, v r + (u i - v i) := by
  have h := sum_eq_single (s := s) (f := fun r => u r - v r) i
    (fun r _ hr => by simp [hrest r hr]) (fun h => absurd hi h)
  rw [sum_sub_distrib] at h
  linarith

/-- **Strong duality for `(P_I)`.** If `(P_I)` is feasible, there is `λ ≥ 0` with
`L_I(λ) ≤ V(I)`; with weak duality, `V(I) = L_I(λ) = min_{μ ≥ 0} L_I(μ)`. This `λ` is at most
any `L ≥ 0` with `f_i'(xmin) ≤ L` for every EV of `I`. -/
theorem strong_duality (hR : Regular grp xmax xmin f f') {I : Finset ι}
    (hI : ∃ x, Feasible grp xmax xmin B I x) :
    ∃ lam, 0 ≤ lam ∧ (∀ L, 0 ≤ L → (∀ i ∈ I, f' i xmin ≤ L) → lam ≤ L) ∧
      Lag grp xmax xmin B f I lam ≤ V grp xmax xmin B f I := by
  obtain ⟨x, hxbox, hxB, hxmax⟩ := exists_opt hR hI
  have hxfeas : Feasible grp xmax xmin B I x := ⟨fun i _ => hxbox i, hxB⟩
  have hbox0 : ∀ i, x i ∈ Icc 0 (xmax (grp i)) :=
    fun i => ⟨hR.xmin_pos.le.trans (hxbox i).1, (hxbox i).2⟩
  -- the EVs of `I` below their maximum rate
  set A := I.filter (fun i => x i < xmax (grp i)) with hA
  -- the multiplier: the largest marginal utility over `A` (or `0`)
  obtain ⟨lam, hlam0, hlamA, hlam_le, hlam_empty⟩ : ∃ lam : ℝ, 0 ≤ lam ∧
      (∀ i ∈ A, f' i (x i) ≤ lam) ∧ (∀ c, 0 ≤ c → (∀ i ∈ A, f' i (x i) ≤ c) → lam ≤ c) ∧
      (A = ∅ → lam = 0) := by
    by_cases hne : A.Nonempty
    · refine ⟨max 0 (A.sup' hne (fun i => f' i (x i))), le_max_left _ _,
        fun i hi => le_max_of_le_right (le_sup' (fun i => f' i (x i)) hi),
        fun c hc h => max_le hc (sup'_le hne _ h), fun h => absurd h hne.ne_empty⟩
    · exact ⟨0, le_rfl, fun i hi => absurd ⟨i, hi⟩ hne, fun c hc _ => hc, fun _ => rfl⟩
  -- exchange: shifting power from an EV above `xmin` to an EV below its maximum cannot help
  have hexch : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → xmin < x i → x j < xmax (grp j) →
      f' j (x j) ≤ f' i (x i) := by
    intro i hi j hj hij hxi hxj
    by_contra hcon
    push_neg at hcon
    have hdj : HasDerivAt (fun t => f j (x j + t)) (f' j (x j)) 0 :=
      HasDerivAt.comp_const_add (x j) 0 (by rw [add_zero]; exact hR.deriv j (x j) (hbox0 j))
    have hdi : HasDerivAt (fun t => f i (x i - t)) (-f' i (x i)) 0 :=
      HasDerivAt.comp_const_sub (x i) 0 (by rw [sub_zero]; exact hR.deriv i (x i) (hbox0 i))
    have hd := hdj.add hdi
    have hpos : 0 < f' j (x j) + -f' i (x i) := by linarith
    have hev := hd.tendsto_slope_zero_right.eventually (lt_mem_nhds hpos)
    have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (min (x i - xmin) (xmax (grp j) - x j)) :=
      Ioo_mem_nhdsGT (lt_min (by linarith) (by linarith))
    obtain ⟨t, ht1, ht2⟩ := (hev.and hev2).exists
    simp only [Pi.add_apply, zero_add, add_zero, sub_zero, smul_eq_mul] at ht1
    have ht0 : 0 < t := ht2.1
    have hti : t < x i - xmin := lt_of_lt_of_le ht2.2 (min_le_left _ _)
    have htj : t < xmax (grp j) - x j := lt_of_lt_of_le ht2.2 (min_le_right _ _)
    have hgain : 0 < (f j (x j + t) + f i (x i - t)) - (f j (x j) + f i (x i)) := by
      have h := mul_pos ht0 ht1
      rw [← mul_assoc, mul_inv_cancel₀ ht0.ne', one_mul] at h
      linarith
    set y := Function.update (Function.update x j (x j + t)) i (x i - t) with hy
    have hyi : y i = x i - t := by simp [hy]
    have hyj : y j = x j + t := by simp [hy, Function.update_of_ne (Ne.symm hij)]
    have hyr : ∀ r, r ≠ i → r ≠ j → y r = x r := by
      intro r hri hrj
      simp [hy, Function.update_of_ne hri, Function.update_of_ne hrj]
    have hybox : ∀ r, y r ∈ Icc xmin (xmax (grp r)) := by
      intro r
      by_cases hri : r = i
      · rw [hri, hyi]
        exact ⟨by linarith, by linarith [(hxbox i).2]⟩
      by_cases hrj : r = j
      · rw [hrj, hyj]
        exact ⟨by linarith [(hxbox j).1], by linarith⟩
      rw [hyr r hri hrj]
      exact hxbox r
    have hysum : ∑ r ∈ I, y r = ∑ r ∈ I, x r := by
      rw [sum_two_point hi hj hij y x hyr, hyi, hyj]
      ring
    have hyval : value f I y = value f I x + ((f j (x j + t) + f i (x i - t)) -
        (f j (x j) + f i (x i))) := by
      unfold value
      rw [sum_two_point hi hj hij (fun r => f r (y r)) (fun r => f r (x r))
        (fun r hri hrj => by simp only [hyr r hri hrj]), hyi, hyj]
      ring
    have := hxmax y hybox (hysum ▸ hxB)
    linarith
  -- if the budget is not used up, every EV of `I` is at its maximum rate
  have hslack : ∑ i ∈ I, x i < B → A = ∅ := by
    intro hlt
    by_contra hne
    obtain ⟨i, hiA⟩ := Finset.nonempty_iff_ne_empty.2 hne
    rw [hA, mem_filter] at hiA
    set t := min (xmax (grp i) - x i) (B - ∑ r ∈ I, x r) with ht
    have ht0 : 0 < t := lt_min (by linarith [hiA.2]) (by linarith)
    have htle1 : t ≤ xmax (grp i) - x i := min_le_left _ _
    have htle2 : t ≤ B - ∑ r ∈ I, x r := min_le_right _ _
    set y := Function.update x i (x i + t) with hy
    have hyi : y i = x i + t := by simp [hy]
    have hyr : ∀ r, r ≠ i → y r = x r := fun r hr => by simp [hy, Function.update_of_ne hr]
    have hybox : ∀ r, y r ∈ Icc xmin (xmax (grp r)) := by
      intro r
      by_cases hri : r = i
      · rw [hri, hyi]
        exact ⟨by linarith [(hxbox i).1], by linarith⟩
      · rw [hyr r hri]
        exact hxbox r
    have hysum : ∑ r ∈ I, y r ≤ B := by
      rw [sum_one_point hiA.1 y x hyr, hyi]
      linarith
    have hyval : value f I y = value f I x + (f i (x i + t) - f i (x i)) := by
      unfold value
      rw [sum_one_point hiA.1 (fun r => f r (y r)) (fun r => f r (x r))
        (fun r hr => by simp only [hyr r hr]), hyi]
    have hmem : x i + t ∈ Icc 0 (xmax (grp i)) := ⟨by linarith [(hbox0 i).1], by linarith⟩
    have hinc : f i (x i) < f i (x i + t) := hR.mono i (hbox0 i) hmem (by linarith)
    have := hxmax y hybox hysum
    linarith
  -- every EV of `I` maximizes `f_i(y) - λ y` on its interval
  have hpoint : ∀ i ∈ I, ∀ y ∈ Icc xmin (xmax (grp i)),
      f i y - lam * y ≤ f i (x i) - lam * x i := by
    intro i hi
    apply foc_max (hR.conc i).concaveOn hR.xmin_pos.le (hR.deriv i) (hxbox i)
    · intro hlt
      exact hlamA i (by rw [hA, mem_filter]; exact ⟨hi, hlt⟩)
    · intro hgt
      apply hlam_le
      · exact hR.deriv_nonneg ⟨hR.xmin_pos.trans hgt, (hxbox i).2⟩
      · intro j hjA
        rw [hA, mem_filter] at hjA
        by_cases hji : j = i
        · rw [hji]
        · exact hexch i hi j hjA.1 (Ne.symm hji) hgt hjA.2
  -- complementary slackness
  have hcs : lam * (B - ∑ i ∈ I, x i) = 0 := by
    rcases lt_or_eq_of_le hxB with hlt | heq
    · rw [hlam_empty (hslack hlt), zero_mul]
    · rw [heq, sub_self, mul_zero]
  have hbr : ∀ L, 0 ≤ L → (∀ i ∈ I, f' i xmin ≤ L) → lam ≤ L := by
    intro L hL0 hL
    apply hlam_le L hL0
    intro i hiA
    rw [hA, mem_filter] at hiA
    exact (hR.deriv_antitone i ⟨hR.xmin_pos.le, (hR.xmin_lt i).le⟩ (hbox0 i) (hxbox i).1).trans
      (hL i hiA.1)
  refine ⟨lam, hlam0, hbr, ?_⟩
  have h1 : ∑ i ∈ I, phi grp xmax xmin f i lam ≤ ∑ i ∈ I, (f i (x i) - lam * x i) :=
    sum_le_sum (fun i hi => phi_le hR (hpoint i hi))
  rw [sum_sub_distrib, ← mul_sum] at h1
  have h2 := le_V hR hxfeas
  unfold value at h2
  unfold Lag
  nlinarith

/-- `n ≤ n^max = ⌊B / xmin⌋` exactly when `n xmin ≤ B`. -/
lemma le_nmax_iff (hxmin : 0 < xmin) (hB : 0 ≤ B) (n : ℕ) :
    n ≤ ⌊B / xmin⌋₊ ↔ (n : ℝ) * xmin ≤ B := by
  rw [Nat.le_floor_iff (div_nonneg hB hxmin.le), le_div_iff₀ hxmin]

/-- Lemma 1 for `λ₂ ≤ λ₁` (the "without loss of generality" case of the paper). -/
lemma submod_aux (hR : Regular grp xmax xmin f f') (I1 I2 : Finset ι)
    (hcard : ((I1 ∪ I2).card : ℝ) * xmin ≤ B) {l1 l2 : ℝ} (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2)
    (h12 : l2 ≤ l1)
    (hV1 : V grp xmax xmin B f I1 = Lag grp xmax xmin B f I1 l1)
    (hV2 : V grp xmax xmin B f I2 = Lag grp xmax xmin B f I2 l2) :
    V grp xmax xmin B f (I1 ∪ I2) + V grp xmax xmin B f (I1 ∩ I2) ≤
      V grp xmax xmin B f I1 + V grp xmax xmin B f I2 := by
  have hsub : ∀ J : Finset ι, J ⊆ I1 ∪ I2 → (J.card : ℝ) * xmin ≤ B := fun J hJ =>
    le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (card_le_card hJ)) hR.xmin_pos.le) hcard
  have hU := V_le_Lag hR (feasible_of_card hR hcard) hl1
  have hN := V_le_Lag hR (feasible_of_card hR (hsub (I1 ∩ I2) (inter_subset_left.trans
    subset_union_left))) hl2
  have hsplitU : ∑ i ∈ I1 ∪ I2, phi grp xmax xmin f i l1 =
      ∑ i ∈ I1, phi grp xmax xmin f i l1 + ∑ i ∈ I2 \ I1, phi grp xmax xmin f i l1 := by
    rw [← sum_sdiff (subset_union_left : I1 ⊆ I1 ∪ I2), Finset.union_sdiff_left, add_comm]
  have hsplit2 : ∑ i ∈ I2, phi grp xmax xmin f i l2 =
      ∑ i ∈ I1 ∩ I2, phi grp xmax xmin f i l2 + ∑ i ∈ I2 \ I1, phi grp xmax xmin f i l2 := by
    rw [← sum_sdiff (inter_subset_right : I1 ∩ I2 ⊆ I2), add_comm]
    congr 2
    ext r
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hmono : ∑ i ∈ I2 \ I1, phi grp xmax xmin f i l1 ≤
      ∑ i ∈ I2 \ I1, phi grp xmax xmin f i l2 :=
    sum_le_sum (fun i _ => phi_anti hR i h12)
  rw [hV1, hV2]
  unfold Lag at hU hN ⊢
  rw [hsplitU] at hU
  rw [hsplit2]
  linarith

/-- **Lemma 1 (lem:submod).** If `|I₁ ∪ I₂| ≤ n^max`, then
`V(I₁ ∪ I₂) + V(I₁ ∩ I₂) ≤ V(I₁) + V(I₂)`. -/
theorem submod (hR : Regular grp xmax xmin f f') (hB : 0 ≤ B) (I1 I2 : Finset ι)
    (hcard : (I1 ∪ I2).card ≤ ⌊B / xmin⌋₊) :
    V grp xmax xmin B f (I1 ∪ I2) + V grp xmax xmin B f (I1 ∩ I2) ≤
      V grp xmax xmin B f I1 + V grp xmax xmin B f I2 := by
  have hc := (le_nmax_iff hR.xmin_pos hB _).1 hcard
  have hsub : ∀ J : Finset ι, J ⊆ I1 ∪ I2 → (J.card : ℝ) * xmin ≤ B := fun J hJ =>
    le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (card_le_card hJ)) hR.xmin_pos.le) hc
  have hdual : ∀ J : Finset ι, J ⊆ I1 ∪ I2 →
      ∃ l, 0 ≤ l ∧ V grp xmax xmin B f J = Lag grp xmax xmin B f J l := by
    intro J hJ
    have hJf := feasible_of_card hR (hsub J hJ)
    obtain ⟨l, hl, _, hle⟩ := strong_duality hR hJf
    exact ⟨l, hl, le_antisymm (V_le_Lag hR hJf hl) hle⟩
  obtain ⟨l1, hl1, hV1⟩ := hdual I1 subset_union_left
  obtain ⟨l2, hl2, hV2⟩ := hdual I2 subset_union_right
  rcases le_total l2 l1 with h | h
  · exact submod_aux hR I1 I2 hc hl1 hl2 h hV1 hV2
  · have := submod_aux hR I2 I1 (by rwa [Finset.union_comm]) hl2 hl1 h hV2 hV1
    rw [Finset.union_comm, Finset.inter_comm] at this
    linarith

/-- **Proposition 1, the multiplier bracket `[0, L]`.** Let `|I| xmin ≤ B` and `L ≥ 0` with
`L ≥ λ^th_i = f_i(xmin)/xmin` for every EV of `I` (as for `L = max_i λ^th_i`).
(a) At `λ = L`, every EV of `I` is at `xmin` in any maximizer of `f_i(y) - L y` on its interval,
so the aggregate of `(P_I)` at `λ = L` is `|I| xmin ≤ B`.
(b) `(P_I)` has an optimal multiplier in `[0, L]`: `V(I) = L_I(λ) = min_{μ ≥ 0} L_I(μ)` for some
`λ ∈ [0, L]`. -/
theorem multiplier_bracket (hR : Regular grp xmax xmin f f') (hf0 : ∀ i, f i 0 = 0)
    {I : Finset ι} (hI : (I.card : ℝ) * xmin ≤ B) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ i ∈ I, f i xmin / xmin ≤ L) :
    (∀ x : ι → ℝ, (∀ i ∈ I, x i ∈ Icc xmin (xmax (grp i)) ∧
        ∀ y ∈ Icc xmin (xmax (grp i)), f i y - L * y ≤ f i (x i) - L * x i) →
      ∑ i ∈ I, x i = I.card * xmin ∧ ∑ i ∈ I, x i ≤ B) ∧
    ∃ lam, 0 ≤ lam ∧ lam ≤ L ∧ V grp xmax xmin B f I = Lag grp xmax xmin B f I lam ∧
      ∀ μ, 0 ≤ μ → Lag grp xmax xmin B f I lam ≤ Lag grp xmax xmin B f I μ := by
  have hfeas := feasible_of_card hR hI
  constructor
  · intro x hx
    have hxi : ∀ i ∈ I, x i = xmin := by
      intro i hi
      by_contra hne
      have hmem0 : xmin ∈ Icc 0 (xmax (grp i)) := ⟨hR.xmin_pos.le, (hR.xmin_lt i).le⟩
      have h1 := xmin_unique_max (f' := f' i) (hR.conc i) (hf0 i) hR.xmin_pos (hR.xmin_lt i).le
        (hR.deriv i xmin hmem0) (hL i hi) (x i) (hx i hi).1 hne
      have h2 := (hx i hi).2 xmin ⟨le_rfl, (hR.xmin_lt i).le⟩
      linarith
    have hsum : ∑ i ∈ I, x i = I.card * xmin := by
      rw [sum_congr rfl hxi, sum_const, nsmul_eq_mul]
    exact ⟨hsum, by rw [hsum]; exact hI⟩
  · have hf'L : ∀ i ∈ I, f' i xmin ≤ L := by
      intro i hi
      have hmem0 : xmin ∈ Icc 0 (xmax (grp i)) := ⟨hR.xmin_pos.le, (hR.xmin_lt i).le⟩
      exact (lambda_th_gt (f' := f' i) (hR.conc i) (hf0 i) hR.xmin_pos (hR.xmin_lt i).le
        (hR.deriv i xmin hmem0)).le.trans (hL i hi)
    obtain ⟨lam, hlam0, hbr, hle⟩ := strong_duality hR hfeas
    have hge : ∀ μ, 0 ≤ μ → V grp xmax xmin B f I ≤ Lag grp xmax xmin B f I μ :=
      fun μ hμ => V_le_Lag hR hfeas hμ
    exact ⟨lam, hlam0, hbr L hL0 hf'L, le_antisymm (hge lam hlam0) hle,
      fun μ hμ => hle.trans (hge μ hμ)⟩

end BIC
