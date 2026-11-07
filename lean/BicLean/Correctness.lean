import BicLean.Diminishing
import BicLean.Choose
import BicLean.Everett

/-!
# Theorem 4 of the BIC paper (correctness of BIC), for `K = 2` groups

Exact arithmetic: the tolerances `δ, ε` of the bisections are not modelled. The fast-path part of
Theorem 4 is `fast_path` in `Everett.lean`. This file proves the choosing-phase part: the
allocation that BIC returns after the choosing phase (an optimal solution of `(P_{I*_{c*}})`, and
zero for every other EV) is a global maximizer of (P).
-/

open Finset Set

namespace BIC

variable {ι κ : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq κ] [Fintype κ]
variable {grp : ι → κ} {xmax : κ → ℝ} {xmin B : ℝ} {f f' : ι → ℝ → ℝ}

/-- Feasibility for (P): `x_i ∈ R_i = {0} ∪ [xmin, x_i^max]` and `∑ x_i ≤ B`. -/
def FeasibleP (grp : ι → κ) (xmax : κ → ℝ) (xmin B : ℝ) (x : ι → ℝ) : Prop :=
  (∀ i, x i ∈ admissible xmin (xmax (grp i))) ∧ ∑ i, x i ≤ B

/-- The optimal value of `(P_I)` is attained. -/
lemma exists_attain (hR : Regular grp xmax xmin f f') {I : Finset ι}
    (hI : ∃ x, Feasible grp xmax xmin B I x) :
    ∃ x, Feasible grp xmax xmin B I x ∧ value f I x = V grp xmax xmin B f I := by
  obtain ⟨x, hbox, hB', hmax⟩ := exists_opt hR hI
  have hfx : Feasible grp xmax xmin B I x := ⟨fun i _ => hbox i, hB'⟩
  refine ⟨x, hfx, le_antisymm (le_V hR hfx) ?_⟩
  unfold V
  refine csSup_le ⟨_, x, hfx, rfl⟩ ?_
  rintro v ⟨y, hy, rfl⟩
  let y' : ι → ℝ := fun i => if i ∈ I then y i else xmin
  have hy'box : ∀ i, y' i ∈ Icc xmin (xmax (grp i)) := by
    intro i
    by_cases hi : i ∈ I
    · simp only [y', if_pos hi]
      exact hy.1 i hi
    · simp only [y', if_neg hi]
      exact ⟨le_rfl, (hR.xmin_lt i).le⟩
  have hsum : ∑ i ∈ I, y' i = ∑ i ∈ I, y i := sum_congr rfl (fun i hi => by simp [y', hi])
  have hval : value f I y' = value f I y := sum_congr rfl (fun i hi => by simp [y', hi])
  rw [← hval]
  exact hmax y' hy'box (hsum ▸ hy.2)

/-- Decomposition (eq:decomposition) with Theorem 2: the objective of any feasible allocation of
(P) is at most `V_c` for some `c ∈ 𝒞` (the cardinality vector of its on-set). -/
theorem objective_le_Vc (hR : Regular grp xmax xmin f f') (hP : PriorityOrder grp xmax xmin f)
    (hB : 0 ≤ B) (hf0 : ∀ i, f i 0 = 0) {y : ι → ℝ} (hy : FeasibleP grp xmax xmin B y) :
    ∃ c, InC grp xmin B c ∧ ∑ i, f i (y i) ≤ Vc grp xmax xmin B f c := by
  -- the on-set of `y`
  have hyI : ∀ i ∈ univ.filter (fun i => y i ≠ 0), y i ∈ Icc xmin (xmax (grp i)) := by
    intro i hi
    rcases hy.1 i with h | h
    · exact absurd (Set.mem_singleton_iff.1 h) (mem_filter.1 hi).2
    · exact h
  have hsum : ∑ i ∈ univ.filter (fun i => y i ≠ 0), y i = ∑ i, y i := sum_filter_ne_zero univ
  have hfeasI : Feasible grp xmax xmin B (univ.filter (fun i => y i ≠ 0)) y :=
    ⟨hyI, hsum ▸ hy.2⟩
  have hval : value f (univ.filter (fun i => y i ≠ 0)) y = ∑ i, f i (y i) := by
    unfold value
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    split_ifs with h
    · rfl
    · push_neg at h
      rw [h, hf0]
  have hcn : ∀ k, count grp (univ.filter (fun i => y i ≠ 0)) k ≤ (group grp k).card :=
    fun k => card_le_card (filter_subset_filter _ (subset_univ _))
  have hcard : (univ.filter (fun i => y i ≠ 0)).card ≤ ⌊B / xmin⌋₊ := by
    rw [le_nmax_iff hR.xmin_pos hB]
    calc ((univ.filter (fun i => y i ≠ 0)).card : ℝ) * xmin
        = ∑ _i ∈ univ.filter (fun i => y i ≠ 0), xmin := by simp [sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ univ.filter (fun i => y i ≠ 0), y i := sum_le_sum (fun i hi => (hyI i hi).1)
      _ ≤ B := hfeasI.2
  refine ⟨fun k => count grp (univ.filter (fun i => y i ≠ 0)) k, ⟨hcn, ?_⟩, ?_⟩
  · rw [← card_eq_sum_count (grp := grp)]
    exact hcard
  · rw [← hval]
    exact (le_V hR hfeasI).trans (prefix_theorem grp xmax xmin B f hP (fun i => hR.contOn i) _
      hcn _ (fun k => rfl) ⟨y, hfeasI⟩)

/-- **Theorem 4 (correctness of BIC), choosing-phase part, `K = 2`.** Let `c*` be the output of
Choose (Algorithm 1) on `V_{(c1,c2)}`, and `I* = I*_{c*}`. The optimal value of `(P_{I*})` is
attained, and for any optimal solution `xr` of `(P_{I*})`, the allocation that BIC returns
(`xr` on `I*`, zero elsewhere) is feasible for (P) and a global maximizer of (P). -/
theorem theorem4 {grp : ι → Fin 2} {xmax : Fin 2 → ℝ}
    (hR : Regular grp xmax xmin f f') (hP : PriorityOrder grp xmax xmin f)
    (hB : 0 ≤ B) (hf0 : ∀ i, f i 0 = 0) :
    let cs := choose (fun c1 c2 => Vc grp xmax xmin B f ![c1, c2])
      (group grp 0).card (group grp 1).card ⌊B / xmin⌋₊
    let Is := prefixSet grp ![cs.1, cs.2]
    (∃ xr, Feasible grp xmax xmin B Is xr ∧ value f Is xr = V grp xmax xmin B f Is) ∧
    ∀ xr, Feasible grp xmax xmin B Is xr → value f Is xr = V grp xmax xmin B f Is →
      FeasibleP grp xmax xmin B (fun i => if i ∈ Is then xr i else 0) ∧
      ∀ y, FeasibleP grp xmax xmin B y →
        ∑ i, f i (y i) ≤ ∑ i, f i (if i ∈ Is then xr i else 0) := by
  intro cs Is
  have hF2 : ∀ c1 c2, F2 (group grp 0).card (group grp 1).card ⌊B / xmin⌋₊ c1 c2 ↔
      InC grp xmin B ![c1, c2] := by
    intro c1 c2
    simp [F2, InC, Fin.forall_fin_two, Fin.sum_univ_two, and_assoc]
  have hupd : ∀ a b q : ℕ, Function.update ![a, b] (1 : Fin 2) q = ![a, q] := by
    intro a b q
    funext m
    fin_cases m <;> simp
  have hbest : ∀ c1 c2, bestCount grp xmax xmin B f ![c1, c2] 1 =
      bestCount grp xmax xmin B f ![c1, 0] 1 := by
    intro c1 c2
    unfold bestCount
    simp only [hupd]
  -- the best count `ĉ₂(c1)` is a maximizer
  have hspec : ∀ c1, F2 (group grp 0).card (group grp 1).card ⌊B / xmin⌋₊ c1 0 →
      F2 (group grp 0).card (group grp 1).card ⌊B / xmin⌋₊ c1
        (bestCount grp xmax xmin B f ![c1, 0] 1) ∧
      ∀ c2, F2 (group grp 0).card (group grp 1).card ⌊B / xmin⌋₊ c1 c2 →
        Vc grp xmax xmin B f ![c1, c2] ≤
          Vc grp xmax xmin B f ![c1, bestCount grp xmax xmin B f ![c1, 0] 1] := by
    intro c1 h0
    obtain ⟨h1, h2, _⟩ := bestCount_spec hR hP hB (1 : Fin 2) ((hF2 c1 0).1 h0)
    simp only [hupd] at h1 h2
    exact ⟨(hF2 _ _).2 h1, fun c2 hc2 => h2 c2 ((hF2 _ _).1 hc2)⟩
  -- Theorem 3(a) for group 2
  have ha : ∀ c1 c2, F2 (group grp 0).card (group grp 1).card ⌊B / xmin⌋₊ c1 c2 → 1 ≤ c2 →
      (Vc grp xmax xmin B f ![c1, c2 - 1] < Vc grp xmax xmin B f ![c1, c2] ↔
        c2 ≤ bestCount grp xmax xmin B f ![c1, 0] 1) := by
    intro c1 c2 hF hc2
    have h := theorem3a hR hP hB (k := (1 : Fin 2)) ((hF2 c1 c2).1 hF) (by simpa using hc2)
    have e1 : ![c1, c2] - Pi.single (1 : Fin 2) 1 = ![c1, c2 - 1] := by
      funext m
      fin_cases m <;> simp
    rw [e1, hbest] at h
    simpa using h
  -- Theorem 3(b) with `l` = group 1, `k` = group 2
  have hb : ∀ c1, F2 (group grp 0).card (group grp 1).card ⌊B / xmin⌋₊ (c1 + 1) 0 →
      bestCount grp xmax xmin B f ![c1 + 1, 0] 1 ≤ bestCount grp xmax xmin B f ![c1, 0] 1 := by
    intro c1 hF
    have hc : InC grp xmin B ![c1, 0] :=
      (hF2 c1 0).1 ⟨by have := hF.1; omega, hF.2.1, by have := hF.2.2; omega⟩
    have e : ![c1, 0] + Pi.single (0 : Fin 2) 1 = ![c1 + 1, 0] := by
      funext m
      fin_cases m <;> simp
    have h := theorem3b hR hP hB (k := (1 : Fin 2)) (l := 0) (by decide) hc
      (by rw [e]; exact (hF2 _ _).1 hF)
    rwa [e] at h
  obtain ⟨hFcs, hmaxcs⟩ := choose_correct (W := fun c1 c2 => Vc grp xmax xmin B f ![c1, c2])
    (fun c1 => bestCount grp xmax xmin B f ![c1, 0] 1) hspec ha hb
  have hIsC : InC grp xmin B ![cs.1, cs.2] := (hF2 _ _).1 hFcs
  -- `c*` maximizes `V_c` over `𝒞`
  have hglob : ∀ c, InC grp xmin B c →
      Vc grp xmax xmin B f c ≤ Vc grp xmax xmin B f ![cs.1, cs.2] := by
    intro c hc
    have e : c = ![c 0, c 1] := by
      funext m
      fin_cases m <;> rfl
    have hc' : InC grp xmin B ![c 0, c 1] := by rw [← e]; exact hc
    have := hmaxcs (c 0) (c 1) ((hF2 _ _).2 hc')
    rwa [← e] at this
  have hIsfeas := feasible_of_card hR ((le_nmax_iff hR.xmin_pos hB _).1
    (by rw [card_prefixSet hIsC.1]; exact hIsC.2))
  refine ⟨exists_attain hR hIsfeas, ?_⟩
  intro xr hxr hval
  have hext_val : ∑ i, f i (if i ∈ Is then xr i else 0) = value f Is xr := by
    unfold value
    rw [← sum_subset (subset_univ Is) (fun i _ hi => by rw [if_neg hi, hf0])]
    exact sum_congr rfl (fun i hi => by rw [if_pos hi])
  have hext_sum : ∑ i, (if i ∈ Is then xr i else 0) = ∑ i ∈ Is, xr i := by
    rw [← sum_subset (subset_univ Is) (fun i _ hi => by rw [if_neg hi])]
    exact sum_congr rfl (fun i hi => by rw [if_pos hi])
  refine ⟨⟨fun i => ?_, by rw [hext_sum]; exact hxr.2⟩, fun y hy => ?_⟩
  · by_cases hi : i ∈ Is
    · simp only [admissible, Set.mem_union, Set.mem_singleton_iff, if_pos hi]
      exact Or.inr (hxr.1 i hi)
    · simp only [admissible, Set.mem_union, Set.mem_singleton_iff, if_neg hi]
      exact Or.inl trivial
  · obtain ⟨c, hc, hle⟩ := objective_le_Vc hR hP hB hf0 hy
    rw [hext_val, hval]
    exact hle.trans (hglob c hc)

/-! ## (eq:decomposition) as an equality -/

/-- The optimum of `(P_I)`, extended by zero, is a feasible allocation of (P) with value `V(I)`. -/
lemma extend_opt (hR : Regular grp xmax xmin f f') (hf0 : ∀ i, f i 0 = 0) {I : Finset ι}
    (hI : ∃ x, Feasible grp xmax xmin B I x) :
    ∃ y, FeasibleP grp xmax xmin B y ∧ ∑ i, f i (y i) = V grp xmax xmin B f I := by
  obtain ⟨xr, hxr, hval⟩ := exists_attain hR hI
  have hext_val : ∑ i, f i (if i ∈ I then xr i else 0) = value f I xr := by
    unfold value
    rw [← sum_subset (subset_univ I) (fun i _ hi => by rw [if_neg hi, hf0])]
    exact sum_congr rfl (fun i hi => by rw [if_pos hi])
  have hext_sum : ∑ i, (if i ∈ I then xr i else 0) = ∑ i ∈ I, xr i := by
    rw [← sum_subset (subset_univ I) (fun i _ hi => by rw [if_neg hi])]
    exact sum_congr rfl (fun i hi => by rw [if_pos hi])
  refine ⟨fun i => if i ∈ I then xr i else 0, ⟨fun i => ?_, ?_⟩, ?_⟩
  · by_cases hi : i ∈ I
    · simp only [admissible, Set.mem_union, Set.mem_singleton_iff, if_pos hi]
      exact Or.inr (hxr.1 i hi)
    · simp only [admissible, Set.mem_union, Set.mem_singleton_iff, if_neg hi]
      exact Or.inl trivial
  · show ∑ i, (if i ∈ I then xr i else 0) ≤ B
    rw [hext_sum]
    exact hxr.2
  · show ∑ i, f i (if i ∈ I then xr i else 0) = V grp xmax xmin B f I
    rw [hext_val, hval]

/-- **(eq:decomposition).** Some `c ∈ 𝒞` maximizes `V_c` over `𝒞`, and the optimal value of (P)
equals `V_c` for it: `V_c` is attained by a feasible allocation of (P) and bounds the objective of
every feasible allocation. -/
theorem decomposition (hR : Regular grp xmax xmin f f') (hP : PriorityOrder grp xmax xmin f)
    (hB : 0 ≤ B) (hf0 : ∀ i, f i 0 = 0) :
    ∃ c, InC grp xmin B c ∧ (∀ c', InC grp xmin B c' → Vc grp xmax xmin B f c' ≤
        Vc grp xmax xmin B f c) ∧
      IsGreatest {v | ∃ y, FeasibleP grp xmax xmin B y ∧ ∑ i, f i (y i) = v}
        (Vc grp xmax xmin B f c) := by
  classical
  obtain ⟨c, hcmem, hcmax⟩ := Finset.exists_max_image
    ((Fintype.piFinset fun k => range ((group grp k).card + 1)).filter
      (fun c => InC grp xmin B c)) (Vc grp xmax xmin B f)
      ⟨0, mem_filter.2 ⟨Fintype.mem_piFinset.2 (fun k => Finset.mem_range.2 (Nat.succ_pos _)),
        fun k => Nat.zero_le _, by simp⟩⟩
  have hmemC : ∀ c', InC grp xmin B c' → c' ∈ (Fintype.piFinset fun k =>
      range ((group grp k).card + 1)).filter (fun c => InC grp xmin B c) := by
    intro c' hc'
    simp only [mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    exact ⟨fun k => Nat.lt_succ_of_le (hc'.1 k), hc'⟩
  have hcC : InC grp xmin B c := (mem_filter.1 hcmem).2
  refine ⟨c, hcC, fun c' hc' => hcmax c' (hmemC c' hc'), ?_⟩
  constructor
  · exact extend_opt hR hf0 (feasible_of_card hR ((le_nmax_iff hR.xmin_pos hB _).1
      (by rw [card_prefixSet hcC.1]; exact hcC.2)))
  · rintro v ⟨y, hy, rfl⟩
    obtain ⟨c', hc', hle⟩ := objective_le_Vc hR hP hB hf0 hy
    exact hle.trans (hcmax c' (hmemC c' hc'))

/-! ## The bisection phase: the selector of Algorithm 2, Theorem 1 and the fast-path -/

/-- The allocation `x(λ)` computed in the bisection loop of Algorithm 2: the closed form (chi)
with the projection `[(f_i')⁻¹(λ)]_{xmin}^{x_i^max}`. -/
noncomputable def xsel (grp : ι → κ) (xmax : κ → ℝ) (xmin : ℝ) (f f' : ι → ℝ → ℝ) (lam : ℝ)
    (i : ι) : ℝ :=
  chi (f i) xmin lam (proj (f' i) xmin (xmax (grp i)) lam)

/-- Each `x_i(λ)` of Algorithm 2 is admissible and maximizes `f_i(y) - λ y` over `R_i`
(chi_argmax). Uses continuity of `f_i'` (Assumption 1) for the existence of `(f_i')⁻¹`. -/
lemma xsel_max (hR : Regular grp xmax xmin f f') (hf0 : ∀ i, f i 0 = 0)
    (hcont' : ∀ i, ContinuousOn (f' i) (Icc 0 (xmax (grp i)))) (lam : ℝ) (i : ι) :
    xsel grp xmax xmin f f' lam i ∈ admissible xmin (xmax (grp i)) ∧
    ∀ y ∈ admissible xmin (xmax (grp i)),
      f i y - lam * y ≤ f i (xsel grp xmax xmin f f' lam i) - lam * xsel grp xmax xmin f f' lam i := by
  obtain ⟨h1, h2⟩ := selector_max (hR.conc i).concaveOn (hf0 i) hR.xmin_pos (hR.xmin_lt i).le
    (hR.deriv i) (hcont' i) lam
  unfold xsel
  refine ⟨?_, fun y hy => h2 y ?_⟩
  · simp only [admissible, Set.mem_union, Set.mem_singleton_iff]
    exact h1
  · simp only [admissible, Set.mem_union, Set.mem_singleton_iff] at hy
    exact hy

/-- **Theorem 1 for Algorithm 2's allocation.** If `λ ≥ 0` and `S(λ) = ∑ x_i(λ) = B`, then
`x(λ)` is feasible for (P) and a global maximizer of (P). -/
theorem theorem1_bic (hR : Regular grp xmax xmin f f') (hf0 : ∀ i, f i 0 = 0)
    (hcont' : ∀ i, ContinuousOn (f' i) (Icc 0 (xmax (grp i)))) {lam : ℝ} (hlam : 0 ≤ lam)
    (hS : ∑ i, xsel grp xmax xmin f f' lam i = B) :
    FeasibleP grp xmax xmin B (xsel grp xmax xmin f f' lam) ∧
    ∀ y, FeasibleP grp xmax xmin B y → ∑ i, f i (y i) ≤ ∑ i, f i (xsel grp xmax xmin f f' lam i) :=
  ⟨⟨fun i => (xsel_max hR hf0 hcont' lam i).1, hS.le⟩, fun y hy =>
    everett (fun i => admissible xmin (xmax (grp i))) f B lam hlam _
      (fun i => (xsel_max hR hf0 hcont' lam i).2) hS y hy.1 hy.2⟩

/-- **Fast-path of Algorithm 2 (Theorem 4).** If `λ ≥ 0` and `B - δ ≤ S(λ) ≤ B`, then `x(λ)` is
feasible for (P) and its objective is at most `λ δ` below that of any feasible allocation. -/
theorem fast_path_bic (hR : Regular grp xmax xmin f f') (hf0 : ∀ i, f i 0 = 0)
    (hcont' : ∀ i, ContinuousOn (f' i) (Icc 0 (xmax (grp i)))) {lam δ : ℝ} (hlam : 0 ≤ lam)
    (hlo : B - δ ≤ ∑ i, xsel grp xmax xmin f f' lam i)
    (hhi : ∑ i, xsel grp xmax xmin f f' lam i ≤ B) :
    FeasibleP grp xmax xmin B (xsel grp xmax xmin f f' lam) ∧
    ∀ y, FeasibleP grp xmax xmin B y →
      ∑ i, f i (y i) ≤ ∑ i, f i (xsel grp xmax xmin f f' lam i) + lam * δ :=
  ⟨⟨fun i => (xsel_max hR hf0 hcont' lam i).1, hhi⟩, fun y hy =>
    fast_path (fun i => admissible xmin (xmax (grp i))) f B lam δ hlam _
      (fun i => (xsel_max hR hf0 hcont' lam i).2) hlo y hy.1 hy.2⟩

end BIC
