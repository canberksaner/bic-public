import BicLean.Duality

/-!
# Lemma 2 (lem:dr) and Theorem 3 (thm:dr) of the BIC paper
-/

open Finset

namespace BIC

/-! ## Diminishing gains on a set of counts `{q | F q}` closed downward -/

section Abstract

variable (h : ℕ → ℝ) (F : ℕ → Prop)

/-- Gains `g(q) = h(q) - h(q-1)` do not increase. -/
def GainsAnti : Prop := ∀ q, 1 ≤ q → F (q + 1) → h (q + 1) - h q ≤ h q - h (q - 1)

variable {h F}

lemma gain_anti (hF : ∀ q q', q' ≤ q → F q → F q') (hc : GainsAnti h F) :
    ∀ r s, 1 ≤ r → r ≤ s → F s → h s - h (s - 1) ≤ h r - h (r - 1) := by
  intro r s hr hrs
  induction s, hrs using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ s hrs ih =>
    intro hs
    have h1 := hc s (by omega) hs
    have h2 := ih (hF _ _ (Nat.le_succ s) hs)
    simp only [Nat.add_sub_cancel] at h1 ⊢
    linarith

lemma lt_of_gain_pos (hF : ∀ q q', q' ≤ q → F q → F q') (hc : GainsAnti h F) {q : ℕ}
    (hq1 : 1 ≤ q) (hFq : F q) (hpos : h (q - 1) < h q) : ∀ r, r < q → h r < h q := by
  have hstep : ∀ s, 1 ≤ s → s ≤ q → h (s - 1) < h s := by
    intro s hs1 hsq
    have := gain_anti hF hc s q hs1 hsq hFq
    linarith
  have key : ∀ k, k < q → h (q - 1 - k) < h q := by
    intro k
    induction k with
    | zero => intro _; simpa using hstep q hq1 le_rfl
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hstep (q - 1 - k) (by omega) (by omega)
      rw [show q - 1 - k - 1 = q - 1 - (k + 1) by omega] at h2
      linarith
  intro r hr
  have := key (q - 1 - r) (by omega)
  rwa [show q - 1 - (q - 1 - r) = r by omega] at this

lemma le_of_gain_nonpos (hF : ∀ q q', q' ≤ q → F q → F q') (hc : GainsAnti h F) {q : ℕ}
    (hq1 : 1 ≤ q) (hnp : h q ≤ h (q - 1)) : ∀ r, q - 1 ≤ r → F r → h r ≤ h (q - 1) := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ r hr ih =>
    intro hFr
    have h1 := ih (hF _ _ (Nat.le_succ r) hFr)
    have h2 := gain_anti hF hc q (r + 1) hq1 (by omega) hFr
    simp only [Nat.add_sub_cancel] at h2
    linarith

/-- With non-increasing gains, and `b` the smallest maximizer of `h` on `{q | F q}`:
the gain of the `q`-th unit is positive exactly when `q ≤ b`. -/
lemma gain_pos_iff (hF : ∀ q q', q' ≤ q → F q → F q') (hc : GainsAnti h F) {b : ℕ}
    (hbmax : ∀ q, F q → h q ≤ h b) (hFb : F b) (hbmin : ∀ q, q < b → h q < h b)
    {q : ℕ} (hq1 : 1 ≤ q) (hFq : F q) : h (q - 1) < h q ↔ q ≤ b := by
  constructor
  · intro hpos
    by_contra hlt
    push_neg at hlt
    have := lt_of_gain_pos hF hc hq1 hFq hpos b hlt
    linarith [hbmax q hFq]
  · intro hqb
    by_contra hnp
    push_neg at hnp
    have h1 := le_of_gain_nonpos hF hc hq1 hnp b (by omega) hFb
    have h2 := hbmin (q - 1) (by omega)
    linarith

/-- If the gains of `h'` are at most those of `h` (on the counts `F'` of `h'`, which are counts
of `h`), the smallest maximizer of `h'` is at most that of `h`. -/
lemma best_anti {h' : ℕ → ℝ} {F' : ℕ → Prop} (hF : ∀ q q', q' ≤ q → F q → F q')
    (hc : GainsAnti h F) (hF'F : ∀ q, F' q → F q)
    (hg : ∀ q, 1 ≤ q → F' q → h' q - h' (q - 1) ≤ h q - h (q - 1))
    {b b' : ℕ} (hbmax : ∀ q, F q → h q ≤ h b) (hFb' : F' b')
    (hbmin' : ∀ q, q < b' → h' q < h' b') : b' ≤ b := by
  by_contra hlt
  push_neg at hlt
  have hb'1 : 1 ≤ b' := by omega
  have hpos' := hbmin' (b' - 1) (by omega)
  have hpos : h (b' - 1) < h b' := by linarith [hg b' hb'1 hFb']
  have := lt_of_gain_pos hF hc hb'1 (hF'F b' hFb') hpos b hlt
  linarith [hbmax b' (hF'F b' hFb')]

/-- The smallest maximizer of `h` over `{q | F q}` (0 if there is none). -/
noncomputable def bestIdx (h : ℕ → ℝ) (F : ℕ → Prop) : ℕ := by
  classical
  exact if hex : ∃ q, F q ∧ ∀ q', F q' → h q' ≤ h q then Nat.find hex else 0

lemma bestIdx_spec (N : ℕ) (hbound : ∀ q, F q → q ≤ N) (hF : ∀ q q', q' ≤ q → F q → F q')
    (h0 : F 0) :
    F (bestIdx h F) ∧ (∀ q, F q → h q ≤ h (bestIdx h F)) ∧
      ∀ q, q < bestIdx h F → h q < h (bestIdx h F) := by
  classical
  have hex : ∃ q, F q ∧ ∀ q', F q' → h q' ≤ h q := by
    obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image ((Finset.range (N + 1)).filter F) h
      ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.succ_pos N), h0⟩⟩
    exact ⟨q, (Finset.mem_filter.1 hq).2, fun q' hq' => hmax q' (Finset.mem_filter.2
      ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (hbound q' hq')), hq'⟩)⟩
  have hb : bestIdx h F = Nat.find hex := by
    unfold bestIdx
    rw [dif_pos hex]
  rw [hb]
  refine ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, fun q hq => ?_⟩
  have hnot := Nat.find_min hex hq
  have hFq : F q := hF _ _ hq.le (Nat.find_spec hex).1
  push_neg at hnot
  obtain ⟨q', hFq', hlt⟩ := hnot hFq
  exact lt_of_lt_of_le hlt ((Nat.find_spec hex).2 q' hFq')

end Abstract

/-! ## The model -/

variable {ι κ : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq κ] [Fintype κ]
variable (grp : ι → κ) (xmax : κ → ℝ) (xmin B : ℝ) (f f' : ι → ℝ → ℝ)

/-- The admissible cardinality vectors `𝒞` (cardinalities):
`c_k ≤ n_k` for all `k`, and `∑ c_k ≤ n^max = ⌊B / xmin⌋`. -/
def InC (c : κ → ℕ) : Prop := (∀ k, c k ≤ (group grp k).card) ∧ ∑ k, c k ≤ ⌊B / xmin⌋₊

/-- `V_c = V(I*_c)` (by Theorem 2). -/
noncomputable def Vc (c : κ → ℕ) : ℝ := V grp xmax xmin B f (prefixSet grp c)

/-- The best count `ĉ_k(c)`: the smallest `q` maximizing `V_{c(k;q)}` over `c(k;q) ∈ 𝒞`. -/
noncomputable def bestCount (c : κ → ℕ) (k : κ) : ℕ :=
  bestIdx (fun q => Vc grp xmax xmin B f (Function.update c k q))
    (fun q => InC grp xmin B (Function.update c k q))

variable {grp xmax xmin B f f'}

lemma InC.mono {c d : κ → ℕ} (hd : InC grp xmin B d) (hcd : ∀ k, c k ≤ d k) :
    InC grp xmin B c :=
  ⟨fun k => (hcd k).trans (hd.1 k), (sum_le_sum (fun k _ => hcd k)).trans hd.2⟩

lemma card_eq_sum_count (I : Finset ι) : I.card = ∑ k, count grp I k :=
  card_eq_sum_card_fiberwise (f := grp) (t := univ) (fun _ _ => mem_univ _)

lemma card_prefixSet {c : κ → ℕ} (hc : ∀ k, c k ≤ (group grp k).card) :
    (prefixSet grp c).card = ∑ k, c k := by
  rw [card_eq_sum_count (grp := grp)]
  exact sum_congr rfl (fun k _ => count_prefixSet grp c (hc k))

lemma prefixSet_union (c d : κ → ℕ) :
    prefixSet grp c ∪ prefixSet grp d = prefixSet grp (c ⊔ d) := by
  ext i
  simp [prefixSet, lt_max_iff]

lemma prefixSet_inter (c d : κ → ℕ) :
    prefixSet grp c ∩ prefixSet grp d = prefixSet grp (c ⊓ d) := by
  ext i
  simp [prefixSet, lt_min_iff]

lemma count_insert {S : Finset ι} {j : ι} (hj : j ∉ S) (m : κ) :
    count grp (insert j S) m = count grp S m + if grp j = m then 1 else 0 := by
  unfold count
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => hj (mem_filter.1 h').1)]
  · rfl

/-- **Lemma 2 (lem:dr).** For `c ∈ 𝒞` with `c_k ≥ 1` and `c + e_l ∈ 𝒞` (possibly `l = k`):
`V_{c+e_l} - V_{c+e_l-e_k} ≤ V_c - V_{c-e_k}`. -/
theorem lemma2 (hR : Regular grp xmax xmin f f') (hP : PriorityOrder grp xmax xmin f)
    (hB : 0 ≤ B) {c : κ → ℕ} {k l : κ} (hc : InC grp xmin B c) (hk : 1 ≤ c k)
    (hl : InC grp xmin B (c + Pi.single l 1)) :
    Vc grp xmax xmin B f (c + Pi.single l 1) - Vc grp xmax xmin B f (c + Pi.single l 1 - Pi.single k 1)
      ≤ Vc grp xmax xmin B f c - Vc grp xmax xmin B f (c - Pi.single k 1) := by
  unfold Vc
  by_cases hlk : l = k
  · -- the case `l = k`
    rw [hlk] at hl ⊢
    have hcancel : c + Pi.single k 1 - Pi.single k 1 = c := by
      funext m
      simp
    rw [hcancel]
    have hck : c k < (group grp k).card := by
      have := hl.1 k
      simp only [Pi.add_apply, Pi.single_eq_same] at this
      omega
    -- `j`: the `(c_k + 1)`-th EV of group `k`
    obtain ⟨j, hjG, hjr⟩ : ∃ j ∈ group grp k, rank grp j = c k := by
      have hmem : c k ∈ (group grp k).image (rank grp) := by
        rw [image_rank grp k, mem_range]
        exact hck
      exact mem_image.1 hmem
    have hjk : grp j = k := by simpa [group] using hjG
    have hj_iff : ∀ i, (grp i = k ∧ rank grp i = c k) ↔ i = j := by
      intro i
      constructor
      · rintro ⟨hik, hir⟩
        exact rank_injOn grp k (by simp [group, hik]) hjG (by rw [hir, hjr])
      · rintro rfl
        exact ⟨hjk, hjr⟩
    set d := c - Pi.single k 1 with hd
    have hdk : d k + 1 = c k := by
      simp only [hd, Pi.sub_apply, Pi.single_eq_same]
      omega
    have hdm : ∀ m, m ≠ k → d m = c m := by
      intro m hm
      simp [hd, Pi.single_apply, hm]
    have hdc : ∀ m, d m ≤ c m := by
      intro m
      by_cases hm : m = k
      · rw [hm]; omega
      · rw [hdm m hm]
    have hjnot : j ∉ prefixSet grp d := by
      simp only [prefixSet, mem_filter, mem_univ, true_and, hjk, hjr, not_lt]
      omega
    -- union and intersection of `I*_c` and `I₂ = I*_{c-e_k} ∪ {j}`
    have hU : prefixSet grp c ∪ insert j (prefixSet grp d) = prefixSet grp (c + Pi.single k 1) := by
      ext i
      simp only [mem_union, mem_insert, prefixSet, mem_filter, mem_univ, true_and, Pi.add_apply]
      by_cases hik : grp i = k
      · have e1 : i = j ↔ rank grp i = c k := by rw [← hj_iff]; simp [hik]
        rw [e1, hik, Pi.single_eq_same]
        omega
      · have e1 : i ≠ j := fun h => hik (h ▸ hjk)
        rw [hdm _ hik]
        simp [Pi.single_apply, hik, e1]
    have hN : prefixSet grp c ∩ insert j (prefixSet grp d) = prefixSet grp d := by
      ext i
      simp only [mem_inter, mem_insert, prefixSet, mem_filter, mem_univ, true_and]
      by_cases hik : grp i = k
      · have e1 : i = j ↔ rank grp i = c k := by rw [← hj_iff]; simp [hik]
        rw [e1, hik]
        omega
      · have e1 : i ≠ j := fun h => hik (h ▸ hjk)
        rw [hdm _ hik]
        simp [e1]
    -- `I₂` has cardinality vector `c`
    have hcount : ∀ m, count grp (insert j (prefixSet grp d)) m = c m := by
      intro m
      rw [count_insert hjnot, count_prefixSet grp d ((hdc m).trans (hc.1 m))]
      by_cases hm : m = k
      · rw [hm, if_pos hjk]; omega
      · rw [if_neg (show ¬ grp j = m from fun h => hm (h.symm.trans hjk)), hdm m hm, add_zero]
    have hcard2 : (insert j (prefixSet grp d)).card ≤ ⌊B / xmin⌋₊ := by
      rw [card_eq_sum_count (grp := grp), sum_congr rfl (fun m _ => hcount m)]
      exact hc.2
    have hfeas2 := feasible_of_card hR ((le_nmax_iff hR.xmin_pos hB _).1 hcard2)
    have hthm2 := prefix_theorem grp xmax xmin B f hP (fun i => hR.contOn i) c hc.1 _ hcount hfeas2
    have hsub := submod hR hB (prefixSet grp c) (insert j (prefixSet grp d))
      (by rw [hU, card_prefixSet hl.1]; exact hl.2)
    rw [hU, hN] at hsub
    linarith
  · -- the case `l ≠ k`
    have hU : (c + Pi.single l 1 - Pi.single k 1) ⊔ c = c + Pi.single l 1 := by
      funext m
      simp only [Pi.sup_apply, Pi.add_apply, Pi.sub_apply, Pi.single_apply, max_def]
      split_ifs <;> subst_vars <;> first | omega | simp_all
    have hN : (c + Pi.single l 1 - Pi.single k 1) ⊓ c = c - Pi.single k 1 := by
      funext m
      simp only [Pi.inf_apply, Pi.add_apply, Pi.sub_apply, Pi.single_apply, min_def]
      split_ifs <;> subst_vars <;> first | omega | simp_all
    have hsub := submod hR hB (prefixSet grp (c + Pi.single l 1 - Pi.single k 1))
      (prefixSet grp c) (by rw [prefixSet_union, hU, card_prefixSet hl.1]; exact hl.2)
    rw [prefixSet_union, hU, prefixSet_inter, hN] at hsub
    linarith

/-- **`V_c` as in the paper.** For `c ∈ 𝒞`, `V_c = V(I*_c)` is the largest value in the family
`F_c` of on-sets with cardinality vector `c` (the paper's `V_c := max_{I ∈ F_c} V(I)`), and
`I*_c ∈ F_c` attains it (Theorem 2). -/
theorem Vc_isGreatest (hR : Regular grp xmax xmin f f') (hP : PriorityOrder grp xmax xmin f)
    (hB : 0 ≤ B) {c : κ → ℕ} (hc : InC grp xmin B c) :
    IsGreatest {v | ∃ I : Finset ι, (∀ k, count grp I k = c k) ∧ V grp xmax xmin B f I = v}
      (Vc grp xmax xmin B f c) := by
  refine ⟨⟨prefixSet grp c, fun k => count_prefixSet grp c (hc.1 k), rfl⟩, ?_⟩
  rintro v ⟨I, hI, rfl⟩
  have hcard : I.card ≤ ⌊B / xmin⌋₊ := by
    rw [card_eq_sum_count (grp := grp), sum_congr rfl (fun k _ => hI k)]
    exact hc.2
  exact prefix_theorem grp xmax xmin B f hP (fun i => hR.contOn i) c hc.1 I hI
    (feasible_of_card hR ((le_nmax_iff hR.xmin_pos hB _).1 hcard))

/-! ## Theorem 3 -/

section Theorem3

variable (hR : Regular grp xmax xmin f f') (hP : PriorityOrder grp xmax xmin f) (hB : 0 ≤ B)
include hR hP hB

omit hR hP hB in
lemma update_add_single (c : κ → ℕ) (k : κ) (q : ℕ) :
    Function.update c k q + Pi.single k 1 = Function.update c k (q + 1) := by
  funext m
  by_cases hm : m = k
  · subst hm; simp
  · simp [Function.update_of_ne hm, Pi.single_apply, hm]

omit hR hP hB in
lemma update_sub_single (c : κ → ℕ) (k : κ) (q : ℕ) :
    Function.update c k q - Pi.single k 1 = Function.update c k (q - 1) := by
  funext m
  by_cases hm : m = k
  · subst hm; simp
  · simp [Function.update_of_ne hm, Pi.single_apply, hm]

omit hR hP hB in
lemma inC_update_mono {c : κ → ℕ} {k : κ} :
    ∀ q q', q' ≤ q → InC grp xmin B (Function.update c k q) →
      InC grp xmin B (Function.update c k q') := by
  intro q q' hq hF
  apply hF.mono
  intro m
  by_cases hm : m = k
  · subst hm; simp [hq]
  · simp [Function.update_of_ne hm]

omit hR hP hB in
lemma inC_update_bound {c : κ → ℕ} {k : κ} :
    ∀ q, InC grp xmin B (Function.update c k q) → q ≤ (group grp k).card := by
  intro q hF
  have := hF.1 k
  simpa using this

lemma gainsAnti_update {c : κ → ℕ} {k : κ} :
    GainsAnti (fun q => Vc grp xmax xmin B f (Function.update c k q))
      (fun q => InC grp xmin B (Function.update c k q)) := by
  intro q hq hF
  have hFq := inC_update_mono (q + 1) q (Nat.le_succ q) hF
  have hk : 1 ≤ Function.update c k q k := by simp [hq]
  have h := lemma2 hR hP hB (k := k) (l := k) hFq hk (by rw [update_add_single]; exact hF)
  rw [update_add_single, update_sub_single, update_sub_single, Nat.add_sub_cancel] at h
  exact h

lemma bestCount_spec {c : κ → ℕ} (k : κ) (hc : InC grp xmin B c) :
    InC grp xmin B (Function.update c k (bestCount grp xmax xmin B f c k)) ∧
    (∀ q, InC grp xmin B (Function.update c k q) →
      Vc grp xmax xmin B f (Function.update c k q) ≤
        Vc grp xmax xmin B f (Function.update c k (bestCount grp xmax xmin B f c k))) ∧
    ∀ q, q < bestCount grp xmax xmin B f c k →
      Vc grp xmax xmin B f (Function.update c k q) <
        Vc grp xmax xmin B f (Function.update c k (bestCount grp xmax xmin B f c k)) :=
  bestIdx_spec _ inC_update_bound inC_update_mono
    (inC_update_mono (c k) 0 (Nat.zero_le _) (by rw [Function.update_eq_self]; exact hc))

/-- **Theorem 3(a).** For `c ∈ 𝒞` with `c_k ≥ 1`: `V_c > V_{c-e_k} ⟺ ĉ_k(c) ≥ c_k`. -/
theorem theorem3a {c : κ → ℕ} {k : κ} (hc : InC grp xmin B c) (hk : 1 ≤ c k) :
    Vc grp xmax xmin B f (c - Pi.single k 1) < Vc grp xmax xmin B f c ↔
      c k ≤ bestCount grp xmax xmin B f c k := by
  obtain ⟨hFb, hbmax, hbmin⟩ := bestCount_spec hR hP hB k hc
  have key := gain_pos_iff inC_update_mono (gainsAnti_update hR hP hB) hbmax hFb hbmin hk
    (show InC grp xmin B (Function.update c k (c k)) by rw [Function.update_eq_self]; exact hc)
  simp only [Function.update_eq_self] at key
  rwa [← update_sub_single, Function.update_eq_self] at key

/-- **Theorem 3(b).** For `c ∈ 𝒞`, `l ≠ k` and `c + e_l ∈ 𝒞`: `ĉ_k(c + e_l) ≤ ĉ_k(c)`. -/
theorem theorem3b {c : κ → ℕ} {k l : κ} (hlk : l ≠ k) (hc : InC grp xmin B c)
    (hl : InC grp xmin B (c + Pi.single l 1)) :
    bestCount grp xmax xmin B f (c + Pi.single l 1) k ≤ bestCount grp xmax xmin B f c k := by
  obtain ⟨_, hbmax, _⟩ := bestCount_spec hR hP hB k hc
  obtain ⟨hFb', _, hbmin'⟩ := bestCount_spec hR hP hB k hl
  have hcomm : ∀ q, Function.update c k q + Pi.single l 1 =
      Function.update (c + Pi.single l 1) k q := by
    intro q
    funext m
    by_cases hm : m = k
    · subst hm; simp [Pi.single_apply, Ne.symm hlk]
    · simp [Function.update_of_ne hm]
  have hF'F : ∀ q, InC grp xmin B (Function.update (c + Pi.single l 1) k q) →
      InC grp xmin B (Function.update c k q) := by
    intro q hF
    apply hF.mono
    intro m
    rw [← hcomm]
    simp
  refine best_anti inC_update_mono (gainsAnti_update hR hP hB) hF'F ?_ hbmax hFb' hbmin'
  intro q hq hF
  have hFq := hF'F q hF
  have hk : 1 ≤ Function.update c k q k := by simp [hq]
  have h := lemma2 hR hP hB (k := k) (l := l) hFq hk (by rw [hcomm]; exact hF)
  have e1 : Function.update c k q + Pi.single l 1 - Pi.single k 1 =
      Function.update (c + Pi.single l 1) k (q - 1) := by
    rw [hcomm, update_sub_single]
  rw [e1, hcomm, update_sub_single] at h
  exact h

end Theorem3

end BIC
