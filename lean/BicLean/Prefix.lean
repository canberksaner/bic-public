import Mathlib

/-!
# Theorem 2 of the BIC paper (the prefix theorem), checked in Lean

Setting, as in Section II of the paper:
* `ι`      : the connected EVs (finitely many). The labels are linearly ordered, and the
             priority order within each group is this order restricted to the group.
* `grp i`  : the group of EV `i`.  `xmax k` : the maximum rate of group `k`,
             so `x_i^max = xmax (grp i)`.
* `xmin`   : the common minimum rate.  `B` : the power budget.  `f i` : the utility of EV `i`.
-/

open Finset

namespace BIC

variable {ι κ : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq κ]
variable (grp : ι → κ) (xmax : κ → ℝ) (xmin B : ℝ) (f : ι → ℝ → ℝ)

/-- `x` is feasible for the restriction `(P_I)`: every EV of `I` charges within
`[xmin, x_i^max]`, and the rates of the EVs of `I` sum to at most `B`. -/
def Feasible (I : Finset ι) (x : ι → ℝ) : Prop :=
  (∀ i ∈ I, x i ∈ Set.Icc xmin (xmax (grp i))) ∧ ∑ i ∈ I, x i ≤ B

/-- The objective of `(P_I)`. -/
def value (I : Finset ι) (x : ι → ℝ) : ℝ := ∑ i ∈ I, f i (x i)

/-- `V(I)`: the optimal value of `(P_I)`. -/
noncomputable def V (I : Finset ι) : ℝ :=
  sSup {v | ∃ x, Feasible grp xmax xmin B I x ∧ value f I x = v}

/-- Assumption 2 (priority order), equation (order) of the paper:
`i ≤ j` in the same group implies `f_i(y) ≥ f_j(y)` for all `y ∈ [xmin, x̄_k]`. -/
def PriorityOrder : Prop :=
  ∀ i j, grp i = grp j → i ≤ j → ∀ y ∈ Set.Icc xmin (xmax (grp i)), f j y ≤ f i y

/-- The group `N_k`. -/
def group (k : κ) : Finset ι := univ.filter (fun i => grp i = k)

/-- `c_k = |I ∩ N_k|`: the number of EVs of `I` in group `k`. -/
def count (I : Finset ι) (k : κ) : ℕ := (I.filter (fun i => grp i = k)).card

/-- The number of EVs of the group of `i` that come before `i` in the priority order. -/
def rank (i : ι) : ℕ := (univ.filter (fun j => grp j = grp i ∧ j < i)).card

/-- `I*_c`: the first `c k` EVs of each group `k` in the priority order
(an EV is in it exactly when fewer than `c k` EVs of its group come before it). -/
def prefixSet (c : κ → ℕ) : Finset ι := univ.filter (fun i => rank grp i < c (grp i))

/-- A set that, with each EV, contains every EV of the same group that comes before it. -/
def DownClosed (S : Finset ι) : Prop := ∀ i ∈ S, ∀ j, grp j = grp i → j ≤ i → j ∈ S

/-! ## The swap argument (Appendix, proof of Theorem 2) -/

/-- If `I` and `S` have the same cardinality vector and `j ∈ I \ S`, then some EV of the
same group as `j` lies in `S \ I`. -/
lemma exists_partner {I S : Finset ι} (h : ∀ k, count grp I k = count grp S k)
    {j : ι} (hjI : j ∈ I) (hjS : j ∉ S) : ∃ i ∈ S, i ∉ I ∧ grp i = grp j := by
  by_contra hcon
  push_neg at hcon
  have hsub : S.filter (fun i => grp i = grp j) ⊆ I.filter (fun i => grp i = grp j) := by
    intro i hi
    rw [mem_filter] at hi ⊢
    refine ⟨?_, hi.2⟩
    by_contra hiI
    exact hcon i hi.1 hiI hi.2
  have hss : S.filter (fun i => grp i = grp j) ⊂ I.filter (fun i => grp i = grp j) :=
    (Finset.ssubset_iff_of_subset hsub).2
      ⟨j, mem_filter.2 ⟨hjI, rfl⟩, fun h' => hjS (mem_filter.1 h').1⟩
  have hlt := card_lt_card hss
  have h2 := h (grp j)
  unfold count at h2
  omega

/-- One swap: replace `j ∈ I` by `i ∉ I` of the same group with `i ≤ j`, and give `i` the
rate of `j`. The new allocation is feasible, its value is not lower, and the cardinality
vector is unchanged. -/
lemma swap_step (hP : PriorityOrder grp xmax xmin f) {I : Finset ι} {x : ι → ℝ}
    (hfeas : Feasible grp xmax xmin B I x) {i j : ι} (hiI : i ∉ I) (hjI : j ∈ I)
    (hgrp : grp i = grp j) (hij : i ≤ j) :
    Feasible grp xmax xmin B (insert i (I.erase j)) (Function.update x i (x j)) ∧
    value f I x ≤ value f (insert i (I.erase j)) (Function.update x i (x j)) ∧
    ∀ k, count grp (insert i (I.erase j)) k = count grp I k := by
  unfold Feasible at hfeas ⊢
  have hiE : i ∉ I.erase j := fun h => hiI (mem_of_mem_erase h)
  have hupd : ∀ r ∈ I.erase j, Function.update x i (x j) r = x r := by
    intro r hr
    exact Function.update_of_ne (ne_of_mem_of_not_mem hr hiE) _ _
  have hxj := hfeas.1 j hjI
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    rcases mem_insert.1 hr with rfl | hr
    · rw [Function.update_self, hgrp]; exact hxj
    · rw [hupd r hr]; exact hfeas.1 r (mem_of_mem_erase hr)
  · have h1 : ∑ r ∈ insert i (I.erase j), Function.update x i (x j) r
        = x j + ∑ r ∈ I.erase j, x r := by
      rw [sum_insert hiE, Function.update_self, sum_congr rfl hupd]
    have h2 : x j + ∑ r ∈ I.erase j, x r = ∑ r ∈ I, x r := add_sum_erase I x hjI
    rw [h1, h2]
    exact hfeas.2
  · have h1 : value f (insert i (I.erase j)) (Function.update x i (x j))
        = f i (x j) + ∑ r ∈ I.erase j, f r (x r) := by
      unfold value
      rw [sum_insert hiE, Function.update_self]
      congr 1
      exact sum_congr rfl (fun r hr => by rw [hupd r hr])
    have h2 : f j (x j) + ∑ r ∈ I.erase j, f r (x r) = value f I x :=
      add_sum_erase I (fun r => f r (x r)) hjI
    have h3 : f j (x j) ≤ f i (x j) := hP i j hgrp hij (x j) (by rw [hgrp]; exact hxj)
    linarith
  · intro k
    unfold count
    have h2 : (if grp j = k then 1 else 0) + ∑ a ∈ I.erase j, (if grp a = k then 1 else 0)
        = ∑ a ∈ I, (if grp a = k then 1 else 0) :=
      add_sum_erase I (fun a => if grp a = k then 1 else 0) hjI
    rw [card_filter, card_filter, sum_insert hiE, ← h2, hgrp]

/-- The swap argument, repeated: for any `S` that is closed downward within each group and has
the same cardinality vector as `I`, every feasible allocation on `I` is matched by a feasible
allocation on `S` with at least the same value. By induction on `|I \ S|`. -/
theorem dominate (hP : PriorityOrder grp xmax xmin f) {S : Finset ι}
    (hS : DownClosed grp S) :
    ∀ (n : ℕ) (I : Finset ι) (x : ι → ℝ), (I \ S).card = n →
      (∀ k, count grp I k = count grp S k) → Feasible grp xmax xmin B I x →
      ∃ x', Feasible grp xmax xmin B S x' ∧ value f I x ≤ value f S x' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro I x hn hcnt hfeas
  by_cases hIS : (I \ S).Nonempty
  · obtain ⟨j, hj⟩ := hIS
    rw [mem_sdiff] at hj
    obtain ⟨i, hiS, hiI, hgrp⟩ := exists_partner grp hcnt hj.1 hj.2
    have hij : i < j := by
      rcases lt_or_ge i j with h | h
      · exact h
      · exact absurd (hS i hiS j hgrp.symm h) hj.2
    obtain ⟨hfeas', hval, hcnt'⟩ := swap_step grp xmax xmin B f hP hfeas hiI hj.1 hgrp hij.le
    have hlt : (insert i (I.erase j) \ S).card < n := by
      rw [← hn]
      apply card_lt_card
      have hsub : insert i (I.erase j) \ S ⊆ I \ S := by
        intro r hr
        rw [mem_sdiff] at hr ⊢
        rcases mem_insert.1 hr.1 with h | h
        · exact absurd (h ▸ hiS) hr.2
        · exact ⟨mem_of_mem_erase h, hr.2⟩
      refine (Finset.ssubset_iff_of_subset hsub).2 ⟨j, mem_sdiff.2 hj, ?_⟩
      intro hj'
      rcases mem_insert.1 (mem_sdiff.1 hj').1 with h | h
      · exact hij.ne' h
      · exact (Finset.notMem_erase j I) h
    obtain ⟨x'', h1, h2⟩ :=
      ih _ hlt _ _ rfl (fun k => (hcnt' k).trans (hcnt k)) hfeas'
    exact ⟨x'', h1, hval.trans h2⟩
  · have hIsub : I ⊆ S := by
      intro r hr
      by_contra hrS
      exact hIS ⟨r, mem_sdiff.2 ⟨hr, hrS⟩⟩
    have hSsub : S ⊆ I := by
      intro r hr
      by_contra hrI
      obtain ⟨j, hjI, hjS, _⟩ := exists_partner grp (fun k => (hcnt k).symm) hr hrI
      exact hjS (hIsub hjI)
    have hEq : I = S := Subset.antisymm hIsub hSsub
    subst hEq
    exact ⟨x, hfeas, le_rfl⟩

/-! ## The set `I*_c` of the paper: closed downward, with cardinality vector `c` -/

lemma rank_lt_rank {i i' : ι} (hg : grp i = grp i') (h : i < i') :
    rank grp i < rank grp i' := by
  unfold rank
  apply card_lt_card
  have hsub : univ.filter (fun j => grp j = grp i ∧ j < i)
      ⊆ univ.filter (fun j => grp j = grp i' ∧ j < i') := by
    intro l hl
    simp only [mem_filter, mem_univ, true_and] at hl ⊢
    exact ⟨hl.1.trans hg, hl.2.trans h⟩
  exact (Finset.ssubset_iff_of_subset hsub).2 ⟨i, by simp [hg, h], by simp⟩

lemma rank_lt_card (i : ι) : rank grp i < (group grp (grp i)).card := by
  unfold rank group
  apply card_lt_card
  have hsub : univ.filter (fun j => grp j = grp i ∧ j < i) ⊆ univ.filter (fun j => grp j = grp i) := by
    intro l hl
    simp only [mem_filter, mem_univ, true_and] at hl ⊢
    exact hl.1
  exact (Finset.ssubset_iff_of_subset hsub).2 ⟨i, by simp, by simp⟩

lemma rank_injOn (k : κ) : Set.InjOn (rank grp) (group grp k : Set ι) := by
  intro i hi i' hi' h
  rw [Finset.mem_coe] at hi hi'
  simp only [group, mem_filter, mem_univ, true_and] at hi hi'
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd h (rank_lt_rank grp (hi.trans hi'.symm) hlt).ne
  · exact heq
  · exact absurd h (rank_lt_rank grp (hi'.trans hi.symm) hgt).ne'

lemma image_rank (k : κ) : (group grp k).image (rank grp) = range (group grp k).card := by
  apply eq_of_subset_of_card_le
  · intro m hm
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hm
    have hik : grp i = k := by simpa [group] using hi
    rw [mem_range, ← hik]
    exact rank_lt_card grp i
  · rw [card_range, card_image_of_injOn (rank_injOn grp k)]

lemma prefixSet_downClosed (c : κ → ℕ) : DownClosed grp (prefixSet grp c) := by
  intro i hi j hg hji
  simp only [prefixSet, mem_filter, mem_univ, true_and] at hi ⊢
  rw [hg]
  refine lt_of_le_of_lt ?_ hi
  unfold rank
  apply card_le_card
  intro l hl
  simp only [mem_filter, mem_univ, true_and] at hl ⊢
  exact ⟨hl.1.trans hg, lt_of_lt_of_le hl.2 hji⟩

lemma count_prefixSet (c : κ → ℕ) {k : κ} (hk : c k ≤ (group grp k).card) :
    count grp (prefixSet grp c) k = c k := by
  have h1 : (prefixSet grp c).filter (fun i => grp i = k)
      = (group grp k).filter (fun i => rank grp i < c k) := by
    ext a
    simp only [prefixSet, group, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨ha1, ha2⟩
      exact ⟨ha2, by rw [← ha2]; exact ha1⟩
    · rintro ⟨ha1, ha2⟩
      exact ⟨by rw [ha1]; exact ha2, ha1⟩
  have h2 : ((group grp k).filter (fun i => rank grp i < c k)).image (rank grp)
      = range (c k) := by
    ext m
    simp only [mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨i, ⟨_, hi⟩, rfl⟩
      exact hi
    · intro hm
      have hmem : m ∈ (group grp k).image (rank grp) := by
        rw [image_rank grp k, mem_range]
        omega
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hmem
      exact ⟨i, ⟨hi, hm⟩, rfl⟩
  have hinj : Set.InjOn (rank grp)
      (((group grp k).filter (fun i => rank grp i < c k) : Finset ι) : Set ι) :=
    (rank_injOn grp k).mono (Finset.coe_subset.2 (filter_subset _ _))
  unfold count
  rw [h1, ← card_image_of_injOn hinj, h2, card_range]

/-! ## Theorem 2 -/

/-- **Theorem 2 (prefix theorem).** Let `c` be a cardinality vector with `c_k ≤ n_k` for every
group, and let `I*_c` be the first `c_k` EVs of each group in the priority order. Then
`V(I*_c) ≥ V(I)` for every on-set `I` with cardinality vector `c` for which `(P_I)` is feasible.

Assumptions used: the priority order (Assumption 2) and continuity of each `f_i` on
`[xmin, x_i^max]` (only to make the optimal value `V` finite). Concavity and differentiability
(Assumption 1) are not used. -/
theorem prefix_theorem (hP : PriorityOrder grp xmax xmin f)
    (hcont : ∀ i, ContinuousOn (f i) (Set.Icc xmin (xmax (grp i))))
    (c : κ → ℕ) (hc : ∀ k, c k ≤ (group grp k).card)
    (I : Finset ι) (hI : ∀ k, count grp I k = c k)
    (hfeas : ∃ x, Feasible grp xmax xmin B I x) :
    V grp xmax xmin B f I ≤ V grp xmax xmin B f (prefixSet grp c) := by
  have hS := prefixSet_downClosed grp c
  have hcnt : ∀ k, count grp I k = count grp (prefixSet grp c) k := fun k => by
    rw [hI, count_prefixSet grp c (hc k)]
  have hbdd : BddAbove
      {v | ∃ x, Feasible grp xmax xmin B (prefixSet grp c) x ∧ value f (prefixSet grp c) x = v} := by
    have hM : ∀ i, ∃ M, ∀ y ∈ Set.Icc xmin (xmax (grp i)), f i y ≤ M := fun i => by
      obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn (hcont i)).bddAbove
      exact ⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩
    choose M hM using hM
    refine ⟨∑ i ∈ prefixSet grp c, M i, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    exact sum_le_sum (fun i hi => hM i (x i) (hx.1 i hi))
  unfold V
  apply csSup_le
  · obtain ⟨x, hx⟩ := hfeas
    exact ⟨_, x, hx, rfl⟩
  · rintro v ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hle⟩ := dominate grp xmax xmin B f hP hS _ I x rfl hcnt hx
    exact hle.trans (le_csSup hbdd ⟨x', hx', rfl⟩)

end BIC


