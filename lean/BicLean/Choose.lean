import Mathlib

/-!
# Algorithm 1 (Choose) of the BIC paper, for `K = 2`

`W c1 c2` stands for `V_{(c1, c2)}`. The algorithm is written as in the paper: an outer loop over
`c1 = 0, …, min(n1, n^max)` and an inner while loop that scans `c2` downwards from
`min(c2, n^max - c1)` and stops when `V_{(c1, c2-1)} < V_{(c1, c2)}`. `V_best` starts at `-∞`
(`⊥` in `WithBot ℝ`). The state also records every pair `(c1, c2)` whose value is read, to count
the restrictions solved (Section IV-C and Proposition 1).

* `choose_correct`: given the two properties of Theorem 3, Choose returns a maximizer of `W`
  over `𝒞 = {c1 ≤ n1, c2 ≤ n2, c1 + c2 ≤ n^max}`.
* `card_evals_le`: Choose reads at most `2 (n1 + 1) + n2` values (no assumption needed).
-/

namespace BIC

section Choose

variable (W : ℕ → ℕ → ℝ) (n1 n2 nmax : ℕ)

/-- `(c1, c2) ∈ 𝒞` for `K = 2`. -/
def F2 (c1 c2 : ℕ) : Prop := c1 ≤ n1 ∧ c2 ≤ n2 ∧ c1 + c2 ≤ nmax

/-- The inner while loop (lines ch-while to ch-dec), started at `c2`. -/
noncomputable def inner (c1 : ℕ) : ℕ → ℕ
  | 0 => 0
  | c2 + 1 => if W c1 c2 < W c1 (c2 + 1) then c2 + 1 else inner c1 c2

/-- The pairs whose values the inner loop reads (two per test at line ch-test). -/
noncomputable def innerEvals (c1 : ℕ) : ℕ → Finset (ℕ × ℕ)
  | 0 => ∅
  | c2 + 1 => {(c1, c2), (c1, c2 + 1)} ∪
      (if W c1 c2 < W c1 (c2 + 1) then ∅ else innerEvals c1 c2)

/-- The state of Algorithm 1: current `c2`, `V_best`, `c_best`, and the pairs read so far. -/
structure St where
  c2 : ℕ
  vbest : WithBot ℝ
  cbest : ℕ × ℕ
  evals : Finset (ℕ × ℕ)

/-- One pass of the outer loop for `c1` (lines ch-cap to ch-keep). -/
noncomputable def step (s : St) (c1 : ℕ) : St :=
  if s.vbest < ((W c1 (inner W c1 (min s.c2 (nmax - c1))) : ℝ) : WithBot ℝ) then
    ⟨inner W c1 (min s.c2 (nmax - c1)), (W c1 (inner W c1 (min s.c2 (nmax - c1))) : ℝ),
      (c1, inner W c1 (min s.c2 (nmax - c1))),
      s.evals ∪ innerEvals W c1 (min s.c2 (nmax - c1)) ∪ {(c1, inner W c1 (min s.c2 (nmax - c1)))}⟩
  else
    ⟨inner W c1 (min s.c2 (nmax - c1)), s.vbest, s.cbest,
      s.evals ∪ innerEvals W c1 (min s.c2 (nmax - c1)) ∪ {(c1, inner W c1 (min s.c2 (nmax - c1)))}⟩

/-- The state after the outer loop has processed `c1 = 0, …, t`, from `c2 = n2`, `V_best = -∞`. -/
noncomputable def runC (t : ℕ) : St :=
  (List.range (t + 1)).foldl (step W nmax) ⟨n2, ⊥, (0, 0), ∅⟩

/-- **Algorithm 1 (Choose)**: the returned cardinality vector `c*`. -/
noncomputable def choose : ℕ × ℕ := (runC W n2 nmax (min n1 nmax)).cbest

/-- The pairs `(c1, c2)` whose values `V_{(c1,c2)}` Choose reads, i.e. the restrictions it solves. -/
noncomputable def chooseEvals : Finset (ℕ × ℕ) := (runC W n2 nmax (min n1 nmax)).evals

variable {W n1 n2 nmax}

lemma runC_succ (t : ℕ) : runC W n2 nmax (t + 1) = step W nmax (runC W n2 nmax t) (t + 1) := by
  simp [runC, List.range_succ, List.foldl_append]

lemma runC_zero : runC W n2 nmax 0 = step W nmax ⟨n2, ⊥, (0, 0), ∅⟩ 0 := by
  simp [runC]

/-! ## Correctness -/

lemma inner_eq (chat : ℕ → ℕ)
    (ha : ∀ c1 c2, F2 n1 n2 nmax c1 c2 → 1 ≤ c2 → (W c1 (c2 - 1) < W c1 c2 ↔ c2 ≤ chat c1))
    (c1 : ℕ) : ∀ s, F2 n1 n2 nmax c1 s → chat c1 ≤ s → inner W c1 s = chat c1
  | 0, _, h => by simp only [inner]; omega
  | s + 1, hF, h => by
    have hiff := ha c1 (s + 1) hF (by omega)
    simp only [Nat.add_sub_cancel] at hiff
    simp only [inner]
    split_ifs with hlt
    · have := hiff.1 hlt
      omega
    · have hns : ¬ (s + 1 ≤ chat c1) := fun h' => hlt (hiff.2 h')
      exact inner_eq chat ha c1 s ⟨hF.1, by have := hF.2.1; omega, by have := hF.2.2; omega⟩
        (by omega)

/-- **Correctness of Choose** (the choosing-phase part of Theorem 4). `chat c1` is the best count
`ĉ₂(c1)` (a maximizer of `W c1 ·` over `𝒞`), `ha` is Theorem 3(a) and `hb` is Theorem 3(b). -/
theorem choose_correct (chat : ℕ → ℕ)
    (hspec : ∀ c1, F2 n1 n2 nmax c1 0 →
      F2 n1 n2 nmax c1 (chat c1) ∧ ∀ c2, F2 n1 n2 nmax c1 c2 → W c1 c2 ≤ W c1 (chat c1))
    (ha : ∀ c1 c2, F2 n1 n2 nmax c1 c2 → 1 ≤ c2 → (W c1 (c2 - 1) < W c1 c2 ↔ c2 ≤ chat c1))
    (hb : ∀ c1, F2 n1 n2 nmax (c1 + 1) 0 → chat (c1 + 1) ≤ chat c1) :
    F2 n1 n2 nmax (choose W n1 n2 nmax).1 (choose W n1 n2 nmax).2 ∧
      ∀ c1 c2, F2 n1 n2 nmax c1 c2 → W c1 c2 ≤ W (choose W n1 n2 nmax).1 (choose W n1 n2 nmax).2 := by
  -- invariant after processing `c1 = 0, …, t`
  have inv : ∀ t, t ≤ min n1 nmax →
      (runC W n2 nmax t).c2 = chat t ∧
      (runC W n2 nmax t).vbest = ((W (runC W n2 nmax t).cbest.1 (runC W n2 nmax t).cbest.2 : ℝ) :
        WithBot ℝ) ∧
      F2 n1 n2 nmax (runC W n2 nmax t).cbest.1 (runC W n2 nmax t).cbest.2 ∧
      ∀ c1, c1 ≤ t → W c1 (chat c1) ≤ W (runC W n2 nmax t).cbest.1 (runC W n2 nmax t).cbest.2 := by
    intro t
    induction t with
    | zero =>
      intro _
      have hF0 : F2 n1 n2 nmax 0 0 := ⟨Nat.zero_le _, Nat.zero_le _, by omega⟩
      obtain ⟨hFc, _⟩ := hspec 0 hF0
      have hin : inner W 0 (min n2 (nmax - 0)) = chat 0 :=
        inner_eq chat ha 0 _ ⟨Nat.zero_le _, min_le_left _ _, by omega⟩
          (le_min hFc.2.1 (by have := hFc.2.2; omega))
      rw [runC_zero]
      simp only [step, hin, WithBot.bot_lt_coe, ite_true]
      refine ⟨by trivial, by trivial, hFc, fun c1 hc1 => ?_⟩
      rw [Nat.le_zero.1 hc1]
    | succ t ih =>
      intro ht
      obtain ⟨hc2, hv, hF, hbest⟩ := ih (by omega)
      have hFt0 : F2 n1 n2 nmax t 0 := ⟨by omega, Nat.zero_le _, by omega⟩
      have hFt10 : F2 n1 n2 nmax (t + 1) 0 := ⟨by omega, Nat.zero_le _, by omega⟩
      obtain ⟨hFct, _⟩ := hspec t hFt0
      obtain ⟨hFct1, _⟩ := hspec (t + 1) hFt10
      have hin : inner W (t + 1) (min (runC W n2 nmax t).c2 (nmax - (t + 1))) = chat (t + 1) := by
        rw [hc2]
        apply inner_eq chat ha (t + 1)
        · exact ⟨by omega, (min_le_left _ _).trans hFct.2.1, by omega⟩
        · exact le_min (hb t hFt10) (by have := hFct1.2.2; omega)
      rw [runC_succ]
      unfold step
      rw [hin]
      split_ifs with hlt
      · refine ⟨rfl, rfl, hFct1, fun c1 hc1 => ?_⟩
        rcases Nat.lt_or_ge c1 (t + 1) with h | h
        · have h1 := hbest c1 (by omega)
          rw [hv, WithBot.coe_lt_coe] at hlt
          exact h1.trans hlt.le
        · rw [show c1 = t + 1 by omega]
      · refine ⟨rfl, hv, hF, fun c1 hc1 => ?_⟩
        rw [hv, WithBot.coe_lt_coe, not_lt] at hlt
        rcases Nat.lt_or_ge c1 (t + 1) with h | h
        · exact hbest c1 (by omega)
        · rw [show c1 = t + 1 by omega]
          exact hlt
  obtain ⟨_, _, hF, hbest⟩ := inv (min n1 nmax) le_rfl
  refine ⟨hF, fun c1 c2 hc => ?_⟩
  have hF0 : F2 n1 n2 nmax c1 0 := ⟨hc.1, Nat.zero_le _, by have := hc.2.2; omega⟩
  exact ((hspec c1 hF0).2 c2 hc).trans (hbest c1 (le_min hc.1 (by have := hc.2.2; omega)))

/-! ## Number of restrictions -/

lemma inner_le (c1 : ℕ) : ∀ s, inner W c1 s ≤ s
  | 0 => le_rfl
  | s + 1 => by
    simp only [inner]
    split_ifs
    · exact le_rfl
    · exact (inner_le c1 s).trans (Nat.le_succ s)

lemma mem_innerEvals (c1 : ℕ) : ∀ s, 1 ≤ s → (c1, s) ∈ innerEvals W c1 s ∧
    (c1, inner W c1 s) ∈ innerEvals W c1 s
  | 0, h => absurd h (by omega)
  | s + 1, _ => by
    simp only [innerEvals, inner]
    split_ifs with hlt
    · simp
    · refine ⟨by simp, ?_⟩
      rcases Nat.eq_zero_or_pos s with hs | hs
      · subst hs
        simp [inner]
      · exact Finset.mem_union_right _ (mem_innerEvals c1 s hs).2

lemma card_innerEvals (c1 : ℕ) : ∀ s, (innerEvals W c1 s).card + inner W c1 s ≤ s + 2 ∧
    (1 ≤ s → (innerEvals W c1 s).card ≤ s + 1)
  | 0 => by simp [innerEvals, inner]
  | s + 1 => by
    simp only [innerEvals, inner]
    split_ifs with hlt
    · simp only [Finset.union_empty]
      have : ({(c1, s), (c1, s + 1)} : Finset (ℕ × ℕ)).card ≤ 2 := Finset.card_le_two
      omega
    · rcases Nat.eq_zero_or_pos s with hs | hs
      · subst hs
        simp only [innerEvals, Finset.union_empty, inner]
        have : ({(c1, 0), (c1, 0 + 1)} : Finset (ℕ × ℕ)).card ≤ 2 := Finset.card_le_two
        omega
      · obtain ⟨h1, h2⟩ := card_innerEvals c1 s
        have hmem := (mem_innerEvals (W := W) c1 s hs).1
        have hsub : ({(c1, s), (c1, s + 1)} : Finset (ℕ × ℕ)) ∪ innerEvals W c1 s ⊆
            insert (c1, s + 1) (innerEvals W c1 s) := by
          intro p hp
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
          rcases hp with (rfl | rfl) | hp
          · exact Or.inr hmem
          · exact Or.inl rfl
          · exact Or.inr hp
        have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        have := h2 hs
        have := inner_le (W := W) c1 s
        omega

/-- The pairs read for one `c1`: at most `start - ĉ₂(c1) + 2`. -/
lemma card_pass (c1 s : ℕ) :
    (innerEvals W c1 s ∪ {(c1, inner W c1 s)}).card + inner W c1 s ≤ s + 2 := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    simp [innerEvals, inner]
  · have hmem := (mem_innerEvals (W := W) c1 s hs).2
    rw [Finset.union_eq_left.2 (Finset.singleton_subset_iff.2 hmem)]
    exact (card_innerEvals c1 s).1

lemma card_runC (t : ℕ) :
    (runC W n2 nmax t).evals.card + (runC W n2 nmax t).c2 ≤ n2 + 2 * (t + 1) := by
  induction t with
  | zero =>
    rw [runC_zero]
    have h := card_pass (W := W) 0 (min n2 (nmax - 0))
    have hm : min n2 (nmax - 0) ≤ n2 := min_le_left _ _
    unfold step
    split_ifs <;>
    · simp only [Finset.empty_union] at h ⊢
      omega
  | succ t ih =>
    rw [runC_succ]
    have h := card_pass (W := W) (t + 1) (min (runC W n2 nmax t).c2 (nmax - (t + 1)))
    have hm : min (runC W n2 nmax t).c2 (nmax - (t + 1)) ≤ (runC W n2 nmax t).c2 := min_le_left _ _
    have hu := Finset.card_union_le (runC W n2 nmax t).evals
      (innerEvals W (t + 1) (min (runC W n2 nmax t).c2 (nmax - (t + 1))) ∪
        {(t + 1, inner W (t + 1) (min (runC W n2 nmax t).c2 (nmax - (t + 1))))})
    unfold step
    split_ifs <;>
    · simp only [Finset.union_assoc] at hu ⊢
      omega

/-- **Restriction count (Section IV-C, used in Proposition 1).** Choose reads at most
`2 (n1 + 1) + n2` distinct values `V_{(c1, c2)}`, i.e. solves at most that many restrictions. -/
theorem card_evals_le : (chooseEvals W n1 n2 nmax).card ≤ 2 * (n1 + 1) + n2 := by
  have h := card_runC (W := W) (n2 := n2) (nmax := nmax) (min n1 nmax)
  have hm : min n1 nmax ≤ n1 := min_le_left _ _
  unfold chooseEvals
  omega

end Choose

end BIC
