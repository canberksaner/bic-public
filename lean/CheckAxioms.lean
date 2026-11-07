import BicLean

/-! Lists the axioms behind each result. Only Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) may appear; `sorryAx` would mean a gap.
`lake build` accepts `sorry` with only a warning, so this check is the real guard. -/

-- Theorem 1, fast-path (Theorem 4), Algorithm 2's allocation x(λ)
#print axioms BIC.paper_theorem1
#print axioms BIC.fast_path
#print axioms BIC.xsel_max
#print axioms BIC.theorem1_bic
#print axioms BIC.fast_path_bic
-- Theorem 2, V_c, (eq:decomposition)
#print axioms BIC.prefix_theorem
#print axioms BIC.Vc_isGreatest
#print axioms BIC.objective_le_Vc
#print axioms BIC.decomposition
-- Appendix A and Table I
#print axioms BIC.priority_of_key_increasing
#print axioms BIC.priority_of_key_decreasing
#print axioms BIC.tableI_sllf
#print axioms BIC.tableI_quad
#print axioms BIC.tableI_log
#print axioms BIC.tableI_exp
-- Appendix B
#print axioms BIC.foc_max
#print axioms BIC.clamp_foc
#print axioms BIC.foc_left
#print axioms BIC.foc_right
#print axioms BIC.exists_inv
#print axioms BIC.proj_max
#print axioms BIC.closed_form
#print axioms BIC.selector_max
#print axioms BIC.lambda_th_gt
-- Lemma 1, Lemma 2, Theorem 3
#print axioms BIC.strong_duality
#print axioms BIC.submod
#print axioms BIC.lemma2
#print axioms BIC.theorem3a
#print axioms BIC.theorem3b
-- Algorithm 1, Theorem 4
#print axioms BIC.choose_correct
#print axioms BIC.theorem4
-- Proposition 1
#print axioms BIC.card_evals_le
#print axioms BIC.xmin_unique_max
#print axioms BIC.multiplier_bracket
