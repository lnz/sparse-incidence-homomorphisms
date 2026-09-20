import Paper.RoundingIndependence
import Paper.RoundingDegeneracy
import Paper.BalancedRounding

noncomputable section

namespace Paper.Hypergraph

/-- The existence part of Korchemna et al., Theorem 4.1. -/
theorem twoTerminal_rounding : TwoTerminalRounding := by
  intro H A B x hA hB hx
  let R := H.vertices.filter (fun v => x v ≠ 0)
  by_cases h : 8 + 4 * Real.log ((H.induce R).independenceNumber : ℝ) ≤ (6 * H.degeneracy : ℝ)
  · dsimp only [R] at h
    obtain ⟨S, hS, hsep, hcost⟩ := H.twoTerminal_independence_rounding hA hB hx
    refine ⟨S, hS, hsep, ?_⟩
    simpa only [twoTerminalFactor, min_eq_left h] using hcost
  · dsimp only [R] at h
    obtain ⟨S, hS, hsep, hcost⟩ := H.twoTerminal_degeneracy_rounding hA hB hx
    refine ⟨S, hS, hsep, ?_⟩
    simpa only [twoTerminalFactor, min_eq_right (le_of_not_ge h)] using hcost

/-- Theorem 5.6 with the repaired cut-off argument and the original constants. -/
theorem external_rounding : ExternalRounding :=
  externalRounding_of_twoTerminalRounding twoTerminal_rounding

/-- The manuscript's main width comparison, with no external theorem hypothesis. -/
theorem main_width_comparison : MainWidthComparison := theorem_1_1 external_rounding

end Paper.Hypergraph
