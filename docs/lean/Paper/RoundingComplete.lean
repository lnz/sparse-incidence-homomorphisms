import Paper.RoundingIndependence
import Paper.RoundingDegeneracy
import Paper.BalancedRounding

noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

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

/-- The nontrivial existence branch of Theorem 5.6 with the repaired cut-off
argument and the original constants. -/
theorem balanced_rounding : BalancedRounding :=
  balancedRounding_of_twoTerminalRounding twoTerminal_rounding

/-- The sharp cost factor in the manuscript's half-balanced specialization. -/
theorem manuscript_rounding_cost_bound {q : ℝ} (hq : 0 ≤ q) :
    ((44 + 8 * (Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2)) /
      (1 - (1 / 2 : ℝ))) * q ≤
      120 * q * (Real.log (max 2 q) / Real.log 2) := by
  by_cases hq0 : q = 0
  · simp [hq0]
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let L := Real.log (max 2 q) / Real.log 2
  have hL : 1 ≤ L := by
    apply (le_div_iff₀ h2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (le_max_left 2 q)
  have hlog : Real.log (q / (1 - (1 / 2 : ℝ))) ≤
      Real.log 2 + Real.log (max 2 q) := by
    calc
      _ ≤ Real.log (2 * max 2 q) := by
        apply Real.log_le_log (by positivity)
        have := le_max_right (2 : ℝ) q
        norm_num
        linarith
      _ = _ := Real.log_mul (by norm_num) (ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_left 2 q)))
  have hratio : Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2 ≤ 1 + L := by
    apply (div_le_iff₀ h2).mpr
    calc
      _ ≤ Real.log 2 + Real.log (max 2 q) := hlog
      _ = (1 + L) * Real.log 2 := by dsimp [L]; field_simp
  have hfactor : (44 + 8 * (Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2)) /
      (1 - (1 / 2 : ℝ)) ≤ 120 * L := by
    norm_num at hratio ⊢
    linarith
  calc
    _ ≤ (120 * L) * q := mul_le_mul_of_nonneg_right hfactor hq
    _ = _ := by dsimp [L]; ring

/-- Both manuscript structural factors bound the same rounding estimate. -/
theorem manuscript_rounding_structural_bounds (H : Hypergraph)
    (hne : H.vertices.Nonempty) (T : Finset ℕ) :
    (min (8 + 4 * Real.log ((H.induce T).independenceNumber : ℝ))
      (6 * (H.degeneracy : ℝ)) + 1 ≤ 7 * (H.degeneracy : ℝ)) ∧
    (min (8 + 4 * Real.log ((H.induce T).independenceNumber : ℝ))
      (6 * (H.degeneracy : ℝ)) + 1 ≤
      13 * max 1 (Real.log (H.independenceNumber : ℝ) / Real.log 2)) := by
  have hd : (1 : ℝ) ≤ H.degeneracy := by exact_mod_cast H.degeneracy_ge_one hne
  have hm := log_nat_mono (H.structure_hereditary T).2
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  let L := max 1 (Real.log (H.independenceNumber : ℝ) / Real.log 2)
  have hL : 1 ≤ L := le_max_left _ _
  have hlog : Real.log (H.independenceNumber : ℝ) ≤ L := by
    have hh : Real.log (H.independenceNumber : ℝ) ≤ L * Real.log 2 :=
      (div_le_iff₀ h2).mp (le_max_right _ _)
    have := mul_le_mul_of_nonneg_left h2le (by linarith : 0 ≤ L)
    linarith
  constructor
  · linarith [min_le_right (8 + 4 * Real.log ((H.induce T).independenceNumber : ℝ))
      (6 * (H.degeneracy : ℝ))]
  · change _ ≤ 13 * L
    linarith [min_le_left (8 + 4 * Real.log ((H.induce T).independenceNumber : ℝ))
      (6 * (H.degeneracy : ℝ))]

/-- The manuscript's rounding proposition, with one separator satisfying both
bounds and one universal constant. This is Proposition 6.2 in the blueprint. -/
theorem manuscript_balanced_separator_rounding : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (H : Hypergraph) (γ x : ℕ → ℝ), H.EdgeWeight γ →
    H.FractionalBalanced γ (1 / 2) x →
    ∃ S ⊆ H.vertices, H.IntegralBalanced γ (5 / 6) S ∧
      H.setCoverCost S ≤ C₀ * (H.degeneracy : ℝ) * H.coverCost x *
        (Real.log (max 2 (H.coverCost x)) / Real.log 2) ∧
      H.setCoverCost S ≤ C₀ *
        max 1 (Real.log (H.independenceNumber : ℝ) / Real.log 2) * H.coverCost x *
        (Real.log (max 2 (H.coverCost x)) / Real.log 2) := by
  refine ⟨1560, by norm_num, ?_⟩
  intro H γ x hγ hx
  let q := H.coverCost x
  let L := Real.log (max 2 q) / Real.log 2
  have hq : 0 ≤ q := H.coverCost_nonneg x
  have hL : 0 ≤ L := by
    apply div_nonneg
    · exact Real.log_nonneg (by linarith [le_max_left (2 : ℝ) q])
    · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  by_cases hempty : H.IntegralBalanced γ (5 / 6) ∅
  · refine ⟨∅, empty_subset _, hempty, ?_, ?_⟩ <;>
      rw [show H.setCoverCost ∅ = 0 from H.coverCost_eq_zero_of_nonpos (by simp [indicator])]
    · change 0 ≤ 1560 * (H.degeneracy : ℝ) * q * L
      positivity
    · change 0 ≤ 1560 * max 1 _ * q * L
      positivity
  · have hne : H.vertices.Nonempty := by
      have he : H.edges.Nonempty := by
        by_contra h
        have hz := not_nonempty_iff_eq_empty.mp h
        have := hγ.2
        simp [hz] at this
      obtain ⟨e, he⟩ := he
      obtain ⟨v, hv⟩ := H.edge_nonempty e he
      exact ⟨v, H.edge_subset e he hv⟩
    have hn : ¬ H.IntegralBalanced γ
        ((1 + 3 * (1 / 2 : ℝ)) / (2 + 2 * (1 / 2 : ℝ))) ∅ := by
      norm_num
      exact hempty
    obtain ⟨S, hS, hbal, hcost⟩ := balanced_rounding H γ x (1 / 2)
      (by norm_num) hγ.1 hx hn
    let T := H.vertices.filter (fun v => x v ≠ 0)
    let A := min (8 + 4 * Real.log ((H.induce T).independenceNumber : ℝ))
      (6 * (H.degeneracy : ℝ)) + 1
    have hA : 0 ≤ A := by
      have := log_nat_nonneg (H.induce T).independenceNumber
      dsimp [A]
      positivity
    have hsharp : H.setCoverCost S ≤ A * (120 * q * L) := by
      calc
        _ ≤ _ := hcost
        _ = A * (((44 + 8 * (Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2)) /
            (1 - (1 / 2 : ℝ))) * q) := by dsimp [A, T, q]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (manuscript_rounding_cost_bound hq) hA
    obtain ⟨hd, ha⟩ := H.manuscript_rounding_structural_bounds hne T
    have hd' : A ≤ 13 * (H.degeneracy : ℝ) := by
      dsimp [A]
      linarith [Nat.cast_nonneg (α := ℝ) H.degeneracy]
    refine ⟨S, hS.trans (filter_subset _ _), by norm_num at hbal; exact hbal, ?_, ?_⟩
    · calc
        _ ≤ A * (120 * q * L) := hsharp
        _ ≤ (13 * (H.degeneracy : ℝ)) * (120 * q * L) :=
          mul_le_mul_of_nonneg_right hd' (by positivity)
        _ = _ := by dsimp [q, L]; ring
    · calc
        _ ≤ A * (120 * q * L) := hsharp
        _ ≤ (13 * max 1 (Real.log (H.independenceNumber : ℝ) / Real.log 2)) *
            (120 * q * L) := mul_le_mul_of_nonneg_right ha (by positivity)
        _ = _ := by dsimp [q, L]; ring

/-- The manuscript's main width comparison, with no external theorem hypothesis. -/
theorem main_width_comparison : MainWidthComparison :=
  main_width_comparison_of_rounding balanced_rounding

end Paper.Hypergraph
