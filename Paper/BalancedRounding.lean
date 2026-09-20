import Paper.RoundingRecursion
import Paper.TwoTerminalRounding

/-!
# Balanced rounding from two-terminal rounding

This module discharges the geometric and recursive steps of Theorem 5.6.
Theorem 4.1 remains an explicit hypothesis until its analytic rounding
estimates are formalized.
-/

noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

namespace Paper.Hypergraph

theorem rounding_volume_factor_le {φ : ℝ} (hφ : 0 < φ ∧ φ < 1) :
    φ / (1 - (1 - φ) / 2) ≤ (1 + 3 * φ) / (2 + 2 * φ) := by
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith [mul_nonneg (show 0 ≤ 1 - φ by linarith) (show 0 ≤ 1 + φ by linarith)]

/-- The nontrivial branch has enough cover cost for the logarithmic layer budget. -/
theorem nontrivial_rounding_cover_lower_bound (H : Hypergraph) {γ x : ℕ → ℝ} {φ : ℝ}
    (hφ : 0 < φ ∧ φ < 1) (hγ : ∀ e ∈ H.edges, 0 ≤ γ e)
    (hx : H.FractionalBalanced γ φ x)
    (hnontrivial : ¬ H.IntegralBalanced γ ((1 + 3 * φ) / (2 + 2 * φ)) ∅) :
    (1 - φ) / 4 ≤ H.coverCost x := by
  by_contra h
  have hsmall : H.coverCost x < (1 - φ) / 4 := lt_of_not_ge h
  apply hnontrivial
  refine ⟨empty_subset _, ?_⟩
  intro K hK
  simp only [sdiff_empty] at hK
  have hKV := mem_powerset.mp (mem_filter.mp hK).1
  obtain ⟨c, hcK, _⟩ := (mem_filter.mp hK).2
  have hc := hKV hcK
  have hKB : K ⊆ H.roundingBall x H.vertices c ((1 - φ) / 2) := by
    intro v hv
    apply mem_filter.mpr ⟨hKV hv, ?_⟩
    have hcv := ((H.induce H.vertices).component_mem_iff_reachable hK hcK (hKV hv)).mp hv
    have hd := H.induced_vertexDistance_le_two_coverCost (fun z hz => (hx.1 z hz).1)
      H.vertices hc hcv
    linarith
  have hb := H.roundingBall_volume_le hγ hx H.vertices hc
    (show (1 - φ) / 2 < 1 by linarith)
  change H.edgeVolume γ K ≤ _
  exact ((H.edgeVolume_mono hγ hKB).trans hb).trans
    (mul_le_mul_of_nonneg_right (rounding_volume_factor_le hφ) (sum_nonneg hγ))

theorem rounding_coefficient_identity {K φ : ℝ} (hK : 0 < K) (hφ : φ < 1) :
    (18 + 4 * Real.logb 2 (K / ((1 - φ) / 2))) / ((1 - φ) / 2) =
      (44 + 8 * (Real.log (K / (1 - φ)) / Real.log 2)) / (1 - φ) := by
  have hden : 1 - φ ≠ 0 := ne_of_gt (sub_pos.mpr hφ)
  have harg : K / ((1 - φ) / 2) = 2 * (K / (1 - φ)) := by field_simp
  rw [harg, Real.logb_mul (by norm_num) (div_ne_zero hK.ne' hden),
    Real.logb_self_eq_one (by norm_num)]
  simp only [Real.logb]
  field_simp
  ring

/-- The repaired proof of Theorem 5.6, with Theorem 4.1 as its sole
remaining mathematical input. This does not assert an unconditional theorem. -/
theorem externalRounding_of_twoTerminalRounding (round : TwoTerminalRounding) : ExternalRounding := by
  intro H γ x φ hφ hγ hx hnontrivial
  have hγ0 : ∀ e ∈ H.edges, 0 ≤ γ e := fun e he => (hγ e he).1
  have hn : ∀ v ∈ H.vertices, 0 ≤ x v := fun v hv => (hx.1 v hv).1
  let r := (1 - φ) / 2
  let L := Real.logb 2 (H.coverCost x / r)
  let t := (18 + 4 * L) / r
  let a := t⁻¹
  let R := H.vertices.filter (fun v => x v ≠ 0)
  let C := H.twoTerminalFactor R
  let S₀ := H.roundingThreshold x a
  let Q := H.vertices \ S₀
  have hr : 0 < r ∧ r < 1 := by dsimp [r]; constructor <;> linarith
  have hK : r / 2 ≤ H.coverCost x := by
    have h := H.nontrivial_rounding_cover_lower_bound hφ hγ0 hx hnontrivial
    dsimp [r]
    linarith
  have hKpos : 0 < H.coverCost x := by linarith [hr.1]
  have hL : -1 ≤ L := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (div_pos hKpos hr.1)).2
    norm_num
    exact (le_div_iff₀ hr.1).2 (by linarith)
  have ht : 0 < t := div_pos (by linarith) hr.1
  have ha : 0 < a := inv_pos.mpr ht
  have hC : 0 ≤ C := H.twoTerminalFactor_nonneg R
  have hthreshold : a = (r / (9 + 2 * L)) / 2 := by
    dsimp [a, t]
    rw [inv_div, show 18 + 4 * L = (9 + 2 * L) * 2 by ring]
    exact (div_div r (9 + 2 * L) 2).symm
  have hcut : ∀ U ⊆ Q, U.Nonempty → Nonempty
      (H.CutoffPiece γ x U (φ / (1 - r) * ∑ e ∈ H.edges, γ e) (C * t)) := by
    intro U hU hne
    apply H.cutoff_from_rounding hγ0 hx hr hC hK (hU.trans sdiff_subset) hne
    · intro v hv
      have h := H.demand_lt_threshold_of_mem_compl x a (hU hv)
      rwa [hthreshold] at h
    · exact fun A B z hA hB hz hsupp => twoTerminalRounding_induced round H U x A B z hA hB hz hsupp
  obtain ⟨S, hSQ, hSR, hbal, hcost⟩ := H.cutoff_recursion hγ0 hn (mul_nonneg hC ht.le)
    Q sdiff_subset hcut
  refine ⟨S₀ ∪ S, union_subset (H.roundingThreshold_subset_support x ha) hSR, ?_, ?_⟩
  · refine ⟨union_subset (filter_subset _ _) (hSQ.trans sdiff_subset), ?_⟩
    intro K hKcomp
    have hset : H.vertices \ (S₀ ∪ S) = Q \ S := by
      ext v
      simp [Q]
      tauto
    rw [hset] at hKcomp
    change H.edgeVolume γ K ≤ _
    exact (hbal K hKcomp).trans
      (mul_le_mul_of_nonneg_right (rounding_volume_factor_le hφ) (sum_nonneg hγ0))
  · have hcost' : H.setCoverCost S ≤ C * t * H.coverCost x :=
      hcost.trans (mul_le_mul_of_nonneg_left (H.restrictDemand_cost_le hn Q) (mul_nonneg hC ht.le))
    have hcost₀ : H.setCoverCost S₀ ≤ t * H.coverCost x := by
      simpa [a] using H.roundingThreshold_cost_le hn ha
    have hfinal : H.setCoverCost (S₀ ∪ S) ≤ (C + 1) * t * H.coverCost x := by
      calc
        _ ≤ H.setCoverCost S₀ + H.setCoverCost S := H.setCoverCost_union_le _ _
        _ ≤ t * H.coverCost x + C * t * H.coverCost x := add_le_add hcost₀ hcost'
        _ = _ := by ring
    have ht_eq := rounding_coefficient_identity hKpos hφ.2
    change t = _ at ht_eq
    simpa only [ht_eq, C, R, twoTerminalFactor] using hfinal

end Paper.Hypergraph
