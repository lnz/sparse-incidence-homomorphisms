import Paper.TwoTerminalRounding
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace Paper.Hypergraph

def levelMeasure : Measure ℝ := volume.restrict (Ioo 0 1)

instance : IsProbabilityMeasure levelMeasure := by
  constructor
  simp [levelMeasure]

/-- The integration step following Observation 4.6 for a bounded multiplier. -/
theorem integral_le_one_add_two_log {f : ℝ → ℝ} {M : ℝ}
    (hf : Measurable f) (hn : ∀ r, 0 ≤ f r) (hM : 1 ≤ M)
    (hb : ∀ r, f r ≤ M)
    (htail : ∀ t, 1 ≤ t → levelMeasure.real {r | t ≤ f r} ≤ 2 / t) :
    ∫ r, f r ∂levelMeasure ≤ 1 + 2 * Real.log M := by
  have hi : Integrable f levelMeasure :=
    (integrable_const M).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => by simpa [Real.norm_eq_abs, abs_of_nonneg (hn r)] using hb r)
  let g : ℝ → ℝ := fun t => levelMeasure.real {r | t ≤ f r}
  have hganti : Antitone g := by
    intro a b hab
    exact measureReal_mono (fun r hr => hab.trans hr)
  have hgn : ∀ t, 0 ≤ g t := fun _ => ENNReal.toReal_nonneg
  have hgb : ∀ t, g t ≤ 1 := fun _ => measureReal_le_one
  have hgi (a b : ℝ) : IntervalIntegrable g volume a b := by
    have h : IntegrableOn g (uIcc a b) volume :=
      (integrableOn_const (C := (1 : ℝ)) isCompact_uIcc.measure_ne_top).mono' hganti.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by simpa [Real.norm_eq_abs, abs_of_nonneg (hgn t)] using hgb t)
    exact h.intervalIntegrable
  rw [hi.integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall hn) (Filter.Eventually.of_forall hb)]
  change (∫ t in Ioc 0 M, g t) ≤ _
  rw [← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ M),
    ← intervalIntegral.integral_add_adjacent_intervals (hgi 0 1) (hgi 1 M)]
  have hfirst : (∫ t in (0 : ℝ)..1, g t) ≤ 1 := by
    calc
      _ ≤ ∫ _ in (0 : ℝ)..1, (1 : ℝ) :=
        intervalIntegral.integral_mono_on (by norm_num) (hgi 0 1) intervalIntegrable_const
          (fun t ht => hgb t)
      _ = 1 := by simp
  have hinv : IntervalIntegrable (fun t : ℝ => 2 / t) volume 1 M := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro t ht
    rw [uIcc_of_le hM] at ht
    change t ≠ 0
    linarith [ht.1]
  have hlast : (∫ t in (1 : ℝ)..M, g t) ≤ 2 * Real.log M := by
    calc
      _ ≤ ∫ t in (1 : ℝ)..M, 2 / t :=
        intervalIntegral.integral_mono_on hM (hgi 1 M) hinv (fun t ht => htail t ht.1)
      _ = 2 * Real.log M := by
        simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul,
          integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) (by linarith : 0 < M), inv_one, mul_one]
  exact add_le_add hfirst hlast

def vertexMultiplier (x d : ℕ → ℝ) (v : ℕ) : ℝ → ℝ :=
  (Icc (d v - x v) (d v)).indicator (fun _ => 1 / x v)

def intervalMultiplier (V : Finset ℕ) (hne : V.Nonempty) (x d : ℕ → ℝ) (r : ℝ) : ℝ :=
  V.sup' hne (fun v => vertexMultiplier x d v r)

theorem vertexMultiplier_measurable (x d : ℕ → ℝ) (v : ℕ) :
    Measurable (vertexMultiplier x d v) := measurable_const.indicator measurableSet_Icc

theorem intervalMultiplier_measurable (V : Finset ℕ) (hne : V.Nonempty) (x d : ℕ → ℝ) :
    Measurable (intervalMultiplier V hne x d) := by
  convert Finset.measurable_sup' hne (fun v _ => vertexMultiplier_measurable x d v) using 1
  funext r
  simp [intervalMultiplier, Finset.sup'_apply]

theorem vertexMultiplier_nonneg {x d : ℕ → ℝ} {v : ℕ} (hx : 0 ≤ x v) (r : ℝ) :
    0 ≤ vertexMultiplier x d v r := by
  exact Set.indicator_nonneg (fun _ _ => div_nonneg zero_le_one hx) r

theorem intervalMultiplier_nonneg {V : Finset ℕ} (hne : V.Nonempty) {x d : ℕ → ℝ}
    (hx : ∀ v ∈ V, 0 ≤ x v) (r : ℝ) : 0 ≤ intervalMultiplier V hne x d r := by
  obtain ⟨v, hv⟩ := hne
  unfold intervalMultiplier
  exact (vertexMultiplier_nonneg (d := d) (hx v hv) r).trans
    (Finset.le_sup' (fun w => vertexMultiplier x d w r) hv)

theorem intervalMultiplier_le {V : Finset ℕ} (hne : V.Nonempty) {x d : ℕ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hx : ∀ v ∈ V, x v = 0 ∨ ε ≤ x v) (r : ℝ) :
    intervalMultiplier V hne x d r ≤ 1 / ε := by
  apply Finset.sup'_le
  intro v hv
  rcases hx v hv with h0 | hpos
  · simp [vertexMultiplier, h0]
    positivity
  · by_cases hr : r ∈ Icc (d v - x v) (d v)
    · simpa [vertexMultiplier, hr] using one_div_le_one_div_of_le hε hpos
    · simp [vertexMultiplier, hr, le_of_lt hε]

theorem levelMeasure_Icc_le (a b : ℝ) : levelMeasure.real (Icc a b) ≤ max (b - a) 0 := by
  calc
    _ = volume.real (Icc a b ∩ Ioo 0 1) := measureReal_restrict_apply measurableSet_Icc
    _ ≤ volume.real (Icc a b) := measureReal_mono inter_subset_left isCompact_Icc.measure_ne_top
    _ = _ := Real.volume_real_Icc

/-- All intervals on one edge contain a common point, so their short members
lie in an interval of length at most twice their maximum length. -/
theorem intervalMultiplier_tail {V : Finset ℕ} (hne : V.Nonempty) {x d : ℕ → ℝ} {q : ℝ}
    (hq : ∀ v ∈ V, d v - x v ≤ q ∧ q ≤ d v) {t : ℝ} (ht : 0 < t) :
    levelMeasure.real {r | t ≤ intervalMultiplier V hne x d r} ≤ 2 / t := by
  have hsub : {r | t ≤ intervalMultiplier V hne x d r} ⊆ Icc (q - 1 / t) (q + 1 / t) := by
    intro r hr
    obtain ⟨v, hv, heq⟩ := Finset.exists_mem_eq_sup' hne (fun v => vertexMultiplier x d v r)
    change t ≤ V.sup' hne _ at hr
    rw [heq] at hr
    by_cases hrv : r ∈ Icc (d v - x v) (d v)
    swap
    · simp [vertexMultiplier, hrv] at hr
      linarith
    have hsmall : t ≤ 1 / x v := by simpa [vertexMultiplier, hrv] using hr
    have hxv : 0 < x v := one_div_pos.mp (ht.trans_le hsmall)
    have hxt : x v ≤ 1 / t := (le_div_iff₀ ht).2 (by
      have := (le_div_iff₀ hxv).1 hsmall
      nlinarith)
    have hqv := hq v hv
    exact ⟨by linarith [hrv.1, hrv.2], by linarith [hrv.1, hrv.2]⟩
  calc
    _ ≤ levelMeasure.real (Icc (q - 1 / t) (q + 1 / t)) := measureReal_mono hsub
    _ ≤ max ((q + 1 / t) - (q - 1 / t)) 0 := levelMeasure_Icc_le _ _
    _ = 2 / t := by
      have hn : 0 ≤ (q + 1 / t) - (q - 1 / t) := by linarith [one_div_pos.mpr ht]
      rw [max_eq_left hn]
      ring

theorem intervalMultiplier_integral_le {V : Finset ℕ} (hne : V.Nonempty) {x d : ℕ → ℝ}
    {ε q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hx : ∀ v ∈ V, x v = 0 ∨ ε ≤ x v)
    (hq : ∀ v ∈ V, d v - x v ≤ q ∧ q ≤ d v) :
    ∫ r, intervalMultiplier V hne x d r ∂levelMeasure ≤ 1 + 2 * Real.log (1 / ε) := by
  apply integral_le_one_add_two_log (intervalMultiplier_measurable V hne x d)
    (intervalMultiplier_nonneg hne (fun v hv => by rcases hx v hv with h | h <;> linarith))
    ((le_div_iff₀ hε).2 (by simpa using hε1)) (intervalMultiplier_le hne hε hx)
  intro t ht
  exact intervalMultiplier_tail hne hq (by linarith)

/-- Select an interior level whose cover cost is at most its expectation. -/
theorem rounding_by_average (H : Hypergraph) {A B : Finset ℕ} {x d : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hB : B ⊆ H.vertices)
    (ha : ∀ v ∈ A, d v ≤ x v) (hb : ∀ v ∈ B, 1 ≤ d v)
    (hstep : ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Adj u v → d v ≤ d u + x v)
    (m : ℕ → ℝ → ℝ) (hi : ∀ e ∈ H.edges, Integrable (m e) levelMeasure)
    (hc : ∀ r ∈ Ioo 0 1, H.Cover (indicator (H.levelSeparator x d r)) (fun e => m e r)) :
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralSeparator A B S ∧
      H.setCoverCost S ≤ ∑ e ∈ H.edges, ∫ r, m e r ∂levelMeasure := by
  have hsum : Integrable (fun r => ∑ e ∈ H.edges, m e r) levelMeasure := integrable_finsetSum _ hi
  have hnull : levelMeasure (Ioo (0 : ℝ) 1)ᶜ = 0 := by simp [levelMeasure]
  obtain ⟨r, hr, hcost⟩ := exists_notMem_null_le_integral hsum hnull
  have hr' : r ∈ Ioo (0 : ℝ) 1 := by simpa using hr
  refine ⟨H.levelSeparator x d r, H.levelSeparator_subset_support x d r,
    H.levelSeparator_integral hA hB ha hb hstep hr', ?_⟩
  apply (H.coverCost_le (hc r hr')).trans
  rwa [integral_finsetSum _ hi] at hcost

/-- The minimum-demand bound from Section 4.1 with an explicit positive threshold. -/
theorem twoTerminal_minimum_weight_rounding (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hB : B ⊆ H.vertices) (hx : H.FractionalSeparator A B x)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : ∀ v ∈ H.vertices, x v = 0 ∨ ε ≤ x v) :
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralSeparator A B S ∧
      H.setCoverCost S ≤ (1 + 2 * Real.log (1 / ε)) * H.coverCost x := by
  obtain ⟨d, hd, ha, hb, hstep⟩ := H.twoTerminal_distance_labels hA hx
  obtain ⟨y, hy, _, hcost⟩ := H.coverCost_attained hx.1
  let m : ℕ → ℝ → ℝ := fun e r => if he : e ∈ H.edges then
    intervalMultiplier (H.edge e) (H.edge_nonempty e he) x d r * y e else 0
  have hmult_i (e : ℕ) (he : e ∈ H.edges) :
      Integrable (intervalMultiplier (H.edge e) (H.edge_nonempty e he) x d) levelMeasure := by
    apply (integrable_const (1 / ε)).mono'
      (intervalMultiplier_measurable _ _ _ _).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro r
    rw [Real.norm_eq_abs, abs_of_nonneg (intervalMultiplier_nonneg _
      (fun v hv => (hx.1 v (H.edge_subset e he hv)).1) r)]
    exact intervalMultiplier_le _ hε (fun v hv => hsmall v (H.edge_subset e he hv)) r
  have hi : ∀ e ∈ H.edges, Integrable (m e) levelMeasure := by
    intro e he
    simpa [m, he] using (hmult_i e he).mul_const (y e)
  obtain ⟨S, hS, hsep, hbound⟩ := H.rounding_by_average hA hB ha hb hstep m hi (by
    intro r hr
    have hm0 : ∀ e ∈ H.edges, 0 ≤ m e r := by
      intro e he
      simp only [m, dif_pos he]
      exact mul_nonneg (intervalMultiplier_nonneg _
        (fun v hv => (hx.1 v (H.edge_subset e he hv)).1) r) (hy.1 e he)
    refine ⟨hm0, ?_⟩
    intro v hv
    by_cases hvS : v ∈ H.levelSeparator x d r
    swap
    · simp only [indicator, if_neg hvS]
      exact Finset.sum_nonneg (fun e he => hm0 e (Finset.mem_filter.mp he).1)
    have hvsel := (Finset.mem_filter.mp hvS).2
    have hxv : 0 < x v := lt_of_le_of_ne (hx.1 v hv).1 hvsel.1.symm
    have hmul : 1 ≤ (1 / x v) * ∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), y e := by
      have h := mul_le_mul_of_nonneg_left (hy.2 v hv) (by positivity : 0 ≤ 1 / x v)
      simpa [ne_of_gt hxv] using h
    simp only [indicator, if_pos hvS]
    apply hmul.trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    obtain ⟨he, hve⟩ := Finset.mem_filter.mp he
    simp only [m, dif_pos he]
    apply mul_le_mul_of_nonneg_right _ (hy.1 e he)
    have h := Finset.le_sup' (fun w => vertexMultiplier x d w r) hve
    change 1 / x v ≤ (H.edge e).sup' _ (fun w => vertexMultiplier x d w r)
    have heq : vertexMultiplier x d v r = 1 / x v :=
      Set.indicator_of_mem (show r ∈ Icc (d v - x v) (d v) from hvsel.2) _
    rwa [heq] at h)
  refine ⟨S, hS, hsep, hbound.trans ?_⟩
  rw [hcost, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨q, hq⟩ := H.edge_intervals_common_point hstep (fun v hv => (hx.1 v hv).1) he
  simp only [m, dif_pos he, integral_mul_const]
  exact mul_le_mul_of_nonneg_right (intervalMultiplier_integral_le _ hε hε1
    (fun v hv => hsmall v (H.edge_subset e he hv)) hq) (hy.1 e he)

end Paper.Hypergraph
