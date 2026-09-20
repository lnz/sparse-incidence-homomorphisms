import Paper.Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Towards the external rounding theorem

This module follows Section 5.1 of Korchemna et al., arXiv 2409.20172v1.
It proves Observation 5.7, the cover accounting in Observation 5.12, and
the cost estimate of Observation 5.13 from supplied cut-off pieces.
The two-terminal rounding theorem and the cut-off construction remain unproved.
In particular, this module does not yet prove `ExternalRounding`.
-/

noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

namespace Paper.Hypergraph

/-- The total weight of edges meeting a vertex set. -/
def edgeVolume (H : Hypergraph) (γ : ℕ → ℝ) (Q : Finset ℕ) : ℝ :=
  ∑ e ∈ H.edges.filter (fun e => ¬ Disjoint (H.edge e) Q), γ e

/-- A ball in the induced hypergraph, with the source's truncated distance. -/
def roundingBall (H : Hypergraph) (x : ℕ → ℝ) (Q : Finset ℕ)
    (c : ℕ) (r : ℝ) : Finset ℕ :=
  (H.vertices ∩ Q).filter fun v => (H.induce Q).vertexDistance x c v ≤ r

theorem edgeVolume_mono (H : Hypergraph) {γ : ℕ → ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) {A B : Finset ℕ} (hAB : A ⊆ B) :
    H.edgeVolume γ A ≤ H.edgeVolume γ B := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨he, hm⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨he, fun hd => hm (hd.mono_right hAB)⟩
  · intro e he _
    exact hγ e (mem_filter.mp he).1

theorem vertexDistance_le_one (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {u v : ℕ} (hu : u ∈ H.vertices) :
    H.vertexDistance x u v ≤ 1 :=
  H.vertexDistance_le_option hx hu (Set.mem_insert _ _)

theorem vertexDistance_le_induce (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (Q : Finset ℕ)
    {u v : ℕ} (hu : u ∈ H.vertices) :
    H.vertexDistance x u v ≤ (H.induce Q).vertexDistance x u v := by
  apply le_csInf ⟨1, Set.mem_insert _ _⟩
  rintro r (rfl | ⟨p, hp, rfl⟩)
  · exact H.vertexDistance_le_one hx hu
  · apply H.vertexDistance_le_option hx hu
    refine Set.mem_insert_of_mem 1 ⟨p.mapLe (H.primal_induce_le Q), hp.mapLe _, ?_⟩
    rw [SimpleGraph.Walk.support_mapLe_eq_support]

theorem edgeDistance_le_vertexDistance (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {e f u v : ℕ}
    (he : e ∈ H.edges) (hu : u ∈ H.edge e) (hv : v ∈ H.edge f) :
    H.edgeDistance x e f ≤ H.vertexDistance x u v := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨a, ha, b, hb, rfl⟩
    exact H.vertexDistance_nonneg hx (H.edge_subset e he ha)
  · exact ⟨u, hu, v, hv, rfl⟩

theorem edgeDistance_le_one (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {e f : ℕ}
    (he : e ∈ H.edges) (hf : f ∈ H.edges) : H.edgeDistance x e f ≤ 1 := by
  obtain ⟨u, hu⟩ := H.edge_nonempty e he
  obtain ⟨v, hv⟩ := H.edge_nonempty f hf
  exact (H.edgeDistance_le_vertexDistance hx he hu hv).trans
    (H.vertexDistance_le_one hx (H.edge_subset e he hu))

/-- Observation 5.7, including balls in arbitrary induced subhypergraphs. -/
theorem roundingBall_volume_le (H : Hypergraph) {γ x : ℕ → ℝ} {φ r : ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (hx : H.FractionalBalanced γ φ x)
    (Q : Finset ℕ) {c : ℕ} (hc : c ∈ H.vertices ∩ Q) (hr : r < 1) :
    H.edgeVolume γ (H.roundingBall x Q c r) ≤
      φ / (1 - r) * ∑ e ∈ H.edges, γ e := by
  let B := H.roundingBall x Q c r
  have hn : ∀ v ∈ H.vertices, 0 ≤ x v := fun v hv => (hx.1 v hv).1
  obtain ⟨e, he, hce⟩ := H.no_isolated c (mem_inter.mp hc).1
  have hd : ∀ f ∈ H.edges, ¬ Disjoint (H.edge f) B → H.edgeDistance x e f ≤ r := by
    intro f hf hmeet
    obtain ⟨v, hvf, hvB⟩ := not_disjoint_iff.mp hmeet
    exact (H.edgeDistance_le_vertexDistance hn he hce hvf).trans
      ((H.vertexDistance_le_induce hn Q (mem_inter.mp hc).1).trans
        (mem_filter.mp hvB).2)
  have hsum : (∑ f ∈ H.edges, γ f * H.edgeDistance x e f) ≤
      (∑ f ∈ H.edges, γ f) - (1 - r) * H.edgeVolume γ B := by
    calc
      _ ≤ ∑ f ∈ H.edges, (γ f - (1 - r) *
          (if ¬ Disjoint (H.edge f) B then γ f else 0)) := by
        apply sum_le_sum
        intro f hf
        split_ifs with hm
        · simpa using mul_le_mul_of_nonneg_left (H.edgeDistance_le_one hn he hf) (hγ f hf)
        · have := mul_le_mul_of_nonneg_left (hd f hf hm) (hγ f hf)
          nlinarith
      _ = _ := by rw [sum_sub_distrib, ← mul_sum]; simp [edgeVolume, sum_filter]
  have hbal := (hx.2 e he).trans hsum
  rw [div_mul_eq_mul_div, le_div_iff₀ (sub_pos.mpr hr)]
  nlinarith

/-- The initial threshold set in Algorithm 1. -/
def roundingThreshold (H : Hypergraph) (x : ℕ → ℝ) (a : ℝ) : Finset ℕ :=
  H.vertices.filter fun v => a ≤ x v

theorem roundingThreshold_subset_support (H : Hypergraph) (x : ℕ → ℝ)
    {a : ℝ} (ha : 0 < a) :
    H.roundingThreshold x a ⊆ H.vertices.filter (fun v => x v ≠ 0) := by
  intro v hv
  obtain ⟨hv, hax⟩ := mem_filter.mp hv
  exact mem_filter.mpr ⟨hv, (ha.trans_le hax).ne'⟩

theorem demand_lt_threshold_of_mem_compl (H : Hypergraph) (x : ℕ → ℝ)
    (a : ℝ) {v : ℕ} (hv : v ∈ H.vertices \ H.roundingThreshold x a) : x v < a := by
  obtain ⟨hv, hn⟩ := mem_sdiff.mp hv
  exact lt_of_not_ge fun h => hn (mem_filter.mpr ⟨hv, h⟩)

/-- The threshold contribution in Observation 5.13. -/
theorem roundingThreshold_cost_le (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {a : ℝ} (ha : 0 < a) :
    H.setCoverCost (H.roundingThreshold x a) ≤ a⁻¹ * H.coverCost x := by
  calc
    _ ≤ H.coverCost (a⁻¹ • x) := by
      apply H.coverCost_mono
      intro v hv
      simp only [indicator, Pi.smul_apply, smul_eq_mul]
      split_ifs with hm
      · have hax := (mem_filter.mp hm).2
        calc
          1 = a⁻¹ * a := (inv_mul_cancel₀ ha.ne').symm
          _ ≤ a⁻¹ * x v := mul_le_mul_of_nonneg_left hax (inv_nonneg.mpr ha.le)
      · exact mul_nonneg (inv_nonneg.mpr ha.le) (hx v hv)
    _ = _ := H.coverCost_smul x (inv_pos.mpr ha)

/-- Restrict a demand to a vertex set, retaining the ambient hypergraph. -/
def restrictDemand (x : ℕ → ℝ) (P : Finset ℕ) (v : ℕ) : ℝ :=
  if v ∈ P then x v else 0

/-- The cover accounting in Observation 5.12. Each edge meets at most one piece. -/
theorem sum_restrictDemand_cost_le (H : Hypergraph) {ι : Type*}
    (I : Finset ι) (P : ι → Finset ℕ) (x : ℕ → ℝ)
    (hsep : ∀ e ∈ H.edges, ∀ i ∈ I, ∀ j ∈ I,
      ¬ Disjoint (H.edge e) (P i) → ¬ Disjoint (H.edge e) (P j) → i = j) :
    (∑ i ∈ I, H.coverCost (restrictDemand x (P i))) ≤ H.coverCost x := by
  classical
  apply H.le_coverCost
  intro y hy
  let z : ι → ℕ → ℝ := fun i e => if ¬ Disjoint (H.edge e) (P i) then y e else 0
  have hz : ∀ i, H.Cover (restrictDemand x (P i)) (z i) := by
    intro i
    constructor
    · intro e he
      dsimp [z]
      split_ifs <;> first | exact hy.1 e he | exact le_rfl
    · intro v hv
      by_cases hvi : v ∈ P i
      · have heq : (∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), z i e) =
            ∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), y e := by
          apply sum_congr rfl
          intro e he
          have hm : ¬ Disjoint (H.edge e) (P i) :=
            not_disjoint_iff.mpr ⟨v, (mem_filter.mp he).2, hvi⟩
          simp [z, hm]
        simpa [restrictDemand, hvi, heq] using hy.2 v hv
      · simp only [restrictDemand, if_neg hvi]
        apply sum_nonneg
        intro e he
        dsimp [z]
        split_ifs <;> first | exact hy.1 e (mem_filter.mp he).1 | exact le_rfl
  calc
    _ ≤ ∑ i ∈ I, ∑ e ∈ H.edges, z i e := sum_le_sum fun i _ => H.coverCost_le (hz i)
    _ = ∑ e ∈ H.edges, ∑ i ∈ I, z i e := sum_comm
    _ ≤ ∑ e ∈ H.edges, y e := by
      apply sum_le_sum
      intro e he
      by_cases hm : ∃ i ∈ I, ¬ Disjoint (H.edge e) (P i)
      · obtain ⟨i, hi, hmi⟩ := hm
        have hs : (∑ j ∈ I, z j e) = z i e := by
          apply sum_eq_single i
          · intro j hj hji
            have hd : Disjoint (H.edge e) (P j) := by
              by_contra hnd
              exact hji (hsep e he j hj i hi hnd hmi)
            simp [z, hd]
          · exact fun h => (h hi).elim
        rw [hs]
        simp [z, hmi]
      · have hz0 : ∀ i ∈ I, z i e = 0 := by
          intro i hi
          have hd : Disjoint (H.edge e) (P i) := by
            by_contra hnd
            exact hm ⟨i, hi, hnd⟩
          simp [z, hd]
        rw [sum_eq_zero hz0]
        exact hy.1 e he

/-- Subadditivity for the final union of separators. -/
theorem setCoverCost_biUnion_le (H : Hypergraph) {ι : Type*}
    (I : Finset ι) (S : ι → Finset ℕ) :
    H.setCoverCost (I.biUnion S) ≤ ∑ i ∈ I, H.setCoverCost (S i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [biUnion_empty, sum_empty]
    exact (H.coverCost_eq_zero_of_nonpos (x := indicator ∅)
      (fun _ _ => by simp [indicator])).le
  | @insert i I hi ih =>
    rw [biUnion_insert, sum_insert hi]
    exact (H.setCoverCost_union_le _ _).trans (add_le_add_right ih _)

/-- Observation 5.13 once the cut-off pieces and their separators are supplied. -/
theorem rounding_union_cost_le (H : Hypergraph) {ι : Type*}
    (I : Finset ι) (P S : ι → Finset ℕ) {x : ℕ → ℝ} {a A : ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (ha : 0 < a) (hA : 0 ≤ A)
    (hsep : ∀ e ∈ H.edges, ∀ i ∈ I, ∀ j ∈ I,
      ¬ Disjoint (H.edge e) (P i) → ¬ Disjoint (H.edge e) (P j) → i = j)
    (hcost : ∀ i ∈ I, H.setCoverCost (S i) ≤
      A * a⁻¹ * H.coverCost (restrictDemand x (P i))) :
    H.setCoverCost (H.roundingThreshold x a ∪ I.biUnion S) ≤
      (A + 1) * a⁻¹ * H.coverCost x := by
  have hp := H.sum_restrictDemand_cost_le I P x hsep
  have hs : (∑ i ∈ I, H.setCoverCost (S i)) ≤ A * a⁻¹ * H.coverCost x := by
    calc
      _ ≤ ∑ i ∈ I, A * a⁻¹ * H.coverCost (restrictDemand x (P i)) :=
        sum_le_sum hcost
      _ = A * a⁻¹ * ∑ i ∈ I, H.coverCost (restrictDemand x (P i)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg hA (inv_nonneg.mpr ha.le))
  calc
    _ ≤ H.setCoverCost (H.roundingThreshold x a) + H.setCoverCost (I.biUnion S) :=
      H.setCoverCost_union_le _ _
    _ ≤ a⁻¹ * H.coverCost x + A * a⁻¹ * H.coverCost x :=
      add_le_add (H.roundingThreshold_cost_le hx ha) ((H.setCoverCost_biUnion_le I S).trans hs)
    _ = _ := by ring

/-- A finite growth argument for the corrected cut-off construction. -/
theorem cutoff_layer_exists (a ℓ : ℕ → ℝ) (N : ℕ) {b K : ℝ}
    (hseed : b ≤ a 0) (hbudget : K < 2 ^ N * b) (hupper : a N ≤ K)
    (hadd : ∀ i < N, a i + ℓ i ≤ a (i + 1)) :
    ∃ i < N, ℓ i ≤ a i := by
  by_contra hn
  have hbad : ∀ i < N, a i < ℓ i := by
    intro i hi
    exact lt_of_not_ge fun h => hn ⟨i, hi, h⟩
  have hg : ∀ i ≤ N, 2 ^ i * b ≤ a i := by
    intro i hi
    induction i with
    | zero => simpa using hseed
    | succ i ih =>
      have hprev := ih (by omega)
      have hstep := hadd i (by omega)
      have hstrict := hbad i (by omega)
      rw [pow_succ]
      nlinarith
  have := hg N le_rfl
  linarith

/-- The corrected number of layers fits below radius r and forces growth
beyond the total cover cost. The constants of Lemma 5.9 are unchanged. -/
theorem cutoff_layer_parameters {r K : ℝ} (hr : 0 < r) (hK : r / 2 ≤ K) :
    let L := Real.logb 2 (K / r)
    let δ := r / (9 + 2 * L)
    ∃ N : ℕ, 0 < N ∧
      r / 4 + (N : ℝ) * (3 * δ / 2) ≤ r ∧
      K < (2 : ℝ) ^ N * (5 * r / 56) ∧
      ∀ q : ℝ, q < δ / 2 → 5 * r / 56 ≤ (r / 4 - q) / 2 := by
  dsimp
  let L := Real.logb 2 (K / r)
  have ht : 0 < K / r := div_pos (by linarith) hr
  have hL : -1 ≤ L := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) ht).2
    norm_num
    exact (le_div_iff₀ hr).2 (by linarith)
  have hD : 0 < 9 + 2 * L := by linarith
  let N : ℕ := ⌊L + 7 / 2⌋₊ + 1
  have hNlo : L + 7 / 2 < (N : ℝ) := by
    simpa [N] using Nat.lt_floor_add_one (L + 7 / 2)
  have hNhi : (N : ℝ) ≤ L + 9 / 2 := by
    have hf := Nat.floor_le (show 0 ≤ L + 7 / 2 by linarith)
    dsimp [N]
    push_cast
    linarith
  have hpowconst : (56 / 5 : ℝ) < (2 : ℝ) ^ (7 / 2 : ℝ) := by
    have hs : ((2 : ℝ) ^ (7 / 2 : ℝ)) ^ (2 : ℕ) = 128 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hn := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (7 / 2 : ℝ)
    nlinarith
  have hgrowth : (K / r) * (56 / 5) < (2 : ℝ) ^ N := by
    calc
      _ < (K / r) * (2 : ℝ) ^ (7 / 2 : ℝ) := mul_lt_mul_of_pos_left hpowconst ht
      _ = (2 : ℝ) ^ (L + 7 / 2) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        rw [show (2 : ℝ) ^ L = K / r from
          Real.rpow_logb (by norm_num) (by norm_num) ht]
      _ < (2 : ℝ) ^ N := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hNlo
  refine ⟨N, by dsimp [N]; omega, ?_, ?_, ?_⟩
  · change r / 4 + (N : ℝ) * (3 * (r / (9 + 2 * L)) / 2) ≤ r
    apply (le_of_mul_le_mul_right ?_ hD)
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hNhi hr.le]
  · have hg := mul_lt_mul_of_pos_right hgrowth hr
    field_simp at hg
    nlinarith
  · intro q hq
    change q < (r / (9 + 2 * L)) / 2 at hq
    have hδ : r / (9 + 2 * L) ≤ r / 7 := by
      apply div_le_div_of_nonneg_left hr.le (by norm_num)
      linarith
    linarith

/-- The corrected annuli give unit demands and the original scaling factor. -/
theorem cutoff_annulus_scaling {r L q : ℝ} (hr : 0 < r)
    (hD : 0 < 9 + 2 * L) (hq : q < (r / (9 + 2 * L)) / 2) :
    let δ := r / (9 + 2 * L)
    0 < δ - q ∧
      1 / (δ - q) ≤ (18 + 4 * L) / r ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ q → 0 ≤ u / (δ - q) ∧ u / (δ - q) < 1 := by
  dsimp
  have hδ : 0 < r / (9 + 2 * L) := div_pos hr hD
  have hgap : 0 < r / (9 + 2 * L) - q := by linarith
  refine ⟨hgap, ?_, ?_⟩
  · calc
      _ ≤ 2 / (r / (9 + 2 * L)) := (div_le_div_iff₀ hgap hδ).2 (by linarith)
      _ = _ := by field_simp; ring
  · intro u hu huq
    exact ⟨div_nonneg hu hgap.le, (div_lt_one hgap).2 (by linarith)⟩

end Paper.Hypergraph
