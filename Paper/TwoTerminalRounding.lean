import Paper.RoundingSeparation

noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

namespace Paper.Hypergraph

def twoTerminalFactor (H : Hypergraph) (R : Finset ℕ) : ℝ :=
  min (8 + 4 * Real.log ((H.induce R).independenceNumber : ℝ)) (6 * (H.degeneracy : ℝ))

/-- The existence statement of Theorem 4.1, proved by `twoTerminal_rounding`
in `RoundingComplete.lean`. -/
def TwoTerminalRounding : Prop :=
  ∀ (H : Hypergraph) (A B : Finset ℕ) (x : ℕ → ℝ),
    A ⊆ H.vertices → B ⊆ H.vertices → H.FractionalSeparator A B x →
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralSeparator A B S ∧
      H.setCoverCost S ≤ H.twoTerminalFactor (H.vertices.filter (fun v => x v ≠ 0)) * H.coverCost x

theorem log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn

theorem log_nat_mono {m n : ℕ} (hmn : m ≤ n) : Real.log (m : ℝ) ≤ Real.log (n : ℝ) := by
  by_cases hm : m = 0
  · simpa [hm] using log_nat_nonneg n
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hm) (by exact_mod_cast hmn)

theorem twoTerminalFactor_nonneg (H : Hypergraph) (R : Finset ℕ) : 0 ≤ H.twoTerminalFactor R := by
  apply le_min
  · have := log_nat_nonneg (H.induce R).independenceNumber
    linarith
  · positivity

theorem independenceNumber_induce_mono (H : Hypergraph) {U W : Finset ℕ} (hUW : U ⊆ W) :
    (H.induce U).independenceNumber ≤ (H.induce W).independenceNumber := by
  have h := ((H.induce W).structure_hereditary U).2
  rwa [H.induce_induce, inter_eq_right.mpr hUW] at h

theorem twoTerminalFactor_induce_le (H : Hypergraph) (Q : Finset ℕ) {R T : Finset ℕ}
    (hTR : T ⊆ R) : (H.induce Q).twoTerminalFactor T ≤ H.twoTerminalFactor R := by
  apply min_le_min
  · rw [H.induce_induce]
    have h := log_nat_mono (H.independenceNumber_induce_mono (inter_subset_right.trans hTR : Q ∩ T ⊆ R))
    linarith
  · have h : ((H.induce Q).degeneracy : ℝ) ≤ H.degeneracy := by
      exact_mod_cast (H.structure_hereditary Q).1
    linarith

/-- Apply two-terminal rounding in an induced hypergraph while charging costs
and structural factors to the original hypergraph. -/
theorem twoTerminalRounding_induced (round : TwoTerminalRounding) (H : Hypergraph)
    (Q : Finset ℕ) (x : ℕ → ℝ) (A B : Finset ℕ) (z : ℕ → ℝ)
    (hA : A ⊆ (H.induce Q).vertices) (hB : B ⊆ (H.induce Q).vertices)
    (hz : (H.induce Q).FractionalSeparator A B z)
    (hsupp : ∀ v ∈ (H.induce Q).vertices, z v ≠ 0 → x v ≠ 0) :
    ∃ S ⊆ (H.induce Q).vertices.filter (fun v => z v ≠ 0),
      (H.induce Q).IntegralSeparator A B S ∧
      H.setCoverCost S ≤ H.twoTerminalFactor (H.vertices.filter (fun v => x v ≠ 0)) *
        (H.induce Q).coverCost z := by
  obtain ⟨S, hS, hsep, hcost⟩ := round (H.induce Q) A B z hA hB hz
  have hSQ : S ⊆ Q := fun v hv => (mem_inter.mp (mem_filter.mp (hS hv)).1).2
  have hs : (H.induce Q).vertices.filter (fun v => z v ≠ 0) ⊆
      H.vertices.filter (fun v => x v ≠ 0) := by
    intro v hv
    obtain ⟨hv, hzv⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨(mem_inter.mp hv).1, hsupp v hv hzv⟩
  refine ⟨S, hS, hsep, ?_⟩
  rw [H.cover_restriction hSQ] at hcost
  exact hcost.trans (mul_le_mul_of_nonneg_right (H.twoTerminalFactor_induce_le Q hs)
    ((H.induce Q).coverCost_nonneg z))

theorem demand_le_vertexDistance (H : Hypergraph) {x : ℕ → ℝ} (hx : H.UnitDemand x)
    {u v : ℕ} (hu : u ∈ H.vertices) (hv : v ∈ H.vertices) :
    x v ≤ H.vertexDistance x u v := by
  apply le_csInf ⟨1, Set.mem_insert _ _⟩
  rintro r (rfl | ⟨p, hp, rfl⟩)
  · exact (hx v hv).2
  · apply single_le_sum
    · intro z hz
      exact (hx z (H.walk_vertices p hu z (List.mem_toFinset.mp hz))).1
    · exact List.mem_toFinset.mpr p.end_mem_support

/-- Distances from a terminal set, without adding artificial vertices. -/
theorem twoTerminal_distance_labels (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hx : H.FractionalSeparator A B x) :
    ∃ d : ℕ → ℝ,
      (∀ v ∈ H.vertices, x v ≤ d v ∧ d v ≤ 1) ∧
      (∀ v ∈ A, d v ≤ x v) ∧
      (∀ v ∈ B, 1 ≤ d v) ∧
      (∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Adj u v → d v ≤ d u + x v) := by
  by_cases hne : A.Nonempty
  swap
  · refine ⟨fun _ => 1, (fun v hv => ⟨(hx.1 v hv).2, le_rfl⟩), ?_, (fun _ _ => le_rfl), ?_⟩
    · intro v hv
      exact (hne ⟨v, hv⟩).elim
    · intro u hu v hv huv
      have := (hx.1 v hv).1
      linarith
  let d := fun v => A.inf' hne (fun a => H.vertexDistance x a v)
  have hn : ∀ v ∈ H.vertices, 0 ≤ x v := fun v hv => (hx.1 v hv).1
  have hle : ∀ a ∈ A, ∀ v, d v ≤ H.vertexDistance x a v := by
    intro a ha v
    exact inf'_le _ ha
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · intro v hv
    constructor
    · apply le_inf'
      intro a ha
      exact H.demand_le_vertexDistance hx.1 (hA ha) hv
    · obtain ⟨a, ha⟩ := hne
      exact (hle a ha v).trans (H.vertexDistance_le_one hn (hA ha))
  · intro a ha
    exact (hle a ha a).trans (H.vertexDistance_self_le hn (hA ha))
  · intro b hb
    apply le_inf'
    intro a ha
    exact hx.2 a ha b hb
  · intro u hu v hv huv
    suffices h : d v - x v ≤ d u by linarith
    apply le_inf'
    intro a ha
    have h := (hle a ha v).trans (H.vertexDistance_step hn (hA ha) hv huv)
    linarith

/-- The interval separator used in Section 4. -/
def levelSeparator (H : Hypergraph) (x d : ℕ → ℝ) (r : ℝ) : Finset ℕ :=
  H.vertices.filter fun v => x v ≠ 0 ∧ d v - x v ≤ r ∧ r ≤ d v

theorem levelSeparator_subset_support (H : Hypergraph) (x d : ℕ → ℝ) (r : ℝ) :
    H.levelSeparator x d r ⊆ H.vertices.filter (fun v => x v ≠ 0) := by
  intro v hv
  exact mem_filter.mpr ⟨(mem_filter.mp hv).1, (mem_filter.mp hv).2.1⟩

/-- Observation 4.4 for interior levels, which suffice for averaging. -/
theorem levelSeparator_integral (H : Hypergraph) {A B : Finset ℕ} {x d : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hB : B ⊆ H.vertices)
    (ha : ∀ v ∈ A, d v ≤ x v) (hb : ∀ v ∈ B, 1 ≤ d v)
    (hstep : ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Adj u v → d v ≤ d u + x v)
    {r : ℝ} (hr : 0 < r ∧ r < 1) : H.IntegralSeparator A B (H.levelSeparator x d r) := by
  let S := H.levelSeparator x d r
  have hlow : ∀ v ∈ A \ S, d v < r := by
    intro v hv
    have hvA := (mem_sdiff.mp hv).1
    have hvout := (mem_sdiff.mp hv).2
    by_contra h
    have hd : r ≤ d v := le_of_not_gt h
    have hxa := ha v hvA
    have hxv : x v ≠ 0 := by intro h0; rw [h0] at hxa; linarith [hr.1]
    exact hvout (mem_filter.mpr ⟨hA hvA, hxv, by linarith [hr.1], hd⟩)
  refine ⟨filter_subset _ _, ?_⟩
  intro u hu v hv huv
  let J := H.induce (H.vertices \ S)
  have huJ : u ∈ J.vertices := mem_inter.mpr ⟨hA (mem_sdiff.mp hu).1,
    mem_sdiff.mpr ⟨hA (mem_sdiff.mp hu).1, (mem_sdiff.mp hu).2⟩⟩
  have hclosed : ∀ a ∈ J.vertices.filter (fun w => d w < r), ∀ b ∈ J.vertices,
      J.primal.Adj a b → b ∈ J.vertices.filter (fun w => d w < r) := by
    intro a ha b hb hab
    apply mem_filter.mpr ⟨hb, ?_⟩
    have ha' := mem_filter.mp ha
    have hadj := H.primal_induce_le (H.vertices \ S) hab
    have hds := hstep a (mem_inter.mp ha'.1).1 b (mem_inter.mp hb).1 hadj
    by_contra h
    have hrd : r ≤ d b := le_of_not_gt h
    have hxb : x b ≠ 0 := by intro h0; rw [h0] at hds; linarith
    exact (mem_sdiff.mp (mem_inter.mp hb).2).2
      (mem_filter.mpr ⟨(mem_inter.mp hb).1, hxb, by linarith, hrd⟩)
  have hvlow : v ∈ J.vertices.filter (fun w => d w < r) := by
    -- Propagate the strict lower level along a surviving path.
    obtain ⟨p⟩ := huv
    have hstart : d u < r := hlow u hu
    suffices h : d v < r from mem_filter.mpr
      ⟨mem_inter.mpr ⟨hB (mem_sdiff.mp hv).1,
        mem_sdiff.mpr ⟨hB (mem_sdiff.mp hv).1, (mem_sdiff.mp hv).2⟩⟩, h⟩
    clear hu hlow hv
    induction p with
    | nil => exact hstart
    | @cons a b v hab p ih =>
      have hbJ := J.walk_vertices (.cons hab p) huJ b (by simp)
      have hbLow := hclosed a (mem_filter.mpr ⟨huJ, hstart⟩) b hbJ hab
      exact ih hbJ (mem_filter.mp hbLow).2
  have hlarge := hb v (mem_sdiff.mp hv).1
  have := (mem_filter.mp hvlow).2
  linarith [hr.2]

/-- Observation 4.3 follows by taking the smallest distance on an edge. -/
theorem edge_intervals_common_point (H : Hypergraph) {x d : ℕ → ℝ}
    (hstep : ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Adj u v → d v ≤ d u + x v)
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {e : ℕ} (he : e ∈ H.edges) :
    ∃ q : ℝ, ∀ v ∈ H.edge e, d v - x v ≤ q ∧ q ≤ d v := by
  obtain ⟨u, hu, hmin⟩ := (H.edge e).exists_min_image d (H.edge_nonempty e he)
  refine ⟨d u, ?_⟩
  intro v hv
  refine ⟨?_, hmin v hv⟩
  by_cases huv : u = v
  · subst v
    have := hx u (H.edge_subset e he hu)
    linarith
  · have h := hstep u (H.edge_subset e he hu) v (H.edge_subset e he hv) ⟨huv, e, he, hu, hv⟩
    linarith

end Paper.Hypergraph
