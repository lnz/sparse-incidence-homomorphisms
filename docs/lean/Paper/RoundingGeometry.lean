import Paper.ExternalRounding

/-!
# Geometry of the rounding construction

Weighted paths, annular fractional separators, and separated balls use the
same vertex distance as the external theorem's specification.
-/

noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

namespace Paper.Hypergraph

theorem vertexDistance_le_walk (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {u v : ℕ} (hu : u ∈ H.vertices)
    (p : H.primal.Walk u v) :
    H.vertexDistance x u v ≤ ∑ z ∈ p.support.toFinset, x z := by
  apply (H.vertexDistance_le_option hx hu
    (Set.mem_insert_of_mem 1 ⟨p.bypass, p.bypass_isPath, rfl⟩)).trans
  apply sum_le_sum_of_subset_of_nonneg
  · intro z hz
    exact List.mem_toFinset.mpr (p.support_bypass_subset_support (List.mem_toFinset.mp hz))
  · intro z hz _
    exact hx z (H.walk_vertices p hu z (List.mem_toFinset.mp hz))

theorem vertexDistance_self_le (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {u : ℕ} (hu : u ∈ H.vertices) :
    H.vertexDistance x u u ≤ x u := by
  simpa using H.vertexDistance_le_walk hx hu (.nil : H.primal.Walk u u)

theorem vertexDistance_step (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {c u v : ℕ}
    (hc : c ∈ H.vertices) (hv : v ∈ H.vertices) (huv : H.primal.Adj u v) :
    H.vertexDistance x c v ≤ H.vertexDistance x c u + x v := by
  suffices h : H.vertexDistance x c v - x v ≤ H.vertexDistance x c u by linarith
  apply le_csInf ⟨1, Set.mem_insert _ _⟩
  rintro r (rfl | ⟨p, hp, rfl⟩)
  · have := H.vertexDistance_le_one hx hc (v := v)
    have := hx v hv
    linarith
  · have hd := H.vertexDistance_le_walk hx hc (p.concat huv)
    simp only [SimpleGraph.Walk.support_concat, List.toFinset_append,
      List.toFinset_cons, List.toFinset_nil, union_insert, union_empty] at hd
    by_cases hm : v ∈ p.support.toFinset
    · rw [insert_eq_of_mem hm] at hd
      have := hx v hv
      linarith
    · rw [sum_insert hm] at hd
      linarith

theorem vertexDistance_mono (H : Hypergraph) {x y : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v)
    (hxy : ∀ v ∈ H.vertices, x v ≤ y v) {u v : ℕ} (hu : u ∈ H.vertices) :
    H.vertexDistance x u v ≤ H.vertexDistance y u v := by
  apply le_csInf ⟨1, Set.mem_insert _ _⟩
  rintro r (rfl | ⟨p, hp, rfl⟩)
  · exact H.vertexDistance_le_one hx hu
  · exact (H.vertexDistance_le_walk hx hu p).trans (sum_le_sum fun z hz =>
      hxy z (H.walk_vertices p hu z (List.mem_toFinset.mp hz)))

/-- Adjacent vertices cannot jump across a gap exceeding every vertex demand. -/
theorem roundingBall_no_crossing_edge (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (Q : Finset ℕ) {c : ℕ}
    (hc : c ∈ H.vertices ∩ Q) {s g q : ℝ} (hqg : q < g)
    (hq : ∀ v ∈ H.vertices ∩ Q, x v ≤ q) {e : ℕ} (he : e ∈ H.edges) :
    Disjoint (H.edge e) (H.roundingBall x Q c s) ∨
      Disjoint (H.edge e) ((H.vertices ∩ Q) \ H.roundingBall x Q c (s + g)) := by
  by_contra hn
  obtain ⟨hA, hB⟩ := not_or.mp hn
  obtain ⟨u, hue, huA⟩ := not_disjoint_iff.mp hA
  obtain ⟨v, hve, hvB⟩ := not_disjoint_iff.mp hB
  have huQ := (mem_filter.mp huA).1
  have hvQ := (mem_sdiff.mp hvB).1
  have hud := (mem_filter.mp huA).2
  have hvd : s + g < (H.induce Q).vertexDistance x c v := by
    apply lt_of_not_ge
    intro h
    exact (mem_sdiff.mp hvB).2 (mem_filter.mpr ⟨hvQ, h⟩)
  have huv : u ≠ v := by
    intro h
    subst v
    have := hq u huQ
    have := hx u (mem_inter.mp huQ).1
    linarith
  have hadj : (H.induce Q).primal.Adj u v := by
    apply (H.primal_induce_adj Q (mem_inter.mp huQ).2 (mem_inter.mp hvQ).2).2
    exact ⟨huv, e, he, hue, hve⟩
  have hs := (H.induce Q).vertexDistance_step
    (fun z hz => hx z (mem_inter.mp hz).1) hc hvQ hadj
  have := hq v hvQ
  linarith

/-- A clipped distance provides a potential across an annulus. -/
def annulusPotential (a b q d : ℝ) : ℝ := min (b - a - q) (max 0 (d - a))

theorem annulusPotential_step {a b q du dv z : ℝ}
    (hgap : 0 < b - a - q) (hz : 0 ≤ z) (hzq : z ≤ q) (hd : dv ≤ du + z) :
    annulusPotential a b q dv ≤ annulusPotential a b q du +
      if a < dv ∧ dv ≤ b then z else 0 := by
  by_cases ha : a < dv <;> by_cases hb : dv ≤ b <;>
    simp only [ha, hb, and_self, and_true, and_false, false_and, if_true, if_false,
      annulusPotential, min_def, max_def] <;>
    split_ifs <;> linarith

theorem walk_potential_le (H : Hypergraph) {f z : ℕ → ℝ}
    (hstep : ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Adj u v → f v ≤ f u + z v)
    {u v : ℕ} (hu : u ∈ H.vertices) (p : H.primal.Walk u v) (hp : p.IsPath) :
    f v ≤ f u + (∑ w ∈ p.support.toFinset, z w) - z u := by
  induction p with
  | nil => simp
  | @cons u w v huw p ih =>
    have hw := H.walk_vertices (.cons huw p) hu w (by simp)
    have hp' := (SimpleGraph.Walk.cons_isPath_iff huw p).mp hp
    have hi := ih hw hp'.1
    have hs := hstep u hu w hw huw
    simp only [SimpleGraph.Walk.support_cons, List.toFinset_cons]
    rw [sum_insert (by simpa using hp'.2)]
    linarith

/-- A two-terminal separator meets every path between its terminal sets. -/
def FractionalSeparator (H : Hypergraph) (A B : Finset ℕ) (x : ℕ → ℝ) : Prop :=
  H.UnitDemand x ∧ ∀ u ∈ A, ∀ v ∈ B, 1 ≤ H.vertexDistance x u v

/-- Observation 5.8 in the range used by the repaired cut-off lemma.
The hypothesis q < (b-a)/2 also ensures that the demand is at most one. -/
theorem annulus_fractionalSeparator (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {c : ℕ} (hc : c ∈ H.vertices)
    {a b q : ℝ} (hq : ∀ v ∈ H.vertices, x v ≤ q) (hgap : q < (b - a) / 2)
    (hq0 : 0 ≤ q) :
    let d := H.vertexDistance x c
    let A := H.vertices.filter (fun v => d v ≤ a)
    let B := H.vertices.filter (fun v => b < d v)
    let z := fun v => if a < d v ∧ d v ≤ b then x v / (b - a - q) else 0
    H.FractionalSeparator A B z := by
  dsimp
  let d := H.vertexDistance x c
  let z := fun v => if a < d v ∧ d v ≤ b then x v / (b - a - q) else 0
  let f := fun v => annulusPotential a b q (d v)
  have hg : 0 < b - a - q := by linarith
  have hz : H.UnitDemand z := by
    intro v hv
    dsimp [z]
    split_ifs
    · exact ⟨div_nonneg (hx v hv) hg.le,
        (div_le_one hg).2 (by have := hq v hv; linarith)⟩
    · norm_num
  refine ⟨hz, ?_⟩
  intro u hu v hv
  have huV := (mem_filter.mp hu).1
  have hud : d u ≤ a := (mem_filter.mp hu).2
  have hvd : b < d v := (mem_filter.mp hv).2
  have hfu : f u = 0 := by simp [f, annulusPotential, max_eq_left (by linarith : d u - a ≤ 0), hg.le]
  have hfv : f v = b - a - q := by
    dsimp [f, annulusPotential]
    rw [max_eq_right (by linarith : 0 ≤ d v - a), min_eq_left (by linarith)]
  have hzu : z u = 0 := by simp [z, not_lt.mpr hud]
  apply le_csInf ⟨1, Set.mem_insert _ _⟩
  rintro t (rfl | ⟨p, hp, rfl⟩)
  · exact le_rfl
  · have hstep : ∀ w ∈ H.vertices, ∀ t ∈ H.vertices, H.primal.Adj w t →
        f t ≤ f w + (b - a - q) * z t := by
      intro w hw t ht hwt
      have hs := annulusPotential_step hg (hx t ht) (hq t ht)
        (H.vertexDistance_step hx hc ht hwt)
      dsimp [f, z, d]
      split_ifs with hm
      · simpa [hm, mul_div_cancel₀ _ hg.ne'] using hs
      · simpa [hm] using hs
    have hs := H.walk_potential_le hstep huV p hp
    rw [hfu, hfv, hzu, mul_zero, sub_zero, zero_add, ← mul_sum] at hs
    exact (mul_le_mul_iff_right₀ hg).mp (by simpa [mul_comm] using hs)

end Paper.Hypergraph
