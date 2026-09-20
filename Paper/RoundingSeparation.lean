import Paper.RoundingPaths

noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

namespace Paper.Hypergraph

def IntegralSeparator (H : Hypergraph) (A B S : Finset ℕ) : Prop :=
  S ⊆ H.vertices ∧ ∀ a ∈ A \ S, ∀ b ∈ B \ S,
    ¬ (H.induce (H.vertices \ S)).primal.Reachable a b

/-- The residual components reached from the first terminal set. -/
def separatorRegion (H : Hypergraph) (A S : Finset ℕ) : Finset ℕ :=
  (H.vertices \ S).filter fun v => ∃ a ∈ A \ S,
    (H.induce (H.vertices \ S)).primal.Reachable a v

theorem separatorRegion_subset (H : Hypergraph) (A S : Finset ℕ) :
    H.separatorRegion A S ⊆ H.vertices \ S := filter_subset _ _

theorem terminals_subset_separatorRegion (H : Hypergraph) {A S : Finset ℕ}
    (hA : A ⊆ H.vertices) : A \ S ⊆ H.separatorRegion A S := by
  intro a ha
  exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨hA (mem_sdiff.mp ha).1, (mem_sdiff.mp ha).2⟩,
    a, ha, .rfl⟩

theorem separatorRegion_disjoint_terminals (H : Hypergraph) {A B S : Finset ℕ}
    (hsep : H.IntegralSeparator A B S) : Disjoint (H.separatorRegion A S) B := by
  apply disjoint_left.mpr
  intro b hb hbB
  obtain ⟨hbV, a, ha, hab⟩ := mem_filter.mp hb
  exact hsep.2 a ha b (mem_sdiff.mpr ⟨hbB, (mem_sdiff.mp hbV).2⟩) hab

theorem separatorRegion_closed (H : Hypergraph) (A S : Finset ℕ) {u v : ℕ}
    (hu : u ∈ H.separatorRegion A S) (hv : v ∈ H.vertices \ S)
    (huv : H.primal.Adj u v) : v ∈ H.separatorRegion A S := by
  obtain ⟨huV, a, ha, hau⟩ := mem_filter.mp hu
  have hadj := (H.primal_induce_adj (H.vertices \ S) huV hv).mpr huv
  exact mem_filter.mpr ⟨hv, a, ha, hau.trans hadj.reachable⟩

theorem separatorRegion_no_crossing_edge (H : Hypergraph) (A S : Finset ℕ)
    {e : ℕ} (he : e ∈ H.edges) :
    Disjoint (H.edge e) (H.separatorRegion A S) ∨
      Disjoint (H.edge e) (H.vertices \ (H.separatorRegion A S ∪ S)) := by
  by_contra hn
  obtain ⟨hu, hv⟩ := not_or.mp hn
  obtain ⟨u, hue, huP⟩ := not_disjoint_iff.mp hu
  obtain ⟨v, hve, hvP⟩ := not_disjoint_iff.mp hv
  have hv := mem_sdiff.mp hvP
  have hnP : v ∉ H.separatorRegion A S := fun h => hv.2 (mem_union_left _ h)
  have hnS : v ∉ S := fun h => hv.2 (mem_union_right _ h)
  have huv : u ≠ v := by intro h; subst v; exact hnP huP
  exact hnP (H.separatorRegion_closed A S huP (mem_sdiff.mpr ⟨hv.1, hnS⟩)
    ⟨huv, e, he, hue, hve⟩)

/-- Fractional separation forces integral separation after zero-demand vertices
are retained. This also discharges the empty-support branch of rounding. -/
theorem support_integralSeparator (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hx : H.FractionalSeparator A B x) :
    H.IntegralSeparator A B (H.vertices.filter fun v => x v ≠ 0) := by
  let S := H.vertices.filter fun v => x v ≠ 0
  refine ⟨filter_subset _ _, ?_⟩
  intro a ha b hb hab
  obtain ⟨p⟩ := hab
  have haV := hA (mem_sdiff.mp ha).1
  have haJ : a ∈ (H.induce (H.vertices \ S)).vertices :=
    mem_inter.mpr ⟨haV, mem_sdiff.mpr ⟨haV, (mem_sdiff.mp ha).2⟩⟩
  have hcost : (∑ v ∈ (p.mapLe (H.primal_induce_le _)).support.toFinset, x v) = 0 := by
    rw [SimpleGraph.Walk.support_mapLe_eq_support]
    apply sum_eq_zero
    intro v hv
    have hvJ := (H.induce (H.vertices \ S)).walk_vertices p haJ v (List.mem_toFinset.mp hv)
    have hnS := (mem_sdiff.mp (mem_inter.mp hvJ).2).2
    by_contra h
    exact hnS (mem_filter.mpr ⟨(mem_inter.mp hvJ).1, h⟩)
  have hd := H.vertexDistance_le_walk (fun v hv => (hx.1 v hv).1) haV
    (p.mapLe (H.primal_induce_le _))
  have hl := hx.2 a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1
  rw [hcost] at hd
  linarith

theorem vertexDistance_congr_on_vertices (H : Hypergraph) {x y : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (hxy : ∀ v ∈ H.vertices, x v = y v)
    {u v : ℕ} (hu : u ∈ H.vertices) : H.vertexDistance x u v = H.vertexDistance y u v := by
  apply le_antisymm (H.vertexDistance_mono hx (fun z hz => (hxy z hz).le) hu)
  apply H.vertexDistance_mono (fun z hz => by rw [← hxy z hz]; exact hx z hz)
    (fun z hz => (hxy z hz).symm.le) hu

theorem fractionalSeparator_congr (H : Hypergraph) {A B : Finset ℕ} {x y : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hx : H.FractionalSeparator A B x)
    (hxy : ∀ v ∈ H.vertices, x v = y v) : H.FractionalSeparator A B y := by
  constructor
  · intro v hv
    rw [← hxy v hv]
    exact hx.1 v hv
  · intro u hu v hv
    rw [← H.vertexDistance_congr_on_vertices (fun z hz => (hx.1 z hz).1) hxy (hA hu)]
    exact hx.2 u hu v hv

/-- Ambient and induced cover costs agree after restricting the demand. -/
theorem coverCost_induce_restrictDemand (H : Hypergraph) (z : ℕ → ℝ) (Q : Finset ℕ) :
    (H.induce Q).coverCost z = H.coverCost (restrictDemand z Q) := by
  apply le_antisymm
  · apply H.le_coverCost
    intro y hy
    have hy' : (H.induce Q).Cover z y := by
      refine ⟨fun e he => hy.1 e (mem_filter.mp he).1, ?_⟩
      intro v hv
      rw [H.incident_edges_induce (mem_inter.mp hv).2]
      simpa [restrictDemand, (mem_inter.mp hv).2] using hy.2 v (mem_inter.mp hv).1
    exact ((H.induce Q).coverCost_le hy').trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun e he _ => hy.1 e he))
  · apply (H.induce Q).le_coverCost
    intro y hy
    let y' := fun e => if e ∈ (H.induce Q).edges then y e else 0
    have hy0 : ∀ e, 0 ≤ y' e := by
      intro e
      dsimp [y']
      split_ifs with he
      · exact hy.1 e he
      · exact le_rfl
    have hy' : H.Cover (restrictDemand z Q) y' := by
      refine ⟨fun e _ => hy0 e, ?_⟩
      intro v hv
      by_cases hvQ : v ∈ Q
      · have h := hy.2 v (mem_inter.mpr ⟨hv, hvQ⟩)
        rw [← H.incident_edges_induce hvQ]
        simp only [restrictDemand, if_pos hvQ]
        convert h using 1
        apply sum_congr rfl
        intro e he
        simp [y', (mem_filter.mp he).1]
      · simp only [restrictDemand, if_neg hvQ]
        exact sum_nonneg fun e _ => hy0 e
    apply (H.coverCost_le hy').trans_eq
    dsimp [y']
    rw [← sum_filter]
    congr 1
    ext e
    simp [induce]

end Paper.Hypergraph
