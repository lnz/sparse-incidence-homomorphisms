import Paper.RoundingCutoff

noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

namespace Paper.Hypergraph

theorem walk_stays_in_set (H : Hypergraph) (P : Finset ℕ)
    (hclosed : ∀ u ∈ P, ∀ v ∈ H.vertices, H.primal.Adj u v → v ∈ P)
    {u v : ℕ} (hu : u ∈ H.vertices) (huP : u ∈ P) (p : H.primal.Walk u v) : v ∈ P := by
  induction p with
  | nil => exact huP
  | @cons u w v huw p ih =>
    have hw := H.walk_vertices (.cons huw p) hu w (by simp)
    exact ih hw (hclosed u huP w hw huw)

theorem component_subset_of_edge_partition (H : Hypergraph) {R P T K : Finset ℕ}
    (hR : R ⊆ P ∪ T)
    (hsep : ∀ e ∈ H.edges, Disjoint (H.edge e) P ∨ Disjoint (H.edge e) T)
    (hK : K ∈ (H.induce R).components) : K ⊆ P ∨ K ⊆ T := by
  have hKV := mem_powerset.mp (mem_filter.mp hK).1
  by_cases hmeet : ∃ u ∈ K, u ∈ P
  · obtain ⟨u, huK, huP⟩ := hmeet
    apply Or.inl
    intro v hvK
    have huv := ((H.induce R).component_mem_iff_reachable hK huK (hKV hvK)).mp hvK
    apply (H.induce R).walk_stays_in_set P _ (hKV huK) huP huv.some
    intro a haP b hb hab
    obtain ⟨_, e, he, hae, hbe⟩ := hab
    have heH := (mem_filter.mp he).1
    have hbPT := hR (mem_inter.mp hb).2
    rcases mem_union.mp hbPT with hbP | hbT
    · exact hbP
    · rcases hsep e heH with hdP | hdT
      · exact (disjoint_left.mp hdP (mem_inter.mp hae).1 haP).elim
      · exact (disjoint_left.mp hdT (mem_inter.mp hbe).1 hbT).elim
  · apply Or.inr
    intro v hvK
    have hvPT := hR (mem_inter.mp (hKV hvK)).2
    rcases mem_union.mp hvPT with hvP | hvT
    · exact (hmeet ⟨v, hvK, hvP⟩).elim
    · exact hvT

theorem component_contained_in_induced_component (H : Hypergraph) {R T K : Finset ℕ}
    (hK : K ∈ (H.induce R).components) (hKT : K ⊆ T) :
    ∃ L ∈ (H.induce T).components, K ⊆ L := by
  have hKV := mem_powerset.mp (mem_filter.mp hK).1
  obtain ⟨u, huK, _⟩ := (mem_filter.mp hK).2
  have huT : u ∈ (H.induce T).vertices :=
    mem_inter.mpr ⟨(mem_inter.mp (hKV huK)).1, hKT huK⟩
  obtain ⟨L, hL, huL⟩ := (H.induce T).exists_component_of_mem huT
  have hconn := (H.induce R).component_connected hK
  have hgraph : ((H.induce R).induce K).primal ≤ (H.induce T).primal := by
    rw [H.induce_induce]
    exact H.primal_induce_mono (inter_subset_right.trans hKT)
  refine ⟨L, hL, ?_⟩
  intro v hvK
  have hvT : v ∈ (H.induce T).vertices :=
    mem_inter.mpr ⟨(mem_inter.mp (hKV hvK)).1, hKT hvK⟩
  apply ((H.induce T).component_mem_iff_reachable hL huL hvT).mpr
  have hr := hconn.2 u (mem_inter.mpr ⟨hKV huK, huK⟩) v (mem_inter.mpr ⟨hKV hvK, hvK⟩)
  exact ⟨hr.some.mapLe hgraph⟩

/-- Repeated cut-offs terminate by deleting a nonempty piece at every step.
The accumulated separator has no component heavier than a single piece. -/
theorem cutoff_recursion (H : Hypergraph) {γ x : ℕ → ℝ} {V C : ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (hC : 0 ≤ C)
    (Q : Finset ℕ) (hQ : Q ⊆ H.vertices)
    (hcut : ∀ U ⊆ Q, U.Nonempty → Nonempty (H.CutoffPiece γ x U V C)) :
    ∃ S ⊆ Q, S ⊆ H.vertices.filter (fun v => x v ≠ 0) ∧
      (∀ K ∈ (H.induce (Q \ S)).components, H.edgeVolume γ K ≤ V) ∧
      H.setCoverCost S ≤ C * H.coverCost (restrictDemand x Q) := by
  revert hQ hcut
  induction Q using Finset.strongInductionOn with
  | _ Q ih =>
    intro hQ hcut
    by_cases hne : Q.Nonempty
    swap
    · have hQ0 := Finset.not_nonempty_iff_eq_empty.mp hne
      subst Q
      refine ⟨∅, empty_subset _, empty_subset _, ?_, ?_⟩
      · intro K hK
        simp [components, induce] at hK
        rcases hK with ⟨rfl, v, hv⟩
        simp at hv
      · have hz : H.setCoverCost ∅ = 0 := H.coverCost_eq_zero_of_nonpos
          (fun v hv => by simp [indicator])
        rw [hz]
        exact mul_nonneg hC (H.coverCost_nonneg _)
    obtain ⟨cut⟩ := hcut Q (Subset.refl _) hne
    let U := Q \ (cut.piece ∪ cut.separator)
    have hUQ : U ⊆ Q := sdiff_subset
    have hproper : U ⊂ Q := by
      apply Finset.ssubset_iff_subset_ne.mpr ⟨hUQ, ?_⟩
      intro heq
      obtain ⟨v, hv⟩ := cut.nonempty
      have hvU : v ∈ U := heq.symm ▸ cut.piece_subset hv
      exact (mem_sdiff.mp hvU).2 (mem_union_left _ hv)
    obtain ⟨S, hSU, hSsupp, hSbal, hScost⟩ := ih U hproper (hUQ.trans hQ)
      (fun T hTU hT => hcut T (hTU.trans hUQ) hT)
    refine ⟨cut.separator ∪ S, union_subset cut.separator_subset (hSU.trans hUQ),
      union_subset cut.support hSsupp, ?_, ?_⟩
    · intro K hK
      have hcover : Q \ (cut.separator ∪ S) ⊆ cut.piece ∪ (U \ S) := by
        intro v hv
        obtain ⟨hvQ, hvout⟩ := mem_sdiff.mp hv
        by_cases hvP : v ∈ cut.piece
        · exact mem_union_left _ hvP
        · apply mem_union_right
          apply mem_sdiff.mpr
          refine ⟨mem_sdiff.mpr ⟨hvQ, ?_⟩, ?_⟩
          · intro hv
            rcases mem_union.mp hv with h | h
            · exact hvP h
            · exact hvout (mem_union_left _ h)
          · intro h
            exact hvout (mem_union_right _ h)
      have hsep : ∀ e ∈ H.edges, Disjoint (H.edge e) cut.piece ∨ Disjoint (H.edge e) (U \ S) := by
        intro e he
        rcases cut.separated e he with h | h
        · exact Or.inl h
        · exact Or.inr (h.mono_right sdiff_subset)
      rcases H.component_subset_of_edge_partition hcover hsep hK with hKP | hKT
      · exact (H.edgeVolume_mono hγ hKP).trans cut.volume_le
      · obtain ⟨L, hL, hKL⟩ := H.component_contained_in_induced_component hK hKT
        exact (H.edgeVolume_mono hγ hKL).trans (hSbal L hL)
    · have hsum : H.coverCost (restrictDemand x cut.piece) + H.coverCost (restrictDemand x U) ≤
          H.coverCost (restrictDemand x Q) := by
        apply (H.separated_restrictDemand_cost_add_le x cut.piece U cut.separated).trans
        exact H.restrictDemand_cost_mono hx (union_subset cut.piece_subset hUQ)
      calc
        _ ≤ H.setCoverCost cut.separator + H.setCoverCost S := H.setCoverCost_union_le _ _
        _ ≤ C * H.coverCost (restrictDemand x cut.piece) + C * H.coverCost (restrictDemand x U) :=
          add_le_add cut.cost_le hScost
        _ = C * (H.coverCost (restrictDemand x cut.piece) + H.coverCost (restrictDemand x U)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum hC

end Paper.Hypergraph
