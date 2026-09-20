import Paper.RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric

noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

namespace Paper.Hypergraph

theorem shortest_path_prefix_distance {G : SimpleGraph ℕ} {u v : ℕ}
    (p : G.Walk u v) (hp : p.length = G.dist u v) {i : ℕ} (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i := by
  have ht := G.dist_le (p.take i)
  have hd := G.dist_le (p.drop i)
  have htri := (p.take i).reachable.dist_triangle_left v
  rw [SimpleGraph.Walk.take_length, min_eq_left hi] at ht
  rw [SimpleGraph.Walk.drop_length] at hd
  omega

/-- A shortest unweighted path contains at most two vertices of any clique. -/
theorem shortest_path_clique_card_le_two {G : SimpleGraph ℕ} {u v : ℕ}
    (p : G.Walk u v) (hp : p.length = G.dist u v) (S : Finset ℕ)
    (hS : ∀ z ∈ S, z ∈ p.support)
    (hclique : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b) : S.card ≤ 2 := by
  have hinj : Set.InjOn (G.dist u) (↑S : Set ℕ) := by
    intro a ha b hb heq
    obtain ⟨i, hi, hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hS a ha)
    obtain ⟨j, hj, hjl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hS b hb)
    have hdi := shortest_path_prefix_distance p hp hil
    have hdj := shortest_path_prefix_distance p hp hjl
    rw [hi] at hdi
    rw [hj] at hdj
    have hij : i = j := by omega
    exact hi.symm.trans ((congrArg p.getVert hij).trans hj)
  by_cases hne : S.Nonempty
  · obtain ⟨a, ha, hmin⟩ := S.exists_min_image (G.dist u) hne
    have hmap : Set.MapsTo (G.dist u) (↑S : Set ℕ)
        (↑(Finset.Icc (G.dist u a) (G.dist u a + 1)) : Set ℕ) := by
      intro b hb
      apply mem_Icc.mpr
      refine ⟨hmin b hb, ?_⟩
      by_cases hab : a = b
      · subst b
        omega
      · have hadj := hclique a ha b hb hab
        have ht := hadj.reachable.dist_triangle_right u
        rw [G.dist_eq_one_iff_adj.mpr hadj] at ht
        exact ht
    have := card_le_card_of_injOn (G.dist u) hmap hinj
    simp only [Nat.card_Icc] at this
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

/-- A demand restricted to a smaller vertex set has no larger cover cost. -/
theorem restrictDemand_cost_mono (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {A B : Finset ℕ} (hAB : A ⊆ B) :
    H.coverCost (restrictDemand x A) ≤ H.coverCost (restrictDemand x B) := by
  apply H.coverCost_mono
  intro v hv
  by_cases ha : v ∈ A
  · simp [restrictDemand, ha, hAB ha]
  · simp only [restrictDemand, if_neg ha]
    split_ifs <;> first | exact hx v hv | exact le_rfl

theorem restrictDemand_cost_le (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (A : Finset ℕ) :
    H.coverCost (restrictDemand x A) ≤ H.coverCost x := by
  apply H.coverCost_mono
  intro v hv
  dsimp [restrictDemand]
  split_ifs <;> first | exact le_rfl | exact hx v hv

/-- Counting how many vertices of a set any edge can cover. -/
theorem demand_sum_le_card_bound_mul_coverCost (H : Hypergraph) (x : ℕ → ℝ)
    {S : Finset ℕ} (hS : S ⊆ H.vertices) {n : ℕ}
    (hn : ∀ e ∈ H.edges, (S ∩ H.edge e).card ≤ n) :
    (∑ v ∈ S, x v) ≤ n * H.coverCost (restrictDemand x S) := by
  by_cases hn0 : n = 0
  · subst n
    have hempty : S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨e, he, hve⟩ := H.no_isolated v (hS hv)
      have hpos : 0 < (S ∩ H.edge e).card := card_pos.mpr ⟨v, mem_inter.mpr ⟨hv, hve⟩⟩
      have := hn e he
      omega
    simp [hempty]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  rw [← div_le_iff₀' hnpos]
  apply H.le_coverCost
  intro y hy
  rw [div_le_iff₀' hnpos]
  have hs : (∑ v ∈ S, x v) ≤ ∑ v ∈ S, ∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), y e := by
    apply sum_le_sum
    intro v hv
    simpa [restrictDemand, hv] using hy.2 v (hS hv)
  calc
    _ ≤ _ := hs
    _ = ∑ e ∈ H.edges, ((S ∩ H.edge e).card : ℝ) * y e := by
      simp_rw [sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro e he
      rw [← sum_filter]
      simp [filter_mem_eq_inter, nsmul_eq_mul]
    _ ≤ ∑ e ∈ H.edges, (n : ℝ) * y e := by
      apply sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn e he) (hy.1 e he)
    _ = _ := by rw [mul_sum]

theorem restrictDemand_restrict_of_subset (x : ℕ → ℝ) {A B : Finset ℕ} (hAB : A ⊆ B) :
    restrictDemand (restrictDemand x B) A = restrictDemand x A := by
  funext v
  by_cases ha : v ∈ A
  · simp [restrictDemand, ha, hAB ha]
  · simp [restrictDemand, ha]

/-- Separated sets use disjoint families of covering edges. -/
theorem separated_restrictDemand_cost_add_le (H : Hypergraph) (x : ℕ → ℝ)
    (A B : Finset ℕ)
    (hsep : ∀ e ∈ H.edges, Disjoint (H.edge e) A ∨ Disjoint (H.edge e) B) :
    H.coverCost (restrictDemand x A) + H.coverCost (restrictDemand x B) ≤
      H.coverCost (restrictDemand x (A ∪ B)) := by
  let P : Bool → Finset ℕ := fun b => if b then B else A
  have hs : ∀ e ∈ H.edges, ∀ i ∈ (univ : Finset Bool), ∀ j ∈ (univ : Finset Bool),
      ¬ Disjoint (H.edge e) (P i) → ¬ Disjoint (H.edge e) (P j) → i = j := by
    intro e he i hi j hj hmi hmj
    have h := hsep e he
    cases i <;> cases j <;> simp_all [P] <;>
      rcases hsep e he with h | h <;> contradiction
  have h := H.sum_restrictDemand_cost_le univ P (restrictDemand x (A ∪ B)) hs
  simpa [P, restrictDemand_restrict_of_subset x (subset_union_left : A ⊆ A ∪ B),
    restrictDemand_restrict_of_subset x (subset_union_right : B ⊆ A ∪ B), add_comm] using h

theorem roundingBall_mono (H : Hypergraph) (x : ℕ → ℝ) (Q : Finset ℕ) (c : ℕ)
    {a b : ℝ} (hab : a ≤ b) : H.roundingBall x Q c a ⊆ H.roundingBall x Q c b := by
  intro v hv
  exact mem_filter.mpr ⟨(mem_filter.mp hv).1, (mem_filter.mp hv).2.trans hab⟩

theorem shortest_induced_path_edge_card (H : Hypergraph) (Q : Finset ℕ) {u v : ℕ}
    (hu : u ∈ (H.induce Q).vertices) (p : (H.induce Q).primal.Walk u v)
    (hp : p.length = (H.induce Q).primal.dist u v) {S : Finset ℕ}
    (hS : ∀ z ∈ S, z ∈ p.support) {e : ℕ} (he : e ∈ H.edges) :
    (S ∩ H.edge e).card ≤ 2 := by
  apply shortest_path_clique_card_le_two p hp
  · intro z hz
    exact hS z (mem_inter.mp hz).1
  · intro a ha b hb hab
    have haQ := (mem_inter.mp ((H.induce Q).walk_vertices p hu a (hS a (mem_inter.mp ha).1))).2
    have hbQ := (mem_inter.mp ((H.induce Q).walk_vertices p hu b (hS b (mem_inter.mp hb).1))).2
    apply (H.primal_induce_adj Q haQ hbQ).2
    exact ⟨hab, e, he, (mem_inter.mp ha).2, (mem_inter.mp hb).2⟩

/-- The small-cover case can retain an entire connected component. -/
theorem induced_vertexDistance_le_two_coverCost (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ z ∈ H.vertices, 0 ≤ x z) (Q : Finset ℕ) {u v : ℕ}
    (hu : u ∈ (H.induce Q).vertices) (huv : (H.induce Q).primal.Reachable u v) :
    (H.induce Q).vertexDistance x u v ≤ 2 * H.coverCost x := by
  obtain ⟨p, hp⟩ := huv.exists_walk_length_eq_dist
  have hS : p.support.toFinset ⊆ H.vertices := by
    intro z hz
    exact (mem_inter.mp ((H.induce Q).walk_vertices p hu z (List.mem_toFinset.mp hz))).1
  have hcard : ∀ e ∈ H.edges, (p.support.toFinset ∩ H.edge e).card ≤ 2 := by
    intro e he
    exact H.shortest_induced_path_edge_card Q hu p hp (fun _ hz => List.mem_toFinset.mp hz) he
  calc
    _ ≤ ∑ z ∈ p.support.toFinset, x z :=
      (H.induce Q).vertexDistance_le_walk (fun z hz => hx z (mem_inter.mp hz).1) hu p
    _ ≤ 2 * H.coverCost (restrictDemand x p.support.toFinset) := by
      simpa using H.demand_sum_le_card_bound_mul_coverCost x hS hcard
    _ ≤ _ := mul_le_mul_of_nonneg_left (H.restrictDemand_cost_le hx _) (by norm_num)

/-- The seed estimate for the repaired cut-off construction.
An unweighted shortest path suffices, since only a first exit is needed. -/
theorem roundingBall_seed (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ z ∈ H.vertices, 0 ≤ x z) (Q : Finset ℕ) {c : ℕ}
    (hc : c ∈ H.vertices ∩ Q) {s q : ℝ}
    (hq : ∀ z ∈ H.vertices ∩ Q, x z ≤ q)
    (hout : ∃ v, (H.induce Q).primal.Reachable c v ∧
      s < (H.induce Q).vertexDistance x c v) :
    (s - q) / 2 < H.coverCost (restrictDemand x (H.roundingBall x Q c s)) := by
  obtain ⟨v, hcv, hvd⟩ := hout
  obtain ⟨p, hp⟩ := hcv.exists_walk_length_eq_dist
  have he : ∃ i : ℕ, i ≤ p.length ∧ s < (H.induce Q).vertexDistance x c (p.getVert i) := by
    exact ⟨p.length, le_rfl, by simpa using hvd⟩
  let j := Nat.find he
  have hj := Nat.find_spec he
  change j ≤ p.length ∧ s < (H.induce Q).vertexDistance x c (p.getVert j) at hj
  let T := (p.take j).support.toFinset
  let S := T.erase (p.getVert j)
  have hT : ∀ z ∈ T, z ∈ p.support := by
    intro z hz
    have hz' : z ∈ (p.take j).support := List.mem_toFinset.mp hz
    rw [SimpleGraph.Walk.support_take] at hz'
    exact List.mem_of_mem_take hz'
  have hS : S ⊆ H.roundingBall x Q c s := by
    intro z hz
    obtain ⟨hzj, hzT⟩ := mem_erase.mp hz
    have hzQ := (H.induce Q).walk_vertices p hc z (hT z hzT)
    refine mem_filter.mpr ⟨hzQ, ?_⟩
    obtain ⟨k, hk, hkl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      (List.mem_toFinset.mp hzT)
    rw [SimpleGraph.Walk.take_length, min_eq_left hj.1] at hkl
    rw [SimpleGraph.Walk.take_getVert, min_eq_right hkl] at hk
    have hkj : k < j := by
      have : k ≠ j := by intro h; subst k; exact hzj hk.symm
      omega
    have hmin := Nat.find_min he hkj
    have hkle : k ≤ p.length := hkl.trans hj.1
    rw [← hk]
    exact le_of_not_gt fun h => hmin ⟨hkle, h⟩
  have hSV : S ⊆ H.vertices := fun z hz => (mem_inter.mp (mem_filter.mp (hS hz)).1).1
  have hcard : ∀ e ∈ H.edges, (S ∩ H.edge e).card ≤ 2 := by
    intro e he
    exact H.shortest_induced_path_edge_card Q hc p hp (fun z hz => hT z (mem_erase.mp hz).2) he
  have hsum := H.demand_sum_le_card_bound_mul_coverCost x hSV hcard
  have hmono := H.restrictDemand_cost_mono hx hS
  have hjT : p.getVert j ∈ T := List.mem_toFinset.mpr (p.take j).end_mem_support
  have hsumT : (∑ z ∈ S, x z) + x (p.getVert j) = ∑ z ∈ T, x z := sum_erase_add T x hjT
  have hd := (H.induce Q).vertexDistance_le_walk (fun z hz => hx z (mem_inter.mp hz).1) hc (p.take j)
  have hqj := hq (p.getVert j) ((H.induce Q).walk_vertices p hc _ (p.getVert_mem_support j))
  change (H.induce Q).vertexDistance x c (p.getVert j) ≤ ∑ z ∈ T, x z at hd
  norm_num at hsum
  nlinarith [hj.2]

end Paper.Hypergraph
