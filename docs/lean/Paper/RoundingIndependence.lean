import Paper.RoundingAveraging
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

namespace Paper.Hypergraph

theorem independent_card_le (H : Hypergraph) {S : Finset ℕ}
    (hS : S ⊆ H.vertices) (hi : H.independent S) : S.card ≤ H.independenceNumber :=
  Finset.le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_powerset.mpr hS, hi⟩)

/-- The vertices of a shortest path split into two independent sets. -/
theorem shortest_path_support_card_le_twice_independence (H : Hypergraph)
    (Q R : Finset ℕ) {u v : ℕ} (hu : u ∈ (H.induce Q).vertices)
    (p : (H.induce Q).primal.Walk u v) (hp : p.length = (H.induce Q).primal.dist u v)
    {S : Finset ℕ} (hS : ∀ w ∈ S, w ∈ p.support) (hR : S ⊆ R) :
    S.card ≤ 2 * (H.induce R).independenceNumber := by
  let J := H.induce Q
  let c := fun w => J.primal.dist u w
  have hinj : ∀ a ∈ S, ∀ b ∈ S, c a = c b → a = b := by
    intro a ha b hb heq
    obtain ⟨i, hi, hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hS a ha)
    obtain ⟨j, hj, hjl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hS b hb)
    have hdi := shortest_path_prefix_distance p hp hil
    have hdj := shortest_path_prefix_distance p hp hjl
    rw [hi] at hdi
    rw [hj] at hdj
    have hij : i = j := by change (H.induce Q).primal.dist u a = (H.induce Q).primal.dist u b at heq; omega
    exact hi.symm.trans ((congrArg p.getVert hij).trans hj)
  have hpart (k : ℕ) : (S.filter (fun w => c w % 2 = k)).card ≤ (H.induce R).independenceNumber := by
    apply (H.induce R).independent_card_le
    · intro w hw
      have hwS := (mem_filter.mp hw).1
      exact mem_inter.mpr ⟨(mem_inter.mp (J.walk_vertices p hu w (hS w hwS))).1, hR hwS⟩
    · intro a ha b hb hab
      obtain ⟨haS, hac⟩ := mem_filter.mp ha
      obtain ⟨hbS, hbc⟩ := mem_filter.mp hb
      have haJ := J.walk_vertices p hu a (hS a haS)
      have hbJ := J.walk_vertices p hu b (hS b hbS)
      have hadj : J.primal.Adj a b :=
        (H.primal_induce_adj Q (mem_inter.mp haJ).2 (mem_inter.mp hbJ).2).mpr
          (H.primal_induce_le R hab)
      have h₁ := hadj.reachable.dist_triangle_right u
      have h₂ := hadj.symm.reachable.dist_triangle_right u
      rw [J.primal.dist_eq_one_iff_adj.mpr hadj] at h₁
      rw [J.primal.dist_eq_one_iff_adj.mpr hadj.symm] at h₂
      have heq : c a = c b := by dsimp [c] at *; omega
      exact hab.ne (hinj a haS b hbS heq)
  have hcover : S = S.filter (fun w => c w % 2 = 0) ∪ S.filter (fun w => c w % 2 = 1) := by
    ext w
    simp only [mem_union, mem_filter]
    have := Nat.mod_lt (c w) (by decide : 0 < 2)
    by_cases hw : w ∈ S
    · simp only [hw, true_and, true_iff]
      omega
    · simp [hw]
  calc
    S.card ≤ (S.filter (fun w => c w % 2 = 0)).card + (S.filter (fun w => c w % 2 = 1)).card := by
      conv_lhs => rw [hcover]
      exact card_union_le _ _
    _ ≤ _ := by have h0 := hpart 0; have h1 := hpart 1; omega

def trimDemand (x : ℕ → ℝ) (ε : ℝ) (v : ℕ) : ℝ :=
  if ε ≤ x v then min (2 * x v) 1 else 0

theorem trimDemand_unit (H : Hypergraph) {x : ℕ → ℝ} (hx : H.UnitDemand x) (ε : ℝ) :
    H.UnitDemand (trimDemand x ε) := by
  intro v hv
  dsimp [trimDemand]
  split_ifs
  · exact ⟨le_min (by linarith [(hx v hv).1]) zero_le_one, min_le_right _ _⟩
  · norm_num

theorem trimDemand_support (H : Hypergraph) (x : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    H.vertices.filter (fun v => trimDemand x ε v ≠ 0) ⊆ H.vertices.filter (fun v => x v ≠ 0) := by
  intro v hv
  obtain ⟨hv, hz⟩ := mem_filter.mp hv
  refine mem_filter.mpr ⟨hv, ?_⟩
  intro h0
  simp [trimDemand, h0, not_le.mpr hε] at hz

theorem trimDemand_cost_le (H : Hypergraph) {x : ℕ → ℝ} (hx : H.UnitDemand x) (ε : ℝ) :
    H.coverCost (trimDemand x ε) ≤ 2 * H.coverCost x := by
  rw [← H.coverCost_smul x (by norm_num : (0 : ℝ) < 2)]
  apply H.coverCost_mono
  intro v hv
  change trimDemand x ε v ≤ 2 * x v
  dsimp [trimDemand]
  split_ifs
  · exact min_le_left _ _
  · linarith [(hx v hv).1]

/-- Removing small demands loses at most half the weight of a shortest path. -/
theorem trimDemand_fractionalSeparator (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hx : H.FractionalSeparator A B x) {ε : ℝ} (hε : 0 < ε)
    (hbudget : ε * (2 * (H.induce (H.vertices.filter (fun v => x v ≠ 0))).independenceNumber : ℝ) ≤ 1 / 2) :
    H.FractionalSeparator A B (trimDemand x ε) := by
  let z := trimDemand x ε
  have hz := H.trimDemand_unit hx.1 ε
  refine ⟨hz, ?_⟩
  intro u hu v hv
  apply le_csInf ⟨1, Set.mem_insert _ _⟩
  rintro t (rfl | ⟨p, hp, rfl⟩)
  · exact le_rfl
  let Q := p.support.toFinset
  let R := H.vertices.filter (fun v => x v ≠ 0)
  have huQ : u ∈ (H.induce Q).vertices := mem_inter.mpr
    ⟨hA hu, List.mem_toFinset.mpr p.start_mem_support⟩
  have hpQ := H.walk_reachable_induce p (fun w hw => List.mem_toFinset.mpr hw)
  obtain ⟨q, hq⟩ := hpQ.exists_walk_length_eq_dist
  let T := q.support.toFinset
  have hTV : T ⊆ H.vertices := fun w hw =>
    (mem_inter.mp ((H.induce Q).walk_vertices q huQ w (List.mem_toFinset.mp hw))).1
  have hTQ : T ⊆ Q := fun w hw =>
    (mem_inter.mp ((H.induce Q).walk_vertices q huQ w (List.mem_toFinset.mp hw))).2
  have hxs : 1 ≤ ∑ w ∈ T, x w := by
    have hdist := H.vertexDistance_le_walk (fun w hw => (hx.1 w hw).1) (hA hu)
      (q.mapLe (H.primal_induce_le Q))
    simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using (hx.2 u hu v hv).trans hdist
  have hzs : 1 ≤ ∑ w ∈ T, z w := by
    by_cases hbig : ∃ w ∈ T, 1 ≤ z w
    · obtain ⟨w, hw, hwz⟩ := hbig
      exact hwz.trans (single_le_sum (fun w hw => (hz w (hTV hw)).1) hw)
    have hsmall : ∀ w ∈ T, z w < 1 := by
      intro w hw
      exact lt_of_not_ge (fun h => hbig ⟨w, hw, h⟩)
    have hcard : (T.filter (fun w => x w ≠ 0)).card ≤ 2 * (H.induce R).independenceNumber :=
      H.shortest_path_support_card_le_twice_independence Q R huQ q hq
        (fun w hw => List.mem_toFinset.mp (mem_filter.mp hw).1)
        (fun w hw => mem_filter.mpr ⟨hTV (mem_filter.mp hw).1, (mem_filter.mp hw).2⟩)
    have hpoint : ∀ w ∈ T, x w ≤ z w / 2 + if x w ≠ 0 then ε else 0 := by
      intro w hw
      by_cases hx0 : x w = 0
      · simp only [hx0, ne_eq, not_true_eq_false, if_false, add_zero]
        exact div_nonneg (hz w (hTV hw)).1 (by norm_num)
      · simp only [hx0, ne_eq, not_false_eq_true, if_true]
        by_cases hlarge : ε ≤ x w
        · have hcap : 2 * x w < 1 := by
            have h := hsmall w hw
            change (if ε ≤ x w then min (2 * x w) 1 else 0) < 1 at h
            rw [if_pos hlarge] at h
            exact (min_lt_iff.mp h).resolve_right (lt_irrefl _)
          have heq : z w = 2 * x w := by simp [z, trimDemand, hlarge, min_eq_left hcap.le]
          rw [heq]
          linarith
        · have heq : z w = 0 := by simp [z, trimDemand, hlarge]
          rw [heq]
          linarith
    have hsum := sum_le_sum hpoint
    rw [sum_add_distrib, ← sum_div, ← sum_filter, sum_const, nsmul_eq_mul] at hsum
    have hc : ((T.filter (fun w => x w ≠ 0)).card : ℝ) ≤ 2 * (H.induce R).independenceNumber := by
      exact_mod_cast hcard
    have hb : ε * (2 * (H.induce R).independenceNumber : ℝ) ≤ 1 / 2 := hbudget
    nlinarith
  exact hzs.trans (sum_le_sum_of_subset_of_nonneg hTQ (fun w hw _ =>
    (hz w (H.walk_vertices p (hA hu) w (List.mem_toFinset.mp hw))).1))

/-- The independence-number branch of Theorem 4.1. -/
theorem twoTerminal_independence_rounding (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hB : B ⊆ H.vertices) (hx : H.FractionalSeparator A B x) :
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralSeparator A B S ∧
      H.setCoverCost S ≤
        (8 + 4 * Real.log ((H.induce (H.vertices.filter (fun v => x v ≠ 0))).independenceNumber : ℝ)) *
          H.coverCost x := by
  let R := H.vertices.filter (fun v => x v ≠ 0)
  let α : ℝ := (H.induce R).independenceNumber
  by_cases hR : R.Nonempty
  swap
  · have hR0 := Finset.not_nonempty_iff_eq_empty.mp hR
    refine ⟨R, Subset.refl _, H.support_integralSeparator hA hx, ?_⟩
    have hempty : H.setCoverCost ∅ = 0 := H.coverCost_eq_zero_of_nonpos (fun v hv => by simp [indicator])
    rw [hR0, hempty]
    apply mul_nonneg _ (H.coverCost_nonneg x)
    have := log_nat_nonneg (H.induce R).independenceNumber
    change 0 ≤ 8 + 4 * Real.log α
    dsimp [α]
    linarith
  have hα1 : 1 ≤ α := by
    obtain ⟨v, hv⟩ := hR
    have hcard : ({v} : Finset ℕ).card ≤ (H.induce R).independenceNumber := by
      apply (H.induce R).independent_card_le
      · intro w hw
        have hwv := mem_singleton.mp hw
        subst w
        exact mem_inter.mpr ⟨(mem_filter.mp hv).1, hv⟩
      · intro a ha b hb
        have ha' := mem_singleton.mp ha
        have hb' := mem_singleton.mp hb
        subst a b
        exact fun h => h.ne rfl
    simpa [α] using (show (1 : ℝ) ≤ (H.induce R).independenceNumber by exact_mod_cast hcard)
  have hα : 0 < α := by linarith
  let ε : ℝ := 1 / (4 * α)
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := (div_le_one (by positivity : 0 < 4 * α)).2 (by linarith)
  have hbudget : ε * (2 * (H.induce R).independenceNumber : ℝ) ≤ 1 / 2 := by
    change (1 / (4 * α)) * (2 * α) ≤ 1 / 2
    field_simp
    linarith
  have hz := H.trimDemand_fractionalSeparator hA hx hε hbudget
  have hsmall : ∀ v ∈ H.vertices, trimDemand x ε v = 0 ∨ ε ≤ trimDemand x ε v := by
    intro v hv
    dsimp [trimDemand]
    split_ifs with h
    · exact Or.inr (le_min (by linarith) hε1)
    · exact Or.inl rfl
  obtain ⟨S, hS, hsep, hcost⟩ := H.twoTerminal_minimum_weight_rounding hA hB hz hε hε1 hsmall
  refine ⟨S, hS.trans (H.trimDemand_support x hε), hsep, ?_⟩
  have hlog : Real.log (1 / ε) = Real.log 4 + Real.log α := by
    rw [show 1 / ε = 4 * α by simp [ε], Real.log_mul (by norm_num) (ne_of_gt hα)]
  have hlog4 : Real.log 4 < 3 / 2 := by
    have h := Real.log_two_lt_d9
    have heq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    linarith
  have hc : 0 ≤ 1 + 2 * Real.log (1 / ε) := by
    have h := Real.log_nonneg ((le_div_iff₀ hε).2 (by simpa using hε1))
    linarith
  calc
    H.setCoverCost S ≤ (1 + 2 * Real.log (1 / ε)) * (2 * H.coverCost x) :=
      hcost.trans (mul_le_mul_of_nonneg_left (H.trimDemand_cost_le hx.1 ε) hc)
    _ = ((1 + 2 * Real.log (1 / ε)) * 2) * H.coverCost x := by ring
    _ ≤ (8 + 4 * Real.log α) * H.coverCost x := by
      apply mul_le_mul_of_nonneg_right _ (H.coverCost_nonneg x)
      rw [hlog]
      linarith

end Paper.Hypergraph
