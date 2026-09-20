import Paper.TrustBoundary

/-!
# Checked deductions from the mathematical specification

The specification is in `Paper/TrustBoundary.lean`. This module proves
`ExternalRounding → MainWidthComparison` without admitted proofs or custom
axioms. The existing internal proof uses the regularized separator bounds.
-/

noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

namespace Paper
namespace Hypergraph

/-! ## Statement phase: elementary properties and the dependency chain -/

def oneBag (H : Hypergraph) : H.TreeDecomposition 0 where
  tree := ⊥
  isTree := by
    letI : Subsingleton (Fin (0 + 1)) := ⟨by intro a b; apply Fin.ext; omega⟩
    exact SimpleGraph.IsTree.of_subsingleton
  bag := fun _ => H.vertices
  bag_subset := fun _ => Subset.refl _
  edge_covered := fun e he => ⟨0, H.edge_subset e he⟩
  vertex_covered := fun v hv => ⟨0, hv⟩
  running_intersection := by
    letI : Subsingleton (Fin (0 + 1)) := ⟨by intro a b; apply Fin.ext; omega⟩
    exact fun _ _ => SimpleGraph.Preconnected.of_subsingleton

/-- Lower bounds pass to the optimum; the one-bag tree supplies an upper bound. -/
theorem optimalWidth_bounds (H : Hypergraph) (b : Finset ℕ → ℝ) {L : ℝ}
    (hb : ∀ S ⊆ H.vertices, L ≤ b S) :
    L ≤ H.optimalWidth b ∧ H.optimalWidth b ≤ b H.vertices := by
  have hlo : ∀ r ∈ {r | ∃ n, ∃ D : H.TreeDecomposition n, r = D.bagWidth b},
      L ≤ r := by
    rintro r ⟨n, D, rfl⟩
    exact (hb _ (D.bag_subset 0)).trans
      (le_csSup (Set.finite_range _).bddAbove ⟨0, rfl⟩)
  constructor
  · exact le_csInf ⟨_, 0, H.oneBag, rfl⟩ hlo
  · calc
      H.optimalWidth b ≤ H.oneBag.bagWidth b :=
        csInf_le ⟨L, hlo⟩ ⟨0, H.oneBag, rfl⟩
      _ = b H.vertices := by simp [TreeDecomposition.bagWidth, oneBag]

theorem optimalWidth_le_bagWidth (H : Hypergraph) (b : Finset ℕ → ℝ)
    (hb : ∀ S ⊆ H.vertices, 0 ≤ b S) {n : ℕ} (D : H.TreeDecomposition n) :
    H.optimalWidth b ≤ D.bagWidth b := by
  refine csInf_le ⟨0, ?_⟩ ⟨n, D, rfl⟩
  rintro r ⟨m, D', rfl⟩
  exact (hb _ (D'.bag_subset 0)).trans
    (le_csSup (Set.finite_range _).bddAbove ⟨0, rfl⟩)

/-- A finite demand has a cover because the hypergraph has no isolated vertices. -/
theorem cover_exists (H : Hypergraph) (x : ℕ → ℝ) : ∃ y, H.Cover x y := by
  let M : ℝ := ∑ v ∈ H.vertices, max 0 (x v)
  have hM : 0 ≤ M := sum_nonneg (fun _ _ => le_max_left _ _)
  refine ⟨fun _ => M, (fun _ _ => hM), ?_⟩
  intro v hv
  obtain ⟨e, he, hve⟩ := H.no_isolated v hv
  calc
    x v ≤ max 0 (x v) := le_max_right _ _
    _ ≤ M := single_le_sum (fun _ _ => le_max_left _ _) hv
    _ ≤ ∑ f ∈ H.edges.filter (fun f => v ∈ H.edge f), M :=
      single_le_sum (fun _ _ => hM) (mem_filter.mpr ⟨he, hve⟩)

theorem coverCost_nonneg (H : Hypergraph) (x : ℕ → ℝ) : 0 ≤ H.coverCost x := by
  unfold coverCost
  by_cases hs : {r : ℝ | ∃ y, H.Cover x y ∧ r = ∑ e ∈ H.edges, y e}.Nonempty
  · apply le_csInf hs
    rintro r ⟨y, hy, rfl⟩
    exact sum_nonneg hy.1
  · rw [Set.not_nonempty_iff_eq_empty.mp hs, Real.sInf_empty]

theorem coverCost_le (H : Hypergraph) {x y : ℕ → ℝ} (hy : H.Cover x y) :
    H.coverCost x ≤ ∑ e ∈ H.edges, y e := by
  refine csInf_le ⟨0, ?_⟩ ⟨y, hy, rfl⟩
  rintro r ⟨z, hz, rfl⟩
  exact sum_nonneg hz.1

theorem le_coverCost (H : Hypergraph) (x : ℕ → ℝ) {r : ℝ}
    (h : ∀ y, H.Cover x y → r ≤ ∑ e ∈ H.edges, y e) : r ≤ H.coverCost x := by
  obtain ⟨y, hy⟩ := H.cover_exists x
  refine le_csInf ⟨_, y, hy, rfl⟩ ?_
  rintro z ⟨y', hy', rfl⟩
  exact h y' hy'

theorem coverCost_mono (H : Hypergraph) {x z : ℕ → ℝ}
    (h : ∀ v ∈ H.vertices, x v ≤ z v) : H.coverCost x ≤ H.coverCost z := by
  apply H.le_coverCost
  intro y hy
  exact H.coverCost_le ⟨hy.1, fun v hv => (h v hv).trans (hy.2 v hv)⟩

/-- Capping a cover at one preserves feasibility for unit demands. -/
theorem cover_cap (H : Hypergraph) {x y : ℕ → ℝ} (hx : H.UnitDemand x)
    (hy : H.Cover x y) : H.Cover x (fun e => min (y e) 1) := by
  refine ⟨fun e he => le_min (hy.1 e he) (by norm_num), ?_⟩
  intro v hv
  by_cases h : ∃ e ∈ H.edges.filter (fun e => v ∈ H.edge e), 1 ≤ y e
  · obtain ⟨e, he, he1⟩ := h
    calc
      x v ≤ 1 := (hx v hv).2
      _ = min (y e) 1 := (min_eq_right he1).symm
      _ ≤ ∑ f ∈ H.edges.filter (fun f => v ∈ H.edge f), min (y f) 1 :=
        single_le_sum (fun f hf => le_min (hy.1 f (mem_filter.mp hf).1)
          (by norm_num)) he
  · convert hy.2 v hv using 1
    apply sum_congr rfl
    intro e he
    exact min_eq_left (le_of_not_ge (fun h1 => h ⟨e, he, h1⟩))

/-- The cover cost agrees with the cited paper's coefficients in [0,1]. -/
theorem coverCost_eq_capped (H : Hypergraph) {x : ℕ → ℝ} (hx : H.UnitDemand x) :
    H.coverCost x = sInf {r | ∃ y, H.Cover x y ∧
      (∀ e ∈ H.edges, y e ≤ 1) ∧ r = ∑ e ∈ H.edges, y e} := by
  obtain ⟨y, hy⟩ := H.cover_exists x
  have hne : {r | ∃ y, H.Cover x y ∧
      (∀ e ∈ H.edges, y e ≤ 1) ∧ r = ∑ e ∈ H.edges, y e}.Nonempty :=
    ⟨_, (fun e => min (y e) 1), H.cover_cap hx hy, fun _ _ => min_le_right _ _, rfl⟩
  have hb : BddBelow {r | ∃ y, H.Cover x y ∧
      (∀ e ∈ H.edges, y e ≤ 1) ∧ r = ∑ e ∈ H.edges, y e} := by
    refine ⟨0, ?_⟩
    rintro r ⟨z, hz, _, rfl⟩
    exact sum_nonneg hz.1
  apply le_antisymm
  · refine le_csInf hne ?_
    rintro r ⟨z, hz, _, rfl⟩
    exact H.coverCost_le hz
  · apply H.le_coverCost
    intro z hz
    exact (csInf_le hb ⟨_, H.cover_cap hx hz, fun _ _ => min_le_right _ _, rfl⟩).trans
      (sum_le_sum (fun _ _ => min_le_left _ _))

/-- The minimum cover cost is attained, with coefficients in [0,1]. -/
theorem coverCost_attained (H : Hypergraph) {x : ℕ → ℝ} (hx : H.UnitDemand x) :
    ∃ y, H.Cover x y ∧ (∀ e ∈ H.edges, y e ≤ 1) ∧
      H.coverCost x = ∑ e ∈ H.edges, y e := by
  let E := {e // e ∈ H.edges}
  let extend : (E → ℝ) → ℕ → ℝ := fun z e => if he : e ∈ H.edges then z ⟨e, he⟩ else 0
  have hext (e : ℕ) : Continuous (fun z : E → ℝ => extend z e) := by
    dsimp [extend]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  let K : Set (E → ℝ) := Set.Icc 0 1 ∩ {z | H.Cover x (extend z)}
  have hclosed : IsClosed {z : E → ℝ | H.Cover x (extend z)} := by
    unfold Cover
    simp only [Set.setOf_and, Set.setOf_forall]
    apply IsClosed.inter
    · exact isClosed_iInter fun e => isClosed_iInter fun _ =>
        isClosed_le continuous_const (hext e)
    · exact isClosed_iInter fun v => isClosed_iInter fun _ =>
        isClosed_le continuous_const (continuous_finsetSum _ (fun e _ => hext e))
  have hcompact : IsCompact K := isCompact_Icc.inter_right hclosed
  have hmem (y : ℕ → ℝ) (hy : H.Cover x y) :
      (fun e : E => min (y e) 1) ∈ K := by
    have heq : ∀ e ∈ H.edges,
        extend (fun e : E => min (y e) 1) e = min (y e) 1 := by
      intro e he
      simp [extend, he]
    refine ⟨⟨fun e => le_min (hy.1 e e.property) (by norm_num),
      fun _ => min_le_right _ _⟩, ?_⟩
    refine ⟨fun e he => by rw [heq e he]; exact le_min (hy.1 e he) (by norm_num), ?_⟩
    intro v hv
    convert (H.cover_cap hx hy).2 v hv using 1
    apply sum_congr rfl
    intro e he
    exact heq e (mem_filter.mp he).1
  obtain ⟨y0, hy0⟩ := H.cover_exists x
  have hcont : Continuous (fun z : E → ℝ => ∑ e ∈ H.edges, extend z e) :=
    continuous_finsetSum _ (fun e _ => hext e)
  obtain ⟨z, hz, hmin⟩ := hcompact.exists_isMinOn ⟨_, hmem y0 hy0⟩ hcont.continuousOn
  refine ⟨extend z, hz.2, ?_, le_antisymm (H.coverCost_le hz.2) ?_⟩
  · intro e he
    simpa [extend, he] using hz.1.2 ⟨e, he⟩
  · apply H.le_coverCost
    intro y hy
    calc
      (∑ e ∈ H.edges, extend z e) ≤
          ∑ e ∈ H.edges, extend (fun e : E => min (y e) 1) e := hmin (hmem y hy)
      _ ≤ ∑ e ∈ H.edges, y e := by
        apply sum_le_sum
        intro e he
        simpa [extend, he] using min_le_left (y e) 1

theorem modularWeight_vertex_le_one (H : Hypergraph) {w : ℕ → ℝ}
    (hw : H.ModularWeight w) {v : ℕ} (hv : v ∈ H.vertices) : w v ≤ 1 := by
  obtain ⟨e, he, hve⟩ := H.no_isolated v hv
  exact (single_le_sum (fun u _ => hw.1 u) hve).trans (hw.2 e he)

theorem modularValue_submodular (H : Hypergraph) {w : ℕ → ℝ}
    (hw : H.ModularWeight w) : H.SubmodularWeight (modularValue w) := by
  refine ⟨by simp [modularValue], ?_, ?_, hw.2⟩
  · intro A hA B hB hAB
    exact sum_le_sum_of_subset_of_nonneg hAB (fun v _ _ => hw.1 v)
  · intro A hA B hB
    exact sum_union_inter.le

theorem incident_edges_induce (H : Hypergraph) {W : Finset ℕ} {v : ℕ} (hv : v ∈ W) :
    (H.induce W).edges.filter (fun e => v ∈ (H.induce W).edge e) =
      H.edges.filter (fun e => v ∈ H.edge e) := by
  ext e
  simp only [induce, mem_filter, mem_inter]
  constructor
  · rintro ⟨⟨he, _⟩, hve, _⟩; exact ⟨he, hve⟩
  · rintro ⟨he, hve⟩
    exact ⟨⟨he, ⟨v, mem_inter.mpr ⟨hve, hv⟩⟩⟩, hve, hv⟩

theorem cover_restriction (H : Hypergraph) {X W : Finset ℕ}
    (hXW : X ⊆ W) :
    (H.induce W).setCoverCost X = H.setCoverCost X := by
  change (H.induce W).coverCost (indicator X) = H.coverCost (indicator X)
  apply le_antisymm
  · apply H.le_coverCost
    intro y hy
    have hy' : (H.induce W).Cover (indicator X) y := by
      refine ⟨fun e he => hy.1 e (mem_filter.mp he).1, ?_⟩
      intro v hv
      rw [H.incident_edges_induce (mem_inter.mp hv).2]
      exact hy.2 v (mem_inter.mp hv).1
    exact ((H.induce W).coverCost_le hy').trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun e he _ => hy.1 e he))
  · apply (H.induce W).le_coverCost
    intro y hy
    let y' : ℕ → ℝ := fun e => if e ∈ (H.induce W).edges then y e else 0
    have hy'nonneg : ∀ e, 0 ≤ y' e := by
      intro e
      dsimp [y']
      split_ifs with he
      · exact hy.1 e he
      · exact le_rfl
    have hy' : H.Cover (indicator X) y' := by
      refine ⟨fun e _ => hy'nonneg e, ?_⟩
      intro v hv
      by_cases hvW : v ∈ W
      · have hcov := hy.2 v (mem_inter.mpr ⟨hv, hvW⟩)
        rw [← H.incident_edges_induce hvW]
        convert hcov using 1
        apply sum_congr rfl
        intro e he
        simp only [y', if_pos (mem_filter.mp he).1]
      · have hvX : v ∉ X := fun h => hvW (hXW h)
        simp only [indicator, if_neg hvX]
        exact sum_nonneg (fun e _ => hy'nonneg e)
    calc
      H.coverCost (indicator X) ≤ ∑ e ∈ H.edges, y' e := H.coverCost_le hy'
      _ = ∑ e ∈ (H.induce W).edges, y e := by
        dsimp [y']
        rw [← sum_filter]
        congr 1
        ext e
        simp only [induce, mem_filter, and_self_left]

/-- Nonpositive demands have zero cover cost. -/
theorem coverCost_eq_zero_of_nonpos (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, x v ≤ 0) : H.coverCost x = 0 := by
  apply le_antisymm _ (H.coverCost_nonneg x)
  have hy : H.Cover x (fun _ => 0) := ⟨by simp, by simpa using hx⟩
  simpa using H.coverCost_le hy

theorem cover_add (H : Hypergraph) {x z y u : ℕ → ℝ}
    (hy : H.Cover x y) (hu : H.Cover z u) : H.Cover (x + z) (y + u) := by
  refine ⟨fun e he => add_nonneg (hy.1 e he) (hu.1 e he), ?_⟩
  intro v hv
  simpa [Pi.add_apply, sum_add_distrib] using add_le_add (hy.2 v hv) (hu.2 v hv)

theorem coverCost_add_le (H : Hypergraph) (x z : ℕ → ℝ) :
    H.coverCost (x + z) ≤ H.coverCost x + H.coverCost z := by
  have h : H.coverCost (x + z) - H.coverCost z ≤ H.coverCost x := by
    apply H.le_coverCost
    intro y hy
    have h' : H.coverCost (x + z) - ∑ e ∈ H.edges, y e ≤ H.coverCost z := by
      apply H.le_coverCost
      intro u hu
      have := H.coverCost_le (H.cover_add hy hu)
      simp only [Pi.add_apply, sum_add_distrib] at this
      linarith
    linarith
  linarith

theorem cover_smul (H : Hypergraph) {x y : ℕ → ℝ} (hy : H.Cover x y)
    {c : ℝ} (hc : 0 ≤ c) : H.Cover (c • x) (c • y) := by
  refine ⟨fun e he => mul_nonneg hc (hy.1 e he), ?_⟩
  intro v hv
  simpa [Pi.smul_apply, smul_eq_mul, mul_sum] using
    mul_le_mul_of_nonneg_left (hy.2 v hv) hc

theorem coverCost_smul_le (H : Hypergraph) (x : ℕ → ℝ) {c : ℝ} (hc : 0 < c) :
    H.coverCost (c • x) ≤ c * H.coverCost x := by
  rw [mul_comm c, ← div_le_iff₀ hc]
  apply H.le_coverCost
  intro y hy
  rw [div_le_iff₀ hc]
  simpa [Pi.smul_apply, smul_eq_mul, mul_sum, mul_comm] using
    H.coverCost_le (H.cover_smul hy hc.le)

theorem coverCost_smul (H : Hypergraph) (x : ℕ → ℝ) {c : ℝ} (hc : 0 < c) :
    H.coverCost (c • x) = c * H.coverCost x := by
  apply le_antisymm (H.coverCost_smul_le x hc)
  have hi := H.coverCost_smul_le (c • x) (inv_pos.mpr hc)
  simp only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at hi
  have := mul_le_mul_of_nonneg_left hi hc.le
  simpa [← mul_assoc, mul_inv_cancel₀ hc.ne'] using this

/-- Supporting functional for the sublinear cover cost (finite LP duality). -/
theorem coverCost_support (H : Hypergraph) (x : ℕ → ℝ) :
    ∃ g : (ℕ → ℝ) →ₗ[ℝ] ℝ, g x = H.coverCost x ∧ ∀ z, g z ≤ H.coverCost z := by
  by_cases hx : x = 0
  · subst x
    refine ⟨0, ?_, fun z => H.coverCost_nonneg z⟩
    simp [H.coverCost_eq_zero_of_nonpos (x := 0) (by simp)]
  let f : (ℕ → ℝ) →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton x (H.coverCost x) hx
  have hf : ∀ z : f.domain, f z ≤ H.coverCost z := by
    rintro ⟨z, hz⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    simp only [f, LinearPMap.mkSpanSingleton, LinearPMap.mkSpanSingleton'_apply,
      RingHom.id_apply, smul_eq_mul]
    by_cases hc : 0 < c
    · exact (H.coverCost_smul x hc).ge
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hc)
        (H.coverCost_nonneg x)).trans (H.coverCost_nonneg _)
  obtain ⟨g, hg, hbound⟩ := exists_extension_of_le_sublinear f H.coverCost
    (fun c hc z => H.coverCost_smul z hc) H.coverCost_add_le hf
  refine ⟨g, ?_, hbound⟩
  exact (hg ⟨x, Submodule.mem_span_singleton_self x⟩).trans
    (LinearPMap.mkSpanSingleton_apply ℝ ℝ hx _)

/-- The greedy supporting modular function for a finite polymatroid.
The induction contracts one vertex; the resulting weights are supported on U. -/
theorem submodular_support (U : Finset ℕ) (b : Finset ℕ → ℝ)
    (h0 : b ∅ = 0)
    (hm : ∀ A ⊆ U, ∀ B ⊆ U, A ⊆ B → b A ≤ b B)
    (hs : ∀ A ⊆ U, ∀ B ⊆ U, b (A ∪ B) + b (A ∩ B) ≤ b A + b B) :
    ∃ w : ℕ → ℝ, (∀ v, 0 ≤ w v) ∧ (∀ v ∉ U, w v = 0) ∧
      modularValue w U = b U ∧ ∀ A ⊆ U, modularValue w A ≤ b A := by
  induction U using Finset.induction_on generalizing b with
  | empty =>
    refine ⟨fun _ => 0, by simp, by simp, by simpa [modularValue] using h0.symm, ?_⟩
    intro A hA
    have : A = ∅ := subset_empty.mp hA
    simp [this, modularValue, h0]
  | @insert v U hv ih =>
    let g : Finset ℕ → ℝ := fun A => b (insert v A) - b {v}
    have hg0 : g ∅ = 0 := by simp [g]
    have hgm : ∀ A ⊆ U, ∀ B ⊆ U, A ⊆ B → g A ≤ g B := by
      intro A hA B hB hAB
      exact sub_le_sub_right (hm _ (insert_subset_insert v hA) _
        (insert_subset_insert v hB) (insert_subset_insert v hAB)) _
    have hgs : ∀ A ⊆ U, ∀ B ⊆ U,
        g (A ∪ B) + g (A ∩ B) ≤ g A + g B := by
      intro A hA B hB
      have h := hs (insert v A) (insert_subset_insert v hA)
        (insert v B) (insert_subset_insert v hB)
      have hi : insert v A ∩ insert v B = insert v (A ∩ B) := by
        ext u; simp only [mem_inter, mem_insert]; tauto
      simp only [insert_union, union_insert, insert_idem, hi] at h
      dsimp [g]
      linarith
    obtain ⟨w, hw, hwout, hwsum, hwle⟩ := ih g hg0 hgm hgs
    let z : ℕ → ℝ := fun u => if u = v then b {v} else w u
    have hbv : 0 ≤ b {v} := by
      have h := hm ∅ (empty_subset _) {v} (by simp) (empty_subset _)
      simpa [h0] using h
    have hzsum : ∀ A ⊆ U, modularValue z A = modularValue w A := by
      intro A hA
      apply sum_congr rfl
      intro u hu
      have huv : u ≠ v := by intro heq; subst u; exact hv (hA hu)
      simp only [z, if_neg huv]
    refine ⟨z, ?_, ?_, ?_, ?_⟩
    · intro u; dsimp [z]; split_ifs <;> first | exact hbv | exact hw u
    · intro u hu
      have huv : u ≠ v := by intro h; subst u; exact hu (mem_insert_self _ _)
      have huU : u ∉ U := fun h => hu (mem_insert_of_mem h)
      simp [z, huv, hwout u huU]
    · change (∑ u ∈ insert v U, z u) = _
      rw [sum_insert hv]
      change z v + modularValue z U = _
      rw [hzsum U (Subset.refl U), hwsum]
      simp [z, g]
    · intro A hA
      by_cases hvA : v ∈ A
      · have hAU : A.erase v ⊆ U := by
          intro u hu
          have huA := (mem_erase.mp hu).2
          rcases mem_insert.mp (hA huA) with h | h
          · exact False.elim ((mem_erase.mp hu).1 h)
          · exact h
        have hle := hwle (A.erase v) hAU
        dsimp [g] at hle
        rw [insert_erase hvA] at hle
        calc
          modularValue z A = z v + modularValue z (A.erase v) := by
            simpa [modularValue, add_comm] using (sum_erase_add A z hvA).symm
          _ = b {v} + modularValue w (A.erase v) := by
            rw [hzsum _ hAU]; simp [z]
          _ ≤ b A := by linarith
      · have hAU : A ⊆ U := by
          intro u hu
          rcases mem_insert.mp (hA hu) with h | h
          · subst u; exact False.elim (hvA hu)
          · exact h
        rw [hzsum A hAU]
        have hle := hwle A hAU
        have hsub := hs {v} (by simp) A hA
        have hinter : ({v} : Finset ℕ) ∩ A = ∅ := by simp [hvA]
        simp only [singleton_union, hinter, h0, add_zero] at hsub
        dsimp [g] at hle
        linarith

theorem sum_incidence_swap (H : Hypergraph) (f : ℕ → ℕ → ℝ) :
    (∑ v ∈ H.vertices, ∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), f v e) =
      ∑ e ∈ H.edges, ∑ v ∈ H.edge e, f v e := by
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  rw [← sum_filter]
  congr 1
  ext v
  simp only [mem_filter]
  exact ⟨And.right, fun hv => ⟨H.edge_subset e he hv, hv⟩⟩

theorem modular_le_coverCost (H : Hypergraph) {w : ℕ → ℝ} (hw : H.ModularWeight w)
    (x : ℕ → ℝ) : (∑ v ∈ H.vertices, w v * x v) ≤ H.coverCost x := by
  apply H.le_coverCost
  intro y hy
  calc
    (∑ v ∈ H.vertices, w v * x v) ≤
        ∑ v ∈ H.vertices, w v * (∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), y e) :=
      sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (hy.2 v hv) (hw.1 v))
    _ = ∑ v ∈ H.vertices, ∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), w v * y e := by
      simp_rw [mul_sum]
    _ = ∑ e ∈ H.edges, ∑ v ∈ H.edge e, w v * y e := H.sum_incidence_swap _
    _ ≤ ∑ e ∈ H.edges, y e := by
      apply sum_le_sum
      intro e he
      rw [← sum_mul]
      exact mul_le_of_le_one_left (hy.1 e he) (hw.2 e he)

theorem cover_duality (H : Hypergraph) {x : ℕ → ℝ} (_hx : H.UnitDemand x) :
    ∃ w, H.ModularWeight w ∧ H.coverCost x = ∑ v ∈ H.vertices, w v * x v ∧
      ∀ w', H.ModularWeight w' → (∑ v ∈ H.vertices, w' v * x v) ≤ H.coverCost x := by
  obtain ⟨g, hgx, hg⟩ := H.coverCost_support x
  let w : ℕ → ℝ := fun v => g (Pi.single v 1)
  have hw0 : ∀ v, 0 ≤ w v := by
    intro v
    have hz : H.coverCost (-Pi.single v 1) = 0 := by
      apply H.coverCost_eq_zero_of_nonpos
      intro u hu
      simp only [Pi.neg_apply, Pi.single_apply]
      split_ifs <;> norm_num
    have hh := hg (-Pi.single v 1)
    rw [hz, map_neg] at hh
    dsimp [w]
    linarith
  have hsum (S : Finset ℕ) (z : ℕ → ℝ) :
      g (∑ v ∈ S, z v • Pi.single v (1 : ℝ)) = ∑ v ∈ S, z v * w v := by
    simp [map_sum, map_smul, smul_eq_mul, w]
  have hsingle (S : Finset ℕ) (z : ℕ → ℝ) (u : ℕ) :
      (∑ v ∈ S, z v • Pi.single v (1 : ℝ)) u = if u ∈ S then z u else 0 := by
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  have hwE : ∀ e ∈ H.edges, ∑ v ∈ H.edge e, w v ≤ 1 := by
    intro e he
    have heq : (∑ v ∈ H.edge e, (1 : ℝ) • Pi.single v (1 : ℝ)) = indicator (H.edge e) := by
      ext u
      exact hsingle (H.edge e) (fun _ => 1) u
    have hcover : H.Cover (indicator (H.edge e)) (Pi.single e 1) := by
      refine ⟨?_, ?_⟩
      · intro f hf
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      · intro v hv
        by_cases hve : v ∈ H.edge e
        · simp [indicator, hve, Pi.single_apply, he]
        · simp only [indicator, if_neg hve]
          apply sum_nonneg
          intro f hf
          simp only [Pi.single_apply]
          split_ifs <;> norm_num
    have hc : H.setCoverCost (H.edge e) ≤ 1 := by
      simpa [setCoverCost, Pi.single_apply, he] using H.coverCost_le hcover
    have hh := (hg (indicator (H.edge e))).trans hc
    rw [← heq, hsum] at hh
    simpa using hh
  have hrepr : g x = ∑ v ∈ H.vertices, x v * w v := by
    let z := ∑ v ∈ H.vertices, x v • Pi.single v (1 : ℝ)
    have hz : ∀ v ∈ H.vertices, (x - z) v = 0 := by
      intro v hv
      simp [Pi.sub_apply, z, hsingle, hv]
    have hpos := hg (x - z)
    have hneg := hg (-(x - z))
    rw [H.coverCost_eq_zero_of_nonpos (fun v hv => le_of_eq (hz v hv))] at hpos
    rw [H.coverCost_eq_zero_of_nonpos (by intro v hv; simp [hz v hv]), map_neg] at hneg
    have heq : g (x - z) = 0 := by linarith
    rw [map_sub] at heq
    exact (sub_eq_zero.mp heq).trans (hsum _ _)
  refine ⟨w, ⟨hw0, hwE⟩, ?_, fun w' hw' => H.modular_le_coverCost hw' x⟩
  rw [← hgx, hrepr]
  apply sum_congr rfl
  intro v hv
  exact mul_comm _ _

theorem submodular_le_setCoverCost (H : Hypergraph) {b : Finset ℕ → ℝ}
    (hb : H.SubmodularWeight b) {S : Finset ℕ} (hS : S ⊆ H.vertices) :
    b S ≤ H.setCoverCost S := by
  obtain ⟨w, hw, hout, hsum, hdom⟩ := submodular_support S b hb.1
    (fun A hA B hB hAB => hb.2.1 A (hA.trans hS) B (hB.trans hS) hAB)
    (fun A hA B hB => hb.2.2.1 A (hA.trans hS) B (hB.trans hS))
  have hweight : H.ModularWeight w := by
    refine ⟨hw, ?_⟩
    intro e he
    have hrestrict : modularValue w (H.edge e) = modularValue w (H.edge e ∩ S) := by
      symm
      apply sum_subset inter_subset_left
      intro v hv hnot
      exact hout v (fun hvS => hnot (mem_inter.mpr ⟨hv, hvS⟩))
    change modularValue w (H.edge e) ≤ 1
    rw [hrestrict]
    exact (hdom _ inter_subset_right).trans
      ((hb.2.1 _ (inter_subset_left.trans (H.edge_subset e he)) _
        (H.edge_subset e he) inter_subset_left).trans (hb.2.2.2 e he))
  calc
    b S = modularValue w S := hsum.symm
    _ = ∑ v ∈ H.vertices, w v * indicator S v := by
      simp only [modularValue, indicator, mul_ite, mul_one, mul_zero, ← sum_filter]
      congr 1
      ext v
      simp only [mem_filter]
      exact ⟨fun hv => ⟨hS hv, hv⟩, And.right⟩
    _ ≤ H.setCoverCost S := H.modular_le_coverCost hweight _

theorem optimal_submodular_le_fhw (H : Hypergraph) {b : Finset ℕ → ℝ}
    (hb : H.SubmodularWeight b) : H.optimalWidth b ≤ H.fhw := by
  refine le_csInf ⟨_, 0, H.oneBag, rfl⟩ ?_
  rintro r ⟨n, D, rfl⟩
  have hn : ∀ S ⊆ H.vertices, 0 ≤ b S := by
    intro S hS
    have h := hb.2.1 ∅ (empty_subset _) S hS (empty_subset _)
    simpa [hb.1] using h
  apply (H.optimalWidth_le_bagWidth b hn D).trans
  refine csSup_le ⟨_, 0, rfl⟩ ?_
  rintro r ⟨t, rfl⟩
  exact (H.submodular_le_setCoverCost hb (D.bag_subset t)).trans
    (le_csSup (Set.finite_range _).bddAbove ⟨t, rfl⟩)

theorem width_hierarchy (H : Hypergraph) : H.adw ≤ H.subw ∧ H.subw ≤ H.fhw := by
  have hz : H.ModularWeight (fun _ => 0) := ⟨by simp, by simp⟩
  have hbound : ∀ r ∈ {r | ∃ b, H.SubmodularWeight b ∧ r = H.optimalWidth b},
      r ≤ H.fhw := by
    rintro r ⟨b, hb, rfl⟩
    exact H.optimal_submodular_le_fhw hb
  constructor
  · refine csSup_le ⟨_, _, hz, rfl⟩ ?_
    rintro r ⟨w, hw, rfl⟩
    exact le_csSup ⟨H.fhw, hbound⟩ ⟨modularValue w, H.modularValue_submodular hw, rfl⟩
  · exact csSup_le ⟨_, _, H.modularValue_submodular hz, rfl⟩ hbound

theorem elementary_width_bounds (H : Hypergraph) :
    0 ≤ H.adw ∧ H.adw ≤ H.vertices.card ∧ 0 ≤ H.fhw := by
  have hbound : ∀ r ∈ {r | ∃ w, H.ModularWeight w ∧
      r = H.optimalWidth (modularValue w)}, r ≤ (H.vertices.card : ℝ) := by
    rintro r ⟨w, hw, rfl⟩
    calc
      H.optimalWidth (modularValue w) ≤ modularValue w H.vertices :=
        (H.optimalWidth_bounds _ (fun S _ => sum_nonneg (fun v _ => hw.1 v))).2
      _ ≤ (H.vertices.card : ℝ) := by
        simpa [modularValue] using
          (sum_le_sum (fun v hv => H.modularWeight_vertex_le_one hw hv))
  have hzero : H.ModularWeight (fun _ => 0) := ⟨by simp, by simp⟩
  refine ⟨?_, csSup_le ⟨_, _, hzero, rfl⟩ hbound, ?_⟩
  · exact (H.optimalWidth_bounds (modularValue (fun _ => 0))
      (fun S _ => by simp [modularValue])).1.trans
        (le_csSup ⟨_, hbound⟩ ⟨_, hzero, rfl⟩)
  · exact (H.optimalWidth_bounds _ (fun S _ => H.coverCost_nonneg (indicator S))).1

theorem adw_ge_one (H : Hypergraph) (hH : H.vertices.Nonempty) : 1 ≤ H.adw := by
  obtain ⟨v, hv⟩ := hH
  let w : ℕ → ℝ := fun u => if u = v then 1 else 0
  have hw : H.ModularWeight w := by
    constructor
    · intro u; dsimp [w]; split_ifs <;> norm_num
    · intro e he; simp [w]; split_ifs <;> norm_num
  have hlower : 1 ≤ H.optimalWidth (modularValue w) := by
    unfold optimalWidth
    refine le_csInf ⟨_, 0, H.oneBag, rfl⟩ ?_
    rintro r ⟨n, D, rfl⟩
    obtain ⟨t, ht⟩ := D.vertex_covered v hv
    have hmem : modularValue w (D.bag t) ∈
        Set.range (fun t => modularValue w (D.bag t)) := ⟨t, rfl⟩
    have hle := le_csSup (Set.finite_range _).bddAbove hmem
    simpa [TreeDecomposition.bagWidth, modularValue, w, ht] using hle
  apply hlower.trans
  unfold adw
  refine le_csSup ?_ ⟨w, hw, rfl⟩
  refine ⟨H.vertices.card, ?_⟩
  rintro r ⟨w', hw', rfl⟩
  calc
    H.optimalWidth (modularValue w') ≤ modularValue w' H.vertices :=
      (H.optimalWidth_bounds _ (fun S _ => sum_nonneg (fun u _ => hw'.1 u))).2
    _ ≤ (H.vertices.card : ℝ) := by
      simpa [modularValue] using
        (sum_le_sum (fun u hu => H.modularWeight_vertex_le_one hw' hu))

theorem componentFactor_ge_one (H : Hypergraph) : 1 ≤ H.componentFactor := by
  have hfin : {r : ℝ | ∃ C ∈ H.components,
      r = min ((H.induce C).degeneracy : ℝ)
        (Real.log (2 + ((H.induce C).independenceNumber : ℝ)))}.Finite := by
    apply Set.Finite.subset (H.components.finite_toSet.image
      (fun C => min ((H.induce C).degeneracy : ℝ)
        (Real.log (2 + ((H.induce C).independenceNumber : ℝ)))))
    rintro r ⟨C, hC, rfl⟩
    exact ⟨C, hC, rfl⟩
  have hzero := le_csSup (hfin.insert 0).bddAbove (Set.mem_insert 0 _)
  unfold componentFactor
  linarith

theorem structure_hereditary (H : Hypergraph) (W : Finset ℕ) :
    (H.induce W).degeneracy ≤ H.degeneracy ∧
    (H.induce W).independenceNumber ≤ H.independenceNumber := by
  constructor
  · have hnodes : (H.induce W).incidenceVertices ⊆ H.incidenceVertices := by
      intro z hz
      cases z <;> simp_all [incidenceVertices, induce]
    have hadj : ∀ a b, (H.induce W).incidence.Adj a b → H.incidence.Adj a b := by
      intro a b
      cases a <;> cases b <;> simp [incidence, induce] <;> tauto
    have hdeg : ∀ S ⊆ H.incidenceVertices, S.Nonempty →
        ∃ v ∈ S, (S.filter (H.incidence.Adj v)).card ≤ H.degeneracy := by
      refine csInf_mem (s := {d : ℕ | ∀ S ⊆ H.incidenceVertices, S.Nonempty →
        ∃ v ∈ S, (S.filter (H.incidence.Adj v)).card ≤ d}) ?_
      refine ⟨H.incidenceVertices.card, ?_⟩
      intro S hS hne
      obtain ⟨v, hv⟩ := hne
      exact ⟨v, hv, (card_filter_le _ _).trans (card_le_card hS)⟩
    refine csInf_le (OrderBot.bddBelow _) ?_
    intro S hS hne
    obtain ⟨v, hv, hd⟩ := hdeg S (hS.trans hnodes) hne
    refine ⟨v, hv, le_trans ?_ hd⟩
    apply card_le_card
    intro z hz
    exact mem_filter.mpr ⟨(mem_filter.mp hz).1, hadj v z (mem_filter.mp hz).2⟩
  · apply Finset.sup_le
    intro S hS
    obtain ⟨hSV, hind⟩ := mem_filter.mp hS
    have hsub : S ⊆ H.vertices ∩ W := mem_powerset.mp hSV
    refine Finset.le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_powerset.mpr
      (fun v hv => (mem_inter.mp (hsub hv)).1), ?_⟩)
    intro u hu v hv huv
    obtain ⟨hne, e, he, hue, hve⟩ := huv
    have huW := (mem_inter.mp (hsub hu)).2
    have hvW := (mem_inter.mp (hsub hv)).2
    apply hind u hu v hv
    exact ⟨hne, e, mem_filter.mpr ⟨he, ⟨u, mem_inter.mpr ⟨hue, huW⟩⟩⟩,
      mem_inter.mpr ⟨hue, huW⟩, mem_inter.mpr ⟨hve, hvW⟩⟩

theorem primal_induce_adj (H : Hypergraph) (W : Finset ℕ) {u v : ℕ}
    (hu : u ∈ W) (hv : v ∈ W) :
    (H.induce W).primal.Adj u v ↔ H.primal.Adj u v := by
  constructor
  · rintro ⟨huv, e, he, hue, hve⟩
    exact ⟨huv, e, (mem_filter.mp he).1, (mem_inter.mp hue).1, (mem_inter.mp hve).1⟩
  · rintro ⟨huv, e, he, hue, hve⟩
    exact ⟨huv, e, mem_filter.mpr ⟨he, ⟨u, mem_inter.mpr ⟨hue, hu⟩⟩⟩,
      mem_inter.mpr ⟨hue, hu⟩, mem_inter.mpr ⟨hve, hv⟩⟩

def TreeDecomposition.restrict {H : Hypergraph} {n : ℕ}
    (D : H.TreeDecomposition n) (W : Finset ℕ) : (H.induce W).TreeDecomposition n where
  tree := D.tree
  isTree := D.isTree
  bag := fun t => D.bag t ∩ W
  bag_subset := by
    intro t v hv
    exact mem_inter.mpr ⟨D.bag_subset t (mem_inter.mp hv).1, (mem_inter.mp hv).2⟩
  edge_covered := by
    intro e he
    obtain ⟨t, ht⟩ := D.edge_covered e (mem_filter.mp he).1
    exact ⟨t, fun v hv => mem_inter.mpr ⟨ht (mem_inter.mp hv).1, (mem_inter.mp hv).2⟩⟩
  vertex_covered := by
    intro v hv
    obtain ⟨t, ht⟩ := D.vertex_covered v (mem_inter.mp hv).1
    exact ⟨t, mem_inter.mpr ⟨ht, (mem_inter.mp hv).2⟩⟩
  running_intersection := by
    intro v hv
    have hvW := (mem_inter.mp hv).2
    have hs : {t : Fin (n + 1) | v ∈ D.bag t ∩ W} = {t | v ∈ D.bag t} := by
      ext t
      simp only [Set.mem_setOf_eq, mem_inter, hvW, and_true]
    rw [hs]
    exact D.running_intersection v (mem_inter.mp hv).1

theorem optimal_modular_le_adw (H : Hypergraph) {w : ℕ → ℝ} (hw : H.ModularWeight w) :
    H.optimalWidth (modularValue w) ≤ H.adw := by
  refine le_csSup ?_ ⟨w, hw, rfl⟩
  refine ⟨H.vertices.card, ?_⟩
  rintro r ⟨w', hw', rfl⟩
  calc
    H.optimalWidth (modularValue w') ≤ modularValue w' H.vertices :=
      (H.optimalWidth_bounds _ (fun S _ => sum_nonneg (fun u _ => hw'.1 u))).2
    _ ≤ (H.vertices.card : ℝ) := by
      simpa [modularValue] using
        (sum_le_sum (fun u hu => H.modularWeight_vertex_le_one hw' hu))

theorem width_hereditary (H : Hypergraph) (W : Finset ℕ) :
    (H.induce W).adw ≤ H.adw ∧ (H.induce W).fhw ≤ H.fhw := by
  constructor
  · have hz : (H.induce W).ModularWeight (fun _ => 0) := ⟨by simp, by simp⟩
    refine csSup_le ⟨_, _, hz, rfl⟩ ?_
    rintro r ⟨w, hw, rfl⟩
    let w' : ℕ → ℝ := fun v => if v ∈ W then w v else 0
    have hsum : ∀ S : Finset ℕ, (∑ v ∈ S, w' v) = ∑ v ∈ S ∩ W, w v := by
      intro S
      simp only [w', ← sum_filter]
      congr 1
    have hw' : H.ModularWeight w' := by
      constructor
      · intro v; dsimp [w']; split_ifs <;> first | exact hw.1 v | exact le_rfl
      · intro e he
        rw [hsum]
        by_cases hn : (H.edge e ∩ W).Nonempty
        · exact hw.2 e (mem_filter.mpr ⟨he, hn⟩)
        · rw [Finset.not_nonempty_iff_eq_empty.mp hn, sum_empty]
          norm_num
    apply le_trans ?_ (H.optimal_modular_le_adw hw')
    refine le_csInf ⟨_, 0, H.oneBag, rfl⟩ ?_
    rintro r ⟨n, D, rfl⟩
    calc
      (H.induce W).optimalWidth (modularValue w) ≤ (D.restrict W).bagWidth (modularValue w) :=
        (H.induce W).optimalWidth_le_bagWidth _
          (fun S _ => sum_nonneg (fun v _ => hw.1 v)) _
      _ = D.bagWidth (modularValue w') := by
        unfold TreeDecomposition.bagWidth
        apply congrArg sSup
        exact congrArg Set.range (funext fun t => (hsum (D.bag t)).symm)
  · refine le_csInf ⟨_, 0, H.oneBag, rfl⟩ ?_
    rintro r ⟨n, D, rfl⟩
    apply le_trans ((H.induce W).optimalWidth_le_bagWidth _
      (fun S _ => (H.induce W).coverCost_nonneg (indicator S)) (D.restrict W))
    refine csSup_le ⟨_, 0, rfl⟩ ?_
    rintro r ⟨t, rfl⟩
    have hcost : (H.induce W).setCoverCost (D.bag t ∩ W) ≤ H.setCoverCost (D.bag t) := by
      rw [H.cover_restriction inter_subset_right]
      apply H.coverCost_mono
      intro v hv
      dsimp [indicator]
      split_ifs <;> simp_all
    exact hcost.trans (le_csSup (Set.finite_range _).bddAbove ⟨t, rfl⟩)

theorem component_connected (H : Hypergraph) {C : Finset ℕ} (hC : C ∈ H.components) :
    (H.induce C).Connected := by
  obtain ⟨hCV, a, ha, hreach⟩ := mem_filter.mp hC
  have hsub : C ⊆ H.vertices := mem_powerset.mp hCV
  have lift_walk : ∀ {u v : ℕ}, H.primal.Walk u v → u ∈ C →
      (H.induce C).primal.Reachable u v := by
    intro u v p
    induction p with
    | nil => intro _; exact .rfl
    | @cons u v z huv p ih =>
      intro hu
      obtain ⟨hne, e, he, hue, hve⟩ := huv
      have hvV := H.edge_subset e he hve
      have huv' : H.primal.Adj u v := ⟨hne, e, he, hue, hve⟩
      have hvC : v ∈ C := (hreach v hvV).mpr
        (((hreach u (hsub hu)).mp hu).trans huv'.reachable)
      exact ((H.primal_induce_adj C hu hvC).mpr huv').reachable.trans (ih hvC)
  refine ⟨⟨a, mem_inter.mpr ⟨hsub ha, ha⟩⟩, ?_⟩
  intro u hu v hv
  have huC := (mem_inter.mp hu).2
  have hvC := (mem_inter.mp hv).2
  obtain ⟨p⟩ := ((hreach u (hsub huC)).mp huC).symm.trans
    ((hreach v (hsub hvC)).mp hvC)
  exact lift_walk p huC

theorem component_factor_le_componentFactor (H : Hypergraph) {C : Finset ℕ}
    (hC : C ∈ H.components) : (H.induce C).structuralFactor ≤ H.componentFactor := by
  have hfin : {r : ℝ | ∃ C ∈ H.components,
      r = min ((H.induce C).degeneracy : ℝ)
        (Real.log (2 + ((H.induce C).independenceNumber : ℝ)))}.Finite := by
    apply Set.Finite.subset (H.components.finite_toSet.image
      (fun C => min ((H.induce C).degeneracy : ℝ)
        (Real.log (2 + ((H.induce C).independenceNumber : ℝ)))))
    rintro r ⟨C, hC, rfl⟩
    exact ⟨C, hC, rfl⟩
  have hle := le_csSup (hfin.insert 0).bddAbove (Set.mem_insert_of_mem 0 ⟨C, hC, rfl⟩)
  unfold structuralFactor componentFactor
  linarith

/-- A walk starting in the hypergraph never visits the unused ambient vertices. -/
theorem walk_vertices (H : Hypergraph) {u v : ℕ} (p : H.primal.Walk u v)
    (hu : u ∈ H.vertices) : ∀ z ∈ p.support, z ∈ H.vertices := by
  induction p with
  | nil => simpa using hu
  | @cons u v t huv p ih =>
    intro z hz
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · obtain ⟨_, e, he, _, hve⟩ := huv
      exact ih (H.edge_subset e he hve) z hz

theorem walk_reachable_induce (H : Hypergraph) {u v : ℕ} (p : H.primal.Walk u v)
    {W : Finset ℕ} (hW : ∀ z ∈ p.support, z ∈ W) :
    (H.induce W).primal.Reachable u v := by
  induction p with
  | nil => exact .rfl
  | @cons u v t huv p ih =>
    have huW := hW u (List.mem_cons_self)
    have hvW := hW v (List.mem_cons_of_mem _ p.start_mem_support)
    exact ((H.primal_induce_adj W huW hvW).mpr huv).reachable.trans
      (ih (fun z hz => hW z (List.mem_cons_of_mem _ hz)))

theorem primal_induce_le (H : Hypergraph) (W : Finset ℕ) :
    (H.induce W).primal ≤ H.primal := by
  rintro u v ⟨hne, e, he, hue, hve⟩
  exact ⟨hne, e, (mem_filter.mp he).1, (mem_inter.mp hue).1, (mem_inter.mp hve).1⟩

theorem vertexDistance_indicator (H : Hypergraph) (S : Finset ℕ) {u v : ℕ}
    (hu : u ∈ H.vertices) (_hv : v ∈ H.vertices) :
    H.vertexDistance (indicator S) u v =
      if u ∉ S ∧ v ∉ S ∧ (H.induce (H.vertices \ S)).primal.Reachable u v
      then 0 else 1 := by
  have hnonneg : ∀ z, 0 ≤ indicator S z := by intro z; simp [indicator]; split_ifs <;> norm_num
  let costs : Set ℝ := insert 1 {r | ∃ p : H.primal.Walk u v, p.IsPath ∧
    r = ∑ z ∈ p.support.toFinset, indicator S z}
  have hne : costs.Nonempty := ⟨1, Set.mem_insert _ _⟩
  have hlo : ∀ r ∈ costs, 0 ≤ r := by
    rintro r (rfl | ⟨p, hp, rfl⟩)
    · norm_num
    · exact sum_nonneg (fun z _ => hnonneg z)
  have hbd : BddBelow costs := ⟨0, hlo⟩
  change sInf costs = _
  split_ifs with hh
  · obtain ⟨huS, hvS, hr⟩ := hh
    obtain ⟨p, hp⟩ := hr.exists_isPath
    have huJ : u ∈ (H.induce (H.vertices \ S)).vertices :=
      mem_inter.mpr ⟨hu, mem_sdiff.mpr ⟨hu, huS⟩⟩
    have hzsum : (∑ z ∈ (p.mapLe (H.primal_induce_le _)).support.toFinset,
        indicator S z) = 0 := by
      rw [SimpleGraph.Walk.support_mapLe_eq_support]
      apply sum_eq_zero
      intro z hz
      have hzJ := (H.induce (H.vertices \ S)).walk_vertices p huJ z (List.mem_toFinset.mp hz)
      exact if_neg (mem_sdiff.mp (mem_inter.mp hzJ).2).2
    apply le_antisymm
    · exact csInf_le hbd (Set.mem_insert_of_mem 1
        ⟨p.mapLe (H.primal_induce_le _), hp.mapLe _, hzsum.symm⟩)
    · exact le_csInf hne hlo
  · apply le_antisymm
    · exact csInf_le hbd (Set.mem_insert _ _)
    · refine le_csInf hne ?_
      rintro r (rfl | ⟨p, hp, rfl⟩)
      · exact le_rfl
      · by_contra hlt
        have hav : ∀ z ∈ p.support, z ∉ S := by
          intro z hz hzS
          have hsingle := single_le_sum (fun z _ => hnonneg z) (List.mem_toFinset.mpr hz)
          rw [indicator, if_pos hzS] at hsingle
          exact hlt hsingle
        apply hh
        refine ⟨hav u p.start_mem_support, hav v p.end_mem_support, ?_⟩
        exact H.walk_reachable_induce p (fun z hz =>
          mem_sdiff.mpr ⟨H.walk_vertices p hu z hz, hav z hz⟩)

theorem edgeDistance_indicator (H : Hypergraph) (S : Finset ℕ) {e f : ℕ}
    (he : e ∈ H.edges) (hf : f ∈ H.edges) :
    H.edgeDistance (indicator S) e f =
      if ∃ u ∈ H.edge e, ∃ v ∈ H.edge f,
        u ∉ S ∧ v ∉ S ∧ (H.induce (H.vertices \ S)).primal.Reachable u v
      then 0 else 1 := by
  obtain ⟨u₀, hu₀⟩ := H.edge_nonempty e he
  obtain ⟨v₀, hv₀⟩ := H.edge_nonempty f hf
  have hne : {r | ∃ u ∈ H.edge e, ∃ v ∈ H.edge f,
      r = H.vertexDistance (indicator S) u v}.Nonempty := ⟨_, u₀, hu₀, v₀, hv₀, rfl⟩
  have hlo : ∀ r ∈ {r | ∃ u ∈ H.edge e, ∃ v ∈ H.edge f,
      r = H.vertexDistance (indicator S) u v}, 0 ≤ r := by
    rintro r ⟨u, hu, v, hv, rfl⟩
    rw [H.vertexDistance_indicator S (H.edge_subset e he hu) (H.edge_subset f hf hv)]
    split_ifs <;> norm_num
  unfold edgeDistance
  split_ifs with hh
  · obtain ⟨u, hu, v, hv, huv⟩ := hh
    apply le_antisymm
    · refine csInf_le ⟨0, hlo⟩ ⟨u, hu, v, hv, ?_⟩
      rw [H.vertexDistance_indicator S (H.edge_subset e he hu) (H.edge_subset f hf hv), if_pos huv]
    · exact le_csInf hne hlo
  · have hone : ∀ u ∈ H.edge e, ∀ v ∈ H.edge f, H.vertexDistance (indicator S) u v = 1 := by
      intro u hu v hv
      rw [H.vertexDistance_indicator S (H.edge_subset e he hu) (H.edge_subset f hf hv)]
      exact if_neg (fun h => hh ⟨u, hu, v, hv, h⟩)
    apply le_antisymm
    · exact csInf_le ⟨0, hlo⟩ ⟨u₀, hu₀, v₀, hv₀, (hone u₀ hu₀ v₀ hv₀).symm⟩
    · refine le_csInf hne ?_
      rintro r ⟨u, hu, v, hv, rfl⟩
      rw [hone u hu v hv]

/-- Disjoint union of a family of graphs, retaining the component index. -/
def forestGraph {I : Type*} {V : I → Type*} (G : ∀ i, SimpleGraph (V i)) :
    SimpleGraph (Sigma V) where
  Adj a b := ∃ h : a.1 = b.1, (G a.1).Adj a.2 (h.symm ▸ b.2)
  symm := ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨h, hab⟩
    cases h
    exact ⟨rfl, hab.symm⟩⟩
  loopless := ⟨by
    rintro ⟨i, a⟩ ⟨h, ha⟩
    exact (G i).loopless.irrefl a ha⟩

def forestFiberIso {I : Type*} {V : I → Type*} (G : ∀ i, SimpleGraph (V i)) (i : I) :
    ((forestGraph G).induce {a | a.1 = i}) ≃g G i where
  toFun a := a.property ▸ a.val.2
  invFun a := ⟨⟨i, a⟩, rfl⟩
  left_inv := by rintro ⟨⟨j, a⟩, h⟩; cases h; rfl
  right_inv := by intro a; rfl
  map_rel_iff' := by
    rintro ⟨⟨j, a⟩, ha⟩ ⟨⟨k, b⟩, hb⟩
    cases ha
    cases hb
    change (G j).Adj a b ↔ ∃ h : j = j, (G j).Adj a (h.symm ▸ b)
    simp

theorem forest_acyclic {I : Type*} {V : I → Type*} (G : ∀ i, SimpleGraph (V i))
    (hG : ∀ i, (G i).IsAcyclic) : (forestGraph G).IsAcyclic := by
  have hsupp : ∀ {a b : Sigma V} (p : (forestGraph G).Walk a b),
      ∀ z ∈ p.support, z.1 = a.1 := by
    intro a b p
    induction p with
    | nil => simp
    | @cons a b c hab p ih =>
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · rfl
      · exact (ih z hz).trans hab.choose.symm
  intro a p hp
  let q := p.induce {z : Sigma V | z.1 = a.1} (hsupp p)
  have hq : q.IsCycle := by
    apply (SimpleGraph.Walk.map_isCycle_iff_of_injective
      (f := (SimpleGraph.Embedding.induce {z : Sigma V | z.1 = a.1}).toHom)
      (by intro a b h; exact Subtype.ext h)).mp
    have heq : q.map (SimpleGraph.Embedding.induce {z : Sigma V | z.1 = a.1}).toHom = p :=
      SimpleGraph.Walk.map_induce p _
    rw [heq]
    exact hp
  exact hG a.1 _ (hq.map (f := (forestFiberIso G a.1).toHom)
    (forestFiberIso G a.1).injective)

theorem component_mem_iff_reachable (H : Hypergraph) {K : Finset ℕ}
    (hK : K ∈ H.components) {u v : ℕ} (hu : u ∈ K) (hv : v ∈ H.vertices) :
    v ∈ K ↔ H.primal.Reachable u v := by
  obtain ⟨hKV, a, ha, hr⟩ := mem_filter.mp hK
  have hsub : K ⊆ H.vertices := mem_powerset.mp hKV
  have hau := (hr u (hsub hu)).mp hu
  constructor
  · intro hvK
    exact hau.symm.trans ((hr v hv).mp hvK)
  · intro huv
    exact (hr v hv).mpr (hau.trans huv)

theorem exists_component_of_mem (H : Hypergraph) {u : ℕ} (hu : u ∈ H.vertices) :
    ∃ K ∈ H.components, u ∈ K := by
  let K := H.vertices.filter (fun v => H.primal.Reachable u v)
  have huK : u ∈ K := mem_filter.mpr ⟨hu, .rfl⟩
  refine ⟨K, mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _), u, huK, ?_⟩, huK⟩
  intro v hv
  simp only [K, mem_filter, hv, true_and]

/-- Every surviving vertex of an edge lies in the same residual component. -/
theorem edgeDistance_indicator_component (H : Hypergraph) (S : Finset ℕ)
    {e f u : ℕ} (he : e ∈ H.edges) (hf : f ∈ H.edges) (hue : u ∈ H.edge e)
    {K : Finset ℕ} (hK : K ∈ (H.induce (H.vertices \ S)).components) (huK : u ∈ K) :
    H.edgeDistance (indicator S) e f = if ¬ Disjoint (H.edge f) K then 0 else 1 := by
  have hsub : K ⊆ (H.induce (H.vertices \ S)).vertices :=
    mem_powerset.mp (mem_filter.mp hK).1
  have huW := (mem_inter.mp (hsub huK)).2
  have hiff : (∃ a ∈ H.edge e, ∃ b ∈ H.edge f,
      a ∉ S ∧ b ∉ S ∧ (H.induce (H.vertices \ S)).primal.Reachable a b) ↔
      ¬ Disjoint (H.edge f) K := by
    constructor
    · rintro ⟨a, hae, b, hbf, haS, hbS, hab⟩
      have haW : a ∈ H.vertices \ S := mem_sdiff.mpr ⟨H.edge_subset e he hae, haS⟩
      have hua : (H.induce (H.vertices \ S)).primal.Reachable u a := by
        by_cases h : u = a
        · subst a; exact .rfl
        · exact ((H.primal_induce_adj _ huW haW).mpr ⟨h, e, he, hue, hae⟩).reachable
      have hbV := H.edge_subset f hf hbf
      have hbJ : b ∈ (H.induce (H.vertices \ S)).vertices :=
        mem_inter.mpr ⟨hbV, mem_sdiff.mpr ⟨hbV, hbS⟩⟩
      have hbK := ((H.induce (H.vertices \ S)).component_mem_iff_reachable hK huK hbJ).mpr
        (hua.trans hab)
      exact not_disjoint_iff.mpr ⟨b, hbf, hbK⟩
    · intro hmeet
      obtain ⟨b, hbf, hbK⟩ := not_disjoint_iff.mp hmeet
      have hbJ := hsub hbK
      exact ⟨u, hue, b, hbf, (mem_sdiff.mp huW).2,
        (mem_sdiff.mp (mem_inter.mp hbJ).2).2,
        ((H.induce (H.vertices \ S)).component_mem_iff_reachable hK huK hbJ).mp hbK⟩
  rw [H.edgeDistance_indicator S he hf]
  simp only [hiff]

theorem indicator_balance_sum (H : Hypergraph) (γ : ℕ → ℝ) (S : Finset ℕ)
    {e u : ℕ} (he : e ∈ H.edges) (hue : u ∈ H.edge e)
    {K : Finset ℕ} (hK : K ∈ (H.induce (H.vertices \ S)).components) (huK : u ∈ K) :
    (∑ f ∈ H.edges, γ f * H.edgeDistance (indicator S) e f) =
      (∑ f ∈ H.edges, γ f) -
        ∑ f ∈ H.edges.filter (fun f => ¬ Disjoint (H.edge f) K), γ f := by
  calc
    _ = ∑ f ∈ H.edges, γ f * (if ¬ Disjoint (H.edge f) K then 0 else 1) := by
      apply sum_congr rfl
      intro f hf
      rw [H.edgeDistance_indicator_component S he hf hue hK huK]
    _ = _ := by
      rw [sum_filter, ← sum_sub_distrib]
      apply sum_congr rfl
      intro f hf
      split_ifs <;> ring

theorem indicator_equivalence (H : Hypergraph) {γ : ℕ → ℝ}
    (hγ : H.EdgeWeight γ) {θ : ℝ} (hθ : 0 < θ ∧ θ < 1)
    {S : Finset ℕ} (hS : S ⊆ H.vertices) :
    H.FractionalBalanced γ θ (indicator S) ↔ H.IntegralBalanced γ θ S := by
  constructor
  · intro hfrac
    refine ⟨hS, ?_⟩
    intro K hK
    obtain ⟨u, huK, _⟩ := (mem_filter.mp hK).2
    have hKV := mem_powerset.mp (mem_filter.mp hK).1
    have huV := (mem_inter.mp (hKV huK)).1
    obtain ⟨e, he, hue⟩ := H.no_isolated u huV
    have hbal := hfrac.2 e he
    rw [H.indicator_balance_sum γ S he hue hK huK] at hbal
    linarith
  · intro hint
    refine ⟨?_, ?_⟩
    · intro v hv
      dsimp [indicator]
      split_ifs <;> norm_num
    · intro e he
      by_cases hES : H.edge e ⊆ S
      · have hsum : (∑ f ∈ H.edges, γ f * H.edgeDistance (indicator S) e f) =
            ∑ f ∈ H.edges, γ f := by
          apply sum_congr rfl
          intro f hf
          rw [H.edgeDistance_indicator S he hf]
          have hnot : ¬ ∃ u ∈ H.edge e, ∃ v ∈ H.edge f,
              u ∉ S ∧ v ∉ S ∧ (H.induce (H.vertices \ S)).primal.Reachable u v := by
            rintro ⟨u, hue, v, hvf, huS, _⟩
            exact huS (hES hue)
          rw [if_neg hnot, mul_one]
        rw [hsum]
        have hprod := mul_nonneg hθ.1.le hγ.2.le
        nlinarith
      · obtain ⟨u, hue, huS⟩ := Finset.not_subset.mp hES
        have huV := H.edge_subset e he hue
        have huJ : u ∈ (H.induce (H.vertices \ S)).vertices :=
          mem_inter.mpr ⟨huV, mem_sdiff.mpr ⟨huV, huS⟩⟩
        obtain ⟨K, hK, huK⟩ := (H.induce (H.vertices \ S)).exists_component_of_mem huJ
        rw [H.indicator_balance_sum γ S he hue hK huK]
        have hbal := hint.2 K hK
        linarith

theorem full_fractional_separator (H : Hypergraph) {γ : ℕ → ℝ}
    (hγ : H.EdgeWeight γ) {θ : ℝ} (hθ : 0 < θ ∧ θ < 1) :
    H.FractionalBalanced γ θ (indicator H.vertices) ∧
      H.coverCost (indicator H.vertices) ≤ H.edges.card := by
  constructor
  · apply (H.indicator_equivalence hγ hθ (Subset.refl _)).mpr
    refine ⟨Subset.refl _, ?_⟩
    intro K hK
    simp [components, induce] at hK
    rcases hK with ⟨rfl, v, hv⟩
    simp at hv
  · have hcover : H.Cover (indicator H.vertices) (fun _ => 1) := by
      refine ⟨by simp, ?_⟩
      intro v hv
      obtain ⟨e, he, hve⟩ := H.no_isolated v hv
      simp only [indicator, if_pos hv]
      exact single_le_sum (f := fun _ : ℕ => (1 : ℝ))
        (s := H.edges.filter (fun e => v ∈ H.edge e)) (fun _ _ => zero_le_one)
        (mem_filter.mpr ⟨he, hve⟩)
    simpa using H.coverCost_le hcover

theorem beta_bounds (H : Hypergraph) {γ : ℕ → ℝ} (hγ : H.EdgeWeight γ)
    {θ : ℝ} (hθ : 0 < θ ∧ θ < 1) : 0 ≤ H.beta θ γ ∧ H.beta θ γ ≤ H.edges.card := by
  have hlo : ∀ r ∈ {r | ∃ x, H.FractionalBalanced γ θ x ∧ r = H.coverCost x}, 0 ≤ r := by
    rintro r ⟨x, hx, rfl⟩
    exact H.coverCost_nonneg x
  have hfull := H.full_fractional_separator hγ hθ
  refine ⟨Real.sInf_nonneg hlo, ?_⟩
  exact (csInf_le ⟨0, hlo⟩ ⟨indicator H.vertices, hfull.1, rfl⟩).trans hfull.2

theorem beta_le_fsep (H : Hypergraph) {W : Finset ℕ} (hW : W ⊆ H.vertices)
    {γ : ℕ → ℝ} (hγ : (H.induce W).EdgeWeight γ) {θ : ℝ} (hθ : 0 < θ ∧ θ < 1) :
    (H.induce W).beta θ γ ≤ H.fsep θ := by
  refine le_csSup ?_ (Set.mem_insert_of_mem 0 ⟨W, hW, γ, hγ, rfl⟩)
  refine ⟨H.edges.card, ?_⟩
  rintro r (rfl | ⟨U, hU, δ, hδ, rfl⟩)
  · positivity
  · exact ((H.induce U).beta_bounds hδ hθ).2.trans (by
      exact_mod_cast (card_filter_le H.edges (fun e => (H.edge e ∩ U).Nonempty)))

/-- A weighted distance minimizer in a finite tree has no heavy branch. -/
theorem tree_weighted_median {V I : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.IsTree) (E : Finset I) (a : I → V) (w : I → ℝ)
    (_hw : ∀ e ∈ E, 0 ≤ w e) :
    ∃ t, ∀ s, G.Adj t s →
      (∑ e ∈ E.filter (fun e => G.dist t (a e) = G.dist s (a e) + 1), w e) ≤
        (1 / 2 : ℝ) * ∑ e ∈ E, w e := by
  classical
  let F : V → ℝ := fun t => ∑ e ∈ E, w e * (G.dist t (a e) : ℝ)
  obtain ⟨t, _, ht⟩ := Finset.exists_min_image univ F univ_nonempty
  refine ⟨t, ?_⟩
  intro s hts
  have hstep (e : I) :
      w e * (G.dist s (a e) : ℝ) = w e * (G.dist t (a e) : ℝ) + w e -
        2 * (if G.dist t (a e) = G.dist s (a e) + 1 then w e else 0) := by
    have hd := hG.dist_eq_dist_add_one_of_adj (a e) hts
    rw [SimpleGraph.dist_comm (u := a e) (v := t),
      SimpleGraph.dist_comm (u := a e) (v := s)] at hd
    split_ifs with h
    · have hc : (G.dist t (a e) : ℝ) = (G.dist s (a e) : ℝ) + 1 := by exact_mod_cast h
      rw [hc]
      ring
    · have hc : (G.dist s (a e) : ℝ) = (G.dist t (a e) : ℝ) + 1 := by
        exact_mod_cast hd.resolve_left h
      rw [hc]
      ring
  have heq : F s = F t + (∑ e ∈ E, w e) -
      2 * ∑ e ∈ E.filter (fun e => G.dist t (a e) = G.dist s (a e) + 1), w e := by
    dsimp [F]
    simp_rw [hstep]
    rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_filter]
  have hm := ht s (mem_univ s)
  linarith

/-- In a tree every simple path has shortest length. -/
theorem tree_path_length {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q, hq, hd⟩ := (hG.connected u v).exists_path_of_dist
  have heq := congrArg Subtype.val (hG.isAcyclic.path_unique ⟨p, hp⟩ ⟨q, hq⟩)
  change p = q at heq
  rw [heq]
  exact hd

/-- Every node reachable from a neighbor while avoiding the root is one step closer
from that neighbor than from the root. -/
theorem tree_branch_distance {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {t r u : V} (htr : G.Adj t r) (hu : u ≠ t)
    (hr : (G.induce {v | v ≠ t}).Reachable ⟨r, htr.ne.symm⟩ ⟨u, hu⟩) :
    G.dist t u = G.dist r u + 1 := by
  classical
  obtain ⟨p, hp, _⟩ := hr.exists_path_of_dist
  let q : G.Walk r u := p.map (SimpleGraph.Embedding.induce {v | v ≠ t}).toHom
  have hq : q.IsPath := SimpleGraph.Walk.map_isPath_of_injective (by intro a b h; exact Subtype.ext h) hp
  have ht : t ∉ q.support := by
    have hs : q.support = p.support.map (fun v => v.val) := SimpleGraph.Walk.support_map _ _
    rw [hs]
    simp only [List.mem_map]
    rintro ⟨v, _, hv⟩
    exact v.property hv
  have hc : (SimpleGraph.Walk.cons htr q).IsPath := by
    exact (SimpleGraph.Walk.cons_isPath_iff htr q).mpr ⟨hq, ht⟩
  rw [← tree_path_length hG hc, ← tree_path_length hG hq]
  simp

theorem TreeDecomposition.same_vertex_avoiding {H : Hypergraph} {n : ℕ}
    (D : H.TreeDecomposition n) (t : Fin (n + 1)) {v : ℕ} (hv : v ∈ H.vertices)
    (hvt : v ∉ D.bag t) {a b : Fin (n + 1)} (ha : v ∈ D.bag a) (hb : v ∈ D.bag b) :
    (D.tree.induce {s | s ≠ t}).Reachable
      ⟨a, fun h => hvt (h ▸ ha)⟩ ⟨b, fun h => hvt (h ▸ hb)⟩ := by
  have hsub : {s | v ∈ D.bag s} ⊆ {s | s ≠ t} := by
    intro s hs hst
    exact hvt (hst ▸ hs)
  exact ((D.running_intersection v hv) ⟨a, ha⟩ ⟨b, hb⟩).map
    (D.tree.induceHomOfLE hsub).toHom

/-- Bags meeting one residual primal component remain connected after deleting the root bag. -/
theorem TreeDecomposition.walk_avoiding {H : Hypergraph} {n : ℕ}
    (D : H.TreeDecomposition n) (t : Fin (n + 1)) {v w : ℕ}
    (p : (H.induce (H.vertices \ D.bag t)).primal.Walk v w)
    (hv : v ∈ (H.induce (H.vertices \ D.bag t)).vertices)
    {a b : Fin (n + 1)} (ha : v ∈ D.bag a) (hb : w ∈ D.bag b)
    (hat : a ≠ t) (hbt : b ≠ t) :
    (D.tree.induce {s | s ≠ t}).Reachable ⟨a, hat⟩ ⟨b, hbt⟩ := by
  induction p generalizing a with
  | nil =>
    exact D.same_vertex_avoiding t (mem_inter.mp hv).1
      (mem_sdiff.mp (mem_inter.mp hv).2).2 ha hb
  | @cons v z w hvz p ih =>
    obtain ⟨e, he, hve, hze⟩ := hvz.2
    obtain ⟨c, hc⟩ := D.edge_covered e (mem_filter.mp he).1
    have hzc : z ∈ D.bag c := hc (mem_inter.mp hze).1
    have hvct : c ≠ t := fun h => (mem_sdiff.mp (mem_inter.mp hv).2).2
      (h ▸ hc (mem_inter.mp hve).1)
    have hz : z ∈ (H.induce (H.vertices \ D.bag t)).vertices :=
      (H.induce (H.vertices \ D.bag t)).edge_subset e he hze
    exact (D.same_vertex_avoiding t (mem_inter.mp hv).1
      (mem_sdiff.mp (mem_inter.mp hv).2).2 ha (hc (mem_inter.mp hve).1)).trans
      (ih hz hzc hb hvct)

theorem balanced_bag (H : Hypergraph) {γ : ℕ → ℝ}
    (hγ : H.EdgeWeight γ) {n : ℕ} (D : H.TreeDecomposition n) :
    ∃ t, H.IntegralBalanced γ (1 / 2) (D.bag t) := by
  classical
  let assign : ℕ → Fin (n + 1) := fun e =>
    if he : e ∈ H.edges then (D.edge_covered e he).choose else 0
  have ha (e : ℕ) (he : e ∈ H.edges) : H.edge e ⊆ D.bag (assign e) := by
    simpa [assign, he] using (D.edge_covered e he).choose_spec
  obtain ⟨t, ht⟩ := tree_weighted_median D.tree D.isTree H.edges assign γ
    (fun e he => (hγ.1 e he).1)
  refine ⟨t, D.bag_subset t, ?_⟩
  intro K hK
  let J := H.induce (H.vertices \ D.bag t)
  have hKJ : K ⊆ J.vertices := mem_powerset.mp (mem_filter.mp hK).1
  obtain ⟨v, hvK, _⟩ := (mem_filter.mp hK).2
  have hv := hKJ hvK
  have hvt : v ∉ D.bag t := (mem_sdiff.mp (mem_inter.mp hv).2).2
  obtain ⟨u, hvu⟩ := D.vertex_covered v (mem_inter.mp hv).1
  have hut : u ≠ t := fun h => hvt (h ▸ hvu)
  obtain ⟨p, hp, _⟩ := (D.isTree.connected t u).exists_path_of_dist
  cases p with
  | nil => exact (hut rfl).elim
  | @cons _ r _ htr p =>
    have hp' := (SimpleGraph.Walk.cons_isPath_iff htr p).mp hp
    have hsupp : ∀ s ∈ p.support, s ∈ {s | s ≠ t} := by
      intro s hs hst
      exact hp'.2 (hst ▸ hs)
    have hru : (D.tree.induce {s | s ≠ t}).Reachable ⟨r, htr.ne.symm⟩ ⟨u, hut⟩ :=
      ⟨p.induce _ hsupp⟩
    have hdrop : H.edges.filter (fun e => ¬ Disjoint (H.edge e) K) ⊆
        H.edges.filter (fun e => D.tree.dist t (assign e) = D.tree.dist r (assign e) + 1) := by
      intro e he
      obtain ⟨heE, heK⟩ := mem_filter.mp he
      obtain ⟨w, hwe, hwK⟩ := not_disjoint_iff.mp heK
      have hw := hKJ hwK
      have hwa : w ∈ D.bag (assign e) := ha e heE hwe
      have hwat : assign e ≠ t := fun h =>
        (mem_sdiff.mp (mem_inter.mp hw).2).2 (h ▸ hwa)
      have hrw : J.primal.Reachable v w :=
        (J.component_mem_iff_reachable hK hvK hw).mp hwK
      have hutow := D.walk_avoiding t hrw.some hv hvu hwa hut hwat
      exact mem_filter.mpr ⟨heE, tree_branch_distance D.isTree htr hwat (hru.trans hutow)⟩
    exact (sum_le_sum_of_subset_of_nonneg hdrop
      (fun e he _ => (hγ.1 e (mem_filter.mp he).1).1)).trans (ht r htr)


/-- Reindex a finite tree while retaining its designated root bag. -/
theorem finite_rooted_tree_decomposition (H : Hypergraph) {T : Type*} [Fintype T] [Nonempty T]
    (G : SimpleGraph T) (hG : G.IsTree) (bag : T → Finset ℕ)
    (hsub : ∀ t, bag t ⊆ H.vertices)
    (hedge : ∀ e ∈ H.edges, ∃ t, H.edge e ⊆ bag t)
    (hvertex : ∀ v ∈ H.vertices, ∃ t, v ∈ bag t)
    (hrun : ∀ v ∈ H.vertices, (G.induce {t | v ∈ bag t}).Preconnected)
    (root : T) (Z : Finset ℕ) (hroot : Z ⊆ bag root)
    (b : Finset ℕ → ℝ) (r : ℝ) (hwidth : ∀ t, b (bag t) ≤ r) :
    ∃ n, ∃ D : H.TreeDecomposition n, ∃ root, Z ⊆ D.bag root ∧
      ∀ t, b (D.bag t) ≤ r := by
  classical
  let n := Fintype.card T - 1
  have hcard : Fintype.card T = n + 1 := by
    dsimp [n]
    have := Fintype.card_pos (α := T)
    omega
  let e : Fin (n + 1) ≃ T := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨n, {
    tree := G.comap e
    isTree := (SimpleGraph.Iso.comap e G).isTree_iff.mpr hG
    bag := fun t => bag (e t)
    bag_subset := fun t => hsub (e t)
    edge_covered := ?_
    vertex_covered := ?_
    running_intersection := ?_ }, e.symm root, by simpa using hroot, fun t => hwidth (e t)⟩
  · intro f hf
    obtain ⟨t, ht⟩ := hedge f hf
    exact ⟨e.symm t, by simpa using ht⟩
  · intro v hv
    obtain ⟨t, ht⟩ := hvertex v hv
    exact ⟨e.symm t, by simpa using ht⟩
  · intro v hv a c
    let f : G.induce {t | v ∈ bag t} →g
        (G.comap e).induce {t | v ∈ bag (e t)} := {
      toFun := fun t => ⟨e.symm t, by
        change v ∈ bag (e (e.symm t.val))
        rw [e.apply_symm_apply]
        exact t.property⟩
      map_rel' := by
        intro a b hab
        change G.Adj (e (e.symm a.val)) (e (e.symm b.val))
        rw [e.apply_symm_apply, e.apply_symm_apply]
        exact hab }
    have hh := (hrun v hv ⟨e a, a.property⟩ ⟨e c, c.property⟩).map f
    have ha : f ⟨e a, a.property⟩ = a := Subtype.ext (e.symm_apply_apply a)
    have hc : f ⟨e c, c.property⟩ = c := Subtype.ext (e.symm_apply_apply c)
    rw [ha, hc] at hh
    exact hh

/-- Reindex a decomposition on any finite nonempty tree to the representation used here. -/
theorem finite_tree_decomposition (H : Hypergraph) {T : Type*} [Fintype T] [Nonempty T]
    (G : SimpleGraph T) (hG : G.IsTree) (bag : T → Finset ℕ)
    (hsub : ∀ t, bag t ⊆ H.vertices)
    (hedge : ∀ e ∈ H.edges, ∃ t, H.edge e ⊆ bag t)
    (hvertex : ∀ v ∈ H.vertices, ∃ t, v ∈ bag t)
    (hrun : ∀ v ∈ H.vertices, (G.induce {t | v ∈ bag t}).Preconnected)
    (b : Finset ℕ → ℝ) (r : ℝ) (hwidth : ∀ t, b (bag t) ≤ r) :
    ∃ n, ∃ D : H.TreeDecomposition n, ∀ t, b (D.bag t) ≤ r := by
  obtain ⟨n, D, _, _, hD⟩ := H.finite_rooted_tree_decomposition G hG bag
    hsub hedge hvertex hrun (Classical.choice inferInstance) ∅ (empty_subset _) b r hwidth
  exact ⟨n, D, hD⟩

/-- Components that share a vertex are equal. -/
theorem component_eq_of_mem (H : Hypergraph) {C K : Finset ℕ}
    (hC : C ∈ H.components) (hK : K ∈ H.components) {v : ℕ}
    (hvC : v ∈ C) (hvK : v ∈ K) : C = K := by
  have hCV := mem_powerset.mp (mem_filter.mp hC).1
  have hKV := mem_powerset.mp (mem_filter.mp hK).1
  ext w
  by_cases hw : w ∈ H.vertices
  · rw [H.component_mem_iff_reachable hC hvC hw, H.component_mem_iff_reachable hK hvK hw]
  · exact iff_of_false (fun h => hw (hCV h)) (fun h => hw (hKV h))

theorem edge_subset_component (H : Hypergraph) {C : Finset ℕ} (hC : C ∈ H.components)
    {e v : ℕ} (he : e ∈ H.edges) (hve : v ∈ H.edge e) (hvC : v ∈ C) : H.edge e ⊆ C := by
  intro w hw
  apply (H.component_mem_iff_reachable hC hvC (H.edge_subset e he hw)).mpr
  by_cases hvw : v = w
  · subst w; exact SimpleGraph.Reachable.refl _
  · exact (show H.primal.Adj v w from ⟨hvw, e, he, hve, hw⟩).reachable

/-- Glue component decompositions without increasing any bag cost. -/
theorem glue_component_decompositions (H : Hypergraph) (b : Finset ℕ → ℝ) (r : ℝ)
    (hzero : b ∅ ≤ r)
    (hcomp : ∀ C ∈ H.components, ∃ n, ∃ D : (H.induce C).TreeDecomposition n,
      ∀ t, b (D.bag t) ≤ r) :
    ∃ n, ∃ D : H.TreeDecomposition n, ∀ t, b (D.bag t) ≤ r := by
  classical
  by_cases hV : H.vertices.Nonempty
  swap
  · have he : H.vertices = ∅ := not_nonempty_iff_eq_empty.mp hV
    exact ⟨0, H.oneBag, fun t => by simpa [oneBag, he] using hzero⟩
  let I := {C // C ∈ H.components}
  obtain ⟨v, hv⟩ := hV
  obtain ⟨C, hC, _⟩ := H.exists_component_of_mem hv
  letI : Nonempty I := ⟨⟨C, hC⟩⟩
  choose n D hD using (fun i : I => hcomp i i.property)
  let T := Σ i : I, Fin (n i + 1)
  letI : Nonempty T := ⟨⟨⟨C, hC⟩, 0⟩⟩
  let G : SimpleGraph T := forestGraph (fun i => (D i).tree)
  obtain ⟨F, hGF, _, hF⟩ := (SimpleGraph.connected_top (V := T)).exists_isTree_le_of_le_of_isAcyclic
    (H := G) le_top (forest_acyclic _ (fun i => (D i).isTree.isAcyclic))
  let bag : T → Finset ℕ := fun t => (D t.1).bag t.2
  have hsub (t : T) : bag t ⊆ H.vertices :=
    fun v hv => (mem_inter.mp ((D t.1).bag_subset t.2 hv)).1
  apply H.finite_tree_decomposition F hF bag hsub _ _ _ b r (fun t => hD t.1 t.2)
  · intro e he
    obtain ⟨v, hve⟩ := H.edge_nonempty e he
    obtain ⟨C, hC, hvC⟩ := H.exists_component_of_mem (H.edge_subset e he hve)
    let i : I := ⟨C, hC⟩
    have heC : H.edge e ⊆ C := H.edge_subset_component hC he hve hvC
    have heJ : e ∈ (H.induce C).edges := mem_filter.mpr ⟨he, ⟨v, mem_inter.mpr ⟨hve, hvC⟩⟩⟩
    obtain ⟨t, ht⟩ := (D i).edge_covered e heJ
    refine ⟨⟨i, t⟩, ?_⟩
    intro v hv
    exact ht (mem_inter.mpr ⟨hv, heC hv⟩)
  · intro v hv
    obtain ⟨C, hC, hvC⟩ := H.exists_component_of_mem hv
    let i : I := ⟨C, hC⟩
    obtain ⟨t, ht⟩ := (D i).vertex_covered v (mem_inter.mpr ⟨hv, hvC⟩)
    exact ⟨⟨i, t⟩, ht⟩
  · intro v hv a c
    rcases a with ⟨⟨i, a⟩, ha⟩
    rcases c with ⟨⟨j, c⟩, hc⟩
    have hvi : v ∈ i.val := (mem_inter.mp ((D i).bag_subset a ha)).2
    have hvj : v ∈ j.val := (mem_inter.mp ((D j).bag_subset c hc)).2
    have hij : i = j := Subtype.ext (H.component_eq_of_mem i.property j.property hvi hvj)
    subst j
    let f : (D i).tree.induce {t | v ∈ (D i).bag t} →g F.induce {t | v ∈ bag t} := {
      toFun := fun t => ⟨⟨i, t.val⟩, t.property⟩
      map_rel' := by intro a b hab; exact hGF ⟨rfl, hab⟩ }
    exact ((D i).running_intersection v (mem_inter.mpr ⟨hv, hvi⟩) ⟨a, ha⟩ ⟨c, hc⟩).map f

theorem optimalWidth_mono_cost (H : Hypergraph) (b c : Finset ℕ → ℝ)
    (hb : ∀ S ⊆ H.vertices, 0 ≤ b S)
    (hbc : ∀ S ⊆ H.vertices, b S ≤ c S) : H.optimalWidth b ≤ H.optimalWidth c := by
  refine le_csInf ⟨_, 0, H.oneBag, rfl⟩ ?_
  rintro r ⟨n, D, rfl⟩
  apply (H.optimalWidth_le_bagWidth b hb D).trans
  refine csSup_le ⟨_, 0, rfl⟩ ?_
  rintro r ⟨t, rfl⟩
  exact (hbc _ (D.bag_subset t)).trans (le_csSup (Set.finite_range _).bddAbove ⟨t, rfl⟩)

/-- Passing to infima after gluing needs no attainment of optimal decompositions. -/
theorem optimalWidth_le_components (H : Hypergraph) (b : Finset ℕ → ℝ) (r : ℝ)
    (hb : ∀ S ⊆ H.vertices, 0 ≤ b S) (hzero : b ∅ ≤ r)
    (hcomp : ∀ C ∈ H.components, (H.induce C).optimalWidth b ≤ r) :
    H.optimalWidth b ≤ r := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro s hrs
  have hlocal : ∀ C ∈ H.components, ∃ n, ∃ D : (H.induce C).TreeDecomposition n,
      ∀ t, b (D.bag t) ≤ s := by
    intro C hC
    have hlo : (H.induce C).optimalWidth b < s := (hcomp C hC).trans_lt hrs
    obtain ⟨r', ⟨n, D, rfl⟩, hD⟩ := exists_lt_of_csInf_lt
      (show {r | ∃ n, ∃ D : (H.induce C).TreeDecomposition n, r = D.bagWidth b}.Nonempty
        from ⟨_, 0, (H.induce C).oneBag, rfl⟩) hlo
    refine ⟨n, D, fun t => ?_⟩
    exact (le_csSup (Set.finite_range _).bddAbove ⟨t, rfl⟩).trans hD.le
  obtain ⟨n, D, hD⟩ := H.glue_component_decompositions b s (hzero.trans hrs.le) hlocal
  apply (H.optimalWidth_le_bagWidth b hb D).trans
  refine csSup_le ⟨_, 0, rfl⟩ ?_
  rintro r ⟨t, rfl⟩
  exact hD t

theorem component_reduction (H : Hypergraph) :
    H.fhw = sSup (insert 0 {r | ∃ C ∈ H.components, r = (H.induce C).fhw}) ∧
    H.adw = sSup (insert 0 {r | ∃ C ∈ H.components, r = (H.induce C).adw}) := by
  let F : Set ℝ := insert 0 {r | ∃ C ∈ H.components, r = (H.induce C).fhw}
  let A : Set ℝ := insert 0 {r | ∃ C ∈ H.components, r = (H.induce C).adw}
  have hFbound : ∀ r ∈ F, r ≤ H.fhw := by
    rintro r (rfl | ⟨C, hC, rfl⟩)
    · exact H.elementary_width_bounds.2.2
    · exact (H.width_hereditary C).2
  have hAbound : ∀ r ∈ A, r ≤ H.adw := by
    rintro r (rfl | ⟨C, hC, rfl⟩)
    · exact H.elementary_width_bounds.1
    · exact (H.width_hereditary C).1
  have hF0 : 0 ≤ sSup F := le_csSup ⟨H.fhw, hFbound⟩ (Set.mem_insert 0 _)
  have hA0 : 0 ≤ sSup A := le_csSup ⟨H.adw, hAbound⟩ (Set.mem_insert 0 _)
  constructor
  · apply le_antisymm _ (csSup_le ⟨0, Set.mem_insert 0 _⟩ hFbound)
    apply H.optimalWidth_le_components H.setCoverCost (sSup F)
      (fun S _ => H.coverCost_nonneg (indicator S))
    · have hz : H.setCoverCost ∅ = 0 :=
        H.coverCost_eq_zero_of_nonpos (by simp [indicator])
      exact hz ▸ hF0
    · intro C hC
      have hm : (H.induce C).fhw ≤ sSup F :=
        le_csSup ⟨H.fhw, hFbound⟩ (Set.mem_insert_of_mem 0 ⟨C, hC, rfl⟩)
      apply le_trans _ hm
      apply (H.induce C).optimalWidth_mono_cost H.setCoverCost (H.induce C).setCoverCost
        (fun S _ => H.coverCost_nonneg (indicator S))
      intro S hS
      exact (H.cover_restriction (fun v hv => (mem_inter.mp (hS hv)).2)).ge
  · apply le_antisymm _ (csSup_le ⟨0, Set.mem_insert 0 _⟩ hAbound)
    have hz : H.ModularWeight (fun _ => 0) := ⟨by simp, by simp⟩
    refine csSup_le ⟨_, _, hz, rfl⟩ ?_
    rintro r ⟨w, hw, rfl⟩
    apply H.optimalWidth_le_components (modularValue w) (sSup A)
      (fun S _ => sum_nonneg (fun v _ => hw.1 v))
      (by simpa [modularValue] using hA0)
    intro C hC
    have hwC : (H.induce C).ModularWeight w := by
      refine ⟨hw.1, ?_⟩
      intro e he
      exact (sum_le_sum_of_subset_of_nonneg inter_subset_left
        (fun v _ _ => hw.1 v)).trans (hw.2 e (mem_filter.mp he).1)
    exact ((H.induce C).optimal_modular_le_adw hwC).trans
      (le_csSup ⟨H.adw, hAbound⟩ (Set.mem_insert_of_mem 0 ⟨C, hC, rfl⟩))


@[simp] theorem setCoverCost_empty (H : Hypergraph) : H.setCoverCost ∅ = 0 :=
  H.coverCost_eq_zero_of_nonpos (by simp [indicator])

theorem setCoverCost_mono (H : Hypergraph) {A B : Finset ℕ} (h : A ⊆ B) :
    H.setCoverCost A ≤ H.setCoverCost B := by
  apply H.coverCost_mono
  intro v hv
  by_cases ha : v ∈ A
  · simp [indicator, ha, h ha]
  · simp only [indicator, if_neg ha]; split_ifs <;> norm_num

theorem setCoverCost_union_le (H : Hypergraph) (A B : Finset ℕ) :
    H.setCoverCost (A ∪ B) ≤ H.setCoverCost A + H.setCoverCost B := by
  apply le_trans _ (H.coverCost_add_le (indicator A) (indicator B))
  apply H.coverCost_mono
  intro v hv
  simp only [indicator, mem_union, Pi.add_apply]
  split_ifs <;> simp_all

theorem setCoverCost_singleton_le (H : Hypergraph) {v : ℕ} (hv : v ∈ H.vertices) :
    H.setCoverCost {v} ≤ 1 := by
  obtain ⟨e, he, hve⟩ := H.no_isolated v hv
  have hh : H.Cover (indicator {v}) (Pi.single e 1) := by
    refine ⟨?_, ?_⟩
    · intro f hf; simp only [Pi.single_apply]; split_ifs <;> norm_num
    · intro u hu
      by_cases huv : u = v
      · subst u; simp [indicator, Pi.single_apply, he, hve]
      · simp only [indicator, mem_singleton, if_neg huv]
        apply sum_nonneg
        intro f hf; simp only [Pi.single_apply]; split_ifs <;> norm_num
  simpa [setCoverCost, Pi.single_apply, he] using H.coverCost_le hh

theorem cover_mass_ge_one (H : Hypergraph) {Z : Finset ℕ} {γ : ℕ → ℝ}
    (hZ : Z ⊆ H.vertices) (hne : Z.Nonempty) (hγ : H.Cover (indicator Z) γ) :
    1 ≤ ∑ e ∈ H.edges, γ e := by
  obtain ⟨v, hv⟩ := hne
  have hh := hγ.2 v (hZ hv)
  simp only [indicator, if_pos hv] at hh
  exact hh.trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun e he _ => hγ.1 e he))

theorem induce_induce (H : Hypergraph) (W U : Finset ℕ) :
    (H.induce W).induce U = H.induce (W ∩ U) := by
  have hv : (H.vertices ∩ W) ∩ U = H.vertices ∩ (W ∩ U) := inter_assoc _ _ _
  have he : (H.edges.filter (fun e => (H.edge e ∩ W).Nonempty)).filter
      (fun e => ((H.edge e ∩ W) ∩ U).Nonempty) =
      H.edges.filter (fun e => (H.edge e ∩ (W ∩ U)).Nonempty) := by
    ext e
    simp only [mem_filter, inter_assoc]
    constructor
    · tauto
    · rintro ⟨he, v, hv⟩
      exact ⟨⟨he, v, mem_inter.mpr ⟨(mem_inter.mp hv).1, (mem_inter.mp (mem_inter.mp hv).2).1⟩⟩, v, hv⟩
  cases H
  simp only [induce] at hv he ⊢
  congr 1
  funext e
  exact inter_assoc _ _ _

theorem full_integral_separator (H : Hypergraph) (γ : ℕ → ℝ) (η : ℝ) :
    H.IntegralBalanced γ η H.vertices := by
  refine ⟨Subset.refl _, ?_⟩
  intro K hK
  simp [components, induce] at hK
  rcases hK with ⟨rfl, v, hv⟩
  simp at hv

theorem integralOptimum_bounds (H : Hypergraph) (γ : ℕ → ℝ) {η : ℝ}
    (hγ : H.EdgeWeight γ) (hη : 0 < η ∧ η < 1) :
    0 ≤ H.integralOptimum η γ ∧ H.integralOptimum η γ ≤ H.edges.card := by
  have hn : ∀ r ∈ {r | ∃ S, H.IntegralBalanced γ η S ∧ r = H.setCoverCost S}, 0 ≤ r := by
    rintro r ⟨S, _, rfl⟩; exact H.coverCost_nonneg _
  constructor
  · exact le_csInf ⟨_, H.vertices, H.full_integral_separator γ η, rfl⟩ hn
  · exact (csInf_le ⟨0, hn⟩ ⟨H.vertices, H.full_integral_separator γ η, rfl⟩).trans
      (H.full_fractional_separator hγ hη).2

theorem sep_bounds (H : Hypergraph) {η : ℝ} (hη : 0 < η ∧ η < 1) :
    0 ≤ H.sep η ∧ H.sep η ≤ H.edges.card := by
  have hb : ∀ r ∈ insert 0 {r | ∃ W ⊆ H.vertices, ∃ γ,
      (H.induce W).EdgeWeight γ ∧ r = (H.induce W).integralOptimum η γ},
      r ≤ (H.edges.card : ℝ) := by
    rintro r (rfl | ⟨W, hW, γ, hγ, rfl⟩)
    · positivity
    · exact ((H.induce W).integralOptimum_bounds γ hγ hη).2.trans (by
        exact_mod_cast card_filter_le H.edges (fun e => (H.edge e ∩ W).Nonempty))
  exact ⟨le_csSup ⟨_, hb⟩ (Set.mem_insert 0 _), csSup_le ⟨0, Set.mem_insert 0 _⟩ hb⟩

theorem exists_separator_lt (H : Hypergraph) {W : Finset ℕ} (hW : W ⊆ H.vertices)
    {γ : ℕ → ℝ} (hγ : (H.induce W).EdgeWeight γ) {η r : ℝ}
    (hη : 0 < η ∧ η < 1) (hr : H.sep η < r) :
    ∃ S, (H.induce W).IntegralBalanced γ η S ∧ H.setCoverCost S < r := by
  have hb : BddAbove (insert 0 {r | ∃ W ⊆ H.vertices, ∃ γ,
      (H.induce W).EdgeWeight γ ∧ r = (H.induce W).integralOptimum η γ}) := by
    refine ⟨H.edges.card, ?_⟩
    rintro r (rfl | ⟨U, hU, δ, hδ, rfl⟩)
    · positivity
    · exact ((H.induce U).integralOptimum_bounds δ hδ hη).2.trans (by
        exact_mod_cast card_filter_le H.edges (fun e => (H.edge e ∩ U).Nonempty))
  have hh : (H.induce W).integralOptimum η γ < r :=
    (le_csSup hb (Set.mem_insert_of_mem 0 ⟨W, hW, γ, hγ, rfl⟩)).trans_lt hr
  obtain ⟨_, ⟨S, hS, rfl⟩, hc⟩ := exists_lt_of_csInf_lt
    (show {r | ∃ S, (H.induce W).IntegralBalanced γ η S ∧
      r = (H.induce W).setCoverCost S}.Nonempty from
      ⟨_, (H.induce W).vertices, (H.induce W).full_integral_separator γ η, rfl⟩) hh
  refine ⟨S, hS, ?_⟩
  rwa [H.cover_restriction (fun v hv => (mem_inter.mp (hS.1 hv)).2)] at hc

theorem primal_induce_mono (H : Hypergraph) {U W : Finset ℕ} (hUW : U ⊆ W) :
    (H.induce U).primal ≤ (H.induce W).primal := by
  rintro u v ⟨hne, e, he, hue, hve⟩
  refine ⟨hne, e, mem_filter.mpr ⟨(mem_filter.mp he).1, u, ?_⟩, ?_, ?_⟩
  all_goals first
    | exact mem_inter.mpr ⟨(mem_inter.mp hue).1, hUW (mem_inter.mp hue).2⟩
    | exact mem_inter.mpr ⟨(mem_inter.mp hve).1, hUW (mem_inter.mp hve).2⟩

theorem component_induce_mono (H : Hypergraph) {U W K : Finset ℕ} (hUW : U ⊆ W)
    (hK : K ∈ (H.induce U).components) :
    ∃ C ∈ (H.induce W).components, K ⊆ C := by
  have hsub := mem_powerset.mp (mem_filter.mp hK).1
  obtain ⟨v, hv, _⟩ := (mem_filter.mp hK).2
  have hvW : v ∈ (H.induce W).vertices :=
    mem_inter.mpr ⟨(mem_inter.mp (hsub hv)).1, hUW (mem_inter.mp (hsub hv)).2⟩
  obtain ⟨C, hC, hvC⟩ := (H.induce W).exists_component_of_mem hvW
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hzW : z ∈ (H.induce W).vertices :=
    mem_inter.mpr ⟨(mem_inter.mp (hsub hz)).1, hUW (mem_inter.mp (hsub hz)).2⟩
  apply ((H.induce W).component_mem_iff_reachable hC hvC hzW).mpr
  have hh := ((H.induce U).component_mem_iff_reachable hK hv (hsub hz)).mp hz
  exact ⟨hh.some.mapLe (H.primal_induce_mono hUW)⟩

def boundary (H : Hypergraph) (B K : Finset ℕ) : Finset ℕ :=
  B.filter (fun z => ∃ v ∈ K, H.primal.Adj z v)

theorem cover_inter_le_mass (H : Hypergraph) {Z K : Finset ℕ} {γ : ℕ → ℝ}
    (hγ : H.Cover (indicator Z) γ) : H.setCoverCost (Z ∩ K) ≤
      ∑ e ∈ H.edges.filter (fun e => ¬ Disjoint (H.edge e) K), γ e := by
  let δ : ℕ → ℝ := fun e => if ¬ Disjoint (H.edge e) K then γ e else 0
  have hδ : H.Cover (indicator (Z ∩ K)) δ := by
    refine ⟨?_, ?_⟩
    · intro e he
      dsimp [δ]; split_ifs
      · exact le_rfl
      · exact hγ.1 e he
    · intro v hv
      by_cases hvZK : v ∈ Z ∩ K
      · have hh := hγ.2 v hv
        simp only [indicator, if_pos (mem_inter.mp hvZK).1] at hh
        simp only [indicator, if_pos hvZK]
        convert hh using 1
        apply sum_congr rfl
        intro e he
        exact if_pos (not_disjoint_iff.mpr ⟨v, (mem_filter.mp he).2, (mem_inter.mp hvZK).2⟩)
      · simp only [indicator, if_neg hvZK]
        apply sum_nonneg
        intro e he
        dsimp [δ]; split_ifs
        · exact le_rfl
        · exact hγ.1 e (mem_filter.mp he).1
  have hh := H.coverCost_le hδ
  simpa [setCoverCost, δ, sum_filter] using hh

/-- One step of the recursion, including the inherited boundary invariant. -/
theorem recursive_bag_step (H : Hypergraph) {η r : ℝ} (hη : 0 < η ∧ η < 1)
    (hr : H.sep η < r) {W Z : Finset ℕ} (hW : W ⊆ H.vertices) (hZ : Z ⊆ W)
    (hcost : H.setCoverCost Z ≤ (r + 1) / (1 - η)) {u : ℕ} (hu : u ∈ W \ Z) :
    ∃ B, Z ⊆ B ∧ B ⊆ W ∧ u ∈ B ∧
      H.setCoverCost B ≤ (r + 1) / (1 - η) + r + 1 ∧
      ∀ K ∈ (H.induce (W \ B)).components,
        H.setCoverCost ((H.induce W).boundary B K) ≤ (r + 1) / (1 - η) := by
  let L := (r + 1) / (1 - η)
  have hr0 : 0 ≤ r := (H.sep_bounds hη).1.trans hr.le
  have hden : 0 < 1 - η := sub_pos.mpr hη.2
  have hL0 : 0 ≤ L := div_nonneg (by linarith) hden.le
  have hL : L = r + 1 + η * L := by
    dsimp [L]; field_simp [ne_of_gt hden]; ring
  have huW : u ∈ W := (mem_sdiff.mp hu).1
  have huV := hW huW
  by_cases hZe : Z = ∅
  · subst Z
    refine ⟨{u}, empty_subset _, singleton_subset_iff.mpr huW, mem_singleton_self _, ?_, ?_⟩
    · exact (H.setCoverCost_singleton_le huV).trans (by change 1 ≤ L + r + 1; linarith)
    · intro K hK
      have hh := (H.setCoverCost_mono (filter_subset (fun z => ∃ v ∈ K,
        (H.induce W).primal.Adj z v) {u})).trans (H.setCoverCost_singleton_le huV)
      exact hh.trans (by change 1 ≤ L; nlinarith)
  · have hZJ : Z ⊆ (H.induce W).vertices := fun v hv => mem_inter.mpr ⟨hW (hZ hv), hZ hv⟩
    obtain ⟨γ, hγ, hγ1, hγcost⟩ := (H.induce W).coverCost_attained
      (x := indicator Z) (by intro v hv; simp only [indicator]; split_ifs <;> norm_num)
    have hγmass : 0 < ∑ e ∈ (H.induce W).edges, γ e :=
      lt_of_lt_of_le (by norm_num) ((H.induce W).cover_mass_ge_one hZJ
        (nonempty_iff_ne_empty.mpr hZe) hγ)
    have hγweight : (H.induce W).EdgeWeight γ :=
      ⟨fun e he => ⟨hγ.1 e he, hγ1 e he⟩, hγmass⟩
    obtain ⟨S, hS, hScost⟩ := H.exists_separator_lt hW hγweight hη hr
    have hSW : S ⊆ W := fun v hv => (mem_inter.mp (hS.1 hv)).2
    have hmass : (∑ e ∈ (H.induce W).edges, γ e) = H.setCoverCost Z := by
      rw [← hγcost]
      exact H.cover_restriction hZ
    let B := Z ∪ S ∪ {u}
    have hBW : B ⊆ W := union_subset (union_subset hZ hSW) (singleton_subset_iff.mpr huW)
    refine ⟨B, subset_trans subset_union_left subset_union_left, hBW, by simp [B], ?_, ?_⟩
    · exact (H.setCoverCost_union_le (Z ∪ S) {u}).trans (by
        have hh := H.setCoverCost_union_le Z S
        have hs := H.setCoverCost_singleton_le huV
        dsimp [L] at *
        linarith)
    · intro K hK
      have hSB : S ⊆ B := subset_trans subset_union_right subset_union_left
      have hsmall : W \ B ⊆ W \ S := fun v hv =>
        mem_sdiff.mpr ⟨(mem_sdiff.mp hv).1, fun hs => (mem_sdiff.mp hv).2 (hSB hs)⟩
      obtain ⟨C, hC, hKC⟩ := H.component_induce_mono hsmall hK
      have hWcap : H.vertices ∩ W = W := inter_eq_right.mpr hW
      have hC' : C ∈ ((H.induce W).induce ((H.induce W).vertices \ S)).components := by
        rw [H.induce_induce]
        have hid : W ∩ (W \ S) = W \ S := inter_eq_right.mpr sdiff_subset
        change C ∈ (H.induce (W ∩ ((H.vertices ∩ W) \ S))).components
        rw [hWcap, hid]
        exact hC
      have hCsub : C ⊆ (H.induce (W \ S)).vertices := mem_powerset.mp (mem_filter.mp hC).1
      have hcontain : (H.induce W).boundary B K ⊆ S ∪ {u} ∪ (Z ∩ C) := by
        intro z hz
        obtain ⟨hzB, v, hvK, hzv⟩ := mem_filter.mp hz
        by_cases hzS : z ∈ S
        · exact mem_union_left _ (mem_union_left _ hzS)
        by_cases hzu : z = u
        · exact mem_union_left _ (mem_union_right _ (mem_singleton.mpr hzu))
        have hzZ : z ∈ Z := by simpa [B, hzS, hzu] using hzB
        have hzJ : z ∈ (H.induce (W \ S)).vertices := mem_inter.mpr ⟨hW (hZ hzZ), mem_sdiff.mpr ⟨hZ hzZ, hzS⟩⟩
        have hvC := hKC hvK
        have hvWS := (mem_inter.mp (hCsub hvC)).2
        have hadj : (H.induce (W \ S)).primal.Adj v z :=
          (H.primal_induce_adj _ hvWS (mem_sdiff.mpr ⟨hZ hzZ, hzS⟩)).mpr
            ((H.primal_induce_adj W (hZ hzZ) (mem_sdiff.mp hvWS).1).mp hzv).symm
        have hzC := ((H.induce (W \ S)).component_mem_iff_reachable hC hvC hzJ).mpr hadj.reachable
        exact mem_union_right _ (mem_inter.mpr ⟨hzZ, hzC⟩)
      have hZC : H.setCoverCost (Z ∩ C) ≤ η * H.setCoverCost Z := by
        rw [← H.cover_restriction (inter_subset_left.trans hZ)]
        exact ((H.induce W).cover_inter_le_mass hγ).trans (by simpa [hmass] using hS.2 C hC')
      calc
        H.setCoverCost ((H.induce W).boundary B K) ≤ H.setCoverCost (S ∪ {u} ∪ (Z ∩ C)) := H.setCoverCost_mono hcontain
        _ ≤ H.setCoverCost (S ∪ {u}) + H.setCoverCost (Z ∩ C) := H.setCoverCost_union_le _ _
        _ ≤ r + 1 + η * L := by
          have hh := H.setCoverCost_union_le S {u}
          have hs := H.setCoverCost_singleton_le huV
          have hz := mul_le_mul_of_nonneg_left hcost hη.1.le
          change H.setCoverCost Z ≤ L at hcost
          change H.setCoverCost (S ∪ {u}) + H.setCoverCost (Z ∩ C) ≤ r + 1 + η * L
          nlinarith
        _ = _ := hL.symm

/-- The residual component is exactly the interior of its child instance. -/
theorem child_geometry (H : Hypergraph) {W B K : Finset ℕ}
    (hBW : B ⊆ W) (hK : K ∈ (H.induce (W \ B)).components) :
    (K ∪ (H.induce W).boundary B K) ⊆ W ∧
    (K ∪ (H.induce W).boundary B K) \ (H.induce W).boundary B K = K ∧
    (K ∪ (H.induce W).boundary B K) ∩ B = (H.induce W).boundary B K := by
  have hsub : K ⊆ W \ B := fun v hv =>
    (mem_inter.mp (mem_powerset.mp (mem_filter.mp hK).1 hv)).2
  have hbd : (H.induce W).boundary B K ⊆ B := filter_subset _ _
  refine ⟨union_subset (hsub.trans sdiff_subset) (hbd.trans hBW), ?_, ?_⟩
  · ext v
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hv | hv, hn⟩
      · exact hv
      · exact (hn hv).elim
    · intro hv
      exact ⟨Or.inl hv, fun hb => (mem_sdiff.mp (hsub hv)).2 (hbd hb)⟩
  · ext v
    simp only [mem_inter, mem_union]
    constructor
    · rintro ⟨hv | hv, hb⟩
      · exact ((mem_sdiff.mp (hsub hv)).2 hb).elim
      · exact hv
    · intro hv
      exact ⟨Or.inr hv, hbd hv⟩

/-- Removing the pivot makes every recursive call strictly smaller. -/
theorem child_card_lt (H : Hypergraph) {W Z B K : Finset ℕ} {u : ℕ}
    (hZB : Z ⊆ B) (hu : u ∈ W \ Z) (huB : u ∈ B)
    (hK : K ∈ (H.induce (W \ B)).components) : K.card < (W \ Z).card := by
  have hsub : K ⊆ W \ B := fun v hv =>
    (mem_inter.mp (mem_powerset.mp (mem_filter.mp hK).1 hv)).2
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro v hv
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp (hsub hv)).1,
      fun hz => (mem_sdiff.mp (hsub hv)).2 (hZB hz)⟩
  · intro heq
    have huK : u ∈ K := heq ▸ hu
    exact (mem_sdiff.mp (hsub huK)).2 huB

/-- A hyperedge outside the root bag lies in one component together with its boundary. -/
theorem edge_in_child (H : Hypergraph) {W B : Finset ℕ}
    {e : ℕ} (he : e ∈ (H.induce W).edges) (hn : ¬ (H.induce W).edge e ⊆ B) :
    ∃ K ∈ (H.induce (W \ B)).components,
      (H.induce W).edge e ⊆ K ∪ (H.induce W).boundary B K := by
  obtain ⟨v, hve, hvB⟩ := not_subset.mp hn
  have hvJ := (H.induce W).edge_subset e he hve
  have hvR : v ∈ (H.induce (W \ B)).vertices :=
    mem_inter.mpr ⟨(mem_inter.mp hvJ).1, mem_sdiff.mpr ⟨(mem_inter.mp hvJ).2, hvB⟩⟩
  obtain ⟨K, hK, hvK⟩ := (H.induce (W \ B)).exists_component_of_mem hvR
  refine ⟨K, hK, ?_⟩
  intro z hze
  by_cases hzB : z ∈ B
  · apply mem_union_right
    apply mem_filter.mpr
    refine ⟨hzB, v, hvK, ?_⟩
    exact ⟨fun hzv => hvB (hzv ▸ hzB), e, he, hze, hve⟩
  · apply mem_union_left
    have heR : e ∈ (H.induce (W \ B)).edges :=
      mem_filter.mpr ⟨(mem_filter.mp he).1,
        v, mem_inter.mpr ⟨(mem_inter.mp hve).1, (mem_inter.mp hvR).2⟩⟩
    exact (H.induce (W \ B)).edge_subset_component hK heR
      (mem_inter.mpr ⟨(mem_inter.mp hve).1, (mem_inter.mp hvR).2⟩) hvK
      (mem_inter.mpr ⟨(mem_inter.mp hze).1, mem_sdiff.mpr ⟨(mem_inter.mp hze).2, hzB⟩⟩)

/-- Join a family of trees by edges from one designated root to all other roots. -/
theorem rooted_forest_tree {I : Type*} {V : I → Type*}
    (G : ∀ i, SimpleGraph (V i)) (hG : ∀ i, (G i).IsTree)
    (root : ∀ i, V i) (o : I) :
    ∃ F : SimpleGraph (Sigma V), F.IsTree ∧ forestGraph G ≤ F ∧
      ∀ i, i ≠ o → F.Adj ⟨o, root o⟩ ⟨i, root i⟩ := by
  classical
  let c : Sigma V := ⟨o, root o⟩
  let q : I → Sigma V := fun i => ⟨i, root i⟩
  let A := forestGraph G
  let M := A ⊔ ⨆ i, SimpleGraph.edge c (q i)
  have hedge (i : I) (hi : i ≠ o) : M.Adj c (q i) := by
    apply Or.inr
    rw [SimpleGraph.iSup_adj]
    refine ⟨i, (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩⟩
    intro heq
    exact hi (congrArg Sigma.fst heq).symm
  have hinside (i : I) (a b : V i) : M.Reachable ⟨i, a⟩ ⟨i, b⟩ := by
    let f : G i →g A := {
      toFun := fun v => ⟨i, v⟩
      map_rel' := fun h => ⟨rfl, h⟩ }
    exact (((hG i).connected a b).map f).mono le_sup_left
  have htoc (a : Sigma V) : M.Reachable a c := by
    have hh := hinside a.1 a.2 (root a.1)
    by_cases hi : a.1 = o
    · cases a with
      | mk i v =>
        dsimp at hi
        subst i
        exact hh
    · exact hh.trans (hedge a.1 hi).symm.reachable
  letI : Nonempty (Sigma V) := ⟨c⟩
  have hM : M.Connected := ⟨fun a b => (htoc a).trans (htoc b).symm⟩
  obtain ⟨F, hAF, hFM, hF⟩ := hM.exists_isTree_le_of_le_of_isAcyclic
    (H := A) le_sup_left (forest_acyclic G (fun i => (hG i).isAcyclic))
  refine ⟨F, hF, hAF, ?_⟩
  intro i hi
  by_contra hn
  have hstay {a b : Sigma V} (ha : a.1 = i) (hab : F.Adj a b) : b.1 = i := by
    rcases hFM hab with hab' | hab'
    · obtain ⟨heq, _⟩ := hab'
      exact heq.symm.trans ha
    · rw [SimpleGraph.iSup_adj] at hab'
      obtain ⟨j, hj⟩ := hab'
      rcases ((SimpleGraph.edge_adj _ _ _ _).mp hj).1 with ⟨hac, hbq⟩ | ⟨haq, hbc⟩
      · exact (hi (ha.symm.trans (congrArg Sigma.fst hac))).elim
      · have hji : j = i := (congrArg Sigma.fst haq).symm.trans ha
        subst j
        have hh : F.Adj (q i) c := by simpa only [haq, hbc] using hab
        exact (hn hh.symm).elim
  have hpath {a b : Sigma V} (p : F.Walk a b) (ha : a.1 = i) : b.1 = i := by
    induction p with
    | nil => exact ha
    | cons hab p ih => exact ih (hstay ha hab)
  exact hi (hpath (hF.connected (q i) c).some rfl).symm

/-- Rooted gluing preserves running intersection when shared vertices occur in the roots. -/
theorem glue_rooted_bags (H : Hypergraph) {I : Type*} [Fintype I]
    {V : I → Type*} [∀ i, Fintype (V i)]
    (G : ∀ i, SimpleGraph (V i)) (hG : ∀ i, (G i).IsTree)
    (bag : ∀ i, V i → Finset ℕ) (root : ∀ i, V i) (o : I)
    (hsub : ∀ i t, bag i t ⊆ H.vertices)
    (hedge : ∀ e ∈ H.edges, ∃ i t, H.edge e ⊆ bag i t)
    (hvertex : ∀ v ∈ H.vertices, ∃ i t, v ∈ bag i t)
    (hrun : ∀ i v, (G i |>.induce {t | v ∈ bag i t}).Preconnected)
    (hlocal : ∀ i t, bag i t ∩ bag o (root o) ⊆ bag i (root i))
    (hoverlap : ∀ i j, i ≠ j → ∀ a c, bag i a ∩ bag j c ⊆ bag o (root o))
    (b : Finset ℕ → ℝ) (r : ℝ) (hwidth : ∀ i t, b (bag i t) ≤ r) :
    ∃ n, ∃ D : H.TreeDecomposition n, ∃ t, bag o (root o) ⊆ D.bag t ∧
      ∀ t, b (D.bag t) ≤ r := by
  classical
  obtain ⟨F, hF, hGF, hstar⟩ := rooted_forest_tree G hG root o
  letI : Nonempty (Sigma V) := ⟨⟨o, root o⟩⟩
  let bags : Sigma V → Finset ℕ := fun t => bag t.1 t.2
  have hwithin (i : I) (v : ℕ) (a c : V i) (ha : v ∈ bag i a) (hc : v ∈ bag i c) :
      (F.induce {t | v ∈ bags t}).Reachable ⟨⟨i, a⟩, ha⟩ ⟨⟨i, c⟩, hc⟩ := by
    let f : (G i).induce {t | v ∈ bag i t} →g F.induce {t | v ∈ bags t} := {
      toFun := fun t => ⟨⟨i, t.val⟩, t.property⟩
      map_rel' := fun hab => hGF ⟨rfl, hab⟩ }
    exact (hrun i v ⟨a, ha⟩ ⟨c, hc⟩).map f
  apply H.finite_rooted_tree_decomposition F hF bags (fun t => hsub t.1 t.2)
    (by intro e he; obtain ⟨i,t,ht⟩ := hedge e he; exact ⟨⟨i,t⟩, ht⟩)
    (by intro v hv; obtain ⟨i,t,ht⟩ := hvertex v hv; exact ⟨⟨i,t⟩, ht⟩)
    _ ⟨o,root o⟩ (bag o (root o)) (Subset.refl _) b r (fun t => hwidth t.1 t.2)
  intro v hv a c
  by_cases hi : a.val.1 = c.val.1
  · obtain ⟨⟨i,a⟩,ha⟩ := a
    obtain ⟨⟨j,c⟩,hc⟩ := c
    dsimp at hi
    subst j
    exact hwithin i v a c ha hc
  · have hvroot : v ∈ bag o (root o) := hoverlap _ _ hi _ _ (mem_inter.mpr ⟨a.property,c.property⟩)
    have htoc (t : {t : Sigma V // v ∈ bags t}) :
        (F.induce {t | v ∈ bags t}).Reachable t ⟨⟨o,root o⟩,hvroot⟩ := by
      obtain ⟨⟨i,t⟩,ht⟩ := t
      have hri : v ∈ bag i (root i) := hlocal i t (mem_inter.mpr ⟨ht,hvroot⟩)
      have hh := hwithin i v t (root i) ht hri
      by_cases hio : i = o
      · subst i
        exact hh
      · exact hh.trans (show (F.induce {t | v ∈ bags t}).Adj
          ⟨⟨i,root i⟩,hri⟩ ⟨⟨o,root o⟩,hvroot⟩ from (hstar i hio).symm).reachable
    exact (htoc a).trans (htoc c).symm

/-- The rooted invariant used in the LaTeX separator recursion. -/
theorem recursive_rooted_decomposition (H : Hypergraph) {η r : ℝ}
    (hη : 0 < η ∧ η < 1) (hr : H.sep η < r)
    (W Z : Finset ℕ) (hW : W ⊆ H.vertices) (hZ : Z ⊆ W)
    (hcost : H.setCoverCost Z ≤ (r + 1) / (1 - η)) :
    ∃ n, ∃ D : (H.induce W).TreeDecomposition n, ∃ root, Z ⊆ D.bag root ∧
      ∀ t, H.setCoverCost (D.bag t) ≤ (r + 1) / (1 - η) + r + 1 := by
  classical
  generalize hm : (W \ Z).card = m
  induction m using Nat.strong_induction_on generalizing W Z with
  | h m ih =>
    have hr0 : 0 ≤ r := (H.sep_bounds hη).1.trans hr.le
    by_cases hWZ : W = Z
    · subst Z
      refine ⟨0, (H.induce W).oneBag, 0, ?_, ?_⟩
      · simpa [oneBag, induce, inter_eq_right.mpr hW]
      · intro t
        simpa only [oneBag, induce, inter_eq_right.mpr hW] using
          (hcost.trans (by linarith : (r + 1) / (1 - η) ≤ (r + 1) / (1 - η) + r + 1))
    have hne : (W \ Z).Nonempty := by
      by_contra hn
      exact hWZ (subset_antisymm
        (sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp hn)) hZ)
    obtain ⟨u, hu⟩ := hne
    obtain ⟨B, hZB, hBW, huB, hBcost, hbound⟩ := H.recursive_bag_step hη hr hW hZ hcost hu
    let I := {K // K ∈ (H.induce (W \ B)).components}
    let bd : I → Finset ℕ := fun i => (H.induce W).boundary B i.val
    let child : I → Finset ℕ := fun i => i.val ∪ bd i
    have hgeom (i : I) := H.child_geometry hBW i.property
    have hchild (i : I) : ∃ n, ∃ D : (H.induce (child i)).TreeDecomposition n,
        ∃ root, bd i ⊆ D.bag root ∧
          ∀ t, H.setCoverCost (D.bag t) ≤ (r + 1) / (1 - η) + r + 1 := by
      apply ih ((child i \ bd i).card) ?_ (child i) (bd i)
        ((hgeom i).1.trans hW) subset_union_right (hbound i i.property) rfl
      change ((i.val ∪ (H.induce W).boundary B i.val) \ (H.induce W).boundary B i.val).card < m
      rw [(hgeom i).2.1, ← hm]
      exact H.child_card_lt hZB hu huB i.property
    choose n D root hroot hwidth using hchild
    let ns : Option I → ℕ := fun i => match i with | none => 0 | some i => n i
    let G : ∀ i : Option I, SimpleGraph (Fin (ns i + 1)) := fun i => match i with
      | none => (H.induce W).oneBag.tree
      | some i => (D i).tree
    let bag : ∀ i : Option I, Fin (ns i + 1) → Finset ℕ := fun i => match i with
      | none => fun _ => B
      | some i => (D i).bag
    let roots : ∀ i : Option I, Fin (ns i + 1) := fun i => match i with
      | none => 0
      | some i => root i
    have hsub (i : Option I) (t : Fin (ns i + 1)) : bag i t ⊆ (H.induce W).vertices := by
      cases i with
      | none => exact fun v hv => mem_inter.mpr ⟨hW (hBW hv), hBW hv⟩
      | some i =>
        intro v hv
        exact mem_inter.mpr ⟨(mem_inter.mp ((D i).bag_subset t hv)).1,
          (hgeom i).1 (mem_inter.mp ((D i).bag_subset t hv)).2⟩
    have hbsub (i : I) (t : Fin (n i + 1)) : (D i).bag t ⊆ child i :=
      fun v hv => (mem_inter.mp ((D i).bag_subset t hv)).2
    obtain ⟨k, E, q, hq, hE⟩ := (H.induce W).glue_rooted_bags G
      (by intro i; cases i with
          | none => exact (H.induce W).oneBag.isTree
          | some i => exact (D i).isTree)
      bag roots none hsub (by
        intro e he
        by_cases heB : (H.induce W).edge e ⊆ B
        · exact ⟨none, 0, heB⟩
        · obtain ⟨K, hK, heK⟩ := H.edge_in_child he heB
          let i : I := ⟨K, hK⟩
          obtain ⟨v, hve⟩ := (H.induce W).edge_nonempty e he
          have heC : e ∈ (H.induce (child i)).edges := mem_filter.mpr
            ⟨(mem_filter.mp he).1, v, mem_inter.mpr ⟨(mem_inter.mp hve).1, heK hve⟩⟩
          obtain ⟨t, ht⟩ := (D i).edge_covered e heC
          exact ⟨some i, t, fun v hv => ht (mem_inter.mpr ⟨(mem_inter.mp hv).1, heK hv⟩)⟩) (by
        intro v hv
        by_cases hvB : v ∈ B
        · exact ⟨none, 0, hvB⟩
        · have hvR : v ∈ (H.induce (W \ B)).vertices :=
            mem_inter.mpr ⟨(mem_inter.mp hv).1, mem_sdiff.mpr ⟨(mem_inter.mp hv).2, hvB⟩⟩
          obtain ⟨K, hK, hvK⟩ := (H.induce (W \ B)).exists_component_of_mem hvR
          let i : I := ⟨K,hK⟩
          obtain ⟨t,ht⟩ := (D i).vertex_covered v
            (mem_inter.mpr ⟨(mem_inter.mp hv).1, mem_union_left _ hvK⟩)
          exact ⟨some i,t,ht⟩) (by
        intro i v a c
        cases i with
        | none =>
          have heq : a = c := by
            apply Subtype.ext
            apply Fin.ext
            have ha := a.val.isLt
            have hc := c.val.isLt
            dsimp [ns] at ha hc
            omega
          exact heq ▸ SimpleGraph.Reachable.refl a
        | some i => exact (D i).running_intersection v ((D i).bag_subset a.val a.property) a c) (by
        intro i t v hv
        cases i with
        | none => exact (mem_inter.mp hv).1
        | some i =>
          apply hroot i
          have hh : v ∈ child i ∩ B := mem_inter.mpr ⟨hbsub i t (mem_inter.mp hv).1, (mem_inter.mp hv).2⟩
          rwa [(hgeom i).2.2] at hh) (by
        intro i j hij a c v hv
        cases i with
        | none => exact (mem_inter.mp hv).1
        | some i =>
          cases j with
          | none => exact (mem_inter.mp hv).2
          | some j =>
            by_contra hvB
            have hiC := hbsub i a (mem_inter.mp hv).1
            have hjC := hbsub j c (mem_inter.mp hv).2
            have hiK : v ∈ i.val := (mem_union.mp hiC).resolve_right
              (fun h => hvB ((filter_subset _ _) h))
            have hjK : v ∈ j.val := (mem_union.mp hjC).resolve_right
              (fun h => hvB ((filter_subset _ _) h))
            exact hij (congrArg some (Subtype.ext
              ((H.induce (W \ B)).component_eq_of_mem i.property j.property hiK hjK))))
      H.setCoverCost ((r + 1) / (1 - η) + r + 1) (by
        intro i t
        cases i with
        | none => exact hBcost
        | some i => exact hwidth i t)
    exact ⟨k,E,q,hZB.trans hq,hE⟩

/-- Full restriction preserves decompositions, without identifying inactive edge maps. -/
def TreeDecomposition.ofInduceVertices {H : Hypergraph} {n : ℕ}
    (D : (H.induce H.vertices).TreeDecomposition n) : H.TreeDecomposition n where
  tree := D.tree
  isTree := D.isTree
  bag := D.bag
  bag_subset := fun t v hv => (mem_inter.mp (D.bag_subset t hv)).1
  edge_covered := by
    intro e he
    have heq : H.edge e ∩ H.vertices = H.edge e := inter_eq_left.mpr (H.edge_subset e he)
    have he' : e ∈ (H.induce H.vertices).edges :=
      mem_filter.mpr ⟨he, by rw [heq]; exact H.edge_nonempty e he⟩
    obtain ⟨t,ht⟩ := D.edge_covered e he'
    exact ⟨t, by simpa only [induce,heq] using ht⟩
  vertex_covered := fun v hv => D.vertex_covered v (mem_inter.mpr ⟨hv,hv⟩)
  running_intersection := fun v hv => D.running_intersection v (mem_inter.mpr ⟨hv,hv⟩)

theorem recursive_separator_decomposition (H : Hypergraph) {η : ℝ}
    (hη : 0 < η ∧ η < 1) :
    H.fhw ≤ (2 - η) / (1 - η) * (H.sep η + 1) := by
  have hden : 0 < 1 - η := sub_pos.mpr hη.2
  let a := (2 - η) / (1 - η)
  have ha : 0 < a := div_pos (by linarith) hden
  have happrox (r : ℝ) (hr : H.sep η < r) : H.fhw ≤ a * (r + 1) := by
    have hr0 : 0 ≤ r := (H.sep_bounds hη).1.trans hr.le
    obtain ⟨n,D,root,hroot,hD⟩ := H.recursive_rooted_decomposition hη hr H.vertices ∅
      (Subset.refl _) (empty_subset _) (by
        rw [H.setCoverCost_empty]
        exact div_nonneg (by linarith) hden.le)
    have hw : H.fhw ≤ (r + 1) / (1 - η) + r + 1 := by
      apply (H.optimalWidth_le_bagWidth H.setCoverCost
        (fun S _ => H.coverCost_nonneg (indicator S)) D.ofInduceVertices).trans
      refine csSup_le ⟨_,0,rfl⟩ ?_
      rintro s ⟨t,rfl⟩
      exact hD t
    convert hw using 1
    dsimp [a]
    field_simp [ne_of_gt hden]
    ring
  have hlim : H.fhw / a - 1 ≤ H.sep η := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro r hr
    have hh : H.fhw / a ≤ r + 1 := (div_le_iff₀ ha).mpr (by
      simpa only [mul_comm] using happrox r hr)
    linarith
  have hh := (div_le_iff₀ ha).mp (show H.fhw / a ≤ H.sep η + 1 by linarith)
  simpa only [mul_comm] using hh

theorem separator_characterization (H : Hypergraph) {η : ℝ}
    (hη : 1 / 2 ≤ η ∧ η < 1) :
    H.sep η ≤ H.fhw ∧ H.fhw ≤ (2 - η) / (1 - η) * (H.sep η + 1) := by
  refine ⟨?_, H.recursive_separator_decomposition ⟨by linarith [hη.1], hη.2⟩⟩
  refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
  rintro r (rfl | ⟨W, hW, γ, hγ, rfl⟩)
  · exact H.elementary_width_bounds.2.2
  · apply le_trans ?_ (H.width_hereditary W).2
    refine le_csInf ⟨_, 0, (H.induce W).oneBag, rfl⟩ ?_
    rintro r ⟨n, D, rfl⟩
    obtain ⟨t, ht⟩ := (H.induce W).balanced_bag hγ D
    have htη : (H.induce W).IntegralBalanced γ η (D.bag t) := by
      refine ⟨ht.1, ?_⟩
      intro K hK
      exact (ht.2 K hK).trans (mul_le_mul_of_nonneg_right hη.1 hγ.2.le)
    have hopt : (H.induce W).integralOptimum η γ ≤ (H.induce W).setCoverCost (D.bag t) := by
      refine csInf_le ⟨0, ?_⟩ ⟨D.bag t, htη, rfl⟩
      rintro r ⟨S, hS, rfl⟩
      exact (H.induce W).coverCost_nonneg (indicator S)
    exact hopt.trans (le_csSup (Set.finite_range _).bddAbove ⟨t, rfl⟩)

/-- The finitely many path supports relevant to an edge-to-edge distance, together
with the constant-one option implementing truncation. -/
def separatorPathOptions (H : Hypergraph) (e f : ℕ) : Finset (Option (Finset ℕ)) :=
  insert none ((H.vertices.powerset.filter (fun S =>
    ∃ u ∈ H.edge e, ∃ v ∈ H.edge f, ∃ p : H.primal.Walk u v,
      p.IsPath ∧ p.support.toFinset = S)).image some)

def pathOptionCost (o : Option (Finset ℕ)) (x : ℕ → ℝ) : ℝ :=
  o.elim 1 (fun S => ∑ v ∈ S, x v)

def finiteEdgeDistance (H : Hypergraph) (e f : ℕ) (x : ℕ → ℝ) : ℝ :=
  (H.separatorPathOptions e f).inf' (by simp [separatorPathOptions]) (fun o => pathOptionCost o x)

theorem vertexDistance_nonneg (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {u v : ℕ} (hu : u ∈ H.vertices) :
    0 ≤ H.vertexDistance x u v := by
  refine le_csInf ⟨1, Set.mem_insert _ _⟩ ?_
  rintro r (rfl | ⟨p, hp, rfl⟩)
  · norm_num
  · exact sum_nonneg (fun z hz => hx z (H.walk_vertices p hu z (List.mem_toFinset.mp hz)))

theorem vertexDistance_le_option (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {u v : ℕ} (hu : u ∈ H.vertices)
    {r : ℝ} (hr : r ∈ insert 1 {r | ∃ p : H.primal.Walk u v,
      p.IsPath ∧ r = ∑ z ∈ p.support.toFinset, x z}) : H.vertexDistance x u v ≤ r := by
  refine csInf_le ⟨0, ?_⟩ hr
  rintro r (rfl | ⟨p, hp, rfl⟩)
  · norm_num
  · exact sum_nonneg (fun z hz => hx z (H.walk_vertices p hu z (List.mem_toFinset.mp hz)))

theorem edgeDistance_eq_finite (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {e f : ℕ} (he : e ∈ H.edges) (hf : f ∈ H.edges) :
    H.edgeDistance x e f = H.finiteEdgeDistance e f x := by
  have hne : {r | ∃ u ∈ H.edge e, ∃ v ∈ H.edge f, r = H.vertexDistance x u v}.Nonempty := by
    obtain ⟨u, hu⟩ := H.edge_nonempty e he
    obtain ⟨v, hv⟩ := H.edge_nonempty f hf
    exact ⟨_, u, hu, v, hv, rfl⟩
  have hb : BddBelow {r | ∃ u ∈ H.edge e, ∃ v ∈ H.edge f, r = H.vertexDistance x u v} := by
    refine ⟨0, ?_⟩
    rintro r ⟨u, hu, v, hv, rfl⟩
    exact H.vertexDistance_nonneg hx (H.edge_subset e he hu)
  have hop {u v : ℕ} (hu : u ∈ H.edge e) (hv : v ∈ H.edge f)
      (p : H.primal.Walk u v) (hp : p.IsPath) :
      some p.support.toFinset ∈ H.separatorPathOptions e f := by
    apply mem_insert_of_mem
    apply mem_image.mpr
    refine ⟨p.support.toFinset, mem_filter.mpr ⟨mem_powerset.mpr ?_, u, hu, v, hv, p, hp, rfl⟩, rfl⟩
    intro z hz
    exact H.walk_vertices p (H.edge_subset e he hu) z (List.mem_toFinset.mp hz)
  apply le_antisymm
  · apply Finset.le_inf'
    intro o ho
    cases o with
    | none =>
      obtain ⟨u, hu⟩ := H.edge_nonempty e he
      obtain ⟨v, hv⟩ := H.edge_nonempty f hf
      exact (csInf_le hb ⟨u, hu, v, hv, rfl⟩).trans
        (H.vertexDistance_le_option hx (H.edge_subset e he hu) (Set.mem_insert 1 _))
    | some S =>
      have hh : ∃ u ∈ H.edge e, ∃ v ∈ H.edge f, ∃ p : H.primal.Walk u v,
          p.IsPath ∧ p.support.toFinset = S := by
        simp only [separatorPathOptions, mem_insert, Option.some_ne_none, false_or, mem_image, Option.some.injEq, exists_eq_right, mem_filter, mem_powerset] at ho
        exact ho.2
      obtain ⟨u, hu, v, hv, p, hp, rfl⟩ := hh
      exact (csInf_le hb ⟨u, hu, v, hv, rfl⟩).trans
        (H.vertexDistance_le_option hx (H.edge_subset e he hu) (Set.mem_insert_of_mem 1 ⟨p, hp, rfl⟩))
  · refine le_csInf hne ?_
    rintro r ⟨u, hu, v, hv, rfl⟩
    refine le_csInf ⟨1, Set.mem_insert _ _⟩ ?_
    rintro r (rfl | ⟨p, hp, rfl⟩)
    · exact Finset.inf'_le (fun o => pathOptionCost o x) (mem_insert_self none _)
    · exact Finset.inf'_le _ (hop hu hv p hp)

theorem continuous_finiteEdgeDistance (H : Hypergraph) (e f : ℕ) :
    Continuous (H.finiteEdgeDistance e f) := by
  apply Continuous.finset_inf'_apply
  intro o ho
  cases o with
  | none => exact continuous_const
  | some S => exact continuous_finsetSum S (fun v _ => continuous_apply v)

theorem concave_finiteEdgeDistance (H : Hypergraph) (e f : ℕ) :
    ConcaveOn ℝ Set.univ (H.finiteEdgeDistance e f) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  apply Finset.le_inf'
  intro o ho
  have hxle := Finset.inf'_le (fun o => pathOptionCost o x) ho
  have hyle := Finset.inf'_le (fun o => pathOptionCost o y) ho
  have hc : pathOptionCost o (a • x + b • y) =
      a * pathOptionCost o x + b * pathOptionCost o y := by
    cases o with
    | none => simpa [pathOptionCost] using hab.symm
    | some S => simp [pathOptionCost, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, mul_sum]
  change a * H.finiteEdgeDistance e f x + b * H.finiteEdgeDistance e f y ≤ _
  rw [hc]
  exact add_le_add (mul_le_mul_of_nonneg_left hxle ha) (mul_le_mul_of_nonneg_left hyle hb)

/-- We bound the unused ambient coordinates too, to work in a compact product cube. -/
def separatorCube (H : Hypergraph) (γ : ℕ → ℝ) (θ : ℝ) : Set (ℕ → ℝ) :=
  Set.Icc 0 1 ∩ {x | ∀ e ∈ H.edges,
    (1 - θ) * (∑ f ∈ H.edges, γ f) ≤ ∑ f ∈ H.edges, γ f * H.finiteEdgeDistance e f x}

def modularCube (H : Hypergraph) : Set (ℕ → ℝ) :=
  Set.Icc 0 1 ∩ {w | ∀ e ∈ H.edges, ∑ v ∈ H.edge e, w v ≤ 1}

theorem mem_separatorCube (H : Hypergraph) {γ x : ℕ → ℝ} {θ : ℝ}
    (hx : x ∈ Set.Icc (0 : ℕ → ℝ) 1) :
    x ∈ H.separatorCube γ θ ↔ H.FractionalBalanced γ θ x := by
  have hn : ∀ v ∈ H.vertices, 0 ≤ x v := fun v _ => hx.1 v
  have heq (e : ℕ) (he : e ∈ H.edges) :
      (∑ f ∈ H.edges, γ f * H.edgeDistance x e f) =
        ∑ f ∈ H.edges, γ f * H.finiteEdgeDistance e f x := by
    apply sum_congr rfl
    intro f hf
    rw [H.edgeDistance_eq_finite hn he hf]
  constructor
  · intro h
    exact ⟨fun v _ => ⟨hx.1 v, hx.2 v⟩, fun e he => (heq e he).symm ▸ h.2 e he⟩
  · intro h
    exact ⟨hx, fun e he => heq e he ▸ h.2 e he⟩

theorem compact_separatorCube (H : Hypergraph) (γ : ℕ → ℝ) (θ : ℝ) :
    IsCompact (H.separatorCube γ θ) := by
  apply isCompact_Icc.inter_right
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro e
  apply isClosed_iInter
  intro he
  apply isClosed_le continuous_const
  exact continuous_finsetSum _ (fun f _ => continuous_const.mul (H.continuous_finiteEdgeDistance e f))

theorem convex_separatorCube (H : Hypergraph) {γ : ℕ → ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (θ : ℝ) : Convex ℝ (H.separatorCube γ θ) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_Icc (0 : ℕ → ℝ) 1 hx.1 hy.1 ha hb hab, ?_⟩
  intro e he
  have hc : a * (∑ f ∈ H.edges, γ f * H.finiteEdgeDistance e f x) +
      b * (∑ f ∈ H.edges, γ f * H.finiteEdgeDistance e f y) ≤
      ∑ f ∈ H.edges, γ f * H.finiteEdgeDistance e f (a • x + b • y) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro f hf
    have hd := (H.concave_finiteEdgeDistance e f).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    have hh := mul_le_mul_of_nonneg_left hd (hγ f hf)
    dsimp [smul_eq_mul] at hh
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left (hx.2 e he) ha
  have h2 := mul_le_mul_of_nonneg_left (hy.2 e he) hb
  have hh := (add_le_add h1 h2).trans hc
  rwa [← add_mul, hab, one_mul] at hh

theorem compact_modularCube (H : Hypergraph) : IsCompact H.modularCube := by
  apply isCompact_Icc.inter_right
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun e => isClosed_iInter fun _ =>
    isClosed_le (continuous_finsetSum _ (fun v _ => continuous_apply v)) continuous_const

theorem convex_modularCube (H : Hypergraph) : Convex ℝ H.modularCube := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_Icc (0 : ℕ → ℝ) 1 hx.1 hy.1 ha hb hab, ?_⟩
  intro e he
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
  have h1 := mul_le_mul_of_nonneg_left (hx.2 e he) ha
  have h2 := mul_le_mul_of_nonneg_left (hy.2 e he) hb
  nlinarith

theorem finiteEdgeDistance_congr (H : Hypergraph) (e f : ℕ) {x y : ℕ → ℝ}
    (hxy : ∀ v ∈ H.vertices, x v = y v) : H.finiteEdgeDistance e f x = H.finiteEdgeDistance e f y := by
  apply Finset.inf'_congr _ rfl
  intro o ho
  cases o with
  | none => rfl
  | some S =>
    have hS : S ⊆ H.vertices := by
      simp only [separatorPathOptions, mem_insert, Option.some_ne_none, false_or,
        mem_image, Option.some.injEq, exists_eq_right, mem_filter, mem_powerset] at ho
      exact ho.1
    exact sum_congr rfl (fun v hv => hxy v (hS hv))

/-- Zero extension on ambient coordinates preserves all separator constraints. -/
theorem separator_restrict (H : Hypergraph) {γ x : ℕ → ℝ} {θ : ℝ}
    (hx : H.FractionalBalanced γ θ x) :
    (fun v => if v ∈ H.vertices then x v else 0) ∈ H.separatorCube γ θ := by
  let y : ℕ → ℝ := fun v => if v ∈ H.vertices then x v else 0
  have hy : y ∈ Set.Icc (0 : ℕ → ℝ) 1 := by
    constructor <;> intro v <;> dsimp [y] <;> split_ifs with hv
    · exact (hx.1 v hv).1
    · norm_num
    · exact (hx.1 v hv).2
    · norm_num
  refine ⟨hy, ?_⟩
  intro e he
  have heq : (∑ f ∈ H.edges, γ f * H.finiteEdgeDistance e f y) =
      ∑ f ∈ H.edges, γ f * H.edgeDistance x e f := by
    apply sum_congr rfl
    intro f hf
    rw [H.edgeDistance_eq_finite (fun v hv => (hx.1 v hv).1) he hf,
      H.finiteEdgeDistance_congr e f (x := y) (y := x) (by intro v hv; simp [y, hv])]
  exact heq.symm ▸ hx.2 e he

theorem modular_restrict (H : Hypergraph) {w : ℕ → ℝ} (hw : H.ModularWeight w) :
    (fun v => if v ∈ H.vertices then w v else 0) ∈ H.modularCube := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v; dsimp; split_ifs; exact hw.1 v; exact le_rfl
  · intro v; dsimp; split_ifs with hv
    · exact H.modularWeight_vertex_le_one hw hv
    · norm_num
  · intro e he
    convert hw.2 e he using 1
    apply sum_congr rfl
    intro v hv
    exact if_pos (H.edge_subset e he hv)

theorem fractional_cover_minimax (H : Hypergraph) {γ : ℕ → ℝ}
    (hγ : H.EdgeWeight γ) {θ : ℝ} (hθ : 0 < θ ∧ θ < 1) :
    ∃ w, H.ModularWeight w ∧ ∀ x, H.FractionalBalanced γ θ x →
      H.beta θ γ ≤ ∑ v ∈ H.vertices, w v * x v := by
  let X := H.separatorCube γ θ
  let W := H.modularCube
  let f : (ℕ → ℝ) → (ℕ → ℝ) → ℝ := fun x w => ∑ v ∈ H.vertices, w v * x v
  have neX : X.Nonempty := ⟨_, H.separator_restrict (H.full_fractional_separator hγ hθ).1⟩
  have neW : W.Nonempty := ⟨0, by simp [W, modularCube]⟩
  have cX : Convex ℝ X := H.convex_separatorCube (fun e he => (hγ.1 e he).1) θ
  have cW : Convex ℝ W := H.convex_modularCube
  have contX (w : ℕ → ℝ) : Continuous (fun x => f x w) :=
    continuous_finsetSum _ (fun v _ => continuous_const.mul (continuous_apply v))
  have contW (x : ℕ → ℝ) : Continuous (f x) :=
    continuous_finsetSum _ (fun v _ => (continuous_apply v).mul continuous_const)
  have linX (w x y : ℕ → ℝ) (a b : ℝ) : f (a • x + b • y) w = a * f x w + b * f y w := by
    simp [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, sum_add_distrib, mul_sum, mul_left_comm]
  have linW (x w z : ℕ → ℝ) (a b : ℝ) : f x (a • w + b • z) = a * f x w + b * f x z := by
    simp [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib, mul_sum, mul_assoc]
  have cv (w : ℕ → ℝ) : ConvexOn ℝ X (fun x => f x w) := by
    refine ⟨cX, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (linX w x y a b).le
  have cc (x : ℕ → ℝ) : ConcaveOn ℝ W (f x) := by
    refine ⟨cW, ?_⟩
    intro w hw z hz a b ha hb hab
    exact (linW x w z a b).ge
  obtain ⟨x0, hx0, w0, hw0, hsaddle⟩ := Sion.exists_isSaddlePointOn
    neX cX (H.compact_separatorCube γ θ)
    (fun w _ => (contX w).continuousOn.lowerSemicontinuousOn)
    (fun w _ => (cv w).quasiconvexOn)
    cW neW H.compact_modularCube
    (fun x _ => (contW x).continuousOn.upperSemicontinuousOn)
    (fun x _ => (cc x).quasiconcaveOn)
  have hx0bal : H.FractionalBalanced γ θ x0 := (H.mem_separatorCube hx0.1).mp hx0
  obtain ⟨w, hw, hdual, _⟩ := H.cover_duality hx0bal.1
  have hbeta : H.beta θ γ ≤ H.coverCost x0 := by
    refine csInf_le ⟨0, ?_⟩ ⟨x0, hx0bal, rfl⟩
    rintro r ⟨x, hx, rfl⟩
    exact H.coverCost_nonneg x
  refine ⟨w0, ⟨fun v => hw0.1.1 v, hw0.2⟩, ?_⟩
  intro x hx
  have hs := hsaddle _ (H.separator_restrict hx) _ (H.modular_restrict hw)
  have hleft : f x0 (fun v => if v ∈ H.vertices then w v else 0) = H.coverCost x0 := by
    rw [hdual]
    exact sum_congr rfl (fun v hv => by simp [hv])
  have hright : f (fun v => if v ∈ H.vertices then x v else 0) w0 =
      ∑ v ∈ H.vertices, w0 v * x v := by
    exact sum_congr rfl (fun v hv => by simp [hv])
  rw [hleft, hright] at hs
  exact hbeta.trans hs


theorem beta_le_adw (H : Hypergraph) {γ : ℕ → ℝ} (hγ : H.EdgeWeight γ)
    {θ : ℝ} (hθ : 1 / 2 ≤ θ ∧ θ < 1) : H.beta θ γ ≤ H.adw := by
  have hθ' : 0 < θ ∧ θ < 1 := ⟨by linarith [hθ.1], hθ.2⟩
  obtain ⟨w, hw, hminimax⟩ := H.fractional_cover_minimax hγ hθ'
  apply le_trans ?_ (H.optimal_modular_le_adw hw)
  refine le_csInf ⟨_, 0, H.oneBag, rfl⟩ ?_
  rintro r ⟨n, D, rfl⟩
  obtain ⟨t, ht⟩ := H.balanced_bag hγ D
  have htθ : H.IntegralBalanced γ θ (D.bag t) := by
    refine ⟨ht.1, ?_⟩
    intro K hK
    exact (ht.2 K hK).trans (mul_le_mul_of_nonneg_right hθ.1 hγ.2.le)
  have hfrac := (H.indicator_equivalence hγ hθ' (D.bag_subset t)).mpr htθ
  have hdot := hminimax (indicator (D.bag t)) hfrac
  have hsum : (∑ v ∈ H.vertices, w v * indicator (D.bag t) v) =
      modularValue w (D.bag t) := by
    simp only [indicator, mul_ite, mul_one, mul_zero, ← sum_filter, modularValue]
    congr 1
    ext v
    simp only [mem_filter]
    exact ⟨And.right, fun hv => ⟨D.bag_subset t hv, hv⟩⟩
  rw [hsum] at hdot
  exact hdot.trans (le_csSup (Set.finite_range _).bddAbove ⟨t, rfl⟩)

theorem fractional_separators_le_adw (H : Hypergraph) {θ : ℝ}
    (hθ : 1 / 2 ≤ θ ∧ θ < 1) : H.fsep θ ≤ H.adw := by
  refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
  rintro r (rfl | ⟨W, hW, γ, hγ, rfl⟩)
  · exact H.elementary_width_bounds.1
  · exact ((H.induce W).beta_le_adw hγ hθ).trans (H.width_hereditary W).1

/-- Existence part of Korchemna--Lokshtanov--Saurabh--Surianarayanan--Xue,
Theorem 5.6, arXiv:2409.20172v1. The numerical factors are literal:
`Real.log` represents ln, and division by `Real.log 2` represents log base 2.
We import only the nontrivial branch (the empty set is not already balanced).
This restriction avoids the printed bound's negative-log small-cost issue;
it is an additional hypothesis, not a claim that it appears in the source.
The running-time conclusion is outside this existence formalization. -/
theorem cited_rounding_theorem_5_6 (rounding : ExternalRounding) (H : Hypergraph) (γ x : ℕ → ℝ) (φ : ℝ)
    (hφ : 0 < φ ∧ φ < 1)
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e ∧ γ e ≤ 1)
    (hx : H.FractionalBalanced γ φ x)
    (hnontrivial : ¬ H.IntegralBalanced γ ((1 + 3 * φ) / (2 + 2 * φ)) ∅) :
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0),
      H.IntegralBalanced γ ((1 + 3 * φ) / (2 + 2 * φ)) S ∧
      H.setCoverCost S ≤
        (min (8 + 4 * Real.log
          ((H.induce (H.vertices.filter (fun v => x v ≠ 0))).independenceNumber : ℝ))
          (6 * (H.degeneracy : ℝ)) + 1) *
        ((44 + 8 * (Real.log (H.coverCost x / (1 - φ)) / Real.log 2)) / (1 - φ)) *
        H.coverCost x := by
  exact rounding H γ x φ hφ hγ hx hnontrivial

theorem rounding_structural_bound (d a : ℕ) :
    min (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ)) + 1 ≤
      9 * (1 + min (d : ℝ) (Real.log (2 + (a : ℝ)))) := by
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg _
  have hl : 0 ≤ Real.log (2 + (a : ℝ)) := Real.log_nonneg (by linarith)
  have hal : Real.log (a : ℝ) ≤ Real.log (2 + (a : ℝ)) := by
    by_cases h : a = 0
    · simpa [h] using hl
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h) (by linarith)
  rcases le_total (d : ℝ) (Real.log (2 + (a : ℝ))) with h | h
  · rw [min_eq_left h]
    have := min_le_right (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ))
    have : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    linarith [min_le_right (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ))]
  · rw [min_eq_right h]
    linarith [min_le_left (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ))]

theorem rounding_cost_bound {q : ℝ} (hq : 0 ≤ q) :
    ((44 + 8 * (Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2)) /
      (1 - (1 / 2 : ℝ))) * q ≤
      (120 / Real.log 2) * (q + 1) * Real.log (2 + q) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : 0 < Real.log (2 + q) := Real.log_pos (by linarith)
  have hlow : Real.log 2 ≤ Real.log (2 + q) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog : Real.log (q / (1 - (1 / 2 : ℝ))) ≤
      Real.log 2 + Real.log (2 + q) := by
    by_cases hq0 : q = 0
    · simp only [hq0, zero_div, Real.log_zero, add_zero]
      positivity
    · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
      calc
        Real.log (q / (1 - (1 / 2 : ℝ))) ≤ Real.log (2 * (2 + q)) :=
          Real.log_le_log (by positivity) (by norm_num; linarith)
        _ = _ := Real.log_mul (by norm_num) (by linarith)
  have hb : (44 + 8 * (Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2)) /
      (1 - (1 / 2 : ℝ)) ≤ (120 / Real.log 2) * Real.log (2 + q) := by
    norm_num at hlog ⊢
    field_simp at hlog ⊢
    nlinarith
  calc
    _ ≤ ((120 / Real.log 2) * Real.log (2 + q)) * q := mul_le_mul_of_nonneg_right hb hq
    _ ≤ ((120 / Real.log 2) * Real.log (2 + q)) * (q + 1) := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      positivity
    _ = _ := by ring

/-- The paper's regularized consequence of the external theorem.
The specialization and numerical comparison must be proved locally. -/
theorem balanced_separator_rounding (rounding : ExternalRounding) : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (H : Hypergraph) (γ x : ℕ → ℝ), H.EdgeWeight γ →
    H.FractionalBalanced γ (1 / 2) x →
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralBalanced γ (5 / 6) S ∧
      H.setCoverCost S ≤ C₀ *
        (1 + min (H.degeneracy : ℝ)
          (Real.log (2 + ((H.induce (H.vertices.filter (fun v => x v ≠ 0))).independenceNumber : ℝ)))) *
        (H.coverCost x + 1) * Real.log (2 + H.coverCost x) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨9 * (120 / Real.log 2), by positivity, ?_⟩
  intro H γ x hγ hx
  let a := (H.induce (H.vertices.filter (fun v => x v ≠ 0))).independenceNumber
  let d := H.degeneracy
  let q := H.coverCost x
  have hq : 0 ≤ q := H.coverCost_nonneg x
  have hl : 0 ≤ Real.log (2 + q) := Real.log_nonneg (by linarith)
  have hfactor : 0 ≤ 1 + min (d : ℝ) (Real.log (2 + (a : ℝ))) := by
    have : 0 ≤ Real.log (2 + (a : ℝ)) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) a; linarith)
    positivity
  by_cases hempty : H.IntegralBalanced γ (5 / 6) ∅
  · refine ⟨∅, empty_subset _, hempty, ?_⟩
    have hc : H.setCoverCost ∅ ≤ 0 := by
      have hh : H.Cover (indicator ∅) (fun _ => 0) := by
        constructor
        · intros; norm_num
        · intros; simp [indicator]
      simpa [setCoverCost] using H.coverCost_le hh
    apply hc.trans
    change 0 ≤ (9 * (120 / Real.log 2)) *
      (1 + min (d : ℝ) (Real.log (2 + (a : ℝ)))) * (q + 1) * Real.log (2 + q)
    positivity
  · have hn : ¬ H.IntegralBalanced γ
        ((1 + 3 * (1 / 2 : ℝ)) / (2 + 2 * (1 / 2 : ℝ))) ∅ := by
      norm_num
      exact hempty
    obtain ⟨S, hS, hbal, hcost⟩ := cited_rounding_theorem_5_6 rounding H γ x (1 / 2)
      (by norm_num) hγ.1 hx hn
    refine ⟨S, hS, by norm_num at hbal; exact hbal, ?_⟩
    have ha : 0 ≤ Real.log (a : ℝ) := by
      by_cases ha0 : a = 0
      · simp [ha0]
      · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha0)
    have hA : 0 ≤ min (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ)) + 1 := by
      positivity
    have hB : 0 ≤ (120 / Real.log 2) * (q + 1) * Real.log (2 + q) := by positivity
    calc
      H.setCoverCost S ≤ _ := hcost
      _ = (min (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ)) + 1) *
          (((44 + 8 * (Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2)) /
            (1 - (1 / 2 : ℝ))) * q) := by dsimp [a, d, q]; ring
      _ ≤ (min (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ)) + 1) *
          ((120 / Real.log 2) * (q + 1) * Real.log (2 + q)) :=
        mul_le_mul_of_nonneg_left (rounding_cost_bound hq) hA
      _ ≤ (9 * (1 + min (d : ℝ) (Real.log (2 + (a : ℝ))))) *
          ((120 / Real.log 2) * (q + 1) * Real.log (2 + q)) :=
        mul_le_mul_of_nonneg_right (rounding_structural_bound d a) hB
      _ = _ := by dsimp [a, d, q]; ring


theorem width_scale_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (a + 1) * Real.log (2 + a) ≤ (b + 1) * Real.log (2 + b) := by
  exact mul_le_mul (by linarith) (Real.log_le_log (by linarith) (by linarith))
    (Real.log_nonneg (by linarith)) (by linarith)

/-- Pass to the optimum by continuity; attainment is not required. -/
theorem scale_infimum {A : Set ℝ} (hne : A.Nonempty) (hA : ∀ r ∈ A, 0 ≤ r)
    {c : ℝ} (hc : 0 ≤ c) :
    c * (sInf A + 1) * Real.log (2 + sInf A) =
      sInf ((fun r => c * (r + 1) * Real.log (2 + r)) '' A) := by
  have hinf : 0 ≤ sInf A := le_csInf hne hA
  have hlog : ContinuousAt (fun r : ℝ => Real.log (2 + r)) (sInf A) :=
    (continuousAt_const.add continuousAt_id).log (by change 2 + sInf A ≠ 0; linarith)
  have hcont : ContinuousAt (fun r : ℝ => c * (r + 1) * Real.log (2 + r)) (sInf A) :=
    (continuousAt_const.mul (continuousAt_id.add continuousAt_const)).mul hlog
  apply MonotoneOn.map_csInf_of_continuousWithinAt hcont.continuousWithinAt ?_ hne ⟨0, hA⟩
  intro a ha b hb hab
  convert mul_le_mul_of_nonneg_left (width_scale_mono (hA a ha) hab) hc using 1 <;> ring

theorem round_hereditary (rounding : ExternalRounding) : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ H : Hypergraph,
    H.Connected → H.sep (5 / 6) ≤ C₁ * H.structuralFactor *
      (H.fsep (1 / 2) + 1) * Real.log (2 + H.fsep (1 / 2)) := by
  obtain ⟨C₀, hC₀, hround⟩ := balanced_separator_rounding rounding
  refine ⟨C₀, hC₀, ?_⟩
  intro H _hH
  have hf0 : 0 ≤ H.fsep (1 / 2) := Real.sSup_nonneg' ⟨0, Set.mem_insert _ _, le_rfl⟩
  have hl0 : 0 ≤ H.structuralFactor := by
    apply add_nonneg zero_le_one
    exact le_min (Nat.cast_nonneg _) (Real.log_nonneg (by
      have := Nat.cast_nonneg (α := ℝ) H.independenceNumber; linarith))
  have hcoeff : 0 ≤ C₀ * H.structuralFactor := mul_nonneg hC₀.le hl0
  have hlog0 : 0 ≤ Real.log (2 + H.fsep (1 / 2)) := Real.log_nonneg (by linarith)
  refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
  rintro r (rfl | ⟨W, hW, γ, hγ, rfl⟩)
  · positivity
  · let J := H.induce W
    let A : Set ℝ := {r | ∃ x, J.FractionalBalanced γ (1 / 2) x ∧ r = J.coverCost x}
    have hfull := J.full_fractional_separator hγ (θ := 1 / 2) (by norm_num)
    have hne : A.Nonempty := ⟨_, indicator J.vertices, hfull.1, rfl⟩
    have hA : ∀ a ∈ A, 0 ≤ a := by
      rintro a ⟨x, hx, rfl⟩
      exact J.coverCost_nonneg x
    have hinst : J.integralOptimum (5 / 6) γ ≤
        C₀ * H.structuralFactor * (J.beta (1 / 2) γ + 1) * Real.log (2 + J.beta (1 / 2) γ) := by
      change _ ≤ (C₀ * H.structuralFactor) * (sInf A + 1) * Real.log (2 + sInf A)
      rw [scale_infimum hne hA hcoeff]
      refine le_csInf (hne.image _) ?_
      rintro r ⟨a, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨S, hS, hbal, hcost⟩ := hround J γ x hγ hx
      have hopt : J.integralOptimum (5 / 6) γ ≤ J.setCoverCost S := by
        refine csInf_le ⟨0, ?_⟩ ⟨S, hbal, rfl⟩
        rintro r ⟨T, hT, rfl⟩
        exact J.coverCost_nonneg (indicator T)
      have hdeg : (J.degeneracy : ℝ) ≤ H.degeneracy := by
        exact_mod_cast (H.structure_hereditary W).1
      have halpha : (J.induce (J.vertices.filter (fun v => x v ≠ 0))).independenceNumber ≤
          H.independenceNumber :=
        (J.structure_hereditary _).2.trans (H.structure_hereditary W).2
      have hfactor : 1 + min (J.degeneracy : ℝ)
          (Real.log (2 + ((J.induce (J.vertices.filter (fun v => x v ≠ 0))).independenceNumber : ℝ))) ≤
          H.structuralFactor := by
        unfold structuralFactor
        apply add_le_add le_rfl
        apply min_le_min hdeg
        apply Real.log_le_log (by positivity)
        exact_mod_cast (Nat.add_le_add_left halpha 2)
      have hx0 := J.coverCost_nonneg x
      have hxl : 0 ≤ Real.log (2 + J.coverCost x) := Real.log_nonneg (by linarith)
      exact hopt.trans (hcost.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor hC₀.le) (by linarith)) hxl))
    apply hinst.trans
    have hb0 := (J.beta_bounds hγ (θ := 1 / 2) (by norm_num)).1
    have hb := H.beta_le_fsep hW hγ (θ := 1 / 2) (by norm_num)
    convert mul_le_mul_of_nonneg_left (width_scale_mono hb0 hb) hcoeff using 1 <;> ring

theorem connected_width_comparison (rounding : ExternalRounding) : ∃ C : ℝ, 0 < C ∧ ∀ H : Hypergraph,
    H.Connected → H.fhw ≤ C * H.structuralFactor *
      (H.adw + 1) * Real.log (2 + H.adw) := by
  obtain ⟨C₁, hC₁, hround⟩ := round_hereditary rounding
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨7 * (C₁ + (Real.log 2)⁻¹), by positivity, ?_⟩
  intro H hH
  have ha := (H.elementary_width_bounds).1
  have hl : 1 ≤ H.structuralFactor := by
    unfold structuralFactor
    have hn : (0 : ℝ) ≤ H.degeneracy := Nat.cast_nonneg _
    have hlog : 0 ≤ Real.log (2 + (H.independenceNumber : ℝ)) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) H.independenceNumber; linarith)
    have := le_min hn hlog
    linarith
  have hf : 0 ≤ H.fsep (1 / 2) :=
    Real.sSup_nonneg' ⟨0, Set.mem_insert _ _, le_rfl⟩
  have hscale := width_scale_mono hf (H.fractional_separators_le_adw (by norm_num))
  have hs : H.sep (5 / 6) ≤ C₁ * H.structuralFactor *
      ((H.adw + 1) * Real.log (2 + H.adw)) := by
    refine (hround H hH).trans ?_
    convert mul_le_mul_of_nonneg_left hscale (mul_nonneg hC₁.le (by linarith : 0 ≤ H.structuralFactor)) using 1 <;> ring
  have ht : Real.log 2 ≤ H.structuralFactor *
      ((H.adw + 1) * Real.log (2 + H.adw)) := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 + H.adw)
    have hprod : 1 ≤ H.structuralFactor * (H.adw + 1) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ H.structuralFactor) ha]
    calc
      Real.log 2 ≤ Real.log (2 + H.adw) := hlog
      _ ≤ (H.structuralFactor * (H.adw + 1)) * Real.log (2 + H.adw) :=
        le_mul_of_one_le_left (hlog2.le.trans hlog) hprod
      _ = _ := by ring
  have habs : 1 ≤ (Real.log 2)⁻¹ * (H.structuralFactor *
      ((H.adw + 1) * Real.log (2 + H.adw))) := by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hlog2).mpr (by simpa using ht)
  have hc := H.recursive_separator_decomposition (η := 5 / 6) (by norm_num)
  norm_num at hc
  calc
    H.fhw ≤ 7 * (H.sep (5 / 6) + 1) := hc
    _ ≤ 7 * (C₁ * H.structuralFactor * ((H.adw + 1) * Real.log (2 + H.adw)) +
        (Real.log 2)⁻¹ * (H.structuralFactor * ((H.adw + 1) * Real.log (2 + H.adw)))) := by linarith
    _ = _ := by ring

/-- The regularized comparison used to derive the manuscript statement. -/
theorem regularized_main_width_comparison (rounding : ExternalRounding) : ∃ C : ℝ, 0 < C ∧ ∀ H : Hypergraph,
    H.fhw ≤ C * H.componentFactor * (H.adw + 1) * Real.log (2 + H.adw) := by
  obtain ⟨C, hC, hconnected⟩ := connected_width_comparison rounding
  refine ⟨C, hC, ?_⟩
  intro H
  have ha := H.elementary_width_bounds.1
  have hl : 0 ≤ H.componentFactor := by have := H.componentFactor_ge_one; linarith
  have hlog : 0 ≤ Real.log (2 + H.adw) := Real.log_nonneg (by linarith)
  rw [H.component_reduction.1]
  refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
  rintro r (rfl | ⟨K, hK, rfl⟩)
  · positivity
  · have hak := (H.induce K).elementary_width_bounds.1
    have hscale := width_scale_mono hak (H.width_hereditary K).1
    have hfactor := H.component_factor_le_componentFactor hK
    calc
      (H.induce K).fhw ≤ C * (H.induce K).structuralFactor *
          (((H.induce K).adw + 1) * Real.log (2 + (H.induce K).adw)) := by
        convert hconnected (H.induce K) (H.component_connected hK) using 1 <;> ring
      _ ≤ C * H.componentFactor * ((H.adw + 1) * Real.log (2 + H.adw)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hfactor hC.le) hscale
          (mul_nonneg (by linarith) (Real.log_nonneg (by linarith))) (mul_nonneg hC.le hl)
      _ = _ := by ring

/-- Auxiliary reverse comparison for the internal componentwise factor. -/
theorem quantitative_reverse_comparison (rounding : ExternalRounding) : ∃ c : ℝ, 0 < c ∧ ∀ H : Hypergraph,
    H.adw + 1 ≤ H.subw + 1 ∧
    c * (H.fhw / (H.componentFactor * Real.log (2 + H.fhw))) ≤ H.adw + 1 := by
  obtain ⟨C, hC, hmain⟩ := regularized_main_width_comparison rounding
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro H
  have hh := H.width_hierarchy
  have ha := H.elementary_width_bounds.1
  have hf := H.elementary_width_bounds.2.2
  have hl : 0 < H.componentFactor := lt_of_lt_of_le (by norm_num) H.componentFactor_ge_one
  have hlog : 0 < Real.log (2 + H.fhw) := Real.log_pos (by linarith)
  have hlogs : Real.log (2 + H.adw) ≤ Real.log (2 + H.fhw) :=
    Real.log_le_log (by linarith) (by linarith [hh.1.trans hh.2])
  have hm : H.fhw ≤ C * H.componentFactor * (H.adw + 1) * Real.log (2 + H.fhw) :=
    (hmain H).trans (mul_le_mul_of_nonneg_left hlogs (by positivity))
  refine ⟨by linarith [hh.1], ?_⟩
  calc
    C⁻¹ * (H.fhw / (H.componentFactor * Real.log (2 + H.fhw))) =
        H.fhw / (C * (H.componentFactor * Real.log (2 + H.fhw))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ H.adw + 1 := (div_le_iff₀ (mul_pos hC (mul_pos hl hlog))).mpr (by nlinarith [hm])

/-- The former combined statement, retained with its internal componentwise factor. -/
theorem regularized_width_comparisons (rounding : ExternalRounding) :
    (∃ C : ℝ, 0 < C ∧ ∀ H : Hypergraph,
      H.fhw ≤ C * H.componentFactor * (H.adw + 1) * Real.log (2 + H.adw)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ H : Hypergraph,
      H.adw + 1 ≤ H.subw + 1 ∧
      c * (H.fhw / (H.componentFactor * Real.log (2 + H.fhw))) ≤ H.adw + 1) := by
  exact ⟨regularized_main_width_comparison rounding, quantitative_reverse_comparison rounding⟩

theorem degeneracy_ge_one (H : Hypergraph) (hne : H.vertices.Nonempty) :
    1 ≤ H.degeneracy := by
  obtain ⟨v, hv⟩ := hne
  obtain ⟨e, he, hve⟩ := H.no_isolated v hv
  have hd : ∀ S ⊆ H.incidenceVertices, S.Nonempty →
      ∃ z ∈ S, (S.filter (H.incidence.Adj z)).card ≤ H.degeneracy := by
    refine csInf_mem (s := {d : ℕ | ∀ S ⊆ H.incidenceVertices, S.Nonempty →
      ∃ z ∈ S, (S.filter (H.incidence.Adj z)).card ≤ d}) ?_
    refine ⟨H.incidenceVertices.card, ?_⟩
    intro S hS hS'
    obtain ⟨z, hz⟩ := hS'
    exact ⟨z, hz, (card_filter_le _ _).trans (card_le_card hS)⟩
  have hsub : {Sum.inl v, Sum.inr e} ⊆ H.incidenceVertices := by
    simp [insert_subset_iff, singleton_subset_iff, incidenceVertices, hv, he]
  obtain ⟨z, hz, hdeg⟩ := hd _ hsub (by simp)
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl
  · simpa [filter_insert, filter_singleton, incidence, he, hve] using hdeg
  · simpa [filter_insert, filter_singleton, incidence, he, hve] using hdeg

theorem independenceNumber_ge_one (H : Hypergraph) (hne : H.vertices.Nonempty) :
    1 ≤ H.independenceNumber := by
  obtain ⟨v, hv⟩ := hne
  have hmem : {v} ∈ H.vertices.powerset.filter H.independent := by
    simp [independent, hv]
  have hh := Finset.le_sup (f := Finset.card) hmem
  simpa [independenceNumber] using hh

theorem lambda_ge_one (H : Hypergraph) (hne : H.vertices.Nonempty) :
    1 ≤ H.lambda := by
  exact le_min (by exact_mod_cast H.degeneracy_ge_one hne) (le_max_left _ _)

theorem structuralFactor_le_lambda (H : Hypergraph) (hne : H.vertices.Nonempty) :
    H.structuralFactor ≤ 4 * H.lambda := by
  have ha : (1 : ℝ) ≤ H.independenceNumber := by
    exact_mod_cast H.independenceNumber_ge_one hne
  have hd : (1 : ℝ) ≤ H.degeneracy := by exact_mod_cast H.degeneracy_ge_one hne
  let L := max 1 (Real.log (H.independenceNumber : ℝ) / Real.log 2)
  have hL : 1 ≤ L := le_max_left _ _
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h3le : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlog : Real.log (H.independenceNumber : ℝ) ≤ L := by
    have hh : Real.log (H.independenceNumber : ℝ) ≤ L * Real.log 2 :=
      (div_le_iff₀ h2).mp (le_max_right _ _)
    have := mul_le_mul_of_nonneg_left h2le (by linarith : 0 ≤ L)
    nlinarith
  have hb : Real.log (2 + (H.independenceNumber : ℝ)) ≤ 3 * L := by
    calc
      _ ≤ Real.log (3 * (H.independenceNumber : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 3 + Real.log (H.independenceNumber : ℝ) :=
        Real.log_mul (by norm_num) (by linarith)
      _ ≤ 3 * L := by linarith
  change 1 + min (H.degeneracy : ℝ) _ ≤ 4 * min (H.degeneracy : ℝ) L
  rcases le_total (H.degeneracy : ℝ) L with h | h
  · rw [min_eq_left h]
    have := min_le_left (H.degeneracy : ℝ) (Real.log (2 + (H.independenceNumber : ℝ)))
    linarith
  · rw [min_eq_right h]
    have := min_le_right (H.degeneracy : ℝ) (Real.log (2 + (H.independenceNumber : ℝ)))
    linarith

theorem componentFactor_le_structuralFactor (H : Hypergraph) :
    H.componentFactor ≤ H.structuralFactor := by
  unfold componentFactor structuralFactor
  apply add_le_add_right
  refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
  rintro r (rfl | ⟨K, hK, rfl⟩)
  · exact le_min (Nat.cast_nonneg _) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) H.independenceNumber; linarith))
  · apply min_le_min
    · exact_mod_cast (H.structure_hereditary K).1
    · apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.add_le_add_left (H.structure_hereditary K).2 2

/-- The current Theorem 1.1, with one constant for both width ranges.
Nonemptiness matches the input convention in the manuscript. -/
theorem theorem_1_1 (rounding : ExternalRounding) : MainWidthComparison := by
  obtain ⟨C, hC, hmain⟩ := regularized_main_width_comparison rounding
  refine ⟨48 * C, by positivity, ?_⟩
  intro H hne
  have ha := H.elementary_width_bounds.1
  have hl : 0 ≤ H.lambda := le_trans (by norm_num) (H.lambda_ge_one hne)
  have hfactor := H.componentFactor_le_structuralFactor.trans (H.structuralFactor_le_lambda hne)
  have hb : H.fhw ≤ (4 * C) * H.lambda * ((H.adw + 1) * Real.log (2 + H.adw)) := by
    have hh := (hmain H).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor hC.le)
        (by linarith : 0 ≤ H.adw + 1)) (Real.log_nonneg (by linarith)))
    calc
      H.fhw ≤ C * (4 * H.lambda) * (H.adw + 1) * Real.log (2 + H.adw) := hh
      _ = _ := by ring
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  constructor
  · intro hlarge
    have hlog : 0 ≤ Real.log H.adw := Real.log_nonneg (by linarith)
    have hscale : (H.adw + 1) * Real.log (2 + H.adw) ≤
        4 * H.adw * (Real.log H.adw / Real.log 2) := by
      have hupper : Real.log (2 + H.adw) ≤ 2 * Real.log H.adw := by
        calc
          _ ≤ Real.log (H.adw * H.adw) := Real.log_le_log (by linarith) (by nlinarith)
          _ = _ := by rw [Real.log_mul (by linarith) (by linarith)]; ring
      have hdiv : Real.log H.adw ≤ Real.log H.adw / Real.log 2 := by
        apply (le_div_iff₀ h2).mpr
        nlinarith
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hdiv)]
    have hh := hb.trans (mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 4 * C * H.lambda))
    have hp : 0 ≤ C * H.lambda * H.adw * (Real.log H.adw / Real.log 2) := by positivity
    nlinarith
  · intro hsmall
    have hscale : (H.adw + 1) * Real.log (2 + H.adw) ≤ 9 := by
      have hh := Real.log_le_sub_one_of_pos (by linarith : 0 < 2 + H.adw)
      have hn : 0 ≤ Real.log (2 + H.adw) := Real.log_nonneg (by linarith)
      nlinarith
    have hh := hb.trans (mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 4 * C * H.lambda))
    nlinarith [mul_nonneg hC.le hl]

end Hypergraph
end Paper
