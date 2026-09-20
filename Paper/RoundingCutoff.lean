import Paper.RoundingPaths
import Paper.RoundingSeparation

noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

namespace Paper.Hypergraph

/-- The repaired layer argument, now instantiated with actual hypergraph balls. -/
theorem cutoff_good_annulus (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (Q : Finset ℕ) {c : ℕ}
    (hc : c ∈ H.vertices ∩ Q) {r q : ℝ} (hr : 0 < r)
    (hK : r / 2 ≤ H.coverCost x)
    (hq0 : 0 ≤ q) (hq : ∀ v ∈ H.vertices ∩ Q, x v ≤ q)
    (hsmall : q < (r / (9 + 2 * Real.logb 2 (H.coverCost x / r))) / 2)
    (hout : ∃ v, (H.induce Q).primal.Reachable c v ∧
      r / 4 < (H.induce Q).vertexDistance x c v) :
    let δ := r / (9 + 2 * Real.logb 2 (H.coverCost x / r))
    ∃ s : ℝ, r / 4 ≤ s ∧ s + 3 * δ / 2 ≤ r ∧
      H.coverCost (restrictDemand x
        (H.roundingBall x Q c (s + 3 * δ / 2) \ H.roundingBall x Q c (s + δ / 2))) ≤
        H.coverCost (restrictDemand x (H.roundingBall x Q c s)) := by
  let δ := r / (9 + 2 * Real.logb 2 (H.coverCost x / r))
  have hδ : 0 < δ := by change q < δ / 2 at hsmall; linarith
  obtain ⟨N, hN, hrad, hbudget, hseednum⟩ := cutoff_layer_parameters hr hK
  let s : ℕ → ℝ := fun i => r / 4 + (i : ℝ) * (3 * δ / 2)
  let B := fun t => H.roundingBall x Q c t
  let a := fun i => H.coverCost (restrictDemand x (B (s i)))
  let ℓ := fun i => H.coverCost (restrictDemand x (B (s (i + 1)) \ B (s i + δ / 2)))
  have hs : ∀ i, s (i + 1) = s i + 3 * δ / 2 := by intro i; dsimp [s]; push_cast; ring
  have hseed : 5 * r / 56 ≤ a 0 := by
    have h := H.roundingBall_seed hx Q hc hq hout
    have hn := hseednum q hsmall
    dsimp [a, B, s]
    simpa using hn.trans h.le
  have hadd : ∀ i < N, a i + ℓ i ≤ a (i + 1) := by
    intro i hi
    have hsep : ∀ e ∈ H.edges, Disjoint (H.edge e) (B (s i)) ∨
        Disjoint (H.edge e) (B (s (i + 1)) \ B (s i + δ / 2)) := by
      intro e he
      rcases H.roundingBall_no_crossing_edge hx Q hc hsmall hq he (s := s i) with h | h
      · exact Or.inl h
      · apply Or.inr
        apply h.mono_right
        intro v hv
        exact mem_sdiff.mpr ⟨(mem_filter.mp (mem_sdiff.mp hv).1).1, (mem_sdiff.mp hv).2⟩
    apply (H.separated_restrictDemand_cost_add_le x _ _ hsep).trans
    apply H.restrictDemand_cost_mono hx
    apply union_subset
    · apply H.roundingBall_mono
      rw [hs]
      linarith
    · exact sdiff_subset
  have hupper : a N ≤ H.coverCost x := H.restrictDemand_cost_le hx _
  obtain ⟨i, hi, hgood⟩ := cutoff_layer_exists a ℓ N hseed hbudget hupper hadd
  refine ⟨s i, ?_, ?_, ?_⟩
  · dsimp [s]
    have : 0 ≤ (i : ℝ) * (3 * δ / 2) := mul_nonneg (Nat.cast_nonneg _) (by positivity)
    linarith
  · have hiN : (i + 1 : ℝ) ≤ N := by exact_mod_cast (show i + 1 ≤ N by omega)
    have hh := mul_le_mul_of_nonneg_right hiN (show 0 ≤ 3 * δ / 2 by positivity)
    change r / 4 + (N : ℝ) * (3 * δ / 2) ≤ r at hrad
    dsimp [s]
    linarith
  · simpa only [ℓ, a, hs] using hgood

/-- A cut-off piece and its boundary, with ambient volume and cover costs. -/
structure CutoffPiece (H : Hypergraph) (γ x : ℕ → ℝ) (Q : Finset ℕ)
    (volumeBound costFactor : ℝ) where
  piece : Finset ℕ
  separator : Finset ℕ
  nonempty : piece.Nonempty
  piece_subset : piece ⊆ Q
  separator_subset : separator ⊆ Q
  disjoint : Disjoint piece separator
  support : separator ⊆ H.vertices.filter (fun v => x v ≠ 0)
  separated : ∀ e ∈ H.edges, Disjoint (H.edge e) piece ∨
    Disjoint (H.edge e) (Q \ (piece ∪ separator))
  volume_le : H.edgeVolume γ piece ≤ volumeBound
  cost_le : H.setCoverCost separator ≤ costFactor * H.coverCost (restrictDemand x piece)

theorem component_cutoffPiece (H : Hypergraph) {γ x : ℕ → ℝ} {φ r C : ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (hx : H.FractionalBalanced γ φ x)
    (hr : r < 1) (hC : 0 ≤ C) {Q : Finset ℕ} (hQ : Q ⊆ H.vertices)
    {c : ℕ} (hc : c ∈ Q)
    (hball : ∀ v, (H.induce Q).primal.Reachable c v → (H.induce Q).vertexDistance x c v ≤ r) :
    Nonempty (H.CutoffPiece γ x Q (φ / (1 - r) * ∑ e ∈ H.edges, γ e) C) := by
  have hcJ : c ∈ (H.induce Q).vertices := mem_inter.mpr ⟨hQ hc, hc⟩
  obtain ⟨P, hP, hcP⟩ := (H.induce Q).exists_component_of_mem hcJ
  have hPV := mem_powerset.mp (mem_filter.mp hP).1
  have hPQ : P ⊆ Q := fun v hv => (mem_inter.mp (hPV hv)).2
  have hPB : P ⊆ H.roundingBall x Q c r := by
    intro v hv
    exact mem_filter.mpr ⟨hPV hv,
      hball v (((H.induce Q).component_mem_iff_reachable hP hcP (hPV hv)).mp hv)⟩
  refine ⟨{
    piece := P
    separator := ∅
    nonempty := ⟨c, hcP⟩
    piece_subset := hPQ
    separator_subset := empty_subset _
    disjoint := by simp
    support := empty_subset _
    separated := ?_
    volume_le := (H.edgeVolume_mono hγ hPB).trans (H.roundingBall_volume_le hγ hx Q hcJ hr)
    cost_le := ?_ }⟩
  · intro e he
    by_contra hn
    obtain ⟨hu, hv⟩ := not_or.mp hn
    obtain ⟨u, hue, huP⟩ := not_disjoint_iff.mp hu
    obtain ⟨v, hve, hvQ⟩ := not_disjoint_iff.mp hv
    have hv := mem_sdiff.mp hvQ
    have hnP : v ∉ P := by simpa using hv.2
    have huv : u ≠ v := by intro h; subst v; exact hnP huP
    have hadj := (H.primal_induce_adj Q (hPQ huP) hv.1).mpr ⟨huv, e, he, hue, hve⟩
    exact hnP (((H.induce Q).component_mem_iff_reachable hP huP
      (mem_inter.mpr ⟨hQ hv.1, hv.1⟩)).mpr hadj.reachable)
  · have hz : H.setCoverCost ∅ = 0 := H.coverCost_eq_zero_of_nonpos
      (fun v hv => by simp [indicator])
    rw [hz]
    exact mul_nonneg hC (H.coverCost_nonneg _)

/-- The graph-theoretic cut-off construction from a two-terminal rounding rule. -/
theorem cutoff_from_rounding (H : Hypergraph) {γ x : ℕ → ℝ} {φ r C : ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (hx : H.FractionalBalanced γ φ x)
    (hr : 0 < r ∧ r < 1) (hC : 0 ≤ C) (hK : r / 2 ≤ H.coverCost x)
    {Q : Finset ℕ} (hQ : Q ⊆ H.vertices) (hne : Q.Nonempty)
    (hsmall : ∀ v ∈ Q, x v < (r / (9 + 2 * Real.logb 2 (H.coverCost x / r))) / 2)
    (hround : ∀ (A B : Finset ℕ) (z : ℕ → ℝ),
      A ⊆ (H.induce Q).vertices → B ⊆ (H.induce Q).vertices →
      (H.induce Q).FractionalSeparator A B z →
      (∀ v ∈ (H.induce Q).vertices, z v ≠ 0 → x v ≠ 0) →
      ∃ S ⊆ (H.induce Q).vertices.filter (fun v => z v ≠ 0),
        (H.induce Q).IntegralSeparator A B S ∧
        H.setCoverCost S ≤ C * (H.induce Q).coverCost z) :
    Nonempty (H.CutoffPiece γ x Q (φ / (1 - r) * ∑ e ∈ H.edges, γ e)
      (C * ((18 + 4 * Real.logb 2 (H.coverCost x / r)) / r))) := by
  let δ := r / (9 + 2 * Real.logb 2 (H.coverCost x / r))
  obtain ⟨c, hc⟩ := hne
  obtain ⟨vmax, hvmax, hmax⟩ := Q.exists_max_image x ⟨c, hc⟩
  let q := x vmax
  have hq0 : 0 ≤ q := (hx.1 vmax (hQ hvmax)).1
  have hq : ∀ v ∈ H.vertices ∩ Q, x v ≤ q := fun v hv => hmax v (mem_inter.mp hv).2
  have hqsmall : q < δ / 2 := hsmall vmax hvmax
  have hδ : 0 < δ := by linarith
  have hgap : 0 < δ - q := by linarith
  have hn : ∀ v ∈ H.vertices, 0 ≤ x v := fun v hv => (hx.1 v hv).1
  have hcJ : c ∈ (H.induce Q).vertices := mem_inter.mpr ⟨hQ hc, hc⟩
  have hcoef : (18 + 4 * Real.logb 2 (H.coverCost x / r)) / r = 2 / δ := by
    dsimp [δ]
    field_simp
    ring
  have hcoef0 : 0 ≤ C * ((18 + 4 * Real.logb 2 (H.coverCost x / r)) / r) := by
    rw [hcoef]
    positivity
  by_cases hout : ∃ v, (H.induce Q).primal.Reachable c v ∧
      r / 4 < (H.induce Q).vertexDistance x c v
  swap
  · apply H.component_cutoffPiece hγ hx hr.2 hcoef0 hQ hc
    intro v hv
    have hle : (H.induce Q).vertexDistance x c v ≤ r / 4 :=
      le_of_not_gt fun h => hout ⟨v, hv, h⟩
    linarith [hr.1]
  obtain ⟨s, hs, hsrad, hcost⟩ := H.cutoff_good_annulus hn Q hcJ hr.1 hK hq0 hq hqsmall hout
  let J := H.induce Q
  let a := s + δ / 2
  let b := s + 3 * δ / 2
  let A := H.roundingBall x Q c a
  let B := J.vertices \ H.roundingBall x Q c b
  let T := H.roundingBall x Q c b \ A
  let z := (δ - q)⁻¹ • restrictDemand x T
  have hA : A ⊆ J.vertices := filter_subset _ _
  have hB : B ⊆ J.vertices := sdiff_subset
  have hTQ : T ⊆ Q := fun v hv => (mem_inter.mp (mem_filter.mp (mem_sdiff.mp hv).1).1).2
  have hzexpr : ∀ v ∈ J.vertices, z v =
      if a < J.vertexDistance x c v ∧ J.vertexDistance x c v ≤ b then x v / (δ - q) else 0 := by
    intro v hv
    change v ∈ H.vertices ∩ Q at hv
    dsimp only [J]
    simp only [z, Pi.smul_apply, smul_eq_mul, restrictDemand, T, A, roundingBall,
      mem_sdiff, mem_filter, hv, true_and, not_le]
    split_ifs <;> simp_all [div_eq_mul_inv, mul_comm]
  have hzfrac : J.FractionalSeparator A B z := by
    have hf := J.annulus_fractionalSeparator (fun v hv => hn v (mem_inter.mp hv).1) hcJ hq
      (show q < (b - a) / 2 by dsimp [a, b]; linarith) hq0
    dsimp only at hf
    have hBexpr : J.vertices.filter (fun v => b < J.vertexDistance x c v) = B := by
      ext v
      simp only [B, roundingBall, mem_filter, mem_sdiff]
      change (v ∈ J.vertices ∧ b < J.vertexDistance x c v) ↔
        v ∈ J.vertices ∧ ¬ (v ∈ J.vertices ∧ J.vertexDistance x c v ≤ b)
      simp only [not_and, not_le]
      tauto
    rw [hBexpr] at hf
    apply J.fractionalSeparator_congr hA hf
    intro v hv
    rw [hzexpr v hv]
    have heq : b - a - q = δ - q := by dsimp [a, b]; ring
    rw [heq]
  have hzsupp : ∀ v ∈ J.vertices, z v ≠ 0 → x v ≠ 0 := by
    intro v hv hz hzero
    exact hz (by simp [z, restrictDemand, hzero])
  obtain ⟨S, hS, hsep, hScost⟩ := hround A B z hA hB hzfrac hzsupp
  have hST : S ⊆ T := by
    intro v hv
    have hne := (mem_filter.mp (hS hv)).2
    by_contra ht
    exact hne (by simp [z, restrictDemand, ht])
  have hSQ : S ⊆ Q := hST.trans hTQ
  have hSsupp : S ⊆ H.vertices.filter (fun v => x v ≠ 0) := by
    intro v hv
    exact mem_filter.mpr ⟨hQ (hSQ hv), hzsupp v (mem_filter.mp (hS hv)).1 (mem_filter.mp (hS hv)).2⟩
  have hAS : Disjoint A S := by
    apply disjoint_left.mpr
    intro v hvA hvS
    exact (mem_sdiff.mp (hST hvS)).2 hvA
  let P := J.separatorRegion A S
  have hPV : P ⊆ J.vertices \ S := J.separatorRegion_subset A S
  have hPQ : P ⊆ Q := fun v hv => (mem_inter.mp (mem_sdiff.mp (hPV hv)).1).2
  have hAP : A ⊆ P := by
    intro v hv
    exact J.terminals_subset_separatorRegion hA (mem_sdiff.mpr ⟨hv, fun hvS => disjoint_left.mp hAS hv hvS⟩)
  have hPB : P ⊆ H.roundingBall x Q c b := by
    intro v hv
    by_contra hnot
    exact disjoint_left.mp (J.separatorRegion_disjoint_terminals hsep) hv
      (mem_sdiff.mpr ⟨(mem_sdiff.mp (hPV hv)).1, hnot⟩)
  have hbaseP : H.roundingBall x Q c s ⊆ P :=
    (H.roundingBall_mono x Q c (show s ≤ a by dsimp [a]; linarith)).trans hAP
  have hcbase : c ∈ H.roundingBall x Q c s := by
    apply mem_filter.mpr ⟨hcJ, ?_⟩
    apply (J.vertexDistance_self_le (fun v hv => hn v (mem_inter.mp hv).1) hcJ).trans
    have hseednum := cutoff_layer_parameters hr.1 hK
    obtain ⟨N, hN, hrad, hbudget, hseed⟩ := hseednum
    have hqbound := hseed q hqsmall
    have hxc := hq c hcJ
    linarith [hr.1]
  have hzQ : restrictDemand z Q = z := by
    funext v
    by_cases hvQ : v ∈ Q
    · simp [restrictDemand, hvQ]
    · have hnot : v ∉ T := fun h => hvQ (hTQ h)
      simp [restrictDemand, hvQ, z, hnot]
  have hzCost : J.coverCost z = (δ - q)⁻¹ * H.coverCost (restrictDemand x T) := by
    rw [H.coverCost_induce_restrictDemand z Q, hzQ]
    exact H.coverCost_smul _ (inv_pos.mpr hgap)
  have hcostP : H.setCoverCost S ≤ C * (2 / δ) * H.coverCost (restrictDemand x P) := by
    rw [hzCost] at hScost
    have hinv : (δ - q)⁻¹ ≤ 2 / δ := by
      rw [inv_eq_one_div]
      exact (div_le_div_iff₀ hgap hδ).2 (by linarith)
    have hcost' : H.coverCost (restrictDemand x T) ≤ H.coverCost
        (restrictDemand x (H.roundingBall x Q c s)) := hcost
    have hTP := hcost'.trans (H.restrictDemand_cost_mono hn hbaseP)
    apply hScost.trans
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hC
    exact mul_le_mul hinv hTP (H.coverCost_nonneg _) (by positivity)
  refine ⟨{
    piece := P
    separator := S
    nonempty := ⟨c, hbaseP hcbase⟩
    piece_subset := hPQ
    separator_subset := hSQ
    disjoint := disjoint_left.mpr (fun v hv hvS => (mem_sdiff.mp (hPV hv)).2 hvS)
    support := hSsupp
    separated := ?_
    volume_le := (H.edgeVolume_mono hγ
      (hPB.trans (H.roundingBall_mono x Q c hsrad))).trans
      (H.roundingBall_volume_le hγ hx Q hcJ hr.2)
    cost_le := by simpa only [hcoef] using hcostP }⟩
  · intro e he
    by_contra hnsep
    obtain ⟨hu, hv⟩ := not_or.mp hnsep
    obtain ⟨u, hue, huP⟩ := not_disjoint_iff.mp hu
    obtain ⟨v, hve, hvR⟩ := not_disjoint_iff.mp hv
    have hv := mem_sdiff.mp hvR
    have hnP : v ∉ P := fun h => hv.2 (mem_union_left _ h)
    have hnS : v ∉ S := fun h => hv.2 (mem_union_right _ h)
    have huv : u ≠ v := by intro h; subst v; exact hnP huP
    have hadj := (H.primal_induce_adj Q (hPQ huP) hv.1).mpr ⟨huv, e, he, hue, hve⟩
    exact hnP (J.separatorRegion_closed A S huP
      (mem_sdiff.mpr ⟨mem_inter.mpr ⟨hQ hv.1, hv.1⟩, hnS⟩) hadj)

end Paper.Hypergraph
