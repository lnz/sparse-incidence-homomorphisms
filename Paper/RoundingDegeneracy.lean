import Paper.RoundingAveraging

noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Paper.Hypergraph

/-- An elimination order of the incidence graph with at most μ later neighbors. -/
theorem incidence_elimination_order (H : Hypergraph) :
    ∃ rank : ℕ ⊕ ℕ → ℕ, Set.InjOn rank (↑H.incidenceVertices : Set (ℕ ⊕ ℕ)) ∧
      ∀ v ∈ H.incidenceVertices,
        (H.incidenceVertices.filter (fun w => H.incidence.Adj v w ∧ rank v < rank w)).card ≤ H.degeneracy := by
  have hdeg : ∀ S ⊆ H.incidenceVertices, S.Nonempty →
      ∃ v ∈ S, (S.filter (H.incidence.Adj v)).card ≤ H.degeneracy := by
    refine csInf_mem (s := {d : ℕ | ∀ S ⊆ H.incidenceVertices, S.Nonempty →
      ∃ v ∈ S, (S.filter (H.incidence.Adj v)).card ≤ d}) ?_
    refine ⟨H.incidenceVertices.card, ?_⟩
    intro S hS hne
    obtain ⟨v, hv⟩ := hne
    exact ⟨v, hv, (card_filter_le _ _).trans (card_le_card hS)⟩
  suffices h : ∀ S ⊆ H.incidenceVertices, ∃ rank : ℕ ⊕ ℕ → ℕ,
      Set.InjOn rank (↑S : Set (ℕ ⊕ ℕ)) ∧ ∀ v ∈ S,
        (S.filter (fun w => H.incidence.Adj v w ∧ rank v < rank w)).card ≤ H.degeneracy from
    h H.incidenceVertices (Subset.refl _)
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hS
    by_cases hne : S.Nonempty
    swap
    · have h0 := Finset.not_nonempty_iff_eq_empty.mp hne
      subst S
      exact ⟨fun _ => 0, by simp, by simp⟩
    obtain ⟨v, hv, hlow⟩ := hdeg S hS hne
    obtain ⟨old, hinj, hlater⟩ := ih (S.erase v) (erase_ssubset hv)
      ((erase_subset _ _).trans hS)
    let rank : ℕ ⊕ ℕ → ℕ := fun w => if w = v then 0 else old w + 1
    refine ⟨rank, ?_, ?_⟩
    · intro a ha b hb heq
      by_cases hav : a = v
      · by_cases hbv : b = v
        · exact hav.trans hbv.symm
        · simp [rank, hav, hbv] at heq
      · by_cases hbv : b = v
        · simp [rank, hav, hbv] at heq
        · apply hinj (mem_erase.mpr ⟨hav, ha⟩) (mem_erase.mpr ⟨hbv, hb⟩)
          simpa [rank, hav, hbv] using heq
    · intro a ha
      by_cases hav : a = v
      · subst a
        apply le_trans (card_le_card ?_) hlow
        intro w hw
        exact mem_filter.mpr ⟨(mem_filter.mp hw).1, (mem_filter.mp hw).2.1⟩
      · apply le_trans _ (hlater a (mem_erase.mpr ⟨hav, ha⟩))
        apply card_le_card
        intro b hb
        obtain ⟨hbS, hab, hrank⟩ := mem_filter.mp hb
        have hbv : b ≠ v := by intro h; simp [rank, h, hav] at hrank
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨hbv, hbS⟩, hab, by simpa [rank, hav, hbv] using hrank⟩

theorem incidence_order_left_card (H : Hypergraph) {rank : ℕ ⊕ ℕ → ℕ}
    (hlater : ∀ v ∈ H.incidenceVertices,
      (H.incidenceVertices.filter (fun w => H.incidence.Adj v w ∧ rank v < rank w)).card ≤ H.degeneracy)
    {e : ℕ} (he : e ∈ H.edges) :
    ((H.edge e).filter (fun v => rank (.inr e) < rank (.inl v))).card ≤ H.degeneracy := by
  have heI : Sum.inr e ∈ H.incidenceVertices := by simp [incidenceVertices, he]
  apply le_trans _ (hlater (.inr e) heI)
  rw [← card_map Function.Embedding.inl]
  apply card_le_card
  intro w hw
  obtain ⟨v, hv, rfl⟩ := mem_map.mp hw
  obtain ⟨hve, hrank⟩ := mem_filter.mp hv
  exact mem_filter.mpr ⟨by simp [incidenceVertices, H.edge_subset e he hve], ⟨he, hve⟩, hrank⟩

theorem incidence_order_right_card (H : Hypergraph) {rank : ℕ ⊕ ℕ → ℕ}
    (hlater : ∀ v ∈ H.incidenceVertices,
      (H.incidenceVertices.filter (fun w => H.incidence.Adj v w ∧ rank v < rank w)).card ≤ H.degeneracy)
    {v : ℕ} (hv : v ∈ H.vertices) :
    (H.edges.filter (fun e => v ∈ H.edge e ∧ rank (.inl v) < rank (.inr e))).card ≤ H.degeneracy := by
  have hvI : Sum.inl v ∈ H.incidenceVertices := by simp [incidenceVertices, hv]
  apply le_trans _ (hlater (.inl v) hvI)
  rw [← card_map Function.Embedding.inr]
  apply card_le_card
  intro w hw
  obtain ⟨e, he, rfl⟩ := mem_map.mp hw
  obtain ⟨he, hve, hrank⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨by simp [incidenceVertices, he], ⟨he, hve⟩, hrank⟩

theorem vertexMultiplier_integrable (x d : ℕ → ℝ) (v : ℕ) :
    Integrable (vertexMultiplier x d v) levelMeasure :=
  (integrable_const _).indicator measurableSet_Icc

theorem vertexMultiplier_integral_le_one {x d : ℕ → ℝ} {v : ℕ} (hx : 0 ≤ x v) :
    ∫ r, vertexMultiplier x d v r ∂levelMeasure ≤ 1 := by
  by_cases h0 : x v = 0
  · simp [vertexMultiplier, h0]
  have hp : 0 < x v := lt_of_le_of_ne hx (Ne.symm h0)
  rw [vertexMultiplier, integral_indicator_const _ measurableSet_Icc]
  change levelMeasure.real (Set.Icc (d v - x v) (d v)) * (1 / x v) ≤ 1
  have h := levelMeasure_Icc_le (d v - x v) (d v)
  have heq : max (d v - (d v - x v)) 0 = x v := by rw [sub_sub_cancel, max_eq_left hx]
  rw [heq] at h
  calc
    _ ≤ x v * (1 / x v) := mul_le_mul_of_nonneg_right h (by positivity)
    _ = 1 := by field_simp

def degeneracyLevelCover (H : Hypergraph) (rank : ℕ ⊕ ℕ → ℕ) (x d y q : ℕ → ℝ)
    (e : ℕ) (r : ℝ) : ℝ :=
  (∑ v ∈ (H.edge e).filter (fun v => rank (.inr e) < rank (.inl v)),
    2 * y e * vertexMultiplier x d v r) +
  (Set.Icc (q e - 2 * H.degeneracy * y e) (q e + 2 * H.degeneracy * y e)).indicator (fun _ => 1) r

theorem degeneracyLevelCover_nonneg (H : Hypergraph) (rank : ℕ ⊕ ℕ → ℕ) {x d y q : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (hy : ∀ e ∈ H.edges, 0 ≤ y e)
    {e : ℕ} (he : e ∈ H.edges) (r : ℝ) : 0 ≤ H.degeneracyLevelCover rank x d y q e r := by
  have hye := hy e he
  apply add_nonneg
  · apply sum_nonneg
    intro v hv
    exact mul_nonneg (by positivity) (vertexMultiplier_nonneg (hx v (H.edge_subset e he (mem_filter.mp hv).1)) r)
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem degeneracyLevelCover_integrable (H : Hypergraph) (rank : ℕ ⊕ ℕ → ℕ) (x d y q : ℕ → ℝ)
    (e : ℕ) : Integrable (H.degeneracyLevelCover rank x d y q e) levelMeasure := by
  apply Integrable.add
  · exact integrable_finsetSum _ (fun v _ => (vertexMultiplier_integrable x d v).const_mul _)
  · exact (integrable_const _).indicator measurableSet_Icc

theorem degeneracyLevelCover_integral_le (H : Hypergraph) {rank : ℕ ⊕ ℕ → ℕ} {x d y q : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (hy : ∀ e ∈ H.edges, 0 ≤ y e)
    (hlater : ∀ v ∈ H.incidenceVertices,
      (H.incidenceVertices.filter (fun w => H.incidence.Adj v w ∧ rank v < rank w)).card ≤ H.degeneracy)
    {e : ℕ} (he : e ∈ H.edges) :
    ∫ r, H.degeneracyLevelCover rank x d y q e r ∂levelMeasure ≤ 6 * H.degeneracy * y e := by
  have hye := hy e he
  let L := (H.edge e).filter (fun v => rank (.inr e) < rank (.inl v))
  have hleft : (∫ r, ∑ v ∈ L, 2 * y e * vertexMultiplier x d v r ∂levelMeasure) ≤ 2 * H.degeneracy * y e := by
    rw [integral_finsetSum _ (fun v _ => (vertexMultiplier_integrable x d v).const_mul _)]
    have hcard : (L.card : ℝ) ≤ H.degeneracy := by exact_mod_cast H.incidence_order_left_card hlater he
    calc
      _ ≤ ∑ _v ∈ L, 2 * y e := sum_le_sum (fun v hv => by
        rw [integral_const_mul]
        exact (mul_le_mul_of_nonneg_left (vertexMultiplier_integral_le_one
          (hx v (H.edge_subset e he (mem_filter.mp hv).1))) (by positivity)).trans_eq (mul_one _))
      _ = (L.card : ℝ) * (2 * y e) := by simp
      _ ≤ _ := by nlinarith
  have hright : (∫ r, (Set.Icc (q e - 2 * H.degeneracy * y e) (q e + 2 * H.degeneracy * y e)).indicator
      (fun _ => (1 : ℝ)) r ∂levelMeasure) ≤ 4 * H.degeneracy * y e := by
    rw [integral_indicator_const _ measurableSet_Icc]
    simp only [smul_eq_mul, mul_one]
    apply (levelMeasure_Icc_le _ _).trans
    have hnonneg : (0 : ℝ) ≤ H.degeneracy * y e := mul_nonneg (Nat.cast_nonneg _) hye
    rw [max_eq_left (by nlinarith)]
    nlinarith
  simp only [degeneracyLevelCover]
  rw [integral_add
    (integrable_finsetSum _ (fun v _ => (vertexMultiplier_integrable x d v).const_mul _))
    ((integrable_const _).indicator measurableSet_Icc)]
  change (∫ r, ∑ v ∈ L, 2 * y e * vertexMultiplier x d v r ∂levelMeasure) + _ ≤ _
  linarith

theorem degeneracyLevelCover_covers (H : Hypergraph) {rank : ℕ ⊕ ℕ → ℕ} {x d y q : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (hy : H.Cover x y)
    (hinj : Set.InjOn rank (↑H.incidenceVertices : Set (ℕ ⊕ ℕ)))
    (hlater : ∀ v ∈ H.incidenceVertices,
      (H.incidenceVertices.filter (fun w => H.incidence.Adj v w ∧ rank v < rank w)).card ≤ H.degeneracy)
    (hq : ∀ e ∈ H.edges, ∀ v ∈ H.edge e, d v - x v ≤ q e ∧ q e ≤ d v) (r : ℝ) :
    H.Cover (indicator (H.levelSeparator x d r)) (fun e => H.degeneracyLevelCover rank x d y q e r) := by
  let m := fun e => H.degeneracyLevelCover rank x d y q e r
  have hm : ∀ e ∈ H.edges, 0 ≤ m e := fun e he => H.degeneracyLevelCover_nonneg rank hx hy.1 he r
  refine ⟨hm, ?_⟩
  intro v hv
  let I := H.edges.filter (fun e => v ∈ H.edge e)
  by_cases hvS : v ∈ H.levelSeparator x d r
  swap
  · simp only [indicator, if_neg hvS]
    exact sum_nonneg (fun e he => hm e (mem_filter.mp he).1)
  have hvsel := (mem_filter.mp hvS).2
  have hxv : 0 < x v := lt_of_le_of_ne (hx v hv) hvsel.1.symm
  have hvm : vertexMultiplier x d v r = 1 / x v :=
    Set.indicator_of_mem (show r ∈ Set.Icc (d v - x v) (d v) from hvsel.2) _
  let L := I.filter (fun e => rank (.inr e) < rank (.inl v))
  let U := I.filter (fun e => ¬rank (.inr e) < rank (.inl v))
  have hLI : L ⊆ I := filter_subset _ _
  have hUI : U ⊆ I := filter_subset _ _
  have hI : I ⊆ H.edges := filter_subset _ _
  have hsum : (∑ e ∈ L, y e) + (∑ e ∈ U, y e) = ∑ e ∈ I, y e := sum_filter_add_sum_filter_not _ _ _
  simp only [indicator, if_pos hvS]
  change 1 ≤ ∑ e ∈ I, m e
  by_cases hleft : x v / 2 ≤ ∑ e ∈ L, y e
  · have hscale : 1 ≤ (2 / x v) * ∑ e ∈ L, y e := by
      have hh := mul_le_mul_of_nonneg_left hleft (by positivity : 0 ≤ 2 / x v)
      have heq : (2 / x v) * (x v / 2) = 1 := by field_simp
      rwa [heq] at hh
    calc
      1 ≤ (2 / x v) * ∑ e ∈ L, y e := hscale
      _ = ∑ e ∈ L, (2 / x v) * y e := mul_sum _ _ _
      _ ≤ ∑ e ∈ L, m e := by
        apply sum_le_sum
        intro e he
        have heE := hI (hLI he)
        have hye := hy.1 e heE
        have hve := (mem_filter.mp (hLI he)).2
        have hrank := (mem_filter.mp he).2
        have hs : 2 * y e * vertexMultiplier x d v r ≤
            ∑ w ∈ (H.edge e).filter (fun w => rank (.inr e) < rank (.inl w)), 2 * y e * vertexMultiplier x d w r := by
          apply single_le_sum (f := fun w => 2 * y e * vertexMultiplier x d w r) (a := v)
          · intro w hw
            exact mul_nonneg (by positivity)
              (vertexMultiplier_nonneg (hx w (H.edge_subset e heE (mem_filter.mp hw).1)) r)
          · exact mem_filter.mpr ⟨hve, hrank⟩
        have hright : 0 ≤ (Set.Icc (q e - 2 * H.degeneracy * y e) (q e + 2 * H.degeneracy * y e)).indicator
            (fun _ => (1 : ℝ)) r := Set.indicator_nonneg (fun _ _ => zero_le_one) _
        change _ ≤ _ + _
        rw [hvm] at hs
        have heq : (2 / x v) * y e = 2 * y e * (1 / x v) := by ring
        rw [heq]
        linarith
      _ ≤ ∑ e ∈ I, m e := sum_le_sum_of_subset_of_nonneg hLI (fun e he _ => hm e (hI he))
  · have hright : x v / 2 < ∑ e ∈ U, y e := by
      have h := hy.2 v hv
      change x v ≤ ∑ e ∈ I, y e at h
      linarith
    have hU : U.Nonempty := by
      by_contra h
      have h0 := Finset.not_nonempty_iff_eq_empty.mp h
      rw [h0, sum_empty] at hright
      linarith
    obtain ⟨e, heU, hemax⟩ := U.exists_max_image y hU
    have heE := hI (hUI heU)
    have hye := hy.1 e heE
    have hUsub : U ⊆ H.edges.filter (fun f => v ∈ H.edge f ∧ rank (.inl v) < rank (.inr f)) := by
      intro f hf
      obtain ⟨hfI, hnot⟩ := mem_filter.mp hf
      obtain ⟨hfE, hvf⟩ := mem_filter.mp hfI
      have hvI : Sum.inl v ∈ H.incidenceVertices := by simp [incidenceVertices, hv]
      have hfI' : Sum.inr f ∈ H.incidenceVertices := by simp [incidenceVertices, hfE]
      have hne : rank (.inl v) ≠ rank (.inr f) := by
        intro h
        have hh := hinj hvI hfI' h
        cases hh
      exact mem_filter.mpr ⟨hfE, hvf, by omega⟩
    have hcard : (U.card : ℝ) ≤ H.degeneracy := by
      exact_mod_cast (card_le_card hUsub).trans (H.incidence_order_right_card hlater hv)
    have hys : (∑ f ∈ U, y f) ≤ (U.card : ℝ) * y e := by
      calc
        _ ≤ ∑ _f ∈ U, y e := sum_le_sum hemax
        _ = _ := by simp
    have hsmall : x v ≤ 2 * H.degeneracy * y e := by
      have hh := mul_le_mul_of_nonneg_right hcard hye
      nlinarith
    have hve := (mem_filter.mp (hUI heU)).2
    have hqv := hq e heE v hve
    have hrwin : r ∈ Set.Icc (q e - 2 * H.degeneracy * y e) (q e + 2 * H.degeneracy * y e) :=
      ⟨by linarith [hvsel.2.1, hvsel.2.2], by linarith [hvsel.2.1, hvsel.2.2]⟩
    have hme : 1 ≤ m e := by
      dsimp [m, degeneracyLevelCover]
      rw [Set.indicator_of_mem hrwin]
      have hn : 0 ≤ ∑ w ∈ (H.edge e).filter (fun w => rank (.inr e) < rank (.inl w)),
          2 * y e * vertexMultiplier x d w r := sum_nonneg (fun w hw =>
        mul_nonneg (by positivity) (vertexMultiplier_nonneg (hx w (H.edge_subset e heE (mem_filter.mp hw).1)) r))
      linarith
    exact hme.trans (single_le_sum (fun f hf => hm f (hI hf)) (hUI heU))

/-- The degeneracy branch of Theorem 4.1. -/
theorem twoTerminal_degeneracy_rounding (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hB : B ⊆ H.vertices) (hx : H.FractionalSeparator A B x) :
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralSeparator A B S ∧
      H.setCoverCost S ≤ (6 * H.degeneracy : ℝ) * H.coverCost x := by
  obtain ⟨d, hd, ha, hb, hstep⟩ := H.twoTerminal_distance_labels hA hx
  obtain ⟨y, hy, _, hcost⟩ := H.coverCost_attained hx.1
  obtain ⟨rank, hinj, hlater⟩ := H.incidence_elimination_order
  have hn : ∀ v ∈ H.vertices, 0 ≤ x v := fun v hv => (hx.1 v hv).1
  let q := fun e => if he : e ∈ H.edges then (H.edge_intervals_common_point hstep hn he).choose else 0
  have hq : ∀ e ∈ H.edges, ∀ v ∈ H.edge e, d v - x v ≤ q e ∧ q e ≤ d v := by
    intro e he
    simp only [q, dif_pos he]
    exact (H.edge_intervals_common_point hstep hn he).choose_spec
  obtain ⟨S, hS, hsep, hbound⟩ := H.rounding_by_average hA hB ha hb hstep
    (H.degeneracyLevelCover rank x d y q)
    (fun e _ => H.degeneracyLevelCover_integrable rank x d y q e)
    (fun r _ => H.degeneracyLevelCover_covers hn hy hinj hlater hq r)
  refine ⟨S, hS, hsep, hbound.trans ?_⟩
  rw [hcost, mul_sum]
  exact sum_le_sum (fun e he => H.degeneracyLevelCover_integral_le hn hy.1 hlater he)

end Paper.Hypergraph
