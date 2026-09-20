import Paper.RoundingComplete

#print axioms Paper.Hypergraph.twoTerminal_minimum_weight_rounding
#print axioms Paper.Hypergraph.twoTerminal_independence_rounding
#print axioms Paper.Hypergraph.twoTerminal_degeneracy_rounding
#print axioms Paper.Hypergraph.twoTerminal_rounding
#print axioms Paper.Hypergraph.external_rounding
#print axioms Paper.Hypergraph.main_width_comparison

#print axioms Paper.Hypergraph.roundingBall_volume_le
#print axioms Paper.Hypergraph.roundingThreshold_cost_le
#print axioms Paper.Hypergraph.sum_restrictDemand_cost_le
#print axioms Paper.Hypergraph.rounding_union_cost_le
#print axioms Paper.Hypergraph.cutoff_layer_exists
#print axioms Paper.Hypergraph.cutoff_layer_parameters
#print axioms Paper.Hypergraph.cutoff_annulus_scaling

-- These proved results should not contain `sorryAx` in their dependencies.
#print axioms Paper.Hypergraph.recursive_bag_step
#print axioms Paper.Hypergraph.rooted_forest_tree
#print axioms Paper.Hypergraph.glue_rooted_bags
#print axioms Paper.Hypergraph.recursive_rooted_decomposition
#print axioms Paper.Hypergraph.recursive_separator_decomposition
#print axioms Paper.Hypergraph.separator_characterization
#print axioms Paper.Hypergraph.fractional_cover_minimax
#print axioms Paper.Hypergraph.beta_le_adw
#print axioms Paper.Hypergraph.fractional_separators_le_adw
#print axioms Paper.Hypergraph.cover_duality
#print axioms Paper.Hypergraph.balanced_bag
#print axioms Paper.Hypergraph.component_reduction
#print axioms Paper.Hypergraph.cover_cap
#print axioms Paper.Hypergraph.coverCost_eq_capped
#print axioms Paper.Hypergraph.coverCost_attained
#print axioms Paper.Hypergraph.rounding_structural_bound
#print axioms Paper.Hypergraph.rounding_cost_bound
#print axioms Paper.Hypergraph.cover_restriction
#print axioms Paper.Hypergraph.elementary_width_bounds
#print axioms Paper.Hypergraph.adw_ge_one
#print axioms Paper.Hypergraph.structure_hereditary
#print axioms Paper.Hypergraph.width_hereditary
#print axioms Paper.Hypergraph.component_connected
#print axioms Paper.Hypergraph.submodular_support
#print axioms Paper.Hypergraph.modular_le_coverCost
#print axioms Paper.Hypergraph.width_hierarchy
#print axioms Paper.Hypergraph.indicator_equivalence
#print axioms Paper.Hypergraph.full_fractional_separator
#print axioms Paper.Hypergraph.beta_le_fsep
#print axioms Paper.Hypergraph.scale_infimum

-- The alignment lemmas use only standard axioms.
#print axioms Paper.Hypergraph.degeneracy_ge_one
#print axioms Paper.Hypergraph.independenceNumber_ge_one
#print axioms Paper.Hypergraph.lambda_ge_one
#print axioms Paper.Hypergraph.structuralFactor_le_lambda
#print axioms Paper.Hypergraph.componentFactor_le_structuralFactor

-- These deductions take ExternalRounding as an explicit hypothesis.
#print axioms Paper.Hypergraph.balanced_separator_rounding
#print axioms Paper.Hypergraph.round_hereditary

-- The final implication must also use only standard axioms.
#print axioms Paper.Hypergraph.theorem_1_1

-- Fail if any declaration in the paper namespace depends on another axiom.
-- The check traverses dependencies, including imported declarations.
open Lean in
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (name, _) in env.constants.toList do
    if (`Paper).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      checked := checked + 1
  logInfo m!"Trust audit passed for {checked} declarations in Paper"
