module

public import Challenge
public import PVsNP

/-!
# Solution Module — Machine-Checked Proofs of All 14 Challenge Statements

Every theorem below discharges the exact corresponding specification in
`Challenge.lean` using only the standard Lean 4 core axioms
(`propext`, `Classical.choice`, `Quot.sound`), with zero `sorry`, zero `admit`,
zero `native_decide`, and zero custom axioms.
-/

namespace Solution

open PVsNP Challenge

public theorem prove_p_subset_np : PSubsetNPStmt :=
  p_subset_np

public theorem prove_baker_gill_solovay : BakerGillSolovayStmt :=
  baker_gill_solovay

public theorem prove_natural_proof_breaks_prf : NaturalProofBreaksPRFStmt :=
  fun P C F hL hU hIn => natural_proof_breaks_prf P C F hL hU hIn

public theorem prove_hybrid_telescoping : HybridTelescopingStmt :=
  hybrid_telescoping_bound

public theorem prove_natural_proof_nonvacuous : NaturalProofNonvacuousStmt :=
  natural_proof_nonvacuous

public theorem prove_odd_cycle_contextual : OddCycleContextualStmt :=
  odd_cycle_xor_maximally_contextual

public theorem prove_mermin_peres_contextual : MerminPeresContextualStmt :=
  mermin_peres_maximally_contextual

public theorem prove_tractable_polymorphisms : TractablePolymorphismsStmt :=
  ⟨xorsat_maltsev, hornsat_and, dualhornsat_or, twosat_majority⟩

public theorem prove_monotone_3sat_rigid : Monotone3SATRigidStmt :=
  ⟨fun _ f h0 h1 => monotone_3sat_only_projections f h0 h1, monotone_3sat_minimal⟩

public theorem prove_markov_inverter_tight : MarkovInverterTightStmt :=
  ⟨markov_inverter_lower, markov_inverter_upper⟩

public theorem prove_fischer_reduction : FischerReductionStmt :=
  fischer_negation_reduction

public theorem prove_multiplicative_complexity : MultiplicativeComplexityStmt :=
  ⟨mc_degree_lower_bound, mc_andN_lower⟩

public theorem prove_perm_det_char2 : PermDetChar2Stmt :=
  ⟨perm_eq_det_mod2, perm_ne_det_witness⟩

public theorem prove_catalytic_algebra : CatalyticAlgebraStmt :=
  ⟨catalytic_program_reversible, fun xs hne dst hdst sign s =>
    catalytic_multilinear_exact xs hne dst hdst sign s⟩

public theorem prove_all_frontier_theorems : AllFrontierTheoremsStmt :=
  ⟨ prove_p_subset_np
  , prove_baker_gill_solovay
  , prove_natural_proof_breaks_prf
  , prove_hybrid_telescoping
  , prove_natural_proof_nonvacuous
  , prove_odd_cycle_contextual
  , prove_mermin_peres_contextual
  , prove_tractable_polymorphisms
  , prove_monotone_3sat_rigid
  , prove_markov_inverter_tight
  , prove_fischer_reduction
  , prove_multiplicative_complexity
  , prove_perm_det_char2
  , prove_catalytic_algebra ⟩

end Solution
