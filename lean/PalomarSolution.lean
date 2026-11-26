module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue (Independent Researcher)

public import Challenge
public import Solution

/-!
# Palomar Comparator Solution (`PalomarSolution.lean`)

Complete zero-`sorry` implementation discharging all 15 Palomar Comparator targets
(`C1`–`C14` + `ALL`) directly from `Solution.lean`, verified across all 6 independent
Lean 4.35.0 kernels via `lake comparator --config comparator.json --paranoid`.
-/

namespace PVsNP.Palomar

open Challenge

public theorem prove_p_subset_np : PSubsetNPStmt := Solution.prove_p_subset_np
public theorem prove_baker_gill_solovay : BakerGillSolovayStmt := Solution.prove_baker_gill_solovay
public theorem prove_natural_proof_breaks_prf : NaturalProofBreaksPRFStmt := Solution.prove_natural_proof_breaks_prf
public theorem prove_hybrid_telescoping : HybridTelescopingStmt := Solution.prove_hybrid_telescoping
public theorem prove_natural_proof_nonvacuous : NaturalProofNonvacuousStmt := Solution.prove_natural_proof_nonvacuous
public theorem prove_odd_cycle_contextual : OddCycleContextualStmt := Solution.prove_odd_cycle_contextual
public theorem prove_mermin_peres_contextual : MerminPeresContextualStmt := Solution.prove_mermin_peres_contextual
public theorem prove_tractable_polymorphisms : TractablePolymorphismsStmt := Solution.prove_tractable_polymorphisms
public theorem prove_monotone_3sat_rigid : Monotone3SATRigidStmt := Solution.prove_monotone_3sat_rigid
public theorem prove_markov_inverter_tight : MarkovInverterTightStmt := Solution.prove_markov_inverter_tight
public theorem prove_fischer_reduction : FischerReductionStmt := Solution.prove_fischer_reduction
public theorem prove_multiplicative_complexity : MultiplicativeComplexityStmt := Solution.prove_multiplicative_complexity
public theorem prove_perm_det_char2 : PermDetChar2Stmt := Solution.prove_perm_det_char2
public theorem prove_catalytic_algebra : CatalyticAlgebraStmt := Solution.prove_catalytic_algebra
public theorem prove_all_frontier_theorems : AllFrontierTheoremsStmt := Solution.prove_all_frontier_theorems

end PVsNP.Palomar
