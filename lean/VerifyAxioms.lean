module

import Solution

/-!
# Axiom Audit (`VerifyAxioms.lean`)

Prints the complete transitive axiom dependency set of all 25 audited declarations:
14 headline theorems (`C1`-`C14`) + master conjunction in `Solution`, 5 concrete
non-vacuity witnesses in `PVsNP.NonVacuity`, and 5 adversarial negative boundary
refutations in `PVsNP.AdversarialTests`. Every declaration MUST depend strictly
on a subset of `[propext, Classical.choice, Quot.sound]`, with ZERO `sorryAx`,
ZERO `Lean.ofReduceBool`, and ZERO custom axioms.
-/

#print axioms Solution.prove_p_subset_np
#print axioms Solution.prove_baker_gill_solovay
#print axioms Solution.prove_natural_proof_breaks_prf
#print axioms Solution.prove_hybrid_telescoping
#print axioms Solution.prove_natural_proof_nonvacuous
#print axioms Solution.prove_odd_cycle_contextual
#print axioms Solution.prove_mermin_peres_contextual
#print axioms Solution.prove_tractable_polymorphisms
#print axioms Solution.prove_monotone_3sat_rigid
#print axioms Solution.prove_markov_inverter_tight
#print axioms Solution.prove_fischer_reduction
#print axioms Solution.prove_multiplicative_complexity
#print axioms Solution.prove_perm_det_char2
#print axioms Solution.prove_catalytic_algebra
#print axioms Solution.prove_all_frontier_theorems
#print axioms PVsNP.NonVacuity.nv_odd_cycle_k0_contextual
#print axioms PVsNP.NonVacuity.nv_mermin_peres_contextual
#print axioms PVsNP.NonVacuity.nv_witness_mat_n2
#print axioms PVsNP.NonVacuity.nv_natural_proof_n1
#print axioms PVsNP.NonVacuity.nv_catalytic_d2_concrete
#print axioms PVsNP.AdversarialTests.adv_const_true_not_projection
#print axioms PVsNP.AdversarialTests.adv_const_false_not_projection
#print axioms PVsNP.AdversarialTests.adv_markov_1not_cannot_invert_2bits
#print axioms PVsNP.AdversarialTests.adv_mc_and3_not_one_gate
#print axioms PVsNP.AdversarialTests.adv_perm_ne_det_mod3_n2
