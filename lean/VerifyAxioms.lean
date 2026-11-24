module

import Solution

/-!
# Axiom Audit (`VerifyAxioms.lean`)

Prints the complete transitive axiom dependency set of every headline theorem
in `Solution`. Every declaration MUST depend strictly on a subset of the three
standard Lean 4 axioms `[propext, Classical.choice, Quot.sound]`, with ZERO
`sorryAx`, ZERO `Lean.ofReduceBool`, and ZERO custom axioms.
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
