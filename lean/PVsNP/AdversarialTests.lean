module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue (Independent Researcher, ORCID 0009-0006-8168-9648)

public import PVsNP.SheafPolymorphism
public import PVsNP.CircuitPhaseTransition
public import PVsNP.CatalyticAlgebra

/-!
# Adversarial Sharpness & Negative Boundary Refutations (`PVsNP.AdversarialTests`)

Formalizes concrete negative counterexamples confirming sharpness of the
barrier and phase-transition boundaries in `Challenge.lean` (C9, C10, C12, C13, C14).
ZERO `sorry`, ZERO `admit`, ZERO `native_decide`, strictly standard axioms.
-/

namespace PVsNP.AdversarialTests

open PVsNP

/-- ADV1 (C9 sharpness): Constant `true` is NOT a ternary projection, even though it preserves `R000`. -/
public theorem adv_const_true_not_projection :
    ¬ IsProjection (fun (_ : Fin 3 → Bool) => true) :=
  (monotone_3sat_minimal 3).1.2

/-- ADV2 (C9 sharpness): Constant `false` is NOT a ternary projection, even though it preserves `R111`. -/
public theorem adv_const_false_not_projection :
    ¬ IsProjection (fun (_ : Fin 3 → Bool) => false) :=
  (monotone_3sat_minimal 3).2.2

/-- ADV3 (C10 sharpness): A single NOT gate (`r = 1`) cannot invert `n = 2` bits (`2^1 <= 2`). -/
public theorem adv_markov_1not_cannot_invert_2bits
    (gs : List GateOp) (hnot : notCount gs ≤ 1) (outs : Fin 2 → Nat) :
    ¬ ComputesInverter 2 gs outs :=
  markov_inverter_lower 2 1 (by decide) gs hnot outs

/-- ADV4 (C12 sharpness): `AND_3` cannot be computed with `<= 1` AND gate (`MC(AND_3) >= 2`). -/
public theorem adv_mc_and3_not_one_gate
    (gs : List XorAndOp) (w : Nat)
    (h : ∀ x : Fin 3 → Bool, (evalXorAndCircuit (vecToBits x) gs).getD w false = andN 3 x) :
    ¬ (andCount gs ≤ 1) := by
  have hlb := mc_andN_lower 3 (by decide) gs w h
  omega

/-- ADV5 (C13 sharpness): Over `Z/3Z`, `permInt 2 (witnessMat 2) != detInt 2 (witnessMat 2)` (`2 != 0`). -/
public theorem adv_perm_ne_det_mod3_n2 :
    permInt 2 (witnessMat 2) % 3 ≠ detInt 2 (witnessMat 2) % 3 :=
  (perm_ne_det_witness 2 (by decide)).2.2 3 (by decide)

end PVsNP.AdversarialTests
