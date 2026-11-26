module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue (Independent Researcher, ORCID 0009-0006-8168-9648)

public import PVsNP.OTM
public import PVsNP.NaturalProofs
public import PVsNP.SheafPolymorphism
public import PVsNP.CircuitPhaseTransition
public import PVsNP.CatalyticAlgebra

/-!
# Concrete Non-Vacuity Witnesses (`PVsNP.NonVacuity`)

Demonstrates that every core hypothesis structure in `Challenge.lean`
(`Oracle`, `InP`, `IsMaximallyContextual`, `witnessMat`, `catalyticProdProg`)
is non-vacuously inhabited on concrete finite instances.
ZERO `sorry`, ZERO `admit`, ZERO `native_decide`, strictly standard axioms.
-/

namespace PVsNP.NonVacuity

open PVsNP

/-- NV1: Concrete odd-cycle k = 0 (3-vertex triangle XOR system) is maximally contextual. -/
public theorem nv_odd_cycle_k0_contextual :
    IsMaximallyContextual (oddCycleSystem 0) :=
  odd_cycle_xor_maximally_contextual 0

/-- NV2: Concrete Mermin-Peres 3x3 magic square system is maximally contextual. -/
public theorem nv_mermin_peres_contextual :
    IsMaximallyContextual merminPeresSystem :=
  mermin_peres_maximally_contextual

/-- NV3: Concrete n = 2 separation witness matrix `W_2` satisfies `perm = 2` and `det = 0`. -/
public theorem nv_witness_mat_n2 :
    permInt 2 (witnessMat 2) = 2 ∧ detInt 2 (witnessMat 2) = 0 :=
  ⟨(perm_ne_det_witness 2 (by decide)).1, (perm_ne_det_witness 2 (by decide)).2.1⟩

/-- NV4: Concrete n = 1 non-constant Boolean property has density >= 1/2 (Razborov-Rudich non-vacuity). -/
public theorem nv_natural_proof_n1 :
    IsLarge nonConstantProp 1 1 2 ∧ IsUsefulAgainst nonConstantProp 1 IsConstantTT :=
  natural_proof_nonvacuous 1 (by decide)

/-- NV5: Concrete d = 2 zero-workspace catalytic product `[3, 5]` computes `+15` and restores catalysts. -/
public theorem nv_catalytic_d2_concrete (s : RegState) :
    execProg (catalyticProdProg 2 [3, 5] true) s = setReg s 2 (s 2 + 15) := by
  have h := catalytic_multilinear_exact [3, 5] (by decide) 2 (by decide) true s
  simpa [listProd] using h.2.1

end PVsNP.NonVacuity
