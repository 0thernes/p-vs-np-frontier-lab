module

public import PVsNP.Basic
public import PVsNP.OTM
public import PVsNP.RelativizationSep
public import PVsNP.RelativizationCol

/-!
# Baker–Gill–Solovay Relativization Barrier (1975)

Combines the constructive collapse oracle (`PVsNP.RelativizationCol`) and
constructive diagonalization separation oracle (`PVsNP.RelativizationSep`)
over the explicit four-tape Oracle Turing Machine model (`PVsNP.OTM`).
-/

namespace PVsNP

/-- Headline Theorem (Baker–Gill–Solovay 1975):
    There exist computable oracles `A` and `B` such that `P^A = NP^A` and `P^B ≠ NP^B`. -/
public theorem baker_gill_solovay :
    (∃ A : Oracle, ∀ L : Language, InP A L ↔ InNP A L) ∧
    (∃ B : Oracle, ∃ L : Language, InNP B L ∧ ¬ InP B L) :=
  ⟨bgs_oracle_collapse, bgs_oracle_separation⟩

end PVsNP
