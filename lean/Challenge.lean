module

public import PVsNP.OTM
public import PVsNP.NaturalProofs
public import PVsNP.SheafPolymorphism
public import PVsNP.CircuitPhaseTransition
public import PVsNP.CatalyticAlgebra

/-!
# Challenge Specification (Human-Auditable Theorem Statements)

Isolates the exact formal statements of every headline theorem proven in
`Solution.lean` so an independent auditor can inspect the exact mathematical
claims in under two minutes without reading proof internals.

ZERO `sorry`, ZERO `admit`, ZERO custom `axiom` declarations anywhere in this file.
-/

namespace Challenge

open PVsNP

@[expose] public section

/-- C1: Non-vacuity of the Oracle Turing Machine complexity classes (`P^O ⊆ NP^O`). -/
def PSubsetNPStmt : Prop :=
  ∀ (O : Oracle) (L : Language), InP O L → InNP O L

/-- C2: Baker–Gill–Solovay (1975) Relativization Barrier:
    computable oracles `A` (collapse) and `B` (separation). -/
def BakerGillSolovayStmt : Prop :=
  (∃ A : Oracle, ∀ L : Language, InP A L ↔ InNP A L) ∧
  (∃ B : Oracle, ∃ L : Language, InNP B L ∧ ¬ InP B L)

/-- C3: Razborov–Rudich (1997) Natural Proofs break PRFs (exact integer bound). -/
def NaturalProofBreaksPRFStmt : Prop :=
  ∀ {n k numer denom : Nat} (P : PRFFamily n k) (C : CombProperty) (F : List Bool → Prop),
    IsLarge C n numer denom →
    IsUsefulAgainst C n F →
    (∀ key : List Bool, key.length = k → F (P.eval key)) →
    prfCount P C = 0 ∧ BreaksPRFWithAdv P C numer denom

/-- C4: Finite Hybrid Telescoping Bound (exact integer GGM hybrid lemma). -/
def HybridTelescopingStmt : Prop :=
  ∀ (m B : Nat) (a : Nat → Int),
    m * B < Int.natAbs (a 0 - a m) →
    ∃ i : Nat, i < m ∧ B < Int.natAbs (a i - a (i + 1))

/-- C5: Non-vacuity of Natural Proofs (`nonConstantProp` has density `≥ 1/2` for all `n ≥ 1`). -/
def NaturalProofNonvacuousStmt : Prop :=
  ∀ n : Nat, 1 ≤ n →
    IsLarge nonConstantProp n 1 2 ∧ IsUsefulAgainst nonConstantProp n IsConstantTT

/-- C6: Infinite maximally contextual odd-cycle XOR-2SAT family inside `P`. -/
def OddCycleContextualStmt : Prop :=
  ∀ k : Nat, IsMaximallyContextual (oddCycleSystem k)

/-- C7: Mermin–Peres `3×3` quantum contextuality gadget is maximally contextual in `XOR-3SAT ⊆ P`. -/
def MerminPeresContextualStmt : Prop :=
  IsMaximallyContextual merminPeresSystem

/-- C8: Tractable Schaefer CSP polymorphism witnesses (`XOR`, `Horn`, `Dual-Horn`, `2-SAT`). -/
def TractablePolymorphismsStmt : Prop :=
  (∀ rhs, Preserves3 (RXor3 rhs) opMaltsev) ∧
  Preserves3 RHorn opAnd ∧
  Preserves3 RDualHorn opOr ∧
  (∀ p q, Preserves2 (R2Clause p q) opMajority)

/-- C9: Inclusion-Minimal All-Arity Rigidity of Monotone 3-SAT `{R000, R111}`:
    for EVERY finite arity `k`, every `k`-ary Boolean polymorphism preserving both
    `R000` and `R111` is a projection, whereas dropping either admits a constant op. -/
def Monotone3SATRigidStmt : Prop :=
  (∀ (k : Nat) (f : (Fin k → Bool) → Bool), Preserves3 R000 f → Preserves3 R111 f → IsProjection f) ∧
  (∀ k : Nat,
    (Preserves3 R000 (fun (_ : Fin k → Bool) => true) ∧ ¬ IsProjection (fun (_ : Fin k → Bool) => true)) ∧
    (Preserves3 R111 (fun (_ : Fin k → Bool) => false) ∧ ¬ IsProjection (fun (_ : Fin k → Bool) => false)))

/-- C10: Markov (1957) exact bounded-negation phase transition (both lower & upper bounds). -/
def MarkovInverterTightStmt : Prop :=
  (∀ (n r : Nat), 2 ^ r ≤ n → ∀ (gs : List GateOp), notCount gs ≤ r → ∀ (outs : Fin n → Nat),
    ¬ ComputesInverter n gs outs) ∧
  (∀ k : Nat, notCount (markovInverter k).1 = k ∧
    ∃ outs : Fin (2 ^ k - 1) → Nat, ComputesInverter (2 ^ k - 1) (markovInverter k).1 outs)

/-- C11: Fischer (1975) universal reduction of any circuit on `2^k - 1` bits to `k` NOT gates. -/
def FischerReductionStmt : Prop :=
  ∀ (k : Nat) (gs : List GateOp),
    (∀ (t : Nat) (ht : t < gs.length),
      match gs[t]'ht with
      | .const _ => True
      | .and i j => i < (2 ^ k - 1) + t ∧ j < (2 ^ k - 1) + t
      | .or i j => i < (2 ^ k - 1) + t ∧ j < (2 ^ k - 1) + t
      | .not i => i < (2 ^ k - 1) + t) →
    notCount (fischerCompile k gs) = k ∧
    ∀ w < (2 ^ k - 1) + gs.length,
      let outWire := (dualRailMap (2 ^ k - 1) (markovInverter k).2 ((2 ^ k - 1) + (markovInverter k).1.length) w).1
      ∀ x : List Bool, x.length = 2 ^ k - 1 →
        (evalCircuit x (fischerCompile k gs)).getD outWire false = (evalCircuit x gs).getD w false

/-- C12: Schnorr / Boyar–Peralta Multiplicative Complexity degree bound & `MC(AND_n) ≥ n - 1`. -/
def MultiplicativeComplexityStmt : Prop :=
  (∀ (n : Nat) (gs : List XorAndOp) (w : Nat),
    HasF2DegLe n (fun x => (evalXorAndCircuit (vecToBits x) gs).getD w false) (andCount gs + 1)) ∧
  (∀ (n : Nat), 1 ≤ n → ∀ (gs : List XorAndOp) (w : Nat),
    (∀ x : Fin n → Bool, (evalXorAndCircuit (vecToBits x) gs).getD w false = andN n x) →
    n - 1 ≤ andCount gs)

/-- C13: Characteristic-2 Permanent/Determinant collapse vs separation over `ℤ` and `ℤ/pℤ` (`p ≥ 3`). -/
def PermDetChar2Stmt : Prop :=
  (∀ (n : Nat) (A : Fin n → Fin n → Int), permInt n A % 2 = detInt n A % 2) ∧
  (∀ (n : Nat), 2 ≤ n →
    permInt n (witnessMat n) = 2 ∧
    detInt n (witnessMat n) = 0 ∧
    (∀ p : Int, 3 ≤ p → permInt n (witnessMat n) % p ≠ detInt n (witnessMat n) % p))

/-- C14: Catalytic zero-workspace reversible algebra (bijective reversibility + exact `d`-fold product). -/
def CatalyticAlgebraStmt : Prop :=
  (∀ (prog : List CatInstr), (∀ i ∈ prog, i.WellFormed) → ∀ s : RegState,
    execProg (invertProg prog) (execProg prog s) = s) ∧
  (∀ (xs : List Int), xs ≠ [] → ∀ (dst : Nat), xs.length ≤ dst → ∀ (sign : Bool) (s : RegState),
    (∀ i ∈ catalyticProdProg dst xs sign, i.WellFormed) ∧
    execProg (catalyticProdProg dst xs sign) s =
      setReg s dst (s dst + (if sign then 1 else -1) * listProd xs) ∧
    (catalyticProdProg dst xs sign).length + 2 = 3 * 4 ^ (xs.length - 1))

/-- Master Conjunction of all 14 formalized frontier claims. -/
def AllFrontierTheoremsStmt : Prop :=
  PSubsetNPStmt ∧
  BakerGillSolovayStmt ∧
  NaturalProofBreaksPRFStmt ∧
  HybridTelescopingStmt ∧
  NaturalProofNonvacuousStmt ∧
  OddCycleContextualStmt ∧
  MerminPeresContextualStmt ∧
  TractablePolymorphismsStmt ∧
  Monotone3SATRigidStmt ∧
  MarkovInverterTightStmt ∧
  FischerReductionStmt ∧
  MultiplicativeComplexityStmt ∧
  PermDetChar2Stmt ∧
  CatalyticAlgebraStmt

end

end Challenge
