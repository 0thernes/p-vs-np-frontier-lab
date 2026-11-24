module

/-!
# Sheaf Contextuality Collapse & Inclusion-Minimal 3-SAT Polymorphism Rigidity

Formalizes two cross-domain algebraic/topological investigations of P vs NP:

1. **Sheaf-Theoretic Contextuality (Wild Path 1 & 2):**
   Models finite Boolean CSPs as constraint presheaves where satisfiability is
   existence of a global section and maximal (strong) contextuality means no
   global section exists while every drop-1 subsystem is locally satisfiable.
   Proves that:
   - The infinite family of odd-cycle XOR-2SAT systems `C_{2k+1}` (`k ≥ 1`) is
     maximally contextual yet purely linear over `F_2` (`XOR-SAT ⊆ P`).
   - The 9-variable, 6-equation Mermin–Peres `3×3` Magic Square is maximally
     contextual and lives strictly inside `XOR-3SAT ⊆ P`.
   Hence maximal sheaf contextuality / `H^1 ≠ 0` does not by itself separate
   `P` from `NP`.

2. **Universal-Algebraic Polymorphism Rigidity (Wild Path 3):**
   Proves that the tractable Schaefer classes admit nontrivial polymorphisms
   (Mal'tsev `x ⊕ y ⊕ z` for XOR-3SAT, `&&` for Horn-3SAT, `||` for Dual-Horn,
   Majority for 2-SAT), whereas **just the two monotone/anti-monotone 3-SAT
   clause relations `{R000, R111}` are already inclusion-minimal rigid across
   ALL finite arities `k ≥ 1`**: every `k`-ary Boolean polymorphism preserving
   both `R000` and `R111` is a dictator/projection `v ↦ v j`, while omitting
   either relation admits a non-projection constant polymorphism.
-/

namespace PVsNP

@[expose] public section

-- ============================================================================
-- Part 1: Constraint Presheaves & Maximal Contextuality
-- ============================================================================

/-- A Boolean constraint on `n` variables. -/
abbrev BoolConstraint (n : Nat) := (Fin n → Bool) → Bool

/-- A constraint system admits a global section (satisfying assignment). -/
def HasGlobalSection {n : Nat} (cs : List (BoolConstraint n)) : Prop :=
  ∃ a : Fin n → Bool, ∀ c ∈ cs, c a = true

/-- Deleting constraint `idx` yields a locally satisfiable subsystem. -/
def SatisfiableWithout {n : Nat} (cs : List (BoolConstraint n)) (idx : Nat) : Prop :=
  ∃ a : Fin n → Bool, ∀ (j : Nat) (hj : j < cs.length), j ≠ idx → (cs[j]'hj) a = true

/-- Maximal (strong) sheaf contextuality: no global section exists, yet every
    drop-1 proper subsystem admits a local section. -/
def IsMaximallyContextual {n : Nat} (cs : List (BoolConstraint n)) : Prop :=
  ¬ HasGlobalSection cs ∧ ∀ idx < cs.length, SatisfiableWithout cs idx

/-- Odd-cycle XOR-2SAT system on `n = 2k + 1` variables:
    for each `i < n`, enforces `x_i ⊕ x_{(i+1) mod n} = 1` (i.e. `x_i ≠ x_{(i+1) mod n}`). -/
def oddCycleConstraint (k : Nat) (i : Nat) : BoolConstraint (2 * k + 1) :=
  fun a =>
    let n := 2 * k + 1
    xor (a ⟨i % n, Nat.mod_lt i (by omega)⟩) (a ⟨(i + 1) % n, Nat.mod_lt (i + 1) (by omega)⟩)

def oddCycleSystem (k : Nat) : List (BoolConstraint (2 * k + 1)) :=
  (List.range (2 * k + 1)).map (oddCycleConstraint k)

/-- Explicit 9-variable, 6-equation Mermin–Peres `3×3` Magic Square in `XOR-3SAT`:
    Rows 0, 1, 2 have parity `0`; Columns 0, 1 have parity `0`; Column 2 has parity `1`. -/
def xor3Constraint (i j l : Fin 9) (rhs : Bool) : BoolConstraint 9 :=
  fun a => (xor (xor (a i) (a j)) (a l)) == rhs

def merminPeresSystem : List (BoolConstraint 9) :=
  [ xor3Constraint ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ false
  , xor3Constraint ⟨3, by decide⟩ ⟨4, by decide⟩ ⟨5, by decide⟩ false
  , xor3Constraint ⟨6, by decide⟩ ⟨7, by decide⟩ ⟨8, by decide⟩ false
  , xor3Constraint ⟨0, by decide⟩ ⟨3, by decide⟩ ⟨6, by decide⟩ false
  , xor3Constraint ⟨1, by decide⟩ ⟨4, by decide⟩ ⟨7, by decide⟩ false
  , xor3Constraint ⟨2, by decide⟩ ⟨5, by decide⟩ ⟨8, by decide⟩ true ]

-- ============================================================================
-- Part 2: Boolean Relations & Polymorphism Clones
-- ============================================================================

/-- Ternary Boolean relation `R ⊆ {0,1}^3` preserved by a `k`-ary operation `f`. -/
def Preserves3 (R : Bool → Bool → Bool → Prop) {k : Nat} (f : (Fin k → Bool) → Bool) : Prop :=
  ∀ x y z : Fin k → Bool,
    (∀ i : Fin k, R (x i) (y i) (z i)) → R (f x) (f y) (f z)

/-- Binary Boolean relation `R ⊆ {0,1}^2` preserved by a `k`-ary operation `f`. -/
def Preserves2 (R : Bool → Bool → Prop) {k : Nat} (f : (Fin k → Bool) → Bool) : Prop :=
  ∀ x y : Fin k → Bool,
    (∀ i : Fin k, R (x i) (y i)) → R (f x) (f y)

/-- All-positive 3-SAT clause `x ∨ y ∨ z` (forbids `(0,0,0)`). -/
def R000 (a b c : Bool) : Prop := a = true ∨ b = true ∨ c = true

/-- All-negative 3-SAT clause `¬x ∨ ¬y ∨ ¬z` (forbids `(1,1,1)`). -/
def R111 (a b c : Bool) : Prop := a = false ∨ b = false ∨ c = false

/-- 3-variable affine XOR relation `x ⊕ y ⊕ z = rhs`. -/
def RXor3 (rhs a b c : Bool) : Prop := xor (xor a b) c = rhs

/-- Horn 3-SAT clause `¬x ∨ ¬y ∨ z`. -/
def RHorn (a b c : Bool) : Prop := a = false ∨ b = false ∨ c = true

/-- Dual-Horn 3-SAT clause `x ∨ y ∨ ¬z`. -/
def RDualHorn (a b c : Bool) : Prop := a = true ∨ b = true ∨ c = false

/-- General 2-SAT clause `(a = p) ∨ (b = q)`. -/
def R2Clause (p q a b : Bool) : Prop := a = p ∨ b = q

/-- Ternary Mal'tsev (affine) operation `x ⊕ y ⊕ z`. -/
def opMaltsev (v : Fin 3 → Bool) : Bool :=
  xor (xor (v ⟨0, by decide⟩) (v ⟨1, by decide⟩)) (v ⟨2, by decide⟩)

/-- Ternary Majority operation. -/
def opMajority (v : Fin 3 → Bool) : Bool :=
  (v ⟨0, by decide⟩ && v ⟨1, by decide⟩) ||
  (v ⟨1, by decide⟩ && v ⟨2, by decide⟩) ||
  (v ⟨0, by decide⟩ && v ⟨2, by decide⟩)

/-- Binary conjunction. -/
def opAnd (v : Fin 2 → Bool) : Bool :=
  v ⟨0, by decide⟩ && v ⟨1, by decide⟩

/-- Binary disjunction. -/
def opOr (v : Fin 2 → Bool) : Bool :=
  v ⟨0, by decide⟩ || v ⟨1, by decide⟩

/-- A `k`-ary Boolean operation is a projection (dictator). -/
def IsProjection {k : Nat} (f : (Fin k → Bool) → Bool) : Prop :=
  ∃ j : Fin k, ∀ v : Fin k → Bool, f v = v j

end

-- ============================================================================
-- Proofs: Part 1 (Odd-Cycle & Mermin–Peres Maximal Contextuality in XOR-SAT)
-- ============================================================================

private theorem bool_xor_eq_true_iff (a b : Bool) : xor a b = true ↔ a = !b := by
  cases a <;> cases b <;> decide

private theorem oddCycle_parity_walk (k : Nat) (a : Fin (2 * k + 1) → Bool)
    (hstep : ∀ i (hi : i < 2 * k), xor (a ⟨i, by omega⟩) (a ⟨i + 1, by omega⟩) = true) :
    ∀ m (hm : m ≤ 2 * k), a ⟨m, by omega⟩ = if m % 2 == 0 then a ⟨0, by omega⟩ else !(a ⟨0, by omega⟩) := by
  intro m
  induction m with
  | zero =>
    intro _
    simp
  | succ m ih =>
    intro hm
    have hprev := ih (by omega)
    have hxor := hstep m (by omega)
    have hflip : a ⟨m + 1, by omega⟩ = !(a ⟨m, by omega⟩) := by
      have := (bool_xor_eq_true_iff (a ⟨m, by omega⟩) (a ⟨m + 1, by omega⟩)).mp hxor
      cases h1 : a ⟨m, by omega⟩ <;> cases h2 : a ⟨m + 1, by omega⟩ <;> simp [h1, h2] at this ⊢
    rw [hflip, hprev]
    by_cases hme : m % 2 = 0
    · have h1m : (m + 1) % 2 = 1 := by omega
      simp [hme, h1m]
    · have h0m : m % 2 = 1 := by omega
      have h1m : (m + 1) % 2 = 0 := by omega
      simp [h0m, h1m]

/-- Headline Theorem (Infinite Maximally Contextual Family inside XOR-SAT ⊆ P):
    For every `k ≥ 1`, the `(2k+1)`-variable odd-cycle XOR-2SAT system is
    maximally contextual (no global section, every drop-1 subsystem satisfiable),
    despite being linear over `F_2` and decidable in linear time. -/
public theorem odd_cycle_xor_maximally_contextual (k : Nat) :
    IsMaximallyContextual (oddCycleSystem k) := by
  constructor
  · -- Unsatisfiability (no global section)
    rintro ⟨a, ha⟩
    have hall : ∀ i < 2 * k + 1, oddCycleConstraint k i a = true := by
      intro i hi
      apply ha
      unfold oddCycleSystem
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
    have hstep : ∀ i (hi : i < 2 * k), xor (a ⟨i, by omega⟩) (a ⟨i + 1, by omega⟩) = true := by
      intro i hi
      have h := hall i (by omega)
      unfold oddCycleConstraint at h
      have hm1 : i % (2 * k + 1) = i := Nat.mod_eq_of_lt (by omega)
      have hm2 : (i + 1) % (2 * k + 1) = i + 1 := Nat.mod_eq_of_lt (by omega)
      simpa only [hm1, hm2] using h
    have hend := oddCycle_parity_walk k a hstep (2 * k) (Nat.le_refl _)
    have hmod2k : (2 * k % 2 == 0) = true := by
      have : (2 * k) % 2 = 0 := by omega
      simp [this]
    rw [hmod2k] at hend
    simp only [↓reduceIte] at hend
    have hwrap := hall (2 * k) (by omega)
    unfold oddCycleConstraint at hwrap
    have hm1 : (2 * k) % (2 * k + 1) = 2 * k := Nat.mod_eq_of_lt (by omega)
    have hm2 : (2 * k + 1) % (2 * k + 1) = 0 := Nat.mod_self (2 * k + 1)
    simp only [hm1, hm2] at hwrap
    rw [hend] at hwrap
    cases a ⟨0, by omega⟩ <;> simp at hwrap
  · -- Every drop-1 subsystem is satisfiable
    intro idx hidx
    have hlen : (oddCycleSystem k).length = 2 * k + 1 := by
      unfold oddCycleSystem; simp
    rw [hlen] at hidx
    let a : Fin (2 * k + 1) → Bool := fun v =>
      if v.val ≤ idx then decide (v.val % 2 == 0) else decide (v.val % 2 == 1)
    refine ⟨a, ?_⟩
    intro j hj hne
    have hjlt : j < 2 * k + 1 := by omega
    have hget : (oddCycleSystem k)[j]'hj = oddCycleConstraint k j := by
      simp [oddCycleSystem]
    rw [hget]
    unfold oddCycleConstraint
    have hm1 : j % (2 * k + 1) = j := Nat.mod_eq_of_lt hjlt
    by_cases hj_last : j = 2 * k
    · -- Wrap-around edge `(2*k, 0)`, so `idx < 2*k`
      subst hj_last
      have hm2 : (2 * k + 1) % (2 * k + 1) = 0 := Nat.mod_self (2 * k + 1)
      change xor (a ⟨2 * k % (2 * k + 1), _⟩) (a ⟨(2 * k + 1) % (2 * k + 1), _⟩) = true
      have ha1 : a ⟨2 * k % (2 * k + 1), Nat.mod_lt _ (by omega)⟩ = false := by
        dsimp only [a]
        simp only [hm1]
        have hgt : ¬ (2 * k ≤ idx) := by omega
        have heven : (2 * k) % 2 = 0 := by omega
        simp [hgt, heven]
      have ha2 : a ⟨(2 * k + 1) % (2 * k + 1), Nat.mod_lt _ (by omega)⟩ = true := by
        dsimp only [a]
        simp only [hm2]
        simp
      rw [ha1, ha2]; rfl
    · -- Interior edge `(j, j + 1)` with `j < 2*k` and `j ≠ idx`
      have hm2 : (j + 1) % (2 * k + 1) = j + 1 := Nat.mod_eq_of_lt (by omega)
      change xor (a ⟨j % (2 * k + 1), _⟩) (a ⟨(j + 1) % (2 * k + 1), _⟩) = true
      dsimp only [a]
      simp only [hm1, hm2]
      by_cases hle : j ≤ idx
      · have hle1 : j + 1 ≤ idx := by omega
        simp only [hle, hle1, ↓reduceIte]
        have hpar : j % 2 = 0 ∨ j % 2 = 1 := by omega
        rcases hpar with h0 | h1
        · have h1' : (j + 1) % 2 = 1 := by omega
          simp [h0, h1']
        · have h0' : (j + 1) % 2 = 0 := by omega
          simp [h1, h0']
      · have hgt1 : ¬ (j + 1 ≤ idx) := by omega
        simp only [hle, hgt1, ↓reduceIte]
        have hpar : j % 2 = 0 ∨ j % 2 = 1 := by omega
        rcases hpar with h0 | h1
        · have h1' : (j + 1) % 2 = 1 := by omega
          simp [h0, h1']
        · have h0' : (j + 1) % 2 = 0 := by omega
          simp [h1, h0']

/-- Headline Theorem (Mermin–Peres Quantum Contextuality Gadget inside XOR-3SAT ⊆ P):
    The 9-variable, 6-equation Mermin–Peres magic square is maximally contextual
    (unsatisfiable globally, every 5-equation sub-system satisfiable), while every
    constraint is a linear XOR-3SAT equation over `F_2`. -/
public theorem mermin_peres_maximally_contextual :
    IsMaximallyContextual merminPeresSystem := by
  constructor
  · rintro ⟨a, ha⟩
    have h0 : xor (xor (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)) (a ⟨2, by decide⟩) = false := by
      have := ha (xor3Constraint ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ false)
        (by unfold merminPeresSystem; simp)
      simpa [xor3Constraint] using this
    have h1 : xor (xor (a ⟨3, by decide⟩) (a ⟨4, by decide⟩)) (a ⟨5, by decide⟩) = false := by
      have := ha (xor3Constraint ⟨3, by decide⟩ ⟨4, by decide⟩ ⟨5, by decide⟩ false)
        (by unfold merminPeresSystem; simp)
      simpa [xor3Constraint] using this
    have h2 : xor (xor (a ⟨6, by decide⟩) (a ⟨7, by decide⟩)) (a ⟨8, by decide⟩) = false := by
      have := ha (xor3Constraint ⟨6, by decide⟩ ⟨7, by decide⟩ ⟨8, by decide⟩ false)
        (by unfold merminPeresSystem; simp)
      simpa [xor3Constraint] using this
    have h3 : xor (xor (a ⟨0, by decide⟩) (a ⟨3, by decide⟩)) (a ⟨6, by decide⟩) = false := by
      have := ha (xor3Constraint ⟨0, by decide⟩ ⟨3, by decide⟩ ⟨6, by decide⟩ false)
        (by unfold merminPeresSystem; simp)
      simpa [xor3Constraint] using this
    have h4 : xor (xor (a ⟨1, by decide⟩) (a ⟨4, by decide⟩)) (a ⟨7, by decide⟩) = false := by
      have := ha (xor3Constraint ⟨1, by decide⟩ ⟨4, by decide⟩ ⟨7, by decide⟩ false)
        (by unfold merminPeresSystem; simp)
      simpa [xor3Constraint] using this
    have h5 : xor (xor (a ⟨2, by decide⟩) (a ⟨5, by decide⟩)) (a ⟨8, by decide⟩) = true := by
      have := ha (xor3Constraint ⟨2, by decide⟩ ⟨5, by decide⟩ ⟨8, by decide⟩ true)
        (by unfold merminPeresSystem; simp)
      simpa [xor3Constraint] using this
    -- Parity contradiction: XOR of all 3 rows = false, XOR of all 3 cols = true
    generalize a ⟨0, by decide⟩ = x0 at h0 h3
    generalize a ⟨1, by decide⟩ = x1 at h0 h4
    generalize a ⟨2, by decide⟩ = x2 at h0 h5
    generalize a ⟨3, by decide⟩ = x3 at h1 h3
    generalize a ⟨4, by decide⟩ = x4 at h1 h4
    generalize a ⟨5, by decide⟩ = x5 at h1 h5
    generalize a ⟨6, by decide⟩ = x6 at h2 h3
    generalize a ⟨7, by decide⟩ = x7 at h2 h4
    generalize a ⟨8, by decide⟩ = x8 at h2 h5
    cases x0 <;> cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;>
    cases x5 <;> cases x6 <;> cases x7 <;> cases x8 <;> simp_all
  · intro idx hidx
    -- Explicit local section for each of the 6 dropped equations
    have hlen : merminPeresSystem.length = 6 := rfl
    rw [hlen] at hidx
    match idx with
    | 0 =>
      refine ⟨fun i => decide (i.val = 2), ?_⟩
      intro j hj hne
      match j with
      | 0 => exact absurd rfl hne
      | 1 | 2 | 3 | 4 | 5 => rfl
    | 1 =>
      refine ⟨fun i => decide (i.val = 5), ?_⟩
      intro j hj hne
      match j with
      | 1 => exact absurd rfl hne
      | 0 | 2 | 3 | 4 | 5 => rfl
    | 2 =>
      refine ⟨fun i => decide (i.val = 8), ?_⟩
      intro j hj hne
      match j with
      | 2 => exact absurd rfl hne
      | 0 | 1 | 3 | 4 | 5 => rfl
    | 3 =>
      refine ⟨fun i => decide (i.val = 0 ∨ i.val = 2), ?_⟩
      intro j hj hne
      match j with
      | 3 => exact absurd rfl hne
      | 0 | 1 | 2 | 4 | 5 => rfl
    | 4 =>
      refine ⟨fun i => decide (i.val = 1 ∨ i.val = 2), ?_⟩
      intro j hj hne
      match j with
      | 4 => exact absurd rfl hne
      | 0 | 1 | 2 | 3 | 5 => rfl
    | 5 =>
      refine ⟨fun _ => false, ?_⟩
      intro j hj hne
      match j with
      | 5 => exact absurd rfl hne
      | 0 | 1 | 2 | 3 | 4 => rfl
    | n + 6 => omega

-- ============================================================================
-- Proofs: Part 2 (Tractable Polymorphisms & Inclusion-Minimal 3-SAT Rigidity)
-- ============================================================================

/-- XOR-3SAT is preserved by the ternary Mal'tsev operation `x ⊕ y ⊕ z`. -/
public theorem xorsat_maltsev (rhs : Bool) : Preserves3 (RXor3 rhs) opMaltsev := by
  intro x y z h
  have h0 := h ⟨0, by decide⟩
  have h1 := h ⟨1, by decide⟩
  have h2 := h ⟨2, by decide⟩
  unfold RXor3 at h0 h1 h2 ⊢
  unfold opMaltsev
  generalize x ⟨0, by decide⟩ = x0 at h0 ⊢
  generalize x ⟨1, by decide⟩ = x1 at h1 ⊢
  generalize x ⟨2, by decide⟩ = x2 at h2 ⊢
  generalize y ⟨0, by decide⟩ = y0 at h0 ⊢
  generalize y ⟨1, by decide⟩ = y1 at h1 ⊢
  generalize y ⟨2, by decide⟩ = y2 at h2 ⊢
  generalize z ⟨0, by decide⟩ = z0 at h0 ⊢
  generalize z ⟨1, by decide⟩ = z1 at h1 ⊢
  generalize z ⟨2, by decide⟩ = z2 at h2 ⊢
  cases rhs <;> cases x0 <;> cases x1 <;> cases x2 <;>
  cases y0 <;> cases y1 <;> cases y2 <;>
  cases z0 <;> cases z1 <;> cases z2 <;> simp_all

/-- Horn-3SAT is preserved by binary conjunction `&&`. -/
public theorem hornsat_and : Preserves3 RHorn opAnd := by
  intro x y z h
  have h0 := h ⟨0, by decide⟩
  have h1 := h ⟨1, by decide⟩
  unfold RHorn at h0 h1 ⊢
  unfold opAnd
  cases hx0 : x ⟨0, by decide⟩ <;> cases hx1 : x ⟨1, by decide⟩ <;>
  cases hy0 : y ⟨0, by decide⟩ <;> cases hy1 : y ⟨1, by decide⟩ <;>
  cases hz0 : z ⟨0, by decide⟩ <;> cases hz1 : z ⟨1, by decide⟩ <;> simp_all

/-- Dual-Horn-3SAT is preserved by binary disjunction `||`. -/
public theorem dualhornsat_or : Preserves3 RDualHorn opOr := by
  intro x y z h
  have h0 := h ⟨0, by decide⟩
  have h1 := h ⟨1, by decide⟩
  unfold RDualHorn at h0 h1 ⊢
  unfold opOr
  cases hx0 : x ⟨0, by decide⟩ <;> cases hx1 : x ⟨1, by decide⟩ <;>
  cases hy0 : y ⟨0, by decide⟩ <;> cases hy1 : y ⟨1, by decide⟩ <;>
  cases hz0 : z ⟨0, by decide⟩ <;> cases hz1 : z ⟨1, by decide⟩ <;> simp_all

/-- Every 2-SAT clause relation is preserved by ternary Majority. -/
public theorem twosat_majority (p q : Bool) : Preserves2 (R2Clause p q) opMajority := by
  intro x y h
  have h0 := h ⟨0, by decide⟩
  have h1 := h ⟨1, by decide⟩
  have h2 := h ⟨2, by decide⟩
  unfold R2Clause at h0 h1 h2 ⊢
  unfold opMajority
  generalize x ⟨0, by decide⟩ = x0 at h0 ⊢
  generalize x ⟨1, by decide⟩ = x1 at h1 ⊢
  generalize x ⟨2, by decide⟩ = x2 at h2 ⊢
  generalize y ⟨0, by decide⟩ = y0 at h0 ⊢
  generalize y ⟨1, by decide⟩ = y1 at h1 ⊢
  generalize y ⟨2, by decide⟩ = y2 at h2 ⊢
  cases p <;> cases q <;> cases x0 <;> cases x1 <;> cases x2 <;>
  cases y0 <;> cases y1 <;> cases y2 <;> simp_all

private theorem find_first_true (P : Nat → Bool) (k : Nat)
    (h0 : P 0 = false) (hk : P k = true) :
    ∃ j : Nat, j < k ∧ P j = false ∧ P (j + 1) = true := by
  induction k with
  | zero =>
    rw [h0] at hk
    exact Bool.noConfusion hk
  | succ k ih =>
    cases hpk : P k
    · exact ⟨k, Nat.lt_succ_self k, hpk, hk⟩
    · rcases ih hpk with ⟨j, hj, hf, ht⟩
      exact ⟨j, Nat.lt_trans hj (Nat.lt_succ_self k), hf, ht⟩

/-- Headline Theorem (Inclusion-Minimal All-Arity Rigidity of Monotone 3-SAT):
    For EVERY finite arity `k ≥ 1` and EVERY Boolean operation `f : (Fin k → Bool) → Bool`,
    if `f` preserves just the two monotone/anti-monotone 3-SAT clause relations
    `R000` (`x ∨ y ∨ z`) and `R111` (`¬x ∨ ¬y ∨ ¬z`), then `f` MUST be a
    projection (dictator): `∃ j : Fin k, ∀ v, f v = v j`. -/
public theorem monotone_3sat_only_projections {k : Nat} (f : (Fin k → Bool) → Bool)
    (h0 : Preserves3 R000 f) (h1 : Preserves3 R111 f) :
    IsProjection f := by
  -- Step 1: Idempotence at all-false and all-true
  have hfF : f (fun _ => false) = false := by
    have hr := h1 (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => Or.inl rfl)
    unfold R111 at hr
    rcases hr with h | h | h <;> exact h
  have hfT : f (fun _ => true) = true := by
    have hr := h0 (fun _ => true) (fun _ => true) (fun _ => true) (fun _ => Or.inl rfl)
    unfold R000 at hr
    rcases hr with h | h | h <;> exact h
  -- Step 2: Disjoint-support exclusion (`u ∧ v = 0 → f u = false ∨ f v = false`)
  have hdisj : ∀ u v : Fin k → Bool,
      (∀ i, u i = false ∨ v i = false) → f u = false ∨ f v = false := by
    intro u v huv
    have hr := h1 u v (fun _ => true) (fun i => by
      rcases huv i with hu | hv
      · exact Or.inl hu
      · exact Or.inr (Or.inl hv))
    unfold R111 at hr
    rw [hfT] at hr
    rcases hr with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Bool.noConfusion h
  -- Step 3: Self-duality (`f (fun i => !u i) = !f u`)
  have hdual : ∀ u : Fin k → Bool, f (fun i => !(u i)) = !(f u) := by
    intro u
    have hor := h0 u (fun i => !(u i)) (fun _ => false) (fun i => by
      cases hu : u i
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl)
    unfold R000 at hor
    rw [hfF] at hor
    have hnotboth := hdisj u (fun i => !(u i)) (fun i => by
      cases hu : u i
      · exact Or.inl rfl
      · exact Or.inr rfl)
    cases hfu : f u <;> cases hfn : f (fun i => !(u i))
    · rcases hor with h | h | h <;> simp [hfu, hfn] at h
    · rfl
    · rfl
    · rcases hnotboth with h | h <;> simp [hfu, hfn] at h
  -- Step 4: Monotonicity (`u ≤ v → f u = true → f v = true`)
  have hmono : ∀ u v : Fin k → Bool,
      (∀ i, u i = true → v i = true) → f u = true → f v = true := by
    intro u v hle hfu
    have hdv : ∀ i, u i = false ∨ (!(v i)) = false := by
      intro i
      cases hu : u i
      · exact Or.inl rfl
      · exact Or.inr (by rw [hle i hu]; rfl)
    rcases hdisj u (fun i => !(v i)) hdv with h | h
    · rw [hfu] at h; exact Bool.noConfusion h
    · rw [hdual v] at h
      cases hfv : f v
      · simp [hfv] at h
      · rfl
  -- Step 5: Finite intersection closure (`f u = true → f v = true → f (u ∧ v) = true`)
  have hand : ∀ u v : Fin k → Bool,
      f u = true → f v = true → f (fun i => u i && v i) = true := by
    intro u v hfu hfv
    have hr := h1 u v (fun i => !(u i && v i)) (fun i => by
      cases hu : u i <;> cases hv : v i
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl))
    unfold R111 at hr
    rw [hfu, hfv] at hr
    rcases hr with h | h | h
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h
    · rw [hdual (fun i => u i && v i)] at h
      cases hfa : f (fun i => u i && v i)
      · simp [hfa] at h
      · rfl
  -- Step 6: Principal ultrafilter extraction via first prefix turning `f` true
  let prefVec : Nat → (Fin k → Bool) := fun m i => decide (i.val < m)
  have hp0 : f (prefVec 0) = false := by
    have heq : prefVec 0 = (fun _ => false) := by
      funext i; simp [prefVec]
    rw [heq]; exact hfF
  have hpk : f (prefVec k) = true := by
    have heq : prefVec k = (fun _ => true) := by
      funext i; simp [prefVec, i.isLt]
    rw [heq]; exact hfT
  rcases find_first_true (fun m => f (prefVec m)) k hp0 hpk with ⟨j, hjlt, hfj, hfj1⟩
  have hcomp_j : f (fun i => !(prefVec j i)) = true := by
    rw [hdual (prefVec j), hfj]; rfl
  have hsing : f (fun i => prefVec (j + 1) i && !(prefVec j i)) = true :=
    hand (prefVec (j + 1)) (fun i => !(prefVec j i)) hfj1 hcomp_j
  let eJ : Fin k → Bool := fun i => decide (i.val = j)
  have heJ_eq : (fun i : Fin k => prefVec (j + 1) i && !(prefVec j i)) = eJ := by
    funext i
    simp only [prefVec, eJ]
    by_cases h : i.val = j
    · subst h; simp
    · by_cases hlt : i.val < j
      · have hlt1 : i.val < j + 1 := by omega
        simp [hlt, hlt1, h]
      · have hnot : ¬ (i.val < j + 1) := by omega
        simp [hlt, hnot, h]
  rw [heJ_eq] at hsing
  refine ⟨⟨j, hjlt⟩, fun v => ?_⟩
  cases hv : v ⟨j, hjlt⟩
  · have hle : ∀ i : Fin k, eJ i = true → !(v i) = true := by
      intro i hi
      simp only [eJ, decide_eq_true_eq] at hi
      have hfin : i = ⟨j, hjlt⟩ := Fin.ext hi
      rw [hfin, hv]; rfl
    have hfnot := hmono eJ (fun i => !(v i)) hle hsing
    rw [hdual v] at hfnot
    cases hfv : f v
    · rfl
    · simp [hfv] at hfnot
  · have hle : ∀ i : Fin k, eJ i = true → v i = true := by
      intro i hi
      simp only [eJ, decide_eq_true_eq] at hi
      have hfin : i = ⟨j, hjlt⟩ := Fin.ext hi
      rw [hfin, hv]
    exact hmono eJ v hle hsing

/-- Minimality Theorem: Omitting either `R111` or `R000` breaks rigidity for
    every arity `k ≥ 1` (witnessed by constant-true and constant-false). -/
public theorem monotone_3sat_minimal (k : Nat) :
    (Preserves3 R000 (fun (_ : Fin k → Bool) => true) ∧
     ¬ IsProjection (fun (_ : Fin k → Bool) => true)) ∧
    (Preserves3 R111 (fun (_ : Fin k → Bool) => false) ∧
     ¬ IsProjection (fun (_ : Fin k → Bool) => false)) := by
  refine ⟨⟨fun _ _ _ _ => Or.inl rfl, ?_⟩, ⟨fun _ _ _ _ => Or.inl rfl, ?_⟩⟩
  · rintro ⟨j, hj⟩
    have := hj (fun _ => false)
    exact Bool.noConfusion this
  · rintro ⟨j, hj⟩
    have := hj (fun _ => true)
    exact Bool.noConfusion this

end PVsNP
