module

public import PVsNP.Basic

/-!
# Circuit Phase Transitions, Multiplicative Complexity, and Characteristic-2 Collapse

Formalizes three foundational lower-bound and structural phase-transition theorems
across Boolean and algebraic circuit complexity:

1. **Bounded-Negation Phase Transition (Markov 1957 & Fischer 1975 — Wild Path 5):**
   - `markov_inverter_lower`: Over arbitrary DAG Boolean circuits `{const, and, or, not}`,
     if `2^r ≤ n`, NO circuit with `≤ r` NOT gates can simultaneously invert `n` inputs
     (proved via constructive chain pigeonhole on `{0^n < ... < 1^n}`).
   - `markov_inverter_upper`: For every `k : Nat`, an explicit DAG circuit `markovInverter k`
     with **exactly `k` NOT gates** simultaneously inverts all `n = 2^k - 1` inputs.
   - `fischer_negation_reduction`: Every Boolean circuit on `n = 2^k - 1` inputs compiles
     via De Morgan dual-rail expansion + `markovInverter k` into an equivalent circuit
     using **exactly `k` NOT gates**.

2. **Multiplicative Complexity / Non-Clifford Degree Bound (Schnorr / Boyar–Peralta — Wild Path 4):**
   - `mc_degree_lower_bound`: Every wire of any `{1, XOR, AND}` circuit with `k` AND gates
     has `F_2` algebraic degree `≤ k + 1` (proved via the subset-product invariant
     `deg(∏_{i ∈ S} g_i) ≤ t + |S|`).
   - `mc_andN_lower`: For every `n ≥ 1`, `AND_n` cannot be represented with degree `≤ n - 1`,
     hence requires at least `n - 1` AND gates (matching the exact `n - 1` upper bound).

3. **Characteristic-2 Permanent/Determinant Collapse vs Separation (Wild Path 9):**
   - `perm_eq_det_mod2`: For every `n` and integer matrix `A`, `permInt n A % 2 = detInt n A % 2`.
   - `perm_ne_det_witness`: For every `n ≥ 2`, the explicit `{0,1}`-matrix `W_n = diag(J_2, I_{n-2})`
     has `permInt n W_n = 2` and `detInt n W_n = 0`, separating `Perm_n` from `det_n` over
     `ℤ` and over `ℤ/pℤ` for EVERY `p ≥ 3`.
-/

namespace PVsNP

@[expose] public section

-- ============================================================================
-- Part 1: Straight-Line Boolean DAG Circuits, Markov (1957), and Fischer (1975)
-- ============================================================================

/-- Elementary gate over the De Morgan basis `{const, and, or, not}`. -/
inductive GateOp where
  | const (b : Bool)
  | and (i j : Nat)
  | or (i j : Nat)
  | not (i : Nat)
  deriving Repr, DecidableEq

/-- Evaluate a single gate against the current wire values. -/
def evalGate (wires : List Bool) : GateOp → Bool
  | .const b => b
  | .and i j => wires.getD i false && wires.getD j false
  | .or i j => wires.getD i false || wires.getD j false
  | .not i => !(wires.getD i false)

/-- Evaluate a straight-line DAG circuit on input bitstring `x`, appending each
    gate's output wire in topological order. -/
def evalCircuit (x : List Bool) (gs : List GateOp) : List Bool :=
  gs.foldl (fun ws g => ws ++ [evalGate ws g]) x

/-- Number of NOT gates in a circuit. -/
def notCount : List GateOp → Nat
  | [] => 0
  | .not _ :: gs => 1 + notCount gs
  | _ :: gs => notCount gs

/-- List of Boolean values produced by all NOT gates in topological order. -/
def notOutputsAux (ws : List Bool) : List GateOp → List Bool
  | [] => []
  | g :: gs =>
    let v := evalGate ws g
    let ws' := ws ++ [v]
    match g with
    | .not _ => v :: notOutputsAux ws' gs
    | _ => notOutputsAux ws' gs

def notOutputs (x : List Bool) (gs : List GateOp) : List Bool :=
  notOutputsAux x gs

/-- Pointwise Boolean order on bitstrings of equal length. -/
def BitsLe (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i : Nat, x.getD i false = true → y.getD i false = true

/-- A circuit with output wire map `outs : Fin n → Nat` inverts all `n` input bits. -/
def ComputesInverter (n : Nat) (gs : List GateOp) (outs : Fin n → Nat) : Prop :=
  ∀ x : List Bool, x.length = n →
    ∀ i : Fin n, (evalCircuit x gs).getD (outs i) false = !(x.getD i.val false)

-- ============================================================================
-- Part 2: Multiplicative Complexity (`{1, XOR, AND}` Straight-Line Circuits)
-- ============================================================================

/-- Elementary gate over the `{1, XOR, AND}` basis (`F_2` polynomials). -/
inductive XorAndOp where
  | const (b : Bool)
  | xor (i j : Nat)
  | and (i j : Nat)
  deriving Repr, DecidableEq

def evalXorAndGate (wires : List Bool) : XorAndOp → Bool
  | .const b => b
  | .xor i j => xor (wires.getD i false) (wires.getD j false)
  | .and i j => wires.getD i false && wires.getD j false

def evalXorAndCircuit (x : List Bool) (gs : List XorAndOp) : List Bool :=
  gs.foldl (fun ws g => ws ++ [evalXorAndGate ws g]) x

def andCount : List XorAndOp → Nat
  | [] => 0
  | .and _ _ :: gs => 1 + andCount gs
  | _ :: gs => andCount gs

/-- Evaluate an `F_2` polynomial given as a list of monomials (lists of variable indices). -/
def evalMonomial {n : Nat} (m : List (Fin n)) (x : Fin n → Bool) : Bool :=
  m.all (fun i => x i)

def evalPolyF2 {n : Nat} (ms : List (List (Fin n))) (x : Fin n → Bool) : Bool :=
  ms.foldl (fun acc m => xor acc (evalMonomial m x)) false

/-- `f : (Fin n → Bool) → Bool` has `F_2` algebraic degree `≤ d`. -/
def HasF2DegLe (n : Nat) (f : (Fin n → Bool) → Bool) (d : Nat) : Prop :=
  ∃ ms : List (List (Fin n)), (∀ m ∈ ms, m.length ≤ d) ∧ ∀ x, f x = evalPolyF2 ms x

/-- `n`-variable conjunction `AND_n(x) = x_0 ∧ ... ∧ x_{n-1}`. -/
def andN (n : Nat) (x : Fin n → Bool) : Bool :=
  (List.finRange n).all x

/-- Extract input bitstring from a `Fin n → Bool` vector. -/
def vecToBits {n : Nat} (x : Fin n → Bool) : List Bool :=
  (List.finRange n).map x

-- ============================================================================
-- Part 3: Integer Permanent & Determinant via Exact Laplace Expansion
-- ============================================================================

/-- Delete row `0` and column `c` from an `(n+1) × (n+1)` matrix. -/
def minor0 {n : Nat} (A : Fin (n + 1) → Fin (n + 1) → Int) (c : Fin (n + 1)) :
    Fin n → Fin n → Int :=
  fun i j =>
    let col : Fin (n + 1) :=
      if j.val < c.val then ⟨j.val, by omega⟩ else ⟨j.val + 1, by omega⟩
    A ⟨i.val + 1, by omega⟩ col

/-- Exact integer Permanent via Laplace expansion along row 0. -/
def permInt : (n : Nat) → (Fin n → Fin n → Int) → Int
  | 0, _ => 1
  | n + 1, A =>
    (List.finRange (n + 1)).foldl
      (fun acc c => acc + A ⟨0, by omega⟩ c * permInt n (minor0 A c)) 0

/-- Exact integer Determinant via Laplace expansion along row 0. -/
def detInt : (n : Nat) → (Fin n → Fin n → Int) → Int
  | 0, _ => 1
  | n + 1, A =>
    (List.finRange (n + 1)).foldl
      (fun acc c =>
        let sgn : Int := if c.val % 2 = 0 then 1 else -1
        acc + sgn * A ⟨0, by omega⟩ c * detInt n (minor0 A c)) 0

/-- Block-diagonal witness matrix `W_n = diag(I_{n-2}, J_2)`:
    top-left `(n-2)×(n-2)` identity block, bottom-right `2×2` all-ones block `J_2`,
    elsewhere `0`. Satisfies `minor0 W_{n+1} 0 = W_n` for all `n ≥ 2`. -/
def witnessMat (n : Nat) (i j : Fin n) : Int :=
  if n - 2 ≤ i.val ∧ n - 2 ≤ j.val then 1
  else if i.val = j.val then 1
  else 0

end

-- ============================================================================
-- Proofs Part 1A: Markov (1957) Exact Lower Bound via Constructive Chain Pigeonhole
-- ============================================================================

private theorem evalCircuit_nil (x : List Bool) : evalCircuit x [] = x := rfl

private theorem evalCircuit_cons (x : List Bool) (g : GateOp) (gs : List GateOp) :
    evalCircuit x (g :: gs) = evalCircuit (x ++ [evalGate x g]) gs := rfl

private theorem evalCircuit_append (x : List Bool) (g1 g2 : List GateOp) :
    evalCircuit x (g1 ++ g2) = evalCircuit (evalCircuit x g1) g2 := by
  unfold evalCircuit; exact List.foldl_append

private theorem evalCircuit_length (x : List Bool) (gs : List GateOp) :
    (evalCircuit x gs).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [evalCircuit]
  | cons g gs ih =>
    rw [evalCircuit_cons, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

private theorem evalCircuit_prefix_preserve (x : List Bool) (gs : List GateOp) :
    ∀ i < x.length, (evalCircuit x gs).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => intro i _; rfl
  | cons g gs ih =>
    intro i hi
    rw [evalCircuit_cons]
    have hi' : i < (x ++ [evalGate x g]).length := by simp; omega
    rw [ih (x ++ [evalGate x g]) i hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem notOutputsAux_length (ws : List Bool) (gs : List GateOp) :
    (notOutputsAux ws gs).length = notCount gs := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp [notOutputsAux, notCount, ih] <;> omega

private theorem bitsLe_append_single {x y : List Bool} {a b : Bool}
    (hxy : BitsLe x y) (hab : a = true → b = true) :
    BitsLe (x ++ [a]) (y ++ [b]) := by
  rcases hxy with ⟨hlen, hle⟩
  refine ⟨by simp [hlen], fun i hi => ?_⟩
  simp only [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < x.length
  · have hlt' : i < y.length := by omega
    rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left hlt']
    have := hle i
    simpa [List.getD_eq_getElem?_getD] using this hi
  · by_cases heq : i = x.length
    · subst heq
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hi
      rw [hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      simpa using hab (by simpa using hi)
    · have hgt : x.length + 1 ≤ i := by omega
      have hnone : (x ++ [a])[i]? = none := by
        apply List.getElem?_eq_none; simp; omega
      rw [hnone] at hi
      exact Bool.noConfusion hi

private theorem evalCircuit_mono_of_same_notOutputs (gs : List GateOp) :
    ∀ x y : List Bool, BitsLe x y → notOutputsAux x gs = notOutputsAux y gs →
      BitsLe (evalCircuit x gs) (evalCircuit y gs) := by
  induction gs with
  | nil => intro x y h _; exact h
  | cons g gs ih =>
    intro x y hle hno
    rw [evalCircuit_cons, evalCircuit_cons]
    cases g with
    | const b =>
      simp only [notOutputsAux] at hno
      exact ih _ _ (bitsLe_append_single hle (fun h => h)) hno
    | and i j =>
      simp only [notOutputsAux] at hno
      apply ih _ _ _ hno
      apply bitsLe_append_single hle
      intro h
      simp only [evalGate, Bool.and_eq_true] at h ⊢
      exact ⟨hle.2 i h.1, hle.2 j h.2⟩
    | or i j =>
      simp only [notOutputsAux] at hno
      apply ih _ _ _ hno
      apply bitsLe_append_single hle
      intro h
      simp only [evalGate, Bool.or_eq_true] at h ⊢
      rcases h with h1 | h2
      · exact Or.inl (hle.2 i h1)
      · exact Or.inr (hle.2 j h2)
    | not i =>
      simp only [notOutputsAux] at hno
      injection hno with hhead htail
      apply ih _ _ _ htail
      apply bitsLe_append_single hle
      intro h
      rw [← hhead]; exact h

private theorem pigeonhole_list {α : Type} [DecidableEq α] :
    ∀ (m : Nat) (pool : List α) (f : Nat → α),
      (∀ i < m, f i ∈ pool) → pool.length < m →
      ∃ i j : Nat, i < j ∧ j < m ∧ f i = f j := by
  intro m
  induction m with
  | zero => intro pool _ _ hlt; omega
  | succ m ih =>
    intro pool f hmem hlt
    by_cases hhit : ∃ i < m, f i = f m
    · rcases hhit with ⟨i, hi, heq⟩
      exact ⟨i, m, hi, Nat.lt_succ_self m, heq⟩
    · have hne : ∀ i < m, f i ≠ f m := fun i hi heq => hhit ⟨i, hi, heq⟩
      have hfm_in : f m ∈ pool := hmem m (Nat.lt_succ_self m)
      let pool' := pool.erase (f m)
      have hmem' : ∀ i < m, f i ∈ pool' := by
        intro i hi
        exact (List.mem_erase_of_ne (hne i hi)).mpr (hmem i (Nat.lt_trans hi (Nat.lt_succ_self m)))
      have hlen' : pool'.length < m := by
        have hpos : 0 < pool.length := List.length_pos_of_mem hfm_in
        have hlen_er : pool'.length = pool.length - 1 := List.length_erase_of_mem hfm_in
        omega
      rcases ih pool' f hmem' hlen' with ⟨i, j, hij, hjm, heq⟩
      exact ⟨i, j, hij, Nat.lt_trans hjm (Nat.lt_succ_self m), heq⟩

/-- Chain input `c_m`: `m` trues followed by `n - m` falses (length `n`, for `m ≤ n`). -/
private def chainVec (n m : Nat) : List Bool :=
  List.replicate m true ++ List.replicate (n - m) false

private theorem chainVec_length (n m : Nat) (hm : m ≤ n) :
    (chainVec n m).length = n := by
  unfold chainVec; simp; omega

private theorem chainVec_getD (n m i : Nat) (hm : m ≤ n) (hi : i < n) :
    (chainVec n m).getD i false = decide (i < m) := by
  unfold chainVec
  simp only [List.getD_eq_getElem?_getD]
  by_cases hlt : i < m
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate]
    simp [hlt]
  · rw [List.getElem?_append_right (by simp; omega), List.length_replicate, List.getElem?_replicate]
    have hlt2 : i - m < n - m := by omega
    simp [hlt, hlt2]

private theorem chainVec_le (n p q : Nat) (hpq : p ≤ q) (hq : q ≤ n) :
    BitsLe (chainVec n p) (chainVec n q) := by
  refine ⟨by rw [chainVec_length n p (by omega), chainVec_length n q hq], fun i hi => ?_⟩
  by_cases hin : i < n
  · rw [chainVec_getD n p i (by omega) hin] at hi
    rw [chainVec_getD n q i hq hin]
    simp only [decide_eq_true_eq] at hi ⊢
    omega
  · have hnone : (chainVec n p)[i]? = none := by
      apply List.getElem?_eq_none; rw [chainVec_length n p (by omega)]; omega
    simp only [List.getD_eq_getElem?_getD, hnone] at hi
    exact Bool.noConfusion hi

/-- Headline Theorem (Markov 1957 Exact Lower Bound):
    If `2^r ≤ n`, NO straight-line Boolean circuit with `≤ r` NOT gates can
    simultaneously invert `n` Boolean inputs (regardless of circuit size). -/
public theorem markov_inverter_lower (n r : Nat) (hle : 2 ^ r ≤ n)
    (gs : List GateOp) (hnot : notCount gs ≤ r) (outs : Fin n → Nat) :
    ¬ ComputesInverter n gs outs := by
  intro hinv
  let r' := notCount gs
  let f : Nat → List Bool := fun m => notOutputs (chainVec n m) gs
  have hmem : ∀ m < n + 1, f m ∈ allBitstrings r' := by
    intro m _
    rw [mem_allBitstrings_iff]
    exact notOutputsAux_length (chainVec n m) gs
  have hlen : (allBitstrings r').length < n + 1 := by
    rw [allBitstrings_length]
    have hpow : 2 ^ r' ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hnot
    omega
  rcases pigeonhole_list (n + 1) (allBitstrings r') f hmem hlen with ⟨p, q, hpq, hqn, hsame⟩
  have hcle : BitsLe (chainVec n p) (chainVec n q) := chainVec_le n p q (by omega) (by omega)
  have hmono := evalCircuit_mono_of_same_notOutputs gs (chainVec n p) (chainVec n q) hcle hsame
  have hp_lt : p < n := by omega
  have hinv_p := hinv (chainVec n p) (chainVec_length n p (by omega)) ⟨p, hp_lt⟩
  have hinv_q := hinv (chainVec n q) (chainVec_length n q (by omega)) ⟨p, hp_lt⟩
  have hcp : (chainVec n p).getD p false = false := by
    rw [chainVec_getD n p p (by omega) hp_lt]; simp
  have hcq : (chainVec n q).getD p false = true := by
    rw [chainVec_getD n q p (by omega) hp_lt]; simp [hpq]
  rw [hcp] at hinv_p
  rw [hcq] at hinv_q
  have hout_q := hmono.2 (outs ⟨p, hp_lt⟩) hinv_p
  rw [hinv_q] at hout_q
  exact Bool.noConfusion hout_q

-- ============================================================================
-- Proofs Part 1B: Constructive Monotone Compiler, Markov Upper Bound & Fischer Reduction
-- ============================================================================

/-- Constructively compile ANY monotone Boolean function `f : List Bool → Bool`
    of arity `m` (reading wires `vars : List Nat`) into a ZERO-NOT-gate circuit
    appended onto an existing wire bank of length `base`.
    Returns `(gates, outWire)`. Uses monotone Shannon expansion:
    `f(v_0 :: vs) = (v_0 ∧ f(true :: vs)) ∨ f(false :: vs)`. -/
private def compileMonotoneAux :
    (vars : List Nat) → (f : List Bool → Bool) → (base : Nat) → List GateOp × Nat
  | [], f, base => ([.const (f [])], base)
  | v :: vs, f, base =>
    let (g0, w0) := compileMonotoneAux vs (fun rest => f (false :: rest)) base
    let base1 := base + g0.length
    let (g1, w1) := compileMonotoneAux vs (fun rest => f (true :: rest)) base1
    let base2 := base1 + g1.length
    let wAnd := base2
    let wOr := base2 + 1
    (g0 ++ g1 ++ [.and v w1, .or wAnd w0], wOr)

private theorem compileMonotoneAux_notCount (vars : List Nat) (f : List Bool → Bool) (base : Nat) :
    notCount (compileMonotoneAux vars f base).1 = 0 := by
  induction vars generalizing f base with
  | nil => rfl
  | cons v vs ih =>
    unfold compileMonotoneAux
    have hnot_app : ∀ a b : List GateOp, notCount (a ++ b) = notCount a + notCount b := by
      intro a b; induction a with
      | nil => simp [notCount]
      | cons g gs iha => cases g <;> simp [notCount, iha] <;> omega
    simp only [hnot_app, notCount]
    rw [ih (fun rest => f (false :: rest)) base, ih (fun rest => f (true :: rest)) _]

private theorem compileMonotoneAux_out_lt (vars : List Nat) (f : List Bool → Bool) (base : Nat) :
    (compileMonotoneAux vars f base).2 < base + (compileMonotoneAux vars f base).1.length := by
  induction vars generalizing f base with
  | nil => simp [compileMonotoneAux]
  | cons v vs ih =>
    unfold compileMonotoneAux
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem evalCircuit_step_last (ws : List Bool) (g : GateOp) :
    (evalCircuit ws [g]).getD ws.length false = evalGate ws g := by
  unfold evalCircuit
  simp [List.getD_eq_getElem?_getD]

private theorem compileMonotoneAux_eval (vars : List Nat) :
    ∀ (f : List Bool → Bool),
      (∀ u v, BitsLe u v → f u = true → f v = true) →
      ∀ (ws : List Bool), (∀ v ∈ vars, v < ws.length) →
      (evalCircuit ws (compileMonotoneAux vars f ws.length).1).getD
        (compileMonotoneAux vars f ws.length).2 false =
      f (vars.map (fun v => ws.getD v false)) := by
  induction vars with
  | nil =>
    intro f _ ws _
    unfold compileMonotoneAux
    exact evalCircuit_step_last ws (.const (f []))
  | cons v vs ih =>
    intro f hmono ws hvars
    have hv_lt : v < ws.length := hvars v (by simp)
    have hvs_lt : ∀ u ∈ vs, u < ws.length := fun u hu => hvars u (by simp [hu])
    have hmono0 : ∀ u w, BitsLe u w → f (false :: u) = true → f (false :: w) = true := by
      intro u w hle hu
      apply hmono (false :: u) (false :: w) _ hu
      refine ⟨by simp [hle.1], fun i hi => ?_⟩
      cases i with
      | zero => simp at hi
      | succ k => exact hle.2 k hi
    have hmono1 : ∀ u w, BitsLe u w → f (true :: u) = true → f (true :: w) = true := by
      intro u w hle hu
      apply hmono (true :: u) (true :: w) _ hu
      refine ⟨by simp [hle.1], fun i hi => ?_⟩
      cases i with
      | zero => rfl
      | succ k => exact hle.2 k hi
    unfold compileMonotoneAux
    dsimp only
    let res0 := compileMonotoneAux vs (fun rest => f (false :: rest)) ws.length
    let ws1 := evalCircuit ws res0.1
    have hlen1 : ws1.length = ws.length + res0.1.length := evalCircuit_length ws res0.1
    let res1 := compileMonotoneAux vs (fun rest => f (true :: rest)) (ws.length + res0.1.length)
    let ws2 := evalCircuit ws1 res1.1
    have hlen2 : ws2.length = ws1.length + res1.1.length := evalCircuit_length ws1 res1.1
    have hw0_lt : res0.2 < ws1.length := by
      rw [hlen1]; exact compileMonotoneAux_out_lt vs _ ws.length
    have hw1_lt : res1.2 < ws2.length := by
      rw [hlen2, hlen1]; exact compileMonotoneAux_out_lt vs _ (ws.length + res0.1.length)
    have hv_ws2 : ws2.getD v false = ws.getD v false := by
      have h1 : ws1.getD v false = ws.getD v false := evalCircuit_prefix_preserve ws res0.1 v hv_lt
      have h2 : ws2.getD v false = ws1.getD v false := evalCircuit_prefix_preserve ws1 res1.1 v (by omega)
      rw [h2, h1]
    have hw0_ws1 : ws1.getD res0.2 false = f (false :: vs.map (fun u => ws.getD u false)) :=
      ih (fun rest => f (false :: rest)) hmono0 ws hvs_lt
    have hw0_ws2 : ws2.getD res0.2 false = f (false :: vs.map (fun u => ws.getD u false)) := by
      rw [evalCircuit_prefix_preserve ws1 res1.1 res0.2 hw0_lt, hw0_ws1]
    have hvs_ws1 : vs.map (fun u => ws1.getD u false) = vs.map (fun u => ws.getD u false) := by
      apply List.map_congr_left
      intro u hu
      exact evalCircuit_prefix_preserve ws res0.1 u (hvs_lt u hu)
    have hw1_ws2 : ws2.getD res1.2 false = f (true :: vs.map (fun u => ws.getD u false)) := by
      have hih1 := ih (fun rest => f (true :: rest)) hmono1 ws1 (fun u hu => by
        have := hvs_lt u hu; omega)
      have heq_res1 : compileMonotoneAux vs (fun rest => f (true :: rest)) ws1.length = res1 := by
        rw [hlen1]
      rw [heq_res1] at hih1
      rw [hih1, hvs_ws1]
    -- Now evaluate the final two gates `.and v res1.2` and `.or (ws2.length) res0.2`
    rw [evalCircuit_append, evalCircuit_append]
    change (evalCircuit ws2 [.and v res1.2, .or (ws.length + res0.1.length + res1.1.length) res0.2]).getD
      (ws.length + res0.1.length + res1.1.length + 1) false = _
    have hws2_len : ws.length + res0.1.length + res1.1.length = ws2.length := by omega
    rw [hws2_len, evalCircuit_cons]
    let ws3 := ws2 ++ [evalGate ws2 (.and v res1.2)]
    have hws3_len : ws3.length = ws2.length + 1 := by simp [ws3]
    rw [← hws3_len, evalCircuit_step_last]
    have hget_and : ws3.getD ws2.length false = (ws2.getD v false && ws2.getD res1.2 false) := by
      simp [ws3, List.getD_eq_getElem?_getD, evalGate]
    have hget_w0 : ws3.getD res0.2 false = ws2.getD res0.2 false := by
      have hlt : res0.2 < ws2.length := by omega
      simp [ws3, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    change (ws3.getD ws2.length false || ws3.getD res0.2 false) = _
    rw [hget_and, hget_w0, hv_ws2, hw1_ws2, hw0_ws2]
    simp only [List.map_cons]
    let tail := vs.map (fun u => ws.getD u false)
    cases hvb : ws.getD v false
    · simp only [Bool.false_and, Bool.false_or]
    · simp only [Bool.true_and]
      cases hf0 : f (false :: tail)
      · simp only [Bool.or_false]
      · have hle_ft : BitsLe (false :: tail) (true :: tail) := by
          refine ⟨rfl, fun i hi => ?_⟩
          cases i with
          | zero => rfl
          | succ k => exact hi
        have hf1 : f (true :: tail) = true := hmono _ _ hle_ft hf0
        simp only [Bool.or_true]
        exact hf1.symm

/-- Hamming weight of a Boolean list. -/
private def hammingWeight : List Bool → Nat
  | [] => 0
  | true :: bs => 1 + hammingWeight bs
  | false :: bs => hammingWeight bs

private theorem hammingWeight_le_length (bs : List Bool) : hammingWeight bs ≤ bs.length := by
  induction bs with
  | nil => simp [hammingWeight]
  | cons b bs ih => cases b <;> simp [hammingWeight] <;> omega

private theorem hammingWeight_mono : ∀ u v : List Bool, BitsLe u v → hammingWeight u ≤ hammingWeight v := by
  intro u
  induction u with
  | nil =>
    intro v h; cases v with
    | nil => exact Nat.le_refl 0
    | cons _ _ => exact absurd h.1 (by simp)
  | cons a as ih =>
    intro v h
    cases v with
    | nil => exact absurd h.1 (by simp)
    | cons b bs =>
      have htail : BitsLe as bs := by
        refine ⟨by have := h.1; simp at this; omega, fun i hi => h.2 (i + 1) hi⟩
      have hih := ih bs htail
      cases a
      · cases b <;> simp [hammingWeight] <;> omega
      · have hb : b = true := h.2 0 rfl
        subst hb; simp [hammingWeight]; omega

/-- Weighted sum of a bit list `∑_{t} weights[t] * bits[t]`. -/
private def weightedSum : List Nat → List Bool → Nat
  | [], _ => 0
  | _, [] => 0
  | w :: ws, b :: bs => (if b then w else 0) + weightedSum ws bs

private theorem weightedSum_mono (ws : List Nat) :
    ∀ u v : List Bool, BitsLe u v → weightedSum ws u ≤ weightedSum ws v := by
  induction ws with
  | nil => intro _ _ _; exact Nat.le_refl 0
  | cons w ws ih =>
    intro u v h
    cases u with
    | nil =>
      cases v with
      | nil => exact Nat.le_refl 0
      | cons _ _ => exact absurd h.1 (by simp)
    | cons a as =>
      cases v with
      | nil => exact absurd h.1 (by simp)
      | cons b bs =>
        have htail : BitsLe as bs := by
          refine ⟨by have := h.1; simp at this; omega, fun i hi => h.2 (i + 1) hi⟩
        have hih := ih as bs htail
        cases a
        · cases b <;> simp [weightedSum] <;> omega
        · have hb : b = true := h.2 0 rfl
          subst hb; simp [weightedSum]; omega

/-- Monotone threshold function `weightedSum weights bits ≥ thresh`. -/
private def weightedThreshFn (weights : List Nat) (thresh : Nat) (bits : List Bool) : Bool :=
  decide (thresh ≤ weightedSum weights bits)

private theorem weightedThreshFn_mono (weights : List Nat) (thresh : Nat) :
    ∀ u v : List Bool, BitsLe u v →
      weightedThreshFn weights thresh u = true → weightedThreshFn weights thresh v = true := by
  intro u v hle hu
  unfold weightedThreshFn at hu ⊢
  simp only [decide_eq_true_eq] at hu ⊢
  have := weightedSum_mono weights u v hle
  omega

/-- Markov bit-extraction stage: given input wire count `n = 2^k - 1`,
    builds `t` MSB-first negated Hamming-weight bits `¬b_{k-1}, ..., ¬b_{k-t}`
    using EXACTLY `t` NOT gates!
    Returns `(gates, negBitWires)` where `negBitWires` has length `t`,
    with `negBitWires[r]` holding `¬b_{k - 1 - r}` (MSB first). -/
private def markovBitsStage (k : Nat) : (t : Nat) → (base : Nat) → List GateOp × List Nat
  | 0, _ => ([], [])
  | t + 1, base =>
    let (gPrev, prevWires) := markovBitsStage k t base
    let base1 := base + gPrev.length
    let n := 2 ^ k - 1
    let bitPos := k - 1 - t
    -- Input wires are `0 .. n - 1` (weight 1 each), followed by `prevWires` (weights `2^(k-1), ..., 2^(k-t)`)
    let inWires := List.range n
    let allVars := inWires ++ prevWires
    let prevWeights := (List.range t).map (fun r => 2 ^ (k - 1 - r))
    let allWeights := List.replicate n 1 ++ prevWeights
    let thresh := 2 ^ k - 2 ^ bitPos
    let (gMon, wBit) := compileMonotoneAux allVars (weightedThreshFn allWeights thresh) base1
    let wNot := base1 + gMon.length
    (gPrev ++ gMon ++ [.not wBit], prevWires ++ [wNot])

/-- Final output layer of Markov's inverter: given `negWires` holding `¬b_{k-1}, ..., ¬b_0`,
    computes `!x_i` for each `i < n = 2^k - 1` via the monotone threshold
    `w(x_{-i}) + ∑_{r<k} 2^{k-1-r} (¬b_{k-1-r}) ≥ 2^k - 1` (ZERO NOT gates!). -/
private def markovOutLayer (k : Nat) (negWires : List Nat) :
    (idx count base : Nat) → List GateOp × List Nat
  | _, 0, _ => ([], [])
  | idx, count + 1, base =>
    let n := 2 ^ k - 1
    let otherIn := (List.range n).filter (fun j => j != idx)
    let allVars := otherIn ++ negWires
    let bitWeights := (List.range k).map (fun r => 2 ^ (k - 1 - r))
    let allWeights := List.replicate otherIn.length 1 ++ bitWeights
    let (gMon, wOut) := compileMonotoneAux allVars (weightedThreshFn allWeights (2 ^ k - 1)) base
    let (gRest, restOuts) := markovOutLayer k negWires (idx + 1) count (base + gMon.length)
    (gMon ++ gRest, wOut :: restOuts)

/-- Complete explicit Markov (1957) `k`-NOT-gate inverter for `n = 2^k - 1` inputs. -/
public def markovInverter (k : Nat) : List GateOp × List Nat :=
  let n := 2 ^ k - 1
  let (gBits, negWires) := markovBitsStage k k n
  let (gOut, outWires) := markovOutLayer k negWires 0 n (n + gBits.length)
  (gBits ++ gOut, outWires)

private theorem notCount_append (a b : List GateOp) :
    notCount (a ++ b) = notCount a + notCount b := by
  induction a with
  | nil => simp [notCount]
  | cons g gs ih => cases g <;> simp [notCount, ih] <;> omega

private theorem markovBitsStage_notCount (k t base : Nat) :
    notCount (markovBitsStage k t base).1 = t := by
  induction t generalizing base with
  | zero => rfl
  | succ t ih =>
    unfold markovBitsStage
    simp only [notCount_append, notCount, compileMonotoneAux_notCount]
    rw [ih base]

private theorem markovOutLayer_notCount (k : Nat) (negWires : List Nat) (idx count base : Nat) :
    notCount (markovOutLayer k negWires idx count base).1 = 0 := by
  induction count generalizing idx base with
  | zero => rfl
  | succ count ih =>
    unfold markovOutLayer
    simp only [notCount_append, compileMonotoneAux_notCount]
    rw [ih (idx + 1) _]

public theorem markovInverter_notCount (k : Nat) :
    notCount (markovInverter k).1 = k := by
  unfold markovInverter
  simp only [notCount_append, markovBitsStage_notCount, markovOutLayer_notCount, Nat.add_zero]

private theorem weightedSum_append (w1 w2 : List Nat) (b1 b2 : List Bool)
    (h1 : w1.length = b1.length) :
    weightedSum (w1 ++ w2) (b1 ++ b2) = weightedSum w1 b1 + weightedSum w2 b2 := by
  induction w1 generalizing b1 with
  | nil =>
    cases b1 with
    | nil => simp [weightedSum]
    | cons _ _ => simp at h1
  | cons w ws ih =>
    cases b1 with
    | nil => simp at h1
    | cons b bs =>
      simp only [List.length_cons] at h1
      simp only [List.cons_append, weightedSum]
      rw [ih bs (by omega)]
      omega

private theorem weightedSum_ones (bs : List Bool) :
    weightedSum (List.replicate bs.length 1) bs = hammingWeight bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.length_cons, List.replicate_succ]
    cases b <;> simp [weightedSum, hammingWeight, ih]

private theorem map_range_getD (x : List Bool) :
    (List.range x.length).map (fun i => x.getD i false) = x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, h2]

/-- Binary-expansion invariant of the first `t` MSB negated bits of `w < 2^k`:
    if `negBits[r] = !(((w / 2^(k-1-r)) % 2) == 1)` for `r < t`, then their
    weighted sum `∑_{r<t} 2^(k-1-r) * negBits[r]` equals `(2^k - 2^(k-t)) - (w - w % 2^(k-t))`. -/
private theorem neg_msb_weighted_sum (k w : Nat) (hw : w < 2 ^ k) :
    ∀ t ≤ k,
      weightedSum ((List.range t).map (fun r => 2 ^ (k - 1 - r)))
        ((List.range t).map (fun r => !((w / 2 ^ (k - 1 - r)) % 2 == 1))) +
      (w - w % 2 ^ (k - t)) = 2 ^ k - 2 ^ (k - t) := by
  intro t
  induction t with
  | zero =>
    intro _
    simp only [List.range_zero, List.map_nil, weightedSum, Nat.sub_zero, Nat.zero_add]
    have hmod : w % 2 ^ k = w := Nat.mod_eq_of_lt hw
    rw [hmod]; omega
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    rw [List.range_succ, List.map_append, List.map_append, List.map_singleton, List.map_singleton]
    rw [weightedSum_append _ _ _ _ (by simp)]
    simp only [weightedSum, Nat.add_zero]
    have hpow_step : 2 ^ (k - t) = 2 * 2 ^ (k - (t + 1)) := by
      have : k - t = (k - (t + 1)) + 1 := by omega
      rw [this, Nat.pow_succ, Nat.mul_comm]
    have hpos_eq : k - 1 - t = k - (t + 1) := by omega
    rw [hpos_eq]
    let p := 2 ^ (k - (t + 1))
    have hp_pos : 0 < p := Nat.two_pow_pos _
    have hdiv_mod : w % (2 * p) = (w / p % 2) * p + w % p := by
      have h1 : w = (w / p) * p + w % p := by
        have := Nat.div_add_mod w p; rw [Nat.mul_comm] at this; omega
      have h2 : w / p = 2 * (w / p / 2) + (w / p) % 2 := by
        have := Nat.div_add_mod (w / p) 2; omega
      have h3 : w = (2 * p) * (w / p / 2) + ((w / p) % 2 * p + w % p) := by
        calc w = (2 * (w / p / 2) + (w / p) % 2) * p + w % p := by rw [← h2]; exact h1
             _ = (2 * p) * (w / p / 2) + ((w / p) % 2 * p + w % p) := by
                rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (w / p / 2) p, ← Nat.mul_assoc]; omega
      have hlt : (w / p) % 2 * p + w % p < 2 * p := by
        have hm2 : (w / p) % 2 < 2 := Nat.mod_lt _ (by omega)
        have hmp : w % p < p := Nat.mod_lt _ hp_pos
        have hmul_le : (w / p) % 2 * p ≤ p := by
          cases hq : (w / p) % 2 with
          | zero => simp
          | succ m =>
            have : m = 0 := by omega
            subst this; simp
        omega
      conv => lhs; rw [h3]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    have hmod_le_w : w % (2 * p) ≤ w := Nat.mod_le w (2 * p)
    have hmodp_le_w : w % p ≤ w := Nat.mod_le w p
    have h2p_le_2k : 2 * p ≤ 2 ^ k := by
      rw [← hpow_step]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    rw [hpow_step] at hprev
    have hprev' : weightedSum ((List.range t).map (fun r => 2 ^ (k - 1 - r)))
        ((List.range t).map (fun r => !((w / 2 ^ (k - 1 - r)) % 2 == 1))) +
        (w - w % (2 * p)) = 2 ^ k - 2 * p := hprev
    have hbit : (w / p) % 2 = 0 ∨ (w / p) % 2 = 1 := by omega
    change weightedSum ((List.range t).map (fun r => 2 ^ (k - 1 - r)))
        ((List.range t).map (fun r => !((w / 2 ^ (k - 1 - r)) % 2 == 1))) +
        (if !((w / p) % 2 == 1) then p else 0) + (w - w % p) = 2 ^ k - p
    rcases hbit with hb0 | hb1
    · rw [hb0] at hdiv_mod ⊢
      simp only [Nat.zero_mul, Nat.zero_add] at hdiv_mod
      have hite : (if (!((0 : Nat) == 1)) = true then p else 0) = p := rfl
      rw [hite]
      omega
    · rw [hb1] at hdiv_mod ⊢
      simp only [Nat.one_mul] at hdiv_mod
      have hite : (if (!((1 : Nat) == 1)) = true then p else 0) = 0 := rfl
      rw [hite]
      omega

private theorem markovBitsStage_spec (k : Nat) (x : List Bool) (hx : x.length = 2 ^ k - 1) :
    ∀ t ≤ k,
      let res := markovBitsStage k t (2 ^ k - 1)
      let ws := evalCircuit x res.1
      res.2.length = t ∧
      (∀ w ∈ res.2, w < ws.length) ∧
      res.2.map (fun w => ws.getD w false) =
        (List.range t).map (fun r => !((hammingWeight x / 2 ^ (k - 1 - r)) % 2 == 1)) := by
  intro t
  induction t with
  | zero =>
    intro _
    simp [markovBitsStage]
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    dsimp only at hprev ⊢
    rcases hprev with ⟨hlenP, hltP, hvalP⟩
    unfold markovBitsStage
    dsimp only
    let resP := markovBitsStage k t (2 ^ k - 1)
    let ws1 := evalCircuit x resP.1
    have hws1_len : ws1.length = (2 ^ k - 1) + resP.1.length := by
      rw [evalCircuit_length, hx]
    let n := 2 ^ k - 1
    let bitPos := k - 1 - t
    let allVars := List.range n ++ resP.2
    let prevWeights := (List.range t).map (fun r => 2 ^ (k - 1 - r))
    let allWeights := List.replicate n 1 ++ prevWeights
    let thresh := 2 ^ k - 2 ^ bitPos
    let resM := compileMonotoneAux allVars (weightedThreshFn allWeights thresh) (n + resP.1.length)
    let ws2 := evalCircuit ws1 resM.1
    have hws2_len : ws2.length = ws1.length + resM.1.length := evalCircuit_length ws1 resM.1
    let wNot := n + resP.1.length + resM.1.length
    let ws3 := evalCircuit ws2 [.not resM.2]
    have hws3_len : ws3.length = ws2.length + 1 := by
      rw [evalCircuit_length]; rfl
    have hvars_lt : ∀ v ∈ allVars, v < ws1.length := by
      intro v hv
      simp only [allVars, List.mem_append, List.mem_range] at hv
      rcases hv with h1 | h2
      · rw [hws1_len]; omega
      · exact hltP v h2
    have hresM_eq : compileMonotoneAux allVars (weightedThreshFn allWeights thresh) ws1.length = resM := by
      rw [hws1_len]
    have hbit_eval : ws2.getD resM.2 false =
        weightedThreshFn allWeights thresh (allVars.map (fun v => ws1.getD v false)) := by
      have h := compileMonotoneAux_eval allVars (weightedThreshFn allWeights thresh)
        (weightedThreshFn_mono allWeights thresh) ws1 hvars_lt
      rw [hresM_eq] at h
      exact h
    have hin_ws1 : (List.range n).map (fun v => ws1.getD v false) = x := by
      have heq : (List.range n).map (fun v => ws1.getD v false) =
          (List.range x.length).map (fun v => x.getD v false) := by
        rw [hx]
        apply List.map_congr_left
        intro v hv
        rw [List.mem_range] at hv
        exact evalCircuit_prefix_preserve x resP.1 v (by omega)
      rw [heq, map_range_getD]
    have hsum_val : weightedSum allWeights (allVars.map (fun v => ws1.getD v false)) =
        hammingWeight x +
        weightedSum prevWeights
          ((List.range t).map (fun r => !((hammingWeight x / 2 ^ (k - 1 - r)) % 2 == 1))) := by
      simp only [allVars, allWeights, List.map_append]
      rw [hin_ws1, hvalP, weightedSum_append _ _ _ _ (by simp [n, hx])]
      have hrep : List.replicate n 1 = List.replicate x.length 1 := by rw [hx]
      rw [hrep, weightedSum_ones]
    have hw_lt_2k : hammingWeight x < 2 ^ k := by
      have h1 := hammingWeight_le_length x
      have h2 : 0 < 2 ^ k := Nat.two_pow_pos k
      omega
    have hmsb := neg_msb_weighted_sum k (hammingWeight x) hw_lt_2k t (by omega)
    -- Show `weightedThreshFn ... = ((hammingWeight x / 2^(k-1-t)) % 2 == 1)`
    have hbit_val : ws2.getD resM.2 false = ((hammingWeight x / 2 ^ bitPos) % 2 == 1) := by
      rw [hbit_eval]
      unfold weightedThreshFn
      rw [hsum_val]
      have hpow_step : 2 ^ (k - t) = 2 * 2 ^ bitPos := by
        have : k - t = bitPos + 1 := by omega
        rw [this, Nat.pow_succ, Nat.mul_comm]
      let w := hammingWeight x
      let p := 2 ^ bitPos
      have hp_pos : 0 < p := Nat.two_pow_pos bitPos
      have hdiv_mod : w % (2 * p) = (w / p % 2) * p + w % p := by
        have h1 : w = (w / p) * p + w % p := by
          have := Nat.div_add_mod w p; rw [Nat.mul_comm] at this; omega
        have h2 : w / p = 2 * (w / p / 2) + (w / p) % 2 := by
          have := Nat.div_add_mod (w / p) 2; omega
        have h3 : w = (2 * p) * (w / p / 2) + ((w / p) % 2 * p + w % p) := by
          calc w = (2 * (w / p / 2) + (w / p) % 2) * p + w % p := by rw [← h2]; exact h1
               _ = (2 * p) * (w / p / 2) + ((w / p) % 2 * p + w % p) := by
                  rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (w / p / 2) p, ← Nat.mul_assoc]; omega
        have hlt : (w / p) % 2 * p + w % p < 2 * p := by
          have hm2 : (w / p) % 2 < 2 := Nat.mod_lt _ (by omega)
          have hmp : w % p < p := Nat.mod_lt _ hp_pos
          have hmul_le : (w / p) % 2 * p ≤ p := by
            cases hq : (w / p) % 2 with
            | zero => simp
            | succ m =>
              cases m with
              | zero => simp
              | succ _ => omega
          omega
        conv => lhs; rw [h3]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      have h2p_le_2k : 2 * p ≤ 2 ^ k := by
        rw [← hpow_step]; exact Nat.pow_le_pow_right (by omega) (by omega)
      have hmod_le_w : w % (2 * p) ≤ w := Nat.mod_le w (2 * p)
      have hmp : w % p < p := Nat.mod_lt _ hp_pos
      have hmsb' : weightedSum prevWeights ((List.range t).map (fun r => !((w / 2 ^ (k - 1 - r)) % 2 == 1))) +
          (w - w % (2 * p)) = 2 ^ k - 2 * p := by
        simpa [hpow_step, prevWeights, w, p] using hmsb
      change decide (thresh ≤ w + weightedSum prevWeights
          ((List.range t).map (fun r => !((w / 2 ^ (k - 1 - r)) % 2 == 1)))) = ((w / p) % 2 == 1)
      have hbit : (w / p) % 2 = 0 ∨ (w / p) % 2 = 1 := by omega
      rcases hbit with hb0 | hb1
      · simp only [hb0, Nat.zero_mul, Nat.zero_add] at hdiv_mod
        have hnot_ge : ¬ (thresh ≤ w + weightedSum prevWeights
            ((List.range t).map (fun r => !((w / 2 ^ (k - 1 - r)) % 2 == 1)))) := by
          dsimp only [thresh, p]; omega
        rw [hb0]; simp [hnot_ge]
      · simp only [hb1, Nat.one_mul] at hdiv_mod
        have hge : thresh ≤ w + weightedSum prevWeights
            ((List.range t).map (fun r => !((w / 2 ^ (k - 1 - r)) % 2 == 1))) := by
          dsimp only [thresh, p]; omega
        rw [hb1]; simp [hge]
    have hnot_eval : ws3.getD wNot false = !((hammingWeight x / 2 ^ bitPos) % 2 == 1) := by
      have hwNot_eq : wNot = ws2.length := by dsimp only [n, wNot]; omega
      rw [hwNot_eq]
      have h := evalCircuit_step_last ws2 (.not resM.2)
      change ws3.getD ws2.length false = _
      rw [h]; simp only [evalGate, hbit_val]
    have hws3_eq : evalCircuit x (resP.1 ++ resM.1 ++ [.not resM.2]) = ws3 := by
      rw [evalCircuit_append, evalCircuit_append]
    rw [hws3_eq]
    refine ⟨by simp [hlenP], ?_, ?_⟩
    · intro w hw
      simp only [List.mem_append, List.mem_singleton] at hw
      rw [hws3_len, hws2_len]
      rcases hw with h1 | rfl
      · have hlt1 : w < ws1.length := hltP w h1
        omega
      · change wNot < ws1.length + resM.1.length + 1
        rw [hws1_len]; dsimp only [wNot, n]; omega
    · rw [List.map_append, List.map_singleton, List.range_succ, List.map_append, List.map_singleton]
      congr 1
      · rw [← hvalP]
        apply List.map_congr_left
        intro w hw
        have hw1 : w < ws1.length := hltP w hw
        have h1 : ws2.getD w false = ws1.getD w false := evalCircuit_prefix_preserve ws1 resM.1 w hw1
        have h2 : ws3.getD w false = ws2.getD w false := evalCircuit_prefix_preserve ws2 [.not resM.2] w (by omega)
        rw [h2, h1]
      · exact congrArg (fun b => [b]) hnot_eval

private theorem hammingWeight_without_idx (x : List Bool) (i : Nat) (hi : i < x.length) :
    hammingWeight (((List.range x.length).filter (fun j => j != i)).map (fun j => x.getD j false)) +
    (if x.getD i false then 1 else 0) = hammingWeight x := by
  have hgen : ∀ (xs : List Bool) (offset : Nat),
      hammingWeight (((List.range xs.length).filter (fun j => (j + offset) != i)).map
        (fun j => xs.getD j false)) +
      (if i ≥ offset ∧ i < offset + xs.length ∧ xs.getD (i - offset) false = true then 1 else 0) =
      hammingWeight xs := by
    intro xs
    induction xs with
    | nil =>
      intro offset
      simp [hammingWeight]
    | cons a as ih =>
      intro offset
      rw [List.length_cons]
      -- Split `List.range (as.length + 1) = 0 :: (List.range as.length).map (· + 1)`
      have hrange : List.range (as.length + 1) = 0 :: (List.range as.length).map (· + 1) := by
        have h : ∀ m, List.range (m + 1) = 0 :: (List.range m).map (· + 1) := by
          intro m; induction m with
          | zero => rfl
          | succ m ihm =>
            conv => lhs; rw [List.range_succ, ihm]
            conv => rhs; rw [List.range_succ, List.map_append, List.map_singleton]
            rfl
        exact h as.length
      rw [hrange, List.filter_cons]
      have htail_eq :
          (((List.range as.length).map (· + 1)).filter (fun j => (j + offset) != i)).map
            (fun j => (a :: as).getD j false) =
          ((List.range as.length).filter (fun j => (j + (offset + 1)) != i)).map
            (fun j => as.getD j false) := by
        have hgen_f : ∀ ls : List Nat,
            ((ls.map (· + 1)).filter (fun j => (j + offset) != i)).map (fun j => (a :: as).getD j false) =
            (ls.filter (fun j => (j + (offset + 1)) != i)).map (fun j => as.getD j false) := by
          intro ls; induction ls with
          | nil => rfl
          | cons u us ihu =>
            have hadd : u + 1 + offset = u + (offset + 1) := by omega
            simp only [List.map_cons, List.filter_cons, hadd]
            cases hb : (u + (offset + 1) != i)
            · simp only [Bool.false_eq_true, ↓reduceIte]; exact ihu
            · simp only [↓reduceIte, List.map_cons, ihu]; rfl
        exact hgen_f (List.range as.length)
      have hih := ih (offset + 1)
      by_cases heq : offset = i
      · subst heq
        have hne_f : (0 + offset != offset) = false := by simp
        simp only [hne_f, Bool.false_eq_true, ↓reduceIte, htail_eq]
        have hgt_f : ¬ (offset ≥ offset + 1 ∧ offset < offset + 1 + as.length ∧
            as.getD (offset - (offset + 1)) false = true) := by omega
        simp only [hgt_f, ↓reduceIte, Nat.add_zero] at hih
        rw [hih]
        have hsub : offset - offset = 0 := Nat.sub_self offset
        cases a <;> simp [hammingWeight, hsub] <;> omega
      · have hne_t : (0 + offset != i) = true := by
          simp only [Nat.zero_add, bne_iff_ne]; exact heq
        simp only [hne_t, ↓reduceIte, List.map_cons, htail_eq]
        have hget0 : (a :: as).getD 0 false = a := rfl
        rw [hget0]
        by_cases hgt : offset < i
        · have hsub : i - offset = (i - (offset + 1)) + 1 := by omega
          have hget_shift : (a :: as).getD (i - offset) false = as.getD (i - (offset + 1)) false := by
            rw [hsub]; rfl
          have hcond_eq :
              (i ≥ offset ∧ i < offset + (as.length + 1) ∧ (a :: as).getD (i - offset) false = true) ↔
              (i ≥ offset + 1 ∧ i < offset + 1 + as.length ∧ as.getD (i - (offset + 1)) false = true) := by
            rw [hget_shift]; constructor <;> intro h <;> exact ⟨by omega, by omega, h.2.2⟩
          by_cases hc : i ≥ offset + 1 ∧ i < offset + 1 + as.length ∧ as.getD (i - (offset + 1)) false = true
          · have hc' := hcond_eq.mpr hc
            have h1 : (if i ≥ offset + 1 ∧ i < offset + 1 + as.length ∧ as.getD (i - (offset + 1)) false = true then 1 else 0) = 1 := by
              split; rfl; contradiction
            have h2 : (if i ≥ offset ∧ i < offset + (as.length + 1) ∧ (a :: as).getD (i - offset) false = true then 1 else 0) = 1 := by
              split; rfl; contradiction
            rw [h1] at hih; rw [h2]
            cases a <;> simp only [hammingWeight] <;> omega
          · have hc' : ¬ (i ≥ offset ∧ i < offset + (as.length + 1) ∧ (a :: as).getD (i - offset) false = true) :=
              fun h => hc (hcond_eq.mp h)
            have h1 : (if i ≥ offset + 1 ∧ i < offset + 1 + as.length ∧ as.getD (i - (offset + 1)) false = true then 1 else 0) = 0 := by
              split; contradiction; rfl
            have h2 : (if i ≥ offset ∧ i < offset + (as.length + 1) ∧ (a :: as).getD (i - offset) false = true then 1 else 0) = 0 := by
              split; contradiction; rfl
            rw [h1] at hih; rw [h2]
            cases a <;> simp only [hammingWeight] <;> omega
        · have hlt : i < offset := by omega
          have hc1 : ¬ (i ≥ offset + 1 ∧ i < offset + 1 + as.length ∧ as.getD (i - (offset + 1)) false = true) := by omega
          have hc2 : ¬ (i ≥ offset ∧ i < offset + (as.length + 1) ∧ (a :: as).getD (i - offset) false = true) := by omega
          have h1 : (if i ≥ offset + 1 ∧ i < offset + 1 + as.length ∧ as.getD (i - (offset + 1)) false = true then 1 else 0) = 0 := by
            split; contradiction; rfl
          have h2 : (if i ≥ offset ∧ i < offset + (as.length + 1) ∧ (a :: as).getD (i - offset) false = true then 1 else 0) = 0 := by
            split; contradiction; rfl
          rw [h1] at hih; rw [h2]
          cases a <;> simp only [hammingWeight] <;> omega
  have h0 := hgen x 0
  simp only [Nat.add_zero, Nat.zero_add, Nat.sub_zero, ge_iff_le, Nat.zero_le, true_and, hi] at h0
  cases hx0 : x.getD i false
  · simp only [hx0, Bool.false_eq_true, ↓reduceIte] at h0 ⊢; exact h0
  · simp only [hx0, ↓reduceIte] at h0 ⊢; exact h0

private theorem markovOutLayer_len (k : Nat) (negWires : List Nat) (idx count base : Nat) :
    (markovOutLayer k negWires idx count base).2.length = count := by
  induction count generalizing idx base with
  | zero => rfl
  | succ count ih => simp [markovOutLayer, ih]

private theorem markovOutLayer_spec (k : Nat) (x : List Bool) (hx : x.length = 2 ^ k - 1)
    (negWires : List Nat) (ws0 : List Bool)
    (hws0_in : ∀ i < 2 ^ k - 1, ws0.getD i false = x.getD i false)
    (hws0_len : 2 ^ k - 1 ≤ ws0.length)
    (hneg_lt : ∀ w ∈ negWires, w < ws0.length)
    (hneg_sum : weightedSum ((List.range k).map (fun r => 2 ^ (k - 1 - r)))
                  (negWires.map (fun w => ws0.getD w false)) + hammingWeight x = 2 ^ k - 1) :
    ∀ (idx count : Nat), idx + count ≤ 2 ^ k - 1 →
      let res := markovOutLayer k negWires idx count ws0.length
      let wsF := evalCircuit ws0 res.1
      ∀ (j : Nat) (hj : j < count),
        wsF.getD (res.2[j]'(by rw [markovOutLayer_len]; exact hj)) false = !(x.getD (idx + j) false) := by
  intro idx count
  induction count generalizing idx ws0 with
  | zero =>
    intro _ j hj; omega
  | succ count ih =>
    intro hbound
    dsimp only
    unfold markovOutLayer
    dsimp only
    let n := 2 ^ k - 1
    let otherIn := (List.range n).filter (fun j => j != idx)
    let allVars := otherIn ++ negWires
    let bitWeights := (List.range k).map (fun r => 2 ^ (k - 1 - r))
    let allWeights := List.replicate otherIn.length 1 ++ bitWeights
    let resM := compileMonotoneAux allVars (weightedThreshFn allWeights (2 ^ k - 1)) ws0.length
    let ws1 := evalCircuit ws0 resM.1
    have hws1_len : ws1.length = ws0.length + resM.1.length := evalCircuit_length ws0 resM.1
    have hvars_lt : ∀ v ∈ allVars, v < ws0.length := by
      intro v hv
      simp only [allVars, otherIn, List.mem_append, List.mem_filter, List.mem_range] at hv
      rcases hv with ⟨h1, _⟩ | h2
      · omega
      · exact hneg_lt v h2
    have hcur_eval : ws1.getD resM.2 false = !(x.getD idx false) := by
      have h := compileMonotoneAux_eval allVars (weightedThreshFn allWeights (2 ^ k - 1))
        (weightedThreshFn_mono allWeights (2 ^ k - 1)) ws0 hvars_lt
      change ws1.getD resM.2 false = _ at h
      rw [h]
      unfold weightedThreshFn
      simp only [allVars, allWeights, List.map_append]
      rw [weightedSum_append _ _ _ _ (by simp)]
      have hmap_in : otherIn.map (fun v => ws0.getD v false) =
          otherIn.map (fun v => x.getD v false) := by
        apply List.map_congr_left
        intro v hv
        simp only [otherIn, List.mem_filter, List.mem_range] at hv
        exact hws0_in v hv.1
      rw [hmap_in]
      have hrep_len : List.replicate otherIn.length 1 =
          List.replicate (otherIn.map (fun v => x.getD v false)).length 1 := by simp
      rw [hrep_len, weightedSum_ones]
      have hhw := hammingWeight_without_idx x idx (by omega)
      have hother_eq : (List.range x.length).filter (fun j => j != idx) = otherIn := by
        simp [otherIn, n, hx]
      rw [hother_eq] at hhw
      have hns' : weightedSum bitWeights (negWires.map (fun w => ws0.getD w false)) + hammingWeight x = 2 ^ k - 1 := hneg_sum
      change decide (2 ^ k - 1 ≤ hammingWeight (otherIn.map (fun v => x.getD v false)) +
          weightedSum bitWeights (negWires.map (fun w => ws0.getD w false))) = !(x.getD idx false)
      cases hxi : x.getD idx false
      · simp only [hxi, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hhw
        have hge : 2 ^ k - 1 ≤ hammingWeight (otherIn.map (fun v => x.getD v false)) +
            weightedSum bitWeights (negWires.map (fun w => ws0.getD w false)) := by omega
        simp only [hge, decide_true, Bool.not_false]
      · simp only [hxi, ↓reduceIte] at hhw
        have hlt : ¬ (2 ^ k - 1 ≤ hammingWeight (otherIn.map (fun v => x.getD v false)) +
            weightedSum bitWeights (negWires.map (fun w => ws0.getD w false))) := by omega
        simp only [hlt, decide_false, Bool.not_true]
    have hws1_in : ∀ i < 2 ^ k - 1, ws1.getD i false = x.getD i false := by
      intro i hi
      rw [evalCircuit_prefix_preserve ws0 resM.1 i (by omega)]
      exact hws0_in i hi
    have hneg_lt1 : ∀ w ∈ negWires, w < ws1.length := fun w hw => by
      have := hneg_lt w hw; omega
    have hneg_sum1 : weightedSum bitWeights (negWires.map (fun w => ws1.getD w false)) +
        hammingWeight x = 2 ^ k - 1 := by
      have hmap : negWires.map (fun w => ws1.getD w false) = negWires.map (fun w => ws0.getD w false) := by
        apply List.map_congr_left
        intro w hw
        exact evalCircuit_prefix_preserve ws0 resM.1 w (hneg_lt w hw)
      rw [hmap]; exact hneg_sum
    have hih := ih ws1 hws1_in (by omega) hneg_lt1 hneg_sum1 (idx + 1) (by omega)
    rw [hws1_len] at hih
    dsimp only at hih
    let resR := markovOutLayer k negWires (idx + 1) count (ws0.length + resM.1.length)
    intro j hj
    rw [evalCircuit_append]
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero]
      have hw_lt : resM.2 < ws1.length := by
        rw [hws1_len]; exact compileMonotoneAux_out_lt allVars _ ws0.length
      rw [evalCircuit_prefix_preserve ws1 resR.1 resM.2 hw_lt, hcur_eval]
    | succ j' =>
      simp only [List.getElem_cons_succ]
      have h := hih j' (by omega)
      have ha : idx + 1 + j' = idx + (j' + 1) := by omega
      rw [ha] at h
      exact h

/-- Headline Theorem (Markov 1957 Exact Upper Bound):
    For EVERY `k : Nat`, the explicit DAG circuit `(markovInverter k).1` uses
    EXACTLY `k` NOT gates and simultaneously inverts all `n = 2^k - 1` inputs. -/
public theorem markov_inverter_upper (k : Nat) :
    notCount (markovInverter k).1 = k ∧
    ∃ outs : Fin (2 ^ k - 1) → Nat, ComputesInverter (2 ^ k - 1) (markovInverter k).1 outs := by
  refine ⟨markovInverter_notCount k, ?_⟩
  let inv := markovInverter k
  have houts_len : inv.2.length = 2 ^ k - 1 := markovOutLayer_len k _ 0 (2 ^ k - 1) _
  refine ⟨fun i => inv.2[i.val]'(by omega), ?_⟩
  intro x hx i
  unfold markovInverter
  dsimp only
  rw [evalCircuit_append]
  have hbits := markovBitsStage_spec k x hx k (Nat.le_refl k)
  dsimp only at hbits
  rcases hbits with ⟨_, hneg_lt, hneg_vals⟩
  let resB := markovBitsStage k k (2 ^ k - 1)
  let ws0 := evalCircuit x resB.1
  have hws0_len : ws0.length = (2 ^ k - 1) + resB.1.length := by
    rw [evalCircuit_length, hx]
  have hws0_in : ∀ j < 2 ^ k - 1, ws0.getD j false = x.getD j false :=
    fun j hj => evalCircuit_prefix_preserve x resB.1 j (by omega)
  have hneg_sum : weightedSum ((List.range k).map (fun r => 2 ^ (k - 1 - r)))
      (resB.2.map (fun w => ws0.getD w false)) + hammingWeight x = 2 ^ k - 1 := by
    rw [hneg_vals]
    have hw_lt : hammingWeight x < 2 ^ k := by
      have h1 := hammingWeight_le_length x
      have h2 : 0 < 2 ^ k := Nat.two_pow_pos k
      omega
    have hmsb := neg_msb_weighted_sum k (hammingWeight x) hw_lt k (Nat.le_refl k)
    simp only [Nat.sub_self, Nat.pow_zero, Nat.mod_one, Nat.sub_zero] at hmsb
    exact hmsb
  have hout := markovOutLayer_spec k x hx resB.2 ws0 hws0_in (by omega) hneg_lt hneg_sum
    0 (2 ^ k - 1) (by omega)
  rw [hws0_len] at hout
  dsimp only at hout
  have hget := hout i.val i.isLt
  simp only [Nat.zero_add] at hget
  exact hget

/-- Dual-rail De Morgan wire map (public so `fischer_negation_reduction` exposes the exact output wire). -/
@[expose] public def dualRailMap (n : Nat) (invOuts : List Nat) (dualBase : Nat) (w : Nat) : Nat × Nat :=
  if w < n then (w, invOuts.getD w 0)
  else (dualBase + 2 * (w - n), dualBase + 2 * (w - n) + 1)

private theorem list_reverseRecOn {α : Type} {motive : List α → Prop}
    (hnil : motive []) (hsnoc : ∀ (xs : List α) (x : α), motive xs → motive (xs ++ [x]))
    (xs : List α) : motive xs := by
  have hrev : ∀ ys : List α, motive ys.reverse := by
    intro ys; induction ys with
    | nil => exact hnil
    | cons y ys ih => rw [List.reverse_cons]; exact hsnoc ys.reverse y ih
  rw [← List.reverse_reverse xs]
  exact hrev xs.reverse

private def fischerTranslateAux (n : Nat) (invOuts : List Nat) (dualBase : Nat) :
    List GateOp → List GateOp
  | [] => []
  | g :: gs =>
    let pair := fun w => dualRailMap n invOuts dualBase w
    let emit : List GateOp := match g with
      | .const b => [.const b, .const (!b)]
      | .and i j =>
        let (pi, ni) := pair i
        let (pj, nj) := pair j
        [.and pi pj, .or ni nj]
      | .or i j =>
        let (pi, ni) := pair i
        let (pj, nj) := pair j
        [.or pi pj, .and ni nj]
      | .not i =>
        let (pi, ni) := pair i
        [.or ni ni, .or pi pi]
    emit ++ fischerTranslateAux n invOuts dualBase gs

/-- Fischer (1975) universal `k`-NOT-gate compiler for arbitrary circuits on `n = 2^k - 1` inputs. -/
public def fischerCompile (k : Nat) (gs : List GateOp) : List GateOp :=
  let n := 2 ^ k - 1
  let (gInv, invOuts) := markovInverter k
  let dualBase := n + gInv.length
  gInv ++ fischerTranslateAux n invOuts dualBase gs

private theorem fischerTranslateAux_notCount (n : Nat) (invOuts : List Nat) (dualBase : Nat)
    (gs : List GateOp) :
    notCount (fischerTranslateAux n invOuts dualBase gs) = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp [fischerTranslateAux, notCount, ih]

private theorem fischerTranslateAux_length (n : Nat) (invOuts : List Nat) (dualBase : Nat)
    (gs : List GateOp) :
    (fischerTranslateAux n invOuts dualBase gs).length = 2 * gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp [fischerTranslateAux, ih] <;> omega

private theorem markovOutLayer_out_lt (k : Nat) (negWires : List Nat) (idx count base : Nat) :
    ∀ w ∈ (markovOutLayer k negWires idx count base).2,
      w < base + (markovOutLayer k negWires idx count base).1.length := by
  induction count generalizing idx base with
  | zero => intro w hw; simp [markovOutLayer] at hw
  | succ count ih =>
    intro w hw
    unfold markovOutLayer at hw ⊢
    dsimp only at hw ⊢
    simp only [List.mem_cons, List.length_append] at hw ⊢
    rcases hw with rfl | hrest
    · have hlt := compileMonotoneAux_out_lt
        ((List.range (2 ^ k - 1)).filter (fun j => j != idx) ++ negWires)
        (weightedThreshFn (List.replicate ((List.range (2 ^ k - 1)).filter (fun j => j != idx)).length 1 ++
          (List.range k).map (fun r => 2 ^ (k - 1 - r))) (2 ^ k - 1)) base
      omega
    · have hlt := ih (idx + 1) _ w hrest
      omega

private theorem fischer_dualRail_inv (n : Nat) (invOuts : List Nat) (dualBase : Nat)
    (x : List Bool) (hx : x.length = n)
    (ws0 : List Bool) (hws0_len : ws0.length = dualBase) (hdb_ge : n ≤ dualBase)
    (hinv_lt : ∀ i < n, invOuts.getD i 0 < dualBase)
    (hinv_ok : ∀ i < n, ws0.getD i false = x.getD i false ∧ ws0.getD (invOuts.getD i 0) false = !(x.getD i false))
    (gs : List GateOp) :
    (∀ (t : Nat) (ht : t < gs.length),
      match gs[t]'ht with
      | .const _ => True
      | .and i j => i < n + t ∧ j < n + t
      | .or i j => i < n + t ∧ j < n + t
      | .not i => i < n + t) →
    let wsOrig := evalCircuit x gs
    let wsDual := evalCircuit ws0 (fischerTranslateAux n invOuts dualBase gs)
    ∀ w < n + gs.length,
      let (pw, nw) := dualRailMap n invOuts dualBase w
      wsDual.getD pw false = wsOrig.getD w false ∧
      wsDual.getD nw false = !(wsOrig.getD w false) := by
  refine list_reverseRecOn (motive := fun gs =>
    (∀ (t : Nat) (ht : t < gs.length),
      match gs[t]'ht with
      | .const _ => True
      | .and i j => i < n + t ∧ j < n + t
      | .or i j => i < n + t ∧ j < n + t
      | .not i => i < n + t) →
    let wsOrig := evalCircuit x gs
    let wsDual := evalCircuit ws0 (fischerTranslateAux n invOuts dualBase gs)
    ∀ w < n + gs.length,
      let (pw, nw) := dualRailMap n invOuts dualBase w
      wsDual.getD pw false = wsOrig.getD w false ∧
      wsDual.getD nw false = !(wsOrig.getD w false)) ?_ ?_ gs
  · intro _
    dsimp only
    intro w hw
    simp only [List.length_nil, Nat.add_zero] at hw
    simp only [fischerTranslateAux, evalCircuit_nil, dualRailMap, hw, ↓reduceIte]
    exact hinv_ok w hw
  · intro gs g ih hwf
    have hwf_prev : ∀ (t : Nat) (ht : t < gs.length),
        match gs[t]'ht with
        | .const _ => True
        | .and i j => i < n + t ∧ j < n + t
        | .or i j => i < n + t ∧ j < n + t
        | .not i => i < n + t := by
      intro t ht
      have h := hwf t (by simp; omega)
      simp only [List.getElem_append_left ht] at h
      exact h
    have hwf_last := hwf gs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero] at hwf_last
    have hprev := ih hwf_prev
    dsimp only at hprev ⊢
    have htrans_app : ∀ a b,
        fischerTranslateAux n invOuts dualBase (a ++ b) =
        fischerTranslateAux n invOuts dualBase a ++ fischerTranslateAux n invOuts dualBase b := by
      intro a b; induction a with
      | nil => rfl
      | cons u us iha =>
        cases u <;> simp [fischerTranslateAux, iha]
    rw [htrans_app, evalCircuit_append, evalCircuit_append]
    let wsO := evalCircuit x gs
    let wsD := evalCircuit ws0 (fischerTranslateAux n invOuts dualBase gs)
    have hwsO_len : wsO.length = n + gs.length := by rw [evalCircuit_length, hx]
    have hwsD_len : wsD.length = dualBase + 2 * gs.length := by
      rw [evalCircuit_length, hws0_len, fischerTranslateAux_length]
    have hpair_lt : ∀ u < n + gs.length,
        (dualRailMap n invOuts dualBase u).1 < wsD.length ∧
        (dualRailMap n invOuts dualBase u).2 < wsD.length := by
      intro u hu
      unfold dualRailMap
      by_cases hlt : u < n
      · simp only [hlt, ↓reduceIte]
        have := hinv_lt u hlt
        omega
      · simp only [hlt, ↓reduceIte]; omega
    intro w hw
    simp only [List.length_append, List.length_singleton] at hw
    by_cases hlt : w < n + gs.length
    · have hwp := hprev w hlt
      have hlt_pair := hpair_lt w hlt
      have hO_pres : (evalCircuit wsO [g]).getD w false = wsO.getD w false :=
        evalCircuit_prefix_preserve wsO [g] w (by omega)
      have hD_pres1 : (evalCircuit wsD (fischerTranslateAux n invOuts dualBase [g])).getD
          (dualRailMap n invOuts dualBase w).1 false =
          wsD.getD (dualRailMap n invOuts dualBase w).1 false :=
        evalCircuit_prefix_preserve wsD _ _ hlt_pair.1
      have hD_pres2 : (evalCircuit wsD (fischerTranslateAux n invOuts dualBase [g])).getD
          (dualRailMap n invOuts dualBase w).2 false =
          wsD.getD (dualRailMap n invOuts dualBase w).2 false :=
        evalCircuit_prefix_preserve wsD _ _ hlt_pair.2
      rw [hO_pres, hD_pres1, hD_pres2]
      exact hwp
    · have hw_eq : w = n + gs.length := by omega
      subst hw_eq
      have hnot_lt_n : ¬ (n + gs.length < n) := by omega
      have hsub_n : n + gs.length - n = gs.length := by omega
      simp only [dualRailMap, hnot_lt_n, ↓reduceIte, hsub_n]
      have hO_last : (evalCircuit wsO [g]).getD (n + gs.length) false = evalGate wsO g := by
        rw [← hwsO_len]; exact evalCircuit_step_last wsO g
      rw [hO_last]
      have htwo_eval : ∀ g1 g2 : GateOp,
          (evalCircuit wsD [g1, g2]).getD (dualBase + 2 * gs.length) false = evalGate wsD g1 ∧
          (evalCircuit wsD [g1, g2]).getD (dualBase + 2 * gs.length + 1) false =
            evalGate (wsD ++ [evalGate wsD g1]) g2 := by
        intro g1 g2
        rw [← hwsD_len]
        constructor
        · rw [evalCircuit_cons]
          have hpres := evalCircuit_prefix_preserve (wsD ++ [evalGate wsD g1]) [g2] wsD.length (by simp)
          rw [hpres]
          simp [List.getD_eq_getElem?_getD]
        · rw [evalCircuit_cons]
          have hlen1 : (wsD ++ [evalGate wsD g1]).length = wsD.length + 1 := by simp
          rw [← hlen1]
          exact evalCircuit_step_last (wsD ++ [evalGate wsD g1]) g2
      have hget_ext : ∀ u < wsD.length, ∀ b : Bool,
          (wsD ++ [b]).getD u false = wsD.getD u false := by
        intro u hu b
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
      cases g with
      | const b =>
        simp only [fischerTranslateAux, List.append_nil]
        have ⟨he1, he2⟩ := htwo_eval (.const b) (.const (!b))
        rw [he1, he2]; exact ⟨rfl, rfl⟩
      | and i j =>
        rcases hwf_last with ⟨hi, hj⟩
        have hpi := hprev i hi
        have hpj := hprev j hj
        have hlti := hpair_lt i hi
        have hltj := hpair_lt j hj
        simp only [fischerTranslateAux, List.append_nil]
        have ⟨he1, he2⟩ := htwo_eval
          (.and (dualRailMap n invOuts dualBase i).1 (dualRailMap n invOuts dualBase j).1)
          (.or (dualRailMap n invOuts dualBase i).2 (dualRailMap n invOuts dualBase j).2)
        rw [he1, he2]
        simp only [evalGate]
        rw [hget_ext _ hlti.2, hget_ext _ hltj.2, hpi.1, hpi.2, hpj.1, hpj.2]
        exact ⟨rfl, by cases wsO.getD i false <;> cases wsO.getD j false <;> rfl⟩
      | or i j =>
        rcases hwf_last with ⟨hi, hj⟩
        have hpi := hprev i hi
        have hpj := hprev j hj
        have hlti := hpair_lt i hi
        have hltj := hpair_lt j hj
        simp only [fischerTranslateAux, List.append_nil]
        have ⟨he1, he2⟩ := htwo_eval
          (.or (dualRailMap n invOuts dualBase i).1 (dualRailMap n invOuts dualBase j).1)
          (.and (dualRailMap n invOuts dualBase i).2 (dualRailMap n invOuts dualBase j).2)
        rw [he1, he2]
        simp only [evalGate]
        rw [hget_ext _ hlti.2, hget_ext _ hltj.2, hpi.1, hpi.2, hpj.1, hpj.2]
        exact ⟨rfl, by cases wsO.getD i false <;> cases wsO.getD j false <;> rfl⟩
      | not i =>
        have hi : i < n + gs.length := hwf_last
        have hpi := hprev i hi
        have hlti := hpair_lt i hi
        simp only [fischerTranslateAux, List.append_nil]
        have ⟨he1, he2⟩ := htwo_eval
          (.or (dualRailMap n invOuts dualBase i).2 (dualRailMap n invOuts dualBase i).2)
          (.or (dualRailMap n invOuts dualBase i).1 (dualRailMap n invOuts dualBase i).1)
        rw [he1, he2]
        simp only [evalGate]
        rw [hget_ext _ hlti.1, hpi.1, hpi.2]
        exact ⟨by cases wsO.getD i false <;> rfl, by cases wsO.getD i false <;> rfl⟩

/-- Headline Theorem (Fischer 1975 Universal Negation Reduction):
    ANY well-formed Boolean circuit `gs` on `n = 2^k - 1` inputs compiles to
    `fischerCompile k gs` using EXACTLY `k` NOT gates while preserving the exact
    Boolean semantics of every wire `w < n + gs.length`. -/
public theorem fischer_negation_reduction (k : Nat) (gs : List GateOp)
    (hwf : ∀ (t : Nat) (ht : t < gs.length),
      match gs[t]'ht with
      | .const _ => True
      | .and i j => i < (2 ^ k - 1) + t ∧ j < (2 ^ k - 1) + t
      | .or i j => i < (2 ^ k - 1) + t ∧ j < (2 ^ k - 1) + t
      | .not i => i < (2 ^ k - 1) + t) :
    notCount (fischerCompile k gs) = k ∧
    ∀ w < (2 ^ k - 1) + gs.length,
      let outWire := (dualRailMap (2 ^ k - 1) (markovInverter k).2 ((2 ^ k - 1) + (markovInverter k).1.length) w).1
      ∀ x : List Bool, x.length = 2 ^ k - 1 →
        (evalCircuit x (fischerCompile k gs)).getD outWire false = (evalCircuit x gs).getD w false := by
  constructor
  · unfold fischerCompile
    rw [notCount_append, markovInverter_notCount, fischerTranslateAux_notCount]
    rfl
  · intro w hw
    dsimp only
    intro x hx
    unfold fischerCompile
    dsimp only
    rw [evalCircuit_append]
    let n := 2 ^ k - 1
    let gInv := (markovInverter k).1
    let invOuts := (markovInverter k).2
    let dualBase := n + gInv.length
    let ws0 := evalCircuit x gInv
    have hws0_len : ws0.length = dualBase := by rw [evalCircuit_length, hx]
    have hinv_len : invOuts.length = n := markovOutLayer_len k _ 0 n _
    have hinv_lt : ∀ i < n, invOuts.getD i 0 < dualBase := by
      intro i hi
      have hmem : invOuts.getD i 0 ∈ invOuts := by
        have hi' : i < invOuts.length := by omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
        exact List.getElem_mem hi'
      have hlt := markovOutLayer_out_lt k (markovBitsStage k k n).2 0 n (n + (markovBitsStage k k n).1.length)
        (invOuts.getD i 0) hmem
      have hglen : gInv.length = (markovBitsStage k k n).1.length +
          (markovOutLayer k (markovBitsStage k k n).2 0 n (n + (markovBitsStage k k n).1.length)).1.length := by
        simp [gInv, markovInverter, n]
      omega
    have hinv_ok : ∀ i < n,
        ws0.getD i false = x.getD i false ∧ ws0.getD (invOuts.getD i 0) false = !(x.getD i false) := by
      intro i hi
      constructor
      · exact evalCircuit_prefix_preserve x gInv i (by omega)
      · have hbits := markovBitsStage_spec k x hx k (Nat.le_refl k)
        dsimp only at hbits
        rcases hbits with ⟨_, hneg_lt, hneg_vals⟩
        let resB := markovBitsStage k k n
        let wsB := evalCircuit x resB.1
        have hwsB_len : wsB.length = n + resB.1.length := by rw [evalCircuit_length, hx]
        have hwsB_in : ∀ j < n, wsB.getD j false = x.getD j false :=
          fun j hj => evalCircuit_prefix_preserve x resB.1 j (by omega)
        have hneg_sum : weightedSum ((List.range k).map (fun r => 2 ^ (k - 1 - r)))
            (resB.2.map (fun u => wsB.getD u false)) + hammingWeight x = n := by
          rw [hneg_vals]
          have hw_lt : hammingWeight x < 2 ^ k := by
            have h1 := hammingWeight_le_length x
            have h2 : 0 < 2 ^ k := Nat.two_pow_pos k
            omega
          have hmsb := neg_msb_weighted_sum k (hammingWeight x) hw_lt k (Nat.le_refl k)
          simp only [Nat.sub_self, Nat.pow_zero, Nat.mod_one, Nat.sub_zero] at hmsb
          exact hmsb
        have hout := markovOutLayer_spec k x hx resB.2 wsB hwsB_in (by omega) hneg_lt hneg_sum
          0 n (by omega)
        rw [hwsB_len] at hout
        dsimp only at hout
        have hget := hout i hi
        simp only [Nat.zero_add] at hget
        have hgetD : invOuts.getD i 0 =
            (markovOutLayer k resB.2 0 n (n + resB.1.length)).2[i]'(by rw [markovOutLayer_len]; exact hi) := by
          have hi' : i < invOuts.length := by omega
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
          rfl
        rw [hgetD]
        simpa [ws0, gInv, markovInverter, evalCircuit_append, resB, wsB, n] using hget
    exact (fischer_dualRail_inv n invOuts dualBase x hx ws0 hws0_len (by omega) hinv_lt hinv_ok gs hwf w hw).1

-- ============================================================================
-- Proofs Part 2: Multiplicative Complexity (`MC(f) ≥ deg_{F_2}(f) - 1`) & `MC(AND_n) ≥ n - 1`
-- ============================================================================

private theorem evalPolyF2_append {n : Nat} (ms1 ms2 : List (List (Fin n))) (x : Fin n → Bool) :
    evalPolyF2 (ms1 ++ ms2) x = xor (evalPolyF2 ms1 x) (evalPolyF2 ms2 x) := by
  have hgen : ∀ (ms : List (List (Fin n))) (init : Bool),
      ms.foldl (fun acc m => xor acc (evalMonomial m x)) init =
      xor init (ms.foldl (fun acc m => xor acc (evalMonomial m x)) false) := by
    intro ms
    induction ms with
    | nil => intro init; cases init <;> rfl
    | cons m ms ih =>
      intro init
      simp only [List.foldl_cons]
      rw [ih (xor init (evalMonomial m x)), ih (xor false (evalMonomial m x))]
      cases init <;> cases evalMonomial m x <;>
        cases (ms.foldl (fun acc m => xor acc (evalMonomial m x)) false) <;> rfl
  unfold evalPolyF2
  rw [List.foldl_append]
  exact hgen ms2 _

private theorem hasF2DegLe_mono {n : Nat} {f : (Fin n → Bool) → Bool} {d1 d2 : Nat}
    (h : HasF2DegLe n f d1) (hle : d1 ≤ d2) : HasF2DegLe n f d2 := by
  rcases h with ⟨ms, hdeg, heval⟩
  exact ⟨ms, fun m hm => Nat.le_trans (hdeg m hm) hle, heval⟩

private theorem hasF2DegLe_const (n : Nat) (b : Bool) :
    HasF2DegLe n (fun _ => b) 0 := by
  cases b
  · exact ⟨[], fun _ h => by simp at h, fun _ => rfl⟩
  · exact ⟨[[]], fun m hm => by simp at hm; subst hm; exact Nat.le_refl 0, fun _ => rfl⟩

private theorem hasF2DegLe_var (n : Nat) (i : Fin n) :
    HasF2DegLe n (fun x => x i) 1 := by
  refine ⟨[[i]], fun m hm => by simp at hm; subst hm; exact Nat.le_refl 1, fun x => ?_⟩
  unfold evalPolyF2 evalMonomial
  simp only [List.foldl_cons, List.foldl_nil, List.all_cons, List.all_nil, Bool.and_true]
  cases x i <;> rfl

private theorem hasF2DegLe_xor {n : Nat} {f g : (Fin n → Bool) → Bool} {d1 d2 : Nat}
    (hf : HasF2DegLe n f d1) (hg : HasF2DegLe n g d2) :
    HasF2DegLe n (fun x => xor (f x) (g x)) (max d1 d2) := by
  rcases hf with ⟨ms1, hd1, he1⟩
  rcases hg with ⟨ms2, hd2, he2⟩
  refine ⟨ms1 ++ ms2, ?_, ?_⟩
  · intro m hm
    simp only [List.mem_append] at hm
    rcases hm with h1 | h2
    · exact Nat.le_trans (hd1 m h1) (Nat.le_max_left d1 d2)
    · exact Nat.le_trans (hd2 m h2) (Nat.le_max_right d1 d2)
  · intro x
    dsimp only
    rw [evalPolyF2_append, he1 x, he2 x]

private theorem hasF2DegLe_and {n : Nat} {f g : (Fin n → Bool) → Bool} {d1 d2 : Nat}
    (hf : HasF2DegLe n f d1) (hg : HasF2DegLe n g d2) :
    HasF2DegLe n (fun x => f x && g x) (d1 + d2) := by
  rcases hf with ⟨ms1, hd1, he1⟩
  rcases hg with ⟨ms2, hd2, he2⟩
  let prod := ms1.flatMap (fun m1 => ms2.map (fun m2 => m1 ++ m2))
  refine ⟨prod, ?_, ?_⟩
  · intro m hm
    simp only [prod, List.mem_flatMap, List.mem_map] at hm
    rcases hm with ⟨m1, hm1, m2, hm2, rfl⟩
    rw [List.length_append]
    have := hd1 m1 hm1
    have := hd2 m2 hm2
    omega
  · intro x
    dsimp only
    rw [he1 x, he2 x]
    have hmul_mon : ∀ (m1 : List (Fin n)) (ms : List (List (Fin n))),
        evalPolyF2 (ms.map (fun m2 => m1 ++ m2)) x = (evalMonomial m1 x && evalPolyF2 ms x) := by
      intro m1 ms
      induction ms with
      | nil => simp [evalPolyF2]
      | cons m2 ms ih =>
        have hcons : (m2 :: ms).map (fun u => m1 ++ u) = [m1 ++ m2] ++ ms.map (fun u => m1 ++ u) := rfl
        rw [hcons, evalPolyF2_append, ih]
        have hcons2 : evalPolyF2 (m2 :: ms) x = xor (evalMonomial m2 x) (evalPolyF2 ms x) := by
          have : m2 :: ms = [m2] ++ ms := rfl
          rw [this, evalPolyF2_append]
          unfold evalPolyF2; simp only [List.foldl_cons, List.foldl_nil]
          cases evalMonomial m2 x <;> rfl
        rw [hcons2]
        have hsingle : evalPolyF2 [m1 ++ m2] x = (evalMonomial m1 x && evalMonomial m2 x) := by
          unfold evalPolyF2 evalMonomial
          simp only [List.foldl_cons, List.foldl_nil, List.all_append]
          cases (m1.all fun i => x i) <;> cases (m2.all fun i => x i) <;> rfl
        rw [hsingle]
        cases evalMonomial m1 x <;> cases evalMonomial m2 x <;> cases evalPolyF2 ms x <;> rfl
    clear hd1 he1 f
    induction ms1 with
    | nil => simp [prod, evalPolyF2]
    | cons m1 ms1 ih =>
      have hfm : (m1 :: ms1).flatMap (fun u => ms2.map (fun v => u ++ v)) =
          ms2.map (fun v => m1 ++ v) ++ ms1.flatMap (fun u => ms2.map (fun v => u ++ v)) := rfl
      change (evalPolyF2 (m1 :: ms1) x && evalPolyF2 ms2 x) =
        evalPolyF2 ((m1 :: ms1).flatMap (fun u => ms2.map (fun v => u ++ v))) x
      rw [hfm, evalPolyF2_append, hmul_mon, ← ih]
      have hcons1 : evalPolyF2 (m1 :: ms1) x = xor (evalMonomial m1 x) (evalPolyF2 ms1 x) := by
        have : m1 :: ms1 = [m1] ++ ms1 := rfl
        rw [this, evalPolyF2_append]
        unfold evalPolyF2; simp only [List.foldl_cons, List.foldl_nil]
        cases evalMonomial m1 x <;> rfl
      rw [hcons1]
      cases evalMonomial m1 x <;> cases evalPolyF2 ms1 x <;> cases evalPolyF2 ms2 x <;> rfl

/-- Product of a finite list of Boolean functions. -/
private def fnProd {n : Nat} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) : Bool :=
  fs.foldl (fun acc f => acc && f x) true

/-- XOR of a finite list of Boolean functions. -/
private def fnXor {n : Nat} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) : Bool :=
  fs.foldl (fun acc f => xor acc (f x)) false

private theorem fnXor_cons {n : Nat} (f : (Fin n → Bool) → Bool) (fs : List ((Fin n → Bool) → Bool))
    (x : Fin n → Bool) :
    fnXor (f :: fs) x = xor (f x) (fnXor fs x) := by
  have hgen : ∀ (ls : List ((Fin n → Bool) → Bool)) (init : Bool),
      ls.foldl (fun acc g => xor acc (g x)) init =
      xor init (ls.foldl (fun acc g => xor acc (g x)) false) := by
    intro ls; induction ls with
    | nil => intro init; cases init <;> rfl
    | cons g gs ih =>
      intro init; simp only [List.foldl_cons]
      rw [ih (xor init (g x)), ih (xor false (g x))]
      cases init <;> cases g x <;> cases (gs.foldl (fun acc h => xor acc (h x)) false) <;> rfl
  unfold fnXor; simp only [List.foldl_cons]
  rw [hgen fs (xor false (f x))]
  cases f x <;> cases (fs.foldl (fun acc g => xor acc (g x)) false) <;> rfl

private theorem hasF2DegLe_fnXor {n : Nat} (d : Nat) (fs : List ((Fin n → Bool) → Bool))
    (h : ∀ f ∈ fs, HasF2DegLe n f d) : HasF2DegLe n (fnXor fs) d := by
  induction fs with
  | nil =>
    exact hasF2DegLe_mono (hasF2DegLe_const n false) (Nat.zero_le d)
  | cons f fs ih =>
    have hf := h f (by simp)
    have hfs := ih (fun g hg => h g (by simp [hg]))
    have hcomb := hasF2DegLe_xor hf hfs
    rw [Nat.max_self] at hcomb
    rcases hcomb with ⟨ms, hd, he⟩
    exact ⟨ms, hd, fun x => by rw [fnXor_cons, ← he x]⟩

private theorem fnProd_cons {n : Nat} (f : (Fin n → Bool) → Bool) (fs : List ((Fin n → Bool) → Bool))
    (x : Fin n → Bool) :
    fnProd (f :: fs) x = (f x && fnProd fs x) := by
  have hgen : ∀ (ls : List ((Fin n → Bool) → Bool)) (init : Bool),
      ls.foldl (fun acc g => acc && g x) init =
      (init && ls.foldl (fun acc g => acc && g x) true) := by
    intro ls; induction ls with
    | nil => intro init; cases init <;> rfl
    | cons g gs ih =>
      intro init; simp only [List.foldl_cons]
      rw [ih (init && g x), ih (true && g x)]
      cases init <;> cases g x <;> cases (gs.foldl (fun acc h => acc && h x) true) <;> rfl
  unfold fnProd; simp only [List.foldl_cons]
  rw [hgen fs (true && f x)]
  cases f x <;> cases (fs.foldl (fun acc g => acc && g x) true) <;> rfl

private theorem fnProd_of_subset_idx {n : Nat} (gs : List ((Fin n → Bool) → Bool))
    (S : List Nat) (x : Fin n → Bool) :
    fnProd (S.map (fun i => gs.getD i (fun _ => false))) x = true ↔
    ∀ i ∈ S, gs.getD i (fun _ => false) x = true := by
  induction S with
  | nil => simp [fnProd]
  | cons i S ih =>
    rw [List.map_cons, fnProd_cons, Bool.and_eq_true, ih]
    simp

/-- Helper: every wire of a circuit is an affine combination of `(inputs, andGates)`,
    and every nonempty subset `S ⊆ {0 .. t-1}` of the `t` AND gates satisfies
    `HasF2DegLe n (∏_{i ∈ S} g_i) (t + S.length)` (using deduplicated subsets!). -/
private def dedupNat : List Nat → List Nat
  | [] => []
  | a :: as => if a ∈ as then dedupNat as else a :: dedupNat as

private theorem mem_dedupNat {a : Nat} {xs : List Nat} : a ∈ dedupNat xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp [dedupNat]
  | cons b bs ih =>
    unfold dedupNat
    by_cases h : b ∈ bs
    · simp only [h, ↓reduceIte, ih, List.mem_cons]
      constructor
      · intro ha; exact Or.inr ha
      · rintro (rfl | ha); exact h; exact ha
    · simp only [h, ↓reduceIte, List.mem_cons, ih]

private theorem dedupNat_length_le (xs : List Nat) : (dedupNat xs).length ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons b bs ih =>
    unfold dedupNat
    by_cases h : b ∈ bs <;> simp [h] <;> omega

private theorem dedupNat_cons_length_le (a : Nat) (xs : List Nat) :
    (dedupNat (a :: xs)).length ≤ (dedupNat xs).length + 1 := by
  conv => lhs; unfold dedupNat
  by_cases h : a ∈ xs <;> simp [h]

private theorem dedupNat_ne_nil_of_ne_nil {xs : List Nat} (hne : xs ≠ []) : dedupNat xs ≠ [] := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons a as =>
    intro hempty
    have hmem : a ∈ dedupNat (a :: as) := mem_dedupNat.mpr (by simp)
    rw [hempty] at hmem
    simp at hmem

private theorem fnProd_dedup_eq {n : Nat} (gs : List ((Fin n → Bool) → Bool))
    (S : List Nat) (x : Fin n → Bool) :
    fnProd ((dedupNat S).map (fun i => gs.getD i (fun _ => false))) x =
    fnProd (S.map (fun i => gs.getD i (fun _ => false))) x := by
  cases h1 : fnProd ((dedupNat S).map (fun i => gs.getD i (fun _ => false))) x <;>
  cases h2 : fnProd (S.map (fun i => gs.getD i (fun _ => false))) x
  · rfl
  · exfalso
    have hall := (fnProd_of_subset_idx gs S x).mp h2
    have hall' : ∀ i ∈ dedupNat S, gs.getD i (fun _ => false) x = true :=
      fun i hi => hall i (mem_dedupNat.mp hi)
    have ht := (fnProd_of_subset_idx gs (dedupNat S) x).mpr hall'
    rw [h1] at ht; exact Bool.noConfusion ht
  · exfalso
    have hall := (fnProd_of_subset_idx gs (dedupNat S) x).mp h1
    have hall' : ∀ i ∈ S, gs.getD i (fun _ => false) x = true :=
      fun i hi => hall i (mem_dedupNat.mpr hi)
    have ht := (fnProd_of_subset_idx gs S x).mpr hall'
    rw [h2] at ht; exact Bool.noConfusion ht
  · rfl

/-- Core inductive invariant for `{1, XOR, AND}` circuits (Schnorr / Boyar–Peralta):
    For any circuit `gs` with `k = andCount gs`, there exists a list `andFns` of
    length `k` such that:
    1. Every wire `w` of `evalXorAndCircuit (vecToBits x) gs` is `ℓ(x) ⊕ ⨁_{i ∈ I} andFns[i](x)`
       for some affine function `ℓ` (deg `≤ 1`) and index list `I ⊆ {0 .. k-1}`;
    2. Every nonempty index list `S ⊆ {0 .. k-1}` has `HasF2DegLe n (∏_{i ∈ S} andFns[i]) (k + (dedupNat S).length)`. -/
private theorem xorAnd_deg_invariant (n : Nat) (gs : List XorAndOp) :
    ∃ (andFns : List ((Fin n → Bool) → Bool)),
      andFns.length = andCount gs ∧
      (∀ w : Nat, ∃ (lin : (Fin n → Bool) → Bool) (idxs : List Nat),
        HasF2DegLe n lin 1 ∧ (∀ i ∈ idxs, i < andFns.length) ∧
        ∀ x : Fin n → Bool,
          (evalXorAndCircuit (vecToBits x) gs).getD w false =
          xor (lin x) (fnXor (idxs.map (fun i => andFns.getD i (fun _ => false))) x)) ∧
      (∀ S : List Nat, S ≠ [] → (∀ i ∈ S, i < andFns.length) →
        HasF2DegLe n (fnProd (S.map (fun i => andFns.getD i (fun _ => false))))
          (andFns.length + (dedupNat S).length)) := by
  refine list_reverseRecOn (motive := fun gs =>
    ∃ (andFns : List ((Fin n → Bool) → Bool)),
      andFns.length = andCount gs ∧
      (∀ w : Nat, ∃ (lin : (Fin n → Bool) → Bool) (idxs : List Nat),
        HasF2DegLe n lin 1 ∧ (∀ i ∈ idxs, i < andFns.length) ∧
        ∀ x : Fin n → Bool,
          (evalXorAndCircuit (vecToBits x) gs).getD w false =
          xor (lin x) (fnXor (idxs.map (fun i => andFns.getD i (fun _ => false))) x)) ∧
      (∀ S : List Nat, S ≠ [] → (∀ i ∈ S, i < andFns.length) →
        HasF2DegLe n (fnProd (S.map (fun i => andFns.getD i (fun _ => false))))
          (andFns.length + (dedupNat S).length))) ?_ ?_ gs
  · refine ⟨[], rfl, ?_, ?_⟩
    · intro w
      by_cases hw : w < n
      · refine ⟨fun x => x ⟨w, hw⟩, [], hasF2DegLe_var n ⟨w, hw⟩, fun _ h => by simp at h, fun x => ?_⟩
        unfold evalXorAndCircuit vecToBits fnXor
        have hlen : ((List.finRange n).map x).length = n := by simp
        have hlt : w < ((List.finRange n).map x).length := by omega
        simp only [List.foldl_nil, List.map_nil, Bool.xor_false, List.getD_eq_getElem?_getD,
                   List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_map, List.getElem_finRange]
        rfl
      · refine ⟨fun _ => false, [], hasF2DegLe_mono (hasF2DegLe_const n false) (by omega),
          fun _ h => by simp at h, fun x => ?_⟩
        unfold evalXorAndCircuit vecToBits fnXor
        have hnone : ((List.finRange n).map x)[w]? = none := by
          apply List.getElem?_eq_none; simp; omega
        simp [List.getD_eq_getElem?_getD, hnone]
    · intro S hne hlt
      cases S with
      | nil => exact absurd rfl hne
      | cons i _ => have := hlt i (by simp); simp at this
  · intro gs g ih
    rcases ih with ⟨andFns, handLen, hwire, hprod⟩
    have hand_app : ∀ a b, andCount (a ++ b) = andCount a + andCount b := by
      intro a b; induction a with
      | nil => simp [andCount]
      | cons u us iha => cases u <;> simp [andCount, iha] <;> omega
    have heval_app : ∀ (x : List Bool) (a b : List XorAndOp),
        evalXorAndCircuit x (a ++ b) = evalXorAndCircuit (evalXorAndCircuit x a) b := by
      intro x a b; unfold evalXorAndCircuit; exact List.foldl_append
    have hlen_circ : ∀ (x : List Bool) (cs : List XorAndOp),
        (evalXorAndCircuit x cs).length = x.length + cs.length := by
      intro x cs; induction cs generalizing x with
      | nil => simp [evalXorAndCircuit]
      | cons u us ihc =>
        change (evalXorAndCircuit (x ++ [evalXorAndGate x u]) us).length = _
        rw [ihc, List.length_append, List.length_singleton, List.length_cons]; omega
    have hvec_len : ∀ x : Fin n → Bool, (vecToBits x).length = n := fun x => by simp [vecToBits]
    have hstep_get : ∀ (x : Fin n → Bool) (w : Nat),
        (evalXorAndCircuit (vecToBits x) (gs ++ [g])).getD w false =
        if w < n + gs.length then (evalXorAndCircuit (vecToBits x) gs).getD w false
        else if w = n + gs.length then evalXorAndGate (evalXorAndCircuit (vecToBits x) gs) g
        else false := by
      intro x w
      rw [heval_app]
      unfold evalXorAndCircuit
      simp only [List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD]
      have hplen : (gs.foldl (fun ws op => ws ++ [evalXorAndGate ws op]) (vecToBits x)).length = n + gs.length := by
        have := hlen_circ (vecToBits x) gs
        rw [hvec_len] at this; exact this
      by_cases h1 : w < n + gs.length
      · have h1' : w < (gs.foldl (fun ws op => ws ++ [evalXorAndGate ws op]) (vecToBits x)).length := by omega
        simp only [h1, ↓reduceIte, List.getElem?_append_left h1']
      · by_cases h2 : w = n + gs.length
        · subst h2
          simp only [h1, ↓reduceIte]
          rw [← hplen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        · have hnone : (gs.foldl (fun ws op => ws ++ [evalXorAndGate ws op]) (vecToBits x) ++
              [evalXorAndGate (gs.foldl (fun ws op => ws ++ [evalXorAndGate ws op]) (vecToBits x)) g])[w]? = none := by
            apply List.getElem?_eq_none; simp; omega
          simp only [h1, h2, ↓reduceIte, hnone]; rfl
    cases g with
    | const b =>
      refine ⟨andFns, by rw [hand_app, handLen]; simp [andCount], ?_, hprod⟩
      intro w
      by_cases h1 : w < n + gs.length
      · rcases hwire w with ⟨lin, idxs, hld, hid, hev⟩
        exact ⟨lin, idxs, hld, hid, fun x => by rw [hstep_get]; simp only [h1, ↓reduceIte, hev x]⟩
      · by_cases h2 : w = n + gs.length
        · refine ⟨fun _ => b, [], hasF2DegLe_mono (hasF2DegLe_const n b) (by omega),
            fun _ h => by simp at h, fun x => ?_⟩
          rw [hstep_get]; simp only [h1, ↓reduceIte]; simp only [h2, ↓reduceIte, evalXorAndGate, fnXor, List.map_nil, List.foldl_nil]
          cases b <;> rfl
        · refine ⟨fun _ => false, [], hasF2DegLe_mono (hasF2DegLe_const n false) (by omega),
            fun _ h => by simp at h, fun x => ?_⟩
          rw [hstep_get]; simp only [h1, h2, ↓reduceIte, fnXor, List.map_nil, List.foldl_nil]; rfl
    | xor i j =>
      refine ⟨andFns, by rw [hand_app, handLen]; simp [andCount], ?_, hprod⟩
      intro w
      by_cases h1 : w < n + gs.length
      · rcases hwire w with ⟨lin, idxs, hld, hid, hev⟩
        exact ⟨lin, idxs, hld, hid, fun x => by rw [hstep_get]; simp only [h1, ↓reduceIte, hev x]⟩
      · by_cases h2 : w = n + gs.length
        · rcases hwire i with ⟨li, idxi, hldi, hidi, hevi⟩
          rcases hwire j with ⟨lj, idxj, hldj, hidj, hevj⟩
          have hlin := hasF2DegLe_xor hldi hldj
          rw [Nat.max_self] at hlin
          refine ⟨fun x => xor (li x) (lj x), idxi ++ idxj, hlin, ?_, fun x => ?_⟩
          · intro u hu; simp only [List.mem_append] at hu
            rcases hu with ha | hb; exact hidi u ha; exact hidj u hb
          · rw [hstep_get]; simp only [h1, ↓reduceIte]; simp only [h2, ↓reduceIte, evalXorAndGate]
            rw [hevi x, hevj x, List.map_append]
            have hfx_app : ∀ (a b : List ((Fin n → Bool) → Bool)),
                fnXor (a ++ b) x = xor (fnXor a x) (fnXor b x) := by
              intro a b; induction a with
              | nil => simp [fnXor]
              | cons u us iha =>
                rw [List.cons_append, fnXor_cons, fnXor_cons, iha]
                cases u x <;> cases fnXor us x <;> cases fnXor b x <;> rfl
            rw [hfx_app]
            cases li x <;> cases lj x <;> cases fnXor _ x <;> cases fnXor _ x <;> rfl
        · refine ⟨fun _ => false, [], hasF2DegLe_mono (hasF2DegLe_const n false) (by omega),
            fun _ h => by simp at h, fun x => ?_⟩
          rw [hstep_get]; simp only [h1, h2, ↓reduceIte, fnXor, List.map_nil, List.foldl_nil]; rfl
    | and i j =>
      -- Append the new AND gate function `gNew` at index `t = andFns.length`
      let t := andFns.length
      let gNew : (Fin n → Bool) → Bool := fun x =>
        (evalXorAndCircuit (vecToBits x) gs).getD i false &&
        (evalXorAndCircuit (vecToBits x) gs).getD j false
      let andFns' := andFns ++ [gNew]
      have hlen' : andFns'.length = t + 1 := by simp [andFns', t]
      have hget_old : ∀ u < t, andFns'.getD u (fun _ => false) = andFns.getD u (fun _ => false) := by
        intro u hu; simp [andFns', List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
      have hget_new : andFns'.getD t (fun _ => false) = gNew := by
        simp [andFns', t, List.getD_eq_getElem?_getD]
      refine ⟨andFns', by rw [hlen', hand_app, ← handLen]; simp [andCount, t], ?_, ?_⟩
      · -- Wire affine-plus-AND-gates representation
        intro w
        by_cases h1 : w < n + gs.length
        · rcases hwire w with ⟨lin, idxs, hld, hid, hev⟩
          refine ⟨lin, idxs, hld, fun u hu => by have := hid u hu; omega, fun x => ?_⟩
          rw [hstep_get]; simp only [h1, ↓reduceIte, hev x]
          have hmap : idxs.map (fun u => andFns'.getD u (fun _ => false)) =
              idxs.map (fun u => andFns.getD u (fun _ => false)) := by
            apply List.map_congr_left; intro u hu; exact hget_old u (hid u hu)
          rw [hmap]
        · by_cases h2 : w = n + gs.length
          · refine ⟨fun _ => false, [t], hasF2DegLe_mono (hasF2DegLe_const n false) (by omega),
              fun u hu => by simp at hu; subst hu; omega, fun x => ?_⟩
            rw [hstep_get]; simp only [h1, ↓reduceIte]
            simp only [h2, ↓reduceIte, evalXorAndGate, fnXor,
                       List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, hget_new, gNew]
            cases ((evalXorAndCircuit (vecToBits x) gs).getD i false &&
                   (evalXorAndCircuit (vecToBits x) gs).getD j false) <;> rfl
          · refine ⟨fun _ => false, [], hasF2DegLe_mono (hasF2DegLe_const n false) (by omega),
              fun _ h => by simp at h, fun x => ?_⟩
            rw [hstep_get]; simp only [h1, h2, ↓reduceIte, fnXor, List.map_nil, List.foldl_nil]; rfl
      · -- The 4-case subset product degree bound: `deg(∏_{u ∈ S} andFns'[u]) ≤ (t + 1) + |dedup S|`
        intro S hSne hSlt
        let S' := (dedupNat S).filter (fun u => u != t)
        have hS'_lt : ∀ u ∈ S', u < t := by
          intro u hu
          simp only [S', List.mem_filter, bne_iff_ne] at hu
          have h1 := hSlt u (mem_dedupNat.mp hu.1)
          omega
        by_cases ht_in : t ∈ dedupNat S
        · -- Case 2: `t ∈ S`. Write `gNew = (li ⊕ ⨁_U g_u) && (lj ⊕ ⨁_V g_v)` and expand!
          rcases hwire i with ⟨li, U, hli, hU, hevi⟩
          rcases hwire j with ⟨lj, V, hlj, hV, hevj⟩
          have hS'_len : S'.length + 1 = (dedupNat S).length := by
            -- `dedupNat S` has no duplicates and contains `t`, so filtering `!= t` drops exactly 1 element
            have hnodup : ∀ xs : List Nat, (dedupNat xs).Nodup := by
              intro xs; induction xs with
              | nil => exact List.nodup_nil
              | cons a as iha =>
                unfold dedupNat
                by_cases hm : a ∈ as
                · simp [hm, iha]
                · simp only [hm, ↓reduceIte, List.nodup_cons]
                  exact ⟨fun h => hm (mem_dedupNat.mp h), iha⟩
            have hdrop1 : ∀ (ls : List Nat), ls.Nodup → t ∈ ls →
                (ls.filter (fun u => u != t)).length + 1 = ls.length := by
              intro ls hnd hmem
              induction ls with
              | nil => simp at hmem
              | cons a as ihl =>
                simp only [List.nodup_cons] at hnd
                simp only [List.mem_cons] at hmem
                rcases hmem with rfl | hrest
                · have hnotin : t ∉ as := hnd.1
                  have hall : as.filter (fun u => u != t) = as := by
                    apply List.filter_eq_self.mpr
                    intro u hu; simp only [bne_iff_ne]; intro heq; subst heq; exact hnotin hu
                  simp [hall]
                · have hne : a ≠ t := fun heq => hnd.1 (heq ▸ hrest)
                  have hbt : (a != t) = true := by simp [hne]
                  have := ihl hnd.2 hrest
                  simp [hbt]; omega
            exact hdrop1 (dedupNat S) (hnodup S) ht_in
          have hdedup_S'_le : (dedupNat S').length ≤ S'.length := dedupNat_length_le S'
          -- Express `∏_{u ∈ S} andFns'[u]` as `(∏_{u ∈ S'} andFns[u]) && gNew`
          have hsplit_fn : ∀ x,
              fnProd (S.map (fun u => andFns'.getD u (fun _ => false))) x =
              (fnProd (S'.map (fun u => andFns.getD u (fun _ => false))) x && gNew x) := by
            intro x
            rw [← fnProd_dedup_eq andFns' S x]
            cases hl : fnProd ((dedupNat S).map (fun u => andFns'.getD u (fun _ => false))) x <;>
            cases hr : (fnProd (S'.map (fun u => andFns.getD u (fun _ => false))) x && gNew x)
            · rfl
            · exfalso
              rw [Bool.and_eq_true] at hr
              have hall_S' := (fnProd_of_subset_idx andFns S' x).mp hr.1
              have hall : ∀ u ∈ dedupNat S, andFns'.getD u (fun _ => false) x = true := by
                intro u hu
                by_cases hut : u = t
                · subst hut; rw [hget_new]; exact hr.2
                · have huS' : u ∈ S' := by simp [S', hu, hut]
                  rw [hget_old u (hS'_lt u huS')]
                  exact hall_S' u huS'
              have ht := (fnProd_of_subset_idx andFns' (dedupNat S) x).mpr hall
              rw [hl] at ht; exact Bool.noConfusion ht
            · exfalso
              have hall := (fnProd_of_subset_idx andFns' (dedupNat S) x).mp hl
              have hgNew_t : gNew x = true := by
                have := hall t ht_in; rwa [hget_new] at this
              have hall_S' : ∀ u ∈ S', andFns.getD u (fun _ => false) x = true := by
                intro u hu
                have hu1 : u ∈ dedupNat S := (List.mem_filter.mp hu).1
                have := hall u hu1
                rwa [hget_old u (hS'_lt u hu)] at this
              have hS't := (fnProd_of_subset_idx andFns S' x).mpr hall_S'
              rw [hS't, hgNew_t] at hr; exact Bool.noConfusion hr
            · rfl
          let P_S' : (Fin n → Bool) → Bool := fnProd (S'.map (fun u => andFns.getD u (fun _ => false)))
          let D := (t + 1) + (dedupNat S).length
          -- Bound each of the 4 expanded pieces to degree `≤ D = (t + 1) + (S'.length + 1)`!
          -- Piece 1: `P_S' && (li && lj)`
          have hP1 : HasF2DegLe n (fun x => P_S' x && (li x && lj x)) D := by
            have hlij := hasF2DegLe_and hli hlj
            cases hS'e : S' with
            | nil =>
              have heq : (fun x => P_S' x && (li x && lj x)) = (fun x => li x && lj x) := by
                funext x; simp [P_S', hS'e, fnProd]
              rw [heq]; exact hasF2DegLe_mono hlij (by dsimp [D]; omega)
            | cons a as =>
              have hne' : S' ≠ [] := by rw [hS'e]; simp
              have hdegS' := hprod S' hne' hS'_lt
              exact hasF2DegLe_mono (hasF2DegLe_and hdegS' hlij) (by dsimp [D]; omega)
          -- Piece 2: `P_S' && (li && fnXor V)` = `fnXor (V.map (fun v => fun x => li x && (P_S' x && andFns[v] x)))`
          have hP2 : HasF2DegLe n (fun x => P_S' x && (li x && fnXor (V.map (fun v => andFns.getD v (fun _ => false))) x)) D := by
            have hterms : ∀ f ∈ V.map (fun v => fun x => li x && fnProd ((v :: S').map (fun u => andFns.getD u (fun _ => false))) x),
                HasF2DegLe n f D := by
              intro f hf
              rcases List.mem_map.mp hf with ⟨v, hvV, rfl⟩
              have hv_lt : v < t := hV v hvV
              have hdeg_vS := hprod (v :: S') (by simp) (fun u hu => by
                simp only [List.mem_cons] at hu
                rcases hu with rfl | hu'; exact hv_lt; exact hS'_lt u hu')
              have hdl : (dedupNat (v :: S')).length ≤ S'.length + 1 :=
                Nat.le_trans (dedupNat_cons_length_le v S') (by omega)
              exact hasF2DegLe_mono (hasF2DegLe_and hli hdeg_vS) (by dsimp [D]; omega)
            have hxor := hasF2DegLe_fnXor D _ hterms
            rcases hxor with ⟨ms, hmd, hme⟩
            refine ⟨ms, hmd, fun x => ?_⟩
            dsimp only
            rw [← hme x]
            have hdist : ∀ ls : List Nat,
                (P_S' x && (li x && fnXor (ls.map (fun v => andFns.getD v (fun _ => false))) x)) =
                fnXor (ls.map (fun v => fun y => li y && fnProd ((v :: S').map (fun u => andFns.getD u (fun _ => false))) y)) x := by
              intro ls; induction ls with
              | nil => simp [fnXor]
              | cons v vs ihv =>
                rw [List.map_cons, List.map_cons, fnXor_cons, fnXor_cons, ← ihv]
                dsimp only [P_S']
                rw [List.map_cons, fnProd_cons]
                cases fnProd (S'.map (fun u => andFns.getD u (fun _ => false))) x <;>
                  cases li x <;> cases andFns.getD v (fun _ => false) x <;>
                  cases fnXor (vs.map (fun u => andFns.getD u (fun _ => false))) x <;> rfl
            exact hdist V
          -- Piece 3: `P_S' && (lj && fnXor U)`
          have hP3 : HasF2DegLe n (fun x => P_S' x && (lj x && fnXor (U.map (fun u => andFns.getD u (fun _ => false))) x)) D := by
            have hterms : ∀ f ∈ U.map (fun u => fun x => lj x && fnProd ((u :: S').map (fun r => andFns.getD r (fun _ => false))) x),
                HasF2DegLe n f D := by
              intro f hf
              rcases List.mem_map.mp hf with ⟨u, huU, rfl⟩
              have hu_lt : u < t := hU u huU
              have hdeg_uS := hprod (u :: S') (by simp) (fun r hr => by
                simp only [List.mem_cons] at hr
                rcases hr with rfl | hr'; exact hu_lt; exact hS'_lt r hr')
              have hdl : (dedupNat (u :: S')).length ≤ S'.length + 1 :=
                Nat.le_trans (dedupNat_cons_length_le u S') (by omega)
              exact hasF2DegLe_mono (hasF2DegLe_and hlj hdeg_uS) (by dsimp [D]; omega)
            have hxor := hasF2DegLe_fnXor D _ hterms
            rcases hxor with ⟨ms, hmd, hme⟩
            refine ⟨ms, hmd, fun x => ?_⟩
            dsimp only
            rw [← hme x]
            have hdist : ∀ ls : List Nat,
                (P_S' x && (lj x && fnXor (ls.map (fun u => andFns.getD u (fun _ => false))) x)) =
                fnXor (ls.map (fun u => fun y => lj y && fnProd ((u :: S').map (fun r => andFns.getD r (fun _ => false))) y)) x := by
              intro ls; induction ls with
              | nil => simp [fnXor]
              | cons u us ihu =>
                rw [List.map_cons, List.map_cons, fnXor_cons, fnXor_cons, ← ihu]
                dsimp only [P_S']
                rw [List.map_cons, fnProd_cons]
                cases fnProd (S'.map (fun r => andFns.getD r (fun _ => false))) x <;>
                  cases lj x <;> cases andFns.getD u (fun _ => false) x <;>
                  cases fnXor (us.map (fun r => andFns.getD r (fun _ => false))) x <;> rfl
            exact hdist U
          -- Piece 4: `P_S' && (fnXor U && fnXor V)` = `fnXor` over pairs `(u, v) ∈ U × V` of `∏_{r ∈ u :: v :: S'} g_r`
          have hP4 : HasF2DegLe n (fun x =>
              P_S' x && (fnXor (U.map (fun u => andFns.getD u (fun _ => false))) x &&
                         fnXor (V.map (fun v => andFns.getD v (fun _ => false))) x)) D := by
            let pairFns := U.flatMap (fun u => V.map (fun v =>
              fun x => fnProd ((u :: v :: S').map (fun r => andFns.getD r (fun _ => false))) x))
            have hterms : ∀ f ∈ pairFns, HasF2DegLe n f D := by
              intro f hf
              simp only [pairFns, List.mem_flatMap, List.mem_map] at hf
              rcases hf with ⟨u, huU, v, hvV, rfl⟩
              have hu_lt : u < t := hU u huU
              have hv_lt : v < t := hV v hvV
              have hdeg_uvS := hprod (u :: v :: S') (by simp) (fun r hr => by
                simp only [List.mem_cons] at hr
                rcases hr with rfl | rfl | hr'
                · exact hu_lt
                · exact hv_lt
                · exact hS'_lt r hr')
              have hdl1 : (dedupNat (u :: v :: S')).length ≤ (dedupNat (v :: S')).length + 1 :=
                dedupNat_cons_length_le u (v :: S')
              have hdl2 : (dedupNat (v :: S')).length ≤ (dedupNat S').length + 1 :=
                dedupNat_cons_length_le v S'
              exact hasF2DegLe_mono hdeg_uvS (by dsimp [D]; omega)
            have hxor := hasF2DegLe_fnXor D pairFns hterms
            rcases hxor with ⟨ms, hmd, hme⟩
            refine ⟨ms, hmd, fun x => ?_⟩
            dsimp only
            rw [← hme x]
            have hfx_app : ∀ (a b : List ((Fin n → Bool) → Bool)),
                fnXor (a ++ b) x = xor (fnXor a x) (fnXor b x) := by
              intro a b; induction a with
              | nil => simp [fnXor]
              | cons q qs ihq =>
                rw [List.cons_append, fnXor_cons, fnXor_cons, ihq]
                cases q x <;> cases fnXor qs x <;> cases fnXor b x <;> rfl
            have hinner : ∀ (u : Nat) (lsV : List Nat),
                fnXor (lsV.map (fun v => fun y => fnProd ((u :: v :: S').map (fun r => andFns.getD r (fun _ => false))) y)) x =
                (P_S' x && (andFns.getD u (fun _ => false) x && fnXor (lsV.map (fun v => andFns.getD v (fun _ => false))) x)) := by
              intro u lsV
              induction lsV with
              | nil => simp [fnXor]
              | cons v vs ihv =>
                conv => lhs; rw [List.map_cons, fnXor_cons, ihv]
                conv => rhs; rw [List.map_cons, fnXor_cons]
                dsimp only [P_S']
                rw [List.map_cons, List.map_cons, fnProd_cons, fnProd_cons]
                cases fnProd (S'.map (fun r => andFns.getD r (fun _ => false))) x <;>
                  cases andFns.getD u (fun _ => false) x <;>
                  cases andFns.getD v (fun _ => false) x <;>
                  cases fnXor (vs.map (fun r => andFns.getD r (fun _ => false))) x <;> rfl
            have houter : ∀ lsU : List Nat,
                (P_S' x && (fnXor (lsU.map (fun u => andFns.getD u (fun _ => false))) x &&
                            fnXor (V.map (fun v => andFns.getD v (fun _ => false))) x)) =
                fnXor (lsU.flatMap (fun u => V.map (fun v =>
                  fun y => fnProd ((u :: v :: S').map (fun r => andFns.getD r (fun _ => false))) y))) x := by
              intro lsU
              induction lsU with
              | nil => simp [fnXor]
              | cons u us ihu =>
                have hfm : (u :: us).flatMap (fun a => V.map (fun v =>
                    fun y => fnProd ((a :: v :: S').map (fun r => andFns.getD r (fun _ => false))) y)) =
                  V.map (fun v => fun y => fnProd ((u :: v :: S').map (fun r => andFns.getD r (fun _ => false))) y) ++
                  us.flatMap (fun a => V.map (fun v =>
                    fun y => fnProd ((a :: v :: S').map (fun r => andFns.getD r (fun _ => false))) y)) := rfl
                rw [hfm, hfx_app, hinner u V, ← ihu]
                simp only [List.map_cons, fnXor_cons]
                cases P_S' x <;> cases andFns.getD u (fun _ => false) x <;>
                  cases fnXor (us.map (fun r => andFns.getD r (fun _ => false))) x <;>
                  cases fnXor (V.map (fun v => andFns.getD v (fun _ => false))) x <;> rfl
            exact houter U
          -- Combine all 4 pieces via XOR!
          have h12 := hasF2DegLe_xor hP1 hP2
          have h34 := hasF2DegLe_xor hP3 hP4
          have hall := hasF2DegLe_xor h12 h34
          simp only [Nat.max_self] at hall
          rcases hall with ⟨ms, hmd, hme⟩
          refine ⟨ms, fun m hm => by rw [hlen']; exact hmd m hm, fun x => ?_⟩
          rw [hsplit_fn x, ← hme x]
          dsimp only [gNew, P_S']
          rw [hevi x, hevj x]
          cases fnProd (S'.map (fun u => andFns.getD u (fun _ => false))) x <;>
            cases li x <;> cases lj x <;>
            cases fnXor (U.map (fun u => andFns.getD u (fun _ => false))) x <;>
            cases fnXor (V.map (fun v => andFns.getD v (fun _ => false))) x <;> rfl
        · -- Case 1: `t ∉ S`, so all `u ∈ S` satisfy `u < t`
          have hS_old : ∀ u ∈ S, u < t := by
            intro u hu
            have h1 := hSlt u hu
            have hne_t : u ≠ t := fun heq => ht_in (mem_dedupNat.mpr (heq ▸ hu))
            omega
          have hdeg_old := hprod S hSne hS_old
          have heq_fn : fnProd (S.map (fun u => andFns'.getD u (fun _ => false))) =
              fnProd (S.map (fun u => andFns.getD u (fun _ => false))) := by
            funext x
            have hmap : S.map (fun u => andFns'.getD u (fun _ => false)) =
                S.map (fun u => andFns.getD u (fun _ => false)) := by
              apply List.map_congr_left; intro u hu; exact hget_old u (hS_old u hu)
            rw [hmap]
          rw [heq_fn, hlen']
          exact hasF2DegLe_mono hdeg_old (by omega)

/-- Headline Theorem (Schnorr / Boyar–Peralta Multiplicative Complexity Degree Bound):
    Every output wire `w` of ANY `{1, XOR, AND}` circuit `gs` with `k = andCount gs`
    nonlinear AND gates computes a Boolean function of `F_2`-algebraic degree `≤ k + 1`. -/
public theorem mc_degree_lower_bound (n : Nat) (gs : List XorAndOp) (w : Nat) :
    HasF2DegLe n (fun x => (evalXorAndCircuit (vecToBits x) gs).getD w false) (andCount gs + 1) := by
  rcases xorAnd_deg_invariant n gs with ⟨andFns, handLen, hwire, hprod⟩
  rcases hwire w with ⟨lin, idxs, hld, hid, hev⟩
  have hlin' : HasF2DegLe n lin (andCount gs + 1) := hasF2DegLe_mono hld (by omega)
  have hterms : ∀ f ∈ idxs.map (fun i => andFns.getD i (fun _ => false)),
      HasF2DegLe n f (andCount gs + 1) := by
    intro f hf
    rcases List.mem_map.mp hf with ⟨i, hi, rfl⟩
    have hdeg1 := hprod [i] (by simp) (fun u hu => by simp at hu; rw [hu]; exact hid i hi)
    have hsingle : fnProd ([i].map (fun u => andFns.getD u (fun _ => false))) =
        andFns.getD i (fun _ => false) := by
      funext x; unfold fnProd; simp
    rw [hsingle] at hdeg1
    have hdl : (dedupNat [i]).length = 1 := rfl
    rw [hdl, handLen] at hdeg1
    exact hdeg1
  have hxor := hasF2DegLe_fnXor (andCount gs + 1) _ hterms
  have hcomb := hasF2DegLe_xor hlin' hxor
  rw [Nat.max_self] at hcomb
  rcases hcomb with ⟨ms, hmd, hme⟩
  exact ⟨ms, hmd, fun x => by dsimp only at hme ⊢; rw [hev x, ← hme x]⟩

/-- Full-space parity sum `⨁_{x ∈ {0,1}^n} f(x)` (equals the top-degree ANF coefficient of `f`). -/
private def paritySum {n : Nat} (f : (Fin n → Bool) → Bool) : Bool :=
  (allBitstrings n).foldl
    (fun acc bs => xor acc (f (fun i => bs.getD i.val false))) false

private theorem foldl_xor_init {α : Type} (xs : List α) (g : α → Bool) (init : Bool) :
    xs.foldl (fun acc x => xor acc (g x)) init =
    xor init (xs.foldl (fun acc x => xor acc (g x)) false) := by
  induction xs generalizing init with
  | nil => cases init <;> rfl
  | cons a as ih =>
    simp only [List.foldl_cons]
    rw [ih (xor init (g a)), ih (xor false (g a))]
    cases init <;> cases g a <;> cases (as.foldl (fun acc x => xor acc (g x)) false) <;> rfl

private theorem foldl_xor_append {α : Type} (xs ys : List α) (g : α → Bool) :
    (xs ++ ys).foldl (fun acc x => xor acc (g x)) false =
    xor (xs.foldl (fun acc x => xor acc (g x)) false)
        (ys.foldl (fun acc x => xor acc (g x)) false) := by
  rw [List.foldl_append, foldl_xor_init]

private theorem foldl_xor_linear {α : Type} (xs : List α) (g h : α → Bool) :
    xs.foldl (fun acc x => xor acc (xor (g x) (h x))) false =
    xor (xs.foldl (fun acc x => xor acc (g x)) false)
        (xs.foldl (fun acc x => xor acc (h x)) false) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldl_cons]
    rw [foldl_xor_init as (fun x => xor (g x) (h x)),
        foldl_xor_init as g, foldl_xor_init as h, ih]
    cases g a <;> cases h a <;>
      cases (as.foldl (fun acc x => xor acc (g x)) false) <;>
      cases (as.foldl (fun acc x => xor acc (h x)) false) <;> rfl

private theorem foldl_xor_false {α : Type} (xs : List α) (g : α → Bool)
    (h : ∀ x ∈ xs, g x = false) :
    xs.foldl (fun acc x => xor acc (g x)) false = false := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldl_cons, h a (by simp), Bool.xor_false]
    exact ih (fun x hx => h x (by simp [hx]))

private theorem paritySum_monomial_lt (n : Nat) :
    ∀ (m : List (Fin n)), m.length < n → paritySum (evalMonomial m) = false := by
  induction n with
  | zero => intro m hm; omega
  | succ n ih =>
    intro m hm
    unfold paritySum allBitstrings
    rw [foldl_xor_append, List.foldl_map, List.foldl_map]
    by_cases h0 : (⟨0, by omega⟩ : Fin (n + 1)) ∈ m
    · -- `x_0` appears in `m`, so `false :: bs` evaluates `m` to `false`!
      have hleft : (allBitstrings n).foldl (fun acc bs =>
          xor acc (evalMonomial m (fun i => (false :: bs).getD i.val false))) false = false := by
        apply foldl_xor_false
        intro bs _
        unfold evalMonomial
        cases hall : m.all (fun i => (false :: bs).getD i.val false)
        · rfl
        · have := List.all_eq_true.mp hall ⟨0, by omega⟩ h0
          simp at this
      -- On `true :: bs`, drop all occurrences of `0` from `m`; remaining monomial `m'` has length `< n`!
      let shiftDown : Fin (n + 1) → Option (Fin n)
        | ⟨0, _⟩ => none
        | ⟨k + 1, hk⟩ => some ⟨k, by omega⟩
      let m' : List (Fin n) := m.filterMap shiftDown
      have hm'_len : m'.length < n := by
        have hsd0 : ∀ h : 0 < n + 1, shiftDown ⟨0, h⟩ = none := fun _ => rfl
        have hsds : ∀ (k : Nat) (h : k + 1 < n + 1), shiftDown ⟨k + 1, h⟩ = some ⟨k, by omega⟩ := fun _ _ => rfl
        have hle : ∀ us : List (Fin (n + 1)), (us.filterMap shiftDown).length ≤ us.length := by
          intro us; induction us with
          | nil => exact Nat.le_refl 0
          | cons b bs ihu =>
            rcases b with ⟨bv, hbv⟩
            cases bv with
            | zero => rw [List.filterMap_cons, hsd0 hbv]; simp only [List.length_cons]; omega
            | succ k => rw [List.filterMap_cons, hsds k hbv]; simp only [List.length_cons]; omega
        have hdrop : ∀ (ls : List (Fin (n + 1))), (⟨0, by omega⟩ : Fin (n + 1)) ∈ ls →
            (ls.filterMap shiftDown).length < ls.length := by
          intro ls hmem
          induction ls with
          | nil => simp at hmem
          | cons a as ihl =>
            simp only [List.mem_cons] at hmem
            rcases hmem with rfl | hrest
            · rw [List.filterMap_cons, hsd0 (by omega)]
              have := hle as; simp only [List.length_cons]; omega
            · have := ihl hrest
              rcases a with ⟨av, hav⟩
              cases av with
              | zero => rw [List.filterMap_cons, hsd0 hav]; simp only [List.length_cons]; omega
              | succ k => rw [List.filterMap_cons, hsds k hav]; simp only [List.length_cons]; omega
        have := hdrop m h0
        dsimp only [m']; omega
      have hright_eq : ∀ bs : List Bool,
          evalMonomial m (fun i => (true :: bs).getD i.val false) =
          evalMonomial m' (fun j => bs.getD j.val false) := by
        intro bs
        have hgen : ∀ ls : List (Fin (n + 1)),
            evalMonomial ls (fun i => (true :: bs).getD i.val false) =
            evalMonomial (ls.filterMap shiftDown) (fun j => bs.getD j.val false) := by
          intro ls
          induction ls with
          | nil => rfl
          | cons a as iha =>
            unfold evalMonomial at iha ⊢
            rcases a with ⟨av, hav⟩
            cases av with
            | zero =>
              simp only [List.all_cons, List.filterMap_cons, shiftDown]
              have hget0 : (true :: bs).getD 0 false = true := rfl
              rw [hget0, Bool.true_and, iha]
            | succ k =>
              simp only [List.all_cons, List.filterMap_cons, shiftDown]
              have hgetk : (true :: bs).getD (k + 1) false = bs.getD k false := rfl
              rw [hgetk, iha]
        exact hgen m
      have hright : (allBitstrings n).foldl (fun acc bs =>
          xor acc (evalMonomial m (fun i => (true :: bs).getD i.val false))) false =
          paritySum (evalMonomial m') := by
        unfold paritySum
        congr 1; funext acc bs; rw [hright_eq bs]
      rw [hleft, hright, ih m' hm'_len]; rfl
    · -- `x_0 ∉ m`, so `evalMonomial m (false :: bs) = evalMonomial m (true :: bs)` and they cancel identically!
      have hsame : ∀ bs : List Bool,
          evalMonomial m (fun i => (false :: bs).getD i.val false) =
          evalMonomial m (fun i => (true :: bs).getD i.val false) := by
        intro bs
        have hgen : ∀ ls : List (Fin (n + 1)), (⟨0, by omega⟩ : Fin (n + 1)) ∉ ls →
            evalMonomial ls (fun i => (false :: bs).getD i.val false) =
            evalMonomial ls (fun i => (true :: bs).getD i.val false) := by
          intro ls hls
          induction ls with
          | nil => rfl
          | cons a as iha =>
            have hne : a.val ≠ 0 := by
              intro h
              have ha0 : (⟨0, by omega⟩ : Fin (n + 1)) = a := Fin.ext h.symm
              exact hls (ha0 ▸ List.mem_cons_self)
            have hrest : (⟨0, by omega⟩ : Fin (n + 1)) ∉ as :=
              fun h => hls (List.mem_cons_of_mem a h)
            unfold evalMonomial at iha ⊢
            simp only [List.all_cons, iha hrest]
            cases hv : a.val with
            | zero => exact absurd hv hne
            | succ k => rfl
        exact hgen m h0
      have heq :
          (allBitstrings n).foldl (fun acc bs => xor acc (evalMonomial m (fun i => (false :: bs).getD i.val false))) false =
          (allBitstrings n).foldl (fun acc bs => xor acc (evalMonomial m (fun i => (true :: bs).getD i.val false))) false := by
        congr 1; funext acc bs; rw [hsame bs]
      rw [heq]; cases ((allBitstrings n).foldl _ false) <;> rfl

private theorem paritySum_poly_lt {n : Nat} (ms : List (List (Fin n)))
    (hd : ∀ m ∈ ms, m.length < n) :
    paritySum (evalPolyF2 ms) = false := by
  induction ms with
  | nil =>
    unfold paritySum evalPolyF2
    exact foldl_xor_false _ _ (fun _ _ => rfl)
  | cons m ms ih =>
    have hcons : ∀ x, evalPolyF2 (m :: ms) x = xor (evalMonomial m x) (evalPolyF2 ms x) := by
      intro x
      have : m :: ms = [m] ++ ms := rfl
      rw [this, evalPolyF2_append]
      unfold evalPolyF2
      simp only [List.foldl_cons, List.foldl_nil]
      cases evalMonomial m x <;> rfl
    have heq : paritySum (evalPolyF2 (m :: ms)) = xor (paritySum (evalMonomial m)) (paritySum (evalPolyF2 ms)) := by
      unfold paritySum
      have hf : (fun (acc : Bool) (bs : List Bool) => xor acc (evalPolyF2 (m :: ms) (fun i => bs.getD i.val false))) =
          (fun (acc : Bool) (bs : List Bool) => xor acc (xor (evalMonomial m (fun i => bs.getD i.val false))
                                      (evalPolyF2 ms (fun i => bs.getD i.val false)))) := by
        funext acc bs; rw [hcons]
      rw [hf]
      exact foldl_xor_linear (allBitstrings n) _ _
    rw [heq, paritySum_monomial_lt n m (hd m (by simp)), ih (fun u hu => hd u (by simp [hu]))]
    rfl

private theorem paritySum_andN (n : Nat) : paritySum (andN n) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold paritySum allBitstrings
    rw [foldl_xor_append, List.foldl_map, List.foldl_map]
    have hleft : (allBitstrings n).foldl (fun acc bs =>
        xor acc (andN (n + 1) (fun i => (false :: bs).getD i.val false))) false = false := by
      apply foldl_xor_false
      intro bs _
      unfold andN
      cases hall : (List.finRange (n + 1)).all (fun i => (false :: bs).getD i.val false)
      · rfl
      · have := List.all_eq_true.mp hall ⟨0, by omega⟩ (List.mem_finRange _)
        simp at this
    have hright_eq : ∀ bs : List Bool,
        andN (n + 1) (fun i => (true :: bs).getD i.val false) =
        andN n (fun j => bs.getD j.val false) := by
      intro bs
      unfold andN
      rw [List.finRange_succ, List.all_cons, List.all_map]
      have h0 : (true :: bs).getD (0 : Fin (n + 1)).val false = true := rfl
      rw [h0, Bool.true_and]
      rfl
    have hright : (allBitstrings n).foldl (fun acc bs =>
        xor acc (andN (n + 1) (fun i => (true :: bs).getD i.val false))) false =
        paritySum (andN n) := by
      unfold paritySum
      congr 1; funext acc bs; rw [hright_eq bs]
    rw [hleft, hright, ih]; rfl

/-- Headline Theorem (Exact Multiplicative Complexity Lower Bound for `AND_n`):
    For every `n ≥ 1`, any `{1, XOR, AND}` circuit computing `AND_n` uses at least
    `n - 1` nonlinear AND gates (matching the exact `n - 1` chain upper bound). -/
public theorem mc_andN_lower (n : Nat) (hn : 1 ≤ n) (gs : List XorAndOp) (w : Nat)
    (hcomp : ∀ x : Fin n → Bool, (evalXorAndCircuit (vecToBits x) gs).getD w false = andN n x) :
    n - 1 ≤ andCount gs := by
  have hdeg := mc_degree_lower_bound n gs w
  rcases hdeg with ⟨ms, hmd, hme⟩
  have hpoly_eq : evalPolyF2 ms = andN n := by
    funext x; dsimp only at hme; rw [← hme x, hcomp x]
  by_cases hlt : andCount gs + 1 < n
  · exfalso
    have hall_lt : ∀ m ∈ ms, m.length < n := fun m hm => Nat.lt_of_le_of_lt (hmd m hm) hlt
    have hfalse := paritySum_poly_lt ms hall_lt
    rw [hpoly_eq, paritySum_andN n] at hfalse
    exact Bool.noConfusion hfalse
  · omega

-- ============================================================================
-- Proofs Part 3: Characteristic-2 Permanent/Determinant Collapse vs Separation
-- ============================================================================

private theorem foldl_add_mod2 {α : Type} (xs : List α) (f g : α → Int)
    (hfg : ∀ x ∈ xs, f x % 2 = g x % 2) :
    ∀ a b : Int, a % 2 = b % 2 →
      (xs.foldl (fun acc x => acc + f x) a) % 2 =
      (xs.foldl (fun acc x => acc + g x) b) % 2 := by
  induction xs with
  | nil => intro a b hab; exact hab
  | cons u us ih =>
    intro a b hab
    simp only [List.foldl_cons]
    apply ih (fun x hx => hfg x (by simp [hx]))
    have hu := hfg u (by simp)
    omega

/-- Headline Theorem (Characteristic-2 Permanent/Determinant Collapse):
    For EVERY dimension `n : Nat` and EVERY integer matrix `A : Fin n → Fin n → Int`,
    `permInt n A ≡ detInt n A (mod 2)` (explaining why `Perm_n` drops from `#P`-hard
    to `P` over characteristic 2). -/
public theorem perm_eq_det_mod2 :
    ∀ (n : Nat) (A : Fin n → Fin n → Int), permInt n A % 2 = detInt n A % 2 := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro A
    unfold permInt detInt
    apply foldl_add_mod2
    · intro c _
      have hminor := ih (minor0 A c)
      have ha := A ⟨0, by omega⟩ c
      have hp := permInt n (minor0 A c)
      have hd := detInt n (minor0 A c)
      -- Both `(+1) * a * d` and `(-1) * a * d` have the same parity as `a * p` when `p % 2 = d % 2`!
      have hmul_mod2 : (A ⟨0, by omega⟩ c * permInt n (minor0 A c)) % 2 =
          (A ⟨0, by omega⟩ c * detInt n (minor0 A c)) % 2 := by
        rw [Int.mul_emod, hminor, ← Int.mul_emod]
      by_cases heven : c.val % 2 = 0
      · simp only [heven, ↓reduceIte, Int.one_mul]
        exact hmul_mod2
      · simp only [heven, ↓reduceIte]
        have hneg : (-1 * A ⟨0, by omega⟩ c * detInt n (minor0 A c)) =
            -(A ⟨0, by omega⟩ c * detInt n (minor0 A c)) := by
          rw [Int.neg_mul, Int.one_mul, Int.neg_mul]
        rw [hneg]
        omega
    · rfl

private theorem foldl_sum_singleton_nonzero {α : Type} [DecidableEq α] (xs : List α)
    (f : α → Int) (target : α)
    (huniq : xs.count target = 1) (hzero : ∀ x ∈ xs, x ≠ target → f x = 0) :
    xs.foldl (fun acc x => acc + f x) 0 = f target := by
  have hgen : ∀ (ls : List α) (init : Int),
      (∀ x ∈ ls, x ≠ target → f x = 0) →
      ls.foldl (fun acc x => acc + f x) init = init + (ls.count target : Int) * f target := by
    intro ls
    induction ls with
    | nil => intro init _; simp
    | cons a as ih =>
      intro init hz
      simp only [List.foldl_cons]
      rw [ih (init + f a) (fun x hx => hz x (by simp [hx]))]
      by_cases ha : a = target
      · subst ha
        simp only [List.count_cons_self]
        have hcast : ((as.count a + 1 : Nat) : Int) = (as.count a : Int) + 1 := by omega
        rw [hcast, Int.add_mul, Int.one_mul]; omega
      · have hfa : f a = 0 := hz a (by simp) ha
        have hne : (a == target) = false := beq_false_of_ne ha
        simp only [List.count_cons, hne, Bool.false_eq_true, ↓reduceIte, hfa, Nat.add_zero]
        omega
  have := hgen xs 0 hzero
  rw [huniq] at this
  simpa using this

private theorem minor0_witnessMat_succ (k : Nat) :
    minor0 (witnessMat (k + 3)) ⟨0, by omega⟩ = witnessMat (k + 2) := by
  funext i j
  unfold minor0 witnessMat
  simp only [Nat.not_lt_zero, ↓reduceIte]
  by_cases h1 : k ≤ i.val ∧ k ≤ j.val
  · have h2a : k + 3 - 2 ≤ i.val + 1 := by omega
    have h2b : k + 3 - 2 ≤ j.val + 1 := by omega
    have h3a : k + 2 - 2 ≤ i.val := by omega
    have h3b : k + 2 - 2 ≤ j.val := by omega
    simp only [h2a, h2b, h3a, h3b, and_self, ↓reduceIte]
  · have h2 : ¬ (k + 3 - 2 ≤ i.val + 1 ∧ k + 3 - 2 ≤ j.val + 1) := by omega
    have h3 : ¬ (k + 2 - 2 ≤ i.val ∧ k + 2 - 2 ≤ j.val) := by omega
    simp only [h2, h3, ↓reduceIte]
    by_cases hij : i.val = j.val
    · simp only [hij, ↓reduceIte]
    · have hij1 : i.val + 1 ≠ j.val + 1 := by omega
      simp only [hij, hij1, ↓reduceIte]

private theorem count_eq_one_of_nodup_mem {α : Type} [DecidableEq α] {xs : List α} {a : α}
    (hnd : xs.Nodup) (hmem : a ∈ xs) : xs.count a = 1 := by
  induction xs with
  | nil => simp at hmem
  | cons b bs ih =>
    simp only [List.nodup_cons, List.mem_cons] at hnd hmem
    rcases hmem with rfl | hrest
    · have h0 : bs.count a = 0 := List.count_eq_zero.mpr hnd.1
      simp [List.count_cons_self, h0]
    · have hne : b ≠ a := fun h => hnd.1 (h ▸ hrest)
      have hb : (b == a) = false := beq_false_of_ne hne
      simp [List.count_cons, hb, ih hnd.2 hrest]

private theorem finRange_count_one {n : Nat} (a : Fin n) :
    (List.finRange n).count a = 1 :=
  count_eq_one_of_nodup_mem (List.nodup_finRange n) (List.mem_finRange a)

/-- Headline Theorem (Permanent vs Determinant Separation over `ℤ` and `𝔽_p` for `p ≥ 3`):
    For EVERY dimension `n ≥ 2`, the explicit `{0,1}`-matrix `W_n = diag(I_{n-2}, J_2)`
    satisfies `permInt n W_n = 2` and `detInt n W_n = 0`. Hence `Perm_n ≠ det_n` over `ℤ`
    and modulo EVERY modulus `p ≥ 3` (including `𝔽_3`), showing why Valiant's algebraic
    hardness breaks down exclusively in characteristic 2. -/
public theorem perm_ne_det_witness (n : Nat) (hn : 2 ≤ n) :
    permInt n (witnessMat n) = 2 ∧
    detInt n (witnessMat n) = 0 ∧
    (∀ p : Int, 3 ≤ p → permInt n (witnessMat n) % p ≠ detInt n (witnessMat n) % p) := by
  have hcore : ∀ k : Nat, permInt (k + 2) (witnessMat (k + 2)) = 2 ∧
      detInt (k + 2) (witnessMat (k + 2)) = 0 := by
    intro k
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
      constructor
      · unfold permInt
        have hsum := foldl_sum_singleton_nonzero (List.finRange (k + 3))
          (fun c => witnessMat (k + 3) ⟨0, by omega⟩ c * permInt (k + 2) (minor0 (witnessMat (k + 3)) c))
          ⟨0, by omega⟩ (finRange_count_one _) (fun c _ hne => by
            have hcv : c.val ≠ 0 := fun hv => hne (Fin.ext hv)
            unfold witnessMat
            have hn1 : ¬ (k + 3 - 2 ≤ 0 ∧ k + 3 - 2 ≤ c.val) := by omega
            have hn2 : (0 : Nat) ≠ c.val := Ne.symm hcv
            simp only [hn1, hn2, ↓reduceIte, Int.zero_mul])
        rw [hsum, minor0_witnessMat_succ k, ih.1]
        have hw00 : witnessMat (k + 3) ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
          unfold witnessMat; simp
        rw [hw00]; rfl
      · unfold detInt
        have hsum := foldl_sum_singleton_nonzero (List.finRange (k + 3))
          (fun c => (if c.val % 2 = 0 then (1 : Int) else -1) *
            witnessMat (k + 3) ⟨0, by omega⟩ c * detInt (k + 2) (minor0 (witnessMat (k + 3)) c))
          ⟨0, by omega⟩ (finRange_count_one _) (fun c _ hne => by
            have hcv : c.val ≠ 0 := fun hv => hne (Fin.ext hv)
            unfold witnessMat
            have hn1 : ¬ (k + 3 - 2 ≤ 0 ∧ k + 3 - 2 ≤ c.val) := by omega
            have hn2 : (0 : Nat) ≠ c.val := Ne.symm hcv
            simp only [hn1, hn2, ↓reduceIte, Int.mul_zero, Int.zero_mul])
        rw [hsum, minor0_witnessMat_succ k, ih.2]
        simp
  have hkeq : n = (n - 2) + 2 := by omega
  rw [hkeq]
  have ⟨hp, hd⟩ := hcore (n - 2)
  refine ⟨hp, hd, fun p hp3 => ?_⟩
  rw [hp, hd]
  have h2mod : (2 : Int) % p = 2 := Int.emod_eq_of_lt (by omega) (by omega)
  have h0mod : (0 : Int) % p = 0 := Int.zero_emod p
  rw [h2mod, h0mod]
  omega

end PVsNP

