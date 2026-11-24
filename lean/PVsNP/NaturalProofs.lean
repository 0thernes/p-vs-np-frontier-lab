module

public import PVsNP.Basic

/-!
# Razborov–Rudich Natural Proofs Barrier (1997)

Exact-integer formalization of finite combinatorial properties over Boolean
truth tables of length `2^n`, largeness, usefulness against a function class,
pseudorandom function (PRF) distinguishing advantage, the finite hybrid
telescoping lemma, and a non-vacuous explicit property (`nonConstantProp`)
with exact count `2^(2^n) - 2` (density `≥ 1/2` for every `n ≥ 1`).

All probability bounds are expressed as cross-multiplied integer inequalities
with zero floating-point arithmetic.
-/

namespace PVsNP

@[expose] public section

/-- A combinatorial property of `n`-variable Boolean functions, given as a
    Boolean predicate on truth tables of length `2^n`. -/
abbrev CombProperty := List Bool → Bool

/-- Number of `n`-variable truth tables accepted by `C`. -/
def propCount (C : CombProperty) (n : Nat) : Nat :=
  ((allBitstrings (2 ^ n)).filter C).length

/-- Exact integer largeness: `Pr_{f ~ U_n}[C(f) = 1] ≥ numer / denom`. -/
def IsLarge (C : CombProperty) (n numer denom : Nat) : Prop :=
  0 < denom ∧ numer * 2 ^ (2 ^ n) ≤ denom * propCount C n

/-- Usefulness against a class `F` of `n`-variable truth tables: every truth
    table in `F` is rejected by `C`. -/
def IsUsefulAgainst (C : CombProperty) (n : Nat) (F : List Bool → Prop) : Prop :=
  ∀ tt : List Bool, tt.length = 2 ^ n → F tt → C tt = false

/-- A finite keyed pseudorandom function family mapping `k`-bit keys to
    `n`-variable Boolean truth tables of length `2^n`. -/
structure PRFFamily (n k : Nat) where
  eval : List Bool → List Bool
  eval_len : ∀ key : List Bool, key.length = k → (eval key).length = 2 ^ n

/-- Number of `k`-bit keys on which distinguisher `D` accepts the PRF output. -/
def prfCount {n k : Nat} (P : PRFFamily n k) (D : CombProperty) : Nat :=
  ((allBitstrings k).filter (fun key => D (P.eval key))).length

/-- Exact integer distinguishing advantage:
    `|Pr[D(U_n) = 1] - Pr[D(P_k) = 1]| ≥ numer / denom`. -/
def BreaksPRFWithAdv {n k : Nat} (P : PRFFamily n k) (D : CombProperty)
    (numer denom : Nat) : Prop :=
  0 < denom ∧
  numer * (2 ^ (2 ^ n) * 2 ^ k) ≤
    Int.natAbs ((propCount D n * 2 ^ k : Int) - (prfCount P D * 2 ^ (2 ^ n) : Int)) * denom

/-- A truth table is constant if all its entries are equal. -/
def IsConstantTT (tt : List Bool) : Prop :=
  ∃ b : Bool, tt = List.replicate tt.length b

/-- Explicit combinatorial property accepting all non-constant truth tables. -/
def nonConstantProp (tt : List Bool) : Bool :=
  tt.any (fun b => b != tt.headD false)

end

private theorem filter_eq_nil_of_forall_false {α : Type} (xs : List α) (p : α → Bool)
    (h : ∀ x ∈ xs, p x = false) : xs.filter p = [] := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    have ha : p a = false := h a (by simp)
    simp only [List.filter_cons, ha]
    exact ih (fun x hx => h x (by simp [hx]))

/-- If every keyed function in `P` lies in `F` and `C` is useful against `F`,
    then `C` rejects every key of `P`. -/
public theorem prfCount_eq_zero_of_useful {n k : Nat} (P : PRFFamily n k)
    (C : CombProperty) (F : List Bool → Prop)
    (hUse : IsUsefulAgainst C n F)
    (hInF : ∀ key : List Bool, key.length = k → F (P.eval key)) :
    prfCount P C = 0 := by
  unfold prfCount
  have hnil : (allBitstrings k).filter (fun key => C (P.eval key)) = [] := by
    apply filter_eq_nil_of_forall_false
    intro key hmem
    have hlen : key.length = k := (mem_allBitstrings_iff k key).mp hmem
    exact hUse (P.eval key) (P.eval_len key hlen) (hInF key hlen)
  rw [hnil]
  rfl

/-- Headline Theorem (Razborov–Rudich 1997, Natural Proofs Break PRFs):
    Any combinatorial property `C` that is large (density `≥ numer / denom`) and
    useful against a class `F` containing all functions of a PRF family `P`
    distinguishes `P` from a uniformly random function with advantage at least
    `numer / denom` (exact cross-multiplied integer bound). -/
public theorem natural_proof_breaks_prf {n k numer denom : Nat}
    (P : PRFFamily n k) (C : CombProperty) (F : List Bool → Prop)
    (hLarge : IsLarge C n numer denom)
    (hUse : IsUsefulAgainst C n F)
    (hInF : ∀ key : List Bool, key.length = k → F (P.eval key)) :
    prfCount P C = 0 ∧ BreaksPRFWithAdv P C numer denom := by
  have hzero : prfCount P C = 0 := prfCount_eq_zero_of_useful P C F hUse hInF
  refine ⟨hzero, hLarge.1, ?_⟩
  rw [hzero]
  simp only [Int.natCast_zero, Int.zero_mul, Int.sub_zero]
  have hnonneg : Int.natAbs ((propCount C n : Int) * (2 ^ k : Int)) = propCount C n * 2 ^ k := by
    have hcast : ((propCount C n * 2 ^ k : Nat) : Int) = (propCount C n : Int) * (2 ^ k : Int) :=
      Int.natCast_mul (propCount C n) (2 ^ k)
    rw [← hcast, Int.natAbs_natCast]
  rw [hnonneg]
  have hL : numer * 2 ^ (2 ^ n) ≤ denom * propCount C n := hLarge.2
  have hmul : numer * 2 ^ (2 ^ n) * 2 ^ k ≤ denom * propCount C n * 2 ^ k :=
    Nat.mul_le_mul_right (2 ^ k) hL
  have h1 : numer * (2 ^ (2 ^ n) * 2 ^ k) = numer * 2 ^ (2 ^ n) * 2 ^ k := by
    rw [Nat.mul_assoc]
  have h2 : denom * propCount C n * 2 ^ k = propCount C n * 2 ^ k * denom := by
    rw [Nat.mul_comm denom (propCount C n), Nat.mul_right_comm]
  rw [h1, ← h2]
  exact hmul

private theorem natAbs_sub_triangle (x y z : Int) :
    Int.natAbs (x - z) ≤ Int.natAbs (x - y) + Int.natAbs (y - z) := by
  have h : x - z = (x - y) + (y - z) := by omega
  rw [h]
  exact Int.natAbs_add_le (x - y) (y - z)

/-- Headline Theorem (Finite Hybrid Telescoping Lemma):
    If the distinguishing gap between hybrid `0` and hybrid `m` strictly exceeds
    `m * B`, then some adjacent pair `(i, i + 1)` with `i < m` has gap strictly
    exceeding `B`. Used in the GGM reduction from PRGs to PRFs. -/
public theorem hybrid_telescoping_bound :
    ∀ (m B : Nat) (a : Nat → Int),
      m * B < Int.natAbs (a 0 - a m) →
      ∃ i : Nat, i < m ∧ B < Int.natAbs (a i - a (i + 1)) := by
  intro m
  induction m with
  | zero =>
    intro B a h
    simp only [Nat.zero_mul, Int.sub_self, Int.natAbs_zero] at h
    omega
  | succ m ih =>
    intro B a h
    have htri := natAbs_sub_triangle (a 0) (a m) (a (m + 1))
    by_cases hlast : B < Int.natAbs (a m - a (m + 1))
    · exact ⟨m, Nat.lt_succ_self m, hlast⟩
    · have hprev : m * B < Int.natAbs (a 0 - a m) := by
        have hsm : (m + 1) * B = m * B + B := Nat.succ_mul m B
        omega
      rcases ih B a hprev with ⟨i, hi, hgap⟩
      exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self m), hgap⟩

-- ============================================================================
-- Non-Vacuity: Exact Count & Largeness of `nonConstantProp` for All `n ≥ 1`
-- ============================================================================

private theorem all_eq_true_iff (xs : List Bool) (c : Bool) :
    xs.all (fun b => b == c) = true ↔ xs = List.replicate xs.length c := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq, List.length_cons, List.replicate_succ]
    constructor
    · rintro ⟨rfl, htail⟩
      exact congrArg (a :: ·) (ih.mp htail)
    · intro heq
      injection heq with h1 h2
      exact ⟨h1, ih.mpr h2⟩

private theorem nonConstantProp_false_iff (xs : List Bool) :
    nonConstantProp xs = false ↔ IsConstantTT xs := by
  unfold nonConstantProp IsConstantTT
  cases xs with
  | nil =>
    exact ⟨fun _ => ⟨false, rfl⟩, fun _ => rfl⟩
  | cons a as =>
    simp only [List.headD_cons, List.any_cons, bne_self_eq_false, Bool.false_or,
               List.length_cons, List.replicate_succ]
    constructor
    · intro h
      refine ⟨a, ?_⟩
      congr 1
      have hall : as.all (fun b => b == a) = true := by
        induction as with
        | nil => rfl
        | cons x xs' ih =>
          simp only [List.any_cons, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at h
          simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq]
          exact ⟨h.1, ih h.2⟩
      exact (all_eq_true_iff as a).mp hall
    · rintro ⟨b, heq⟩
      injection heq with h1 h2
      subst h1
      rw [h2]
      clear h2
      induction as.length with
      | zero => rfl
      | succ k ih =>
        simp only [List.replicate_succ, List.any_cons, bne_self_eq_false, Bool.false_or]
        exact ih

private theorem filter_partition_length {α : Type} (xs : List α) (p : α → Bool) :
    (xs.filter p).length + (xs.filter (fun x => !p x)).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    cases hp : p a <;> simp [hp] <;> omega

private theorem filter_eq_replicate_count (m : Nat) (b : Bool) :
    ((allBitstrings m).filter (fun w => decide (w = List.replicate m b))).length = 1 := by
  induction m with
  | zero =>
    simp [allBitstrings]
  | succ m ih =>
    unfold allBitstrings
    rw [List.filter_append, List.length_append, List.filter_map, List.filter_map,
        List.length_map, List.length_map]
    cases b
    · have h1 : (allBitstrings m).filter (fun x => decide (false :: x = List.replicate (m + 1) false)) =
          (allBitstrings m).filter (fun x => decide (x = List.replicate m false)) := by
        congr 1; funext x; simp [List.replicate_succ]
      have h2 : (allBitstrings m).filter (fun x => decide (true :: x = List.replicate (m + 1) false)) = [] := by
        apply filter_eq_nil_of_forall_false
        intro x _
        simp [List.replicate_succ]
      change ((allBitstrings m).filter (fun x => decide (false :: x = List.replicate (m + 1) false))).length +
             ((allBitstrings m).filter (fun x => decide (true :: x = List.replicate (m + 1) false))).length = 1
      rw [h1, h2, ih]
      rfl
    · have h1 : (allBitstrings m).filter (fun x => decide (false :: x = List.replicate (m + 1) true)) = [] := by
        apply filter_eq_nil_of_forall_false
        intro x _
        simp [List.replicate_succ]
      have h2 : (allBitstrings m).filter (fun x => decide (true :: x = List.replicate (m + 1) true)) =
          (allBitstrings m).filter (fun x => decide (x = List.replicate m true)) := by
        congr 1; funext x; simp [List.replicate_succ]
      change ((allBitstrings m).filter (fun x => decide (false :: x = List.replicate (m + 1) true))).length +
             ((allBitstrings m).filter (fun x => decide (true :: x = List.replicate (m + 1) true))).length = 1
      rw [h1, h2, ih]
      rfl

private theorem filter_or_disjoint_length {α : Type} (xs : List α) (p q : α → Bool)
    (hdisj : ∀ x ∈ xs, !(p x && q x) = true) :
    (xs.filter (fun x => p x || q x)).length = (xs.filter p).length + (xs.filter q).length := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    have ha := hdisj a (by simp)
    have hrest := ih (fun x hx => hdisj x (by simp [hx]))
    cases hp : p a <;> cases hq : q a
    · simp [hp, hq, hrest]
    · simp [hp, hq, hrest]; omega
    · simp [hp, hq, hrest]; omega
    · simp [hp, hq] at ha

/-- Exact count of non-constant truth tables on `n` variables: `2^(2^n) - 2`. -/
public theorem nonConstantProp_count (n : Nat) :
    propCount nonConstantProp n + 2 = 2 ^ (2 ^ n) := by
  unfold propCount
  have hpart := filter_partition_length (allBitstrings (2 ^ n)) nonConstantProp
  rw [allBitstrings_length] at hpart
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hconst_eq :
      (allBitstrings (2 ^ n)).filter (fun w => !nonConstantProp w) =
      (allBitstrings (2 ^ n)).filter
        (fun w => decide (w = List.replicate (2 ^ n) false) ||
                  decide (w = List.replicate (2 ^ n) true)) := by
    have hcongr : ∀ xs : List (List Bool),
        (∀ w ∈ xs, w.length = 2 ^ n) →
        xs.filter (fun w => !nonConstantProp w) =
        xs.filter (fun w => decide (w = List.replicate (2 ^ n) false) ||
                            decide (w = List.replicate (2 ^ n) true)) := by
      intro xs hxs
      induction xs with
      | nil => rfl
      | cons w ws ih =>
        have hwlen : w.length = 2 ^ n := hxs w (by simp)
        have hpred : (!nonConstantProp w) =
            (decide (w = List.replicate (2 ^ n) false) ||
             decide (w = List.replicate (2 ^ n) true)) := by
          cases hnc : nonConstantProp w
          · have ⟨b, hb⟩ := (nonConstantProp_false_iff w).mp hnc
            rw [hwlen] at hb
            cases b <;> simp [hb]
          · have hnot : ¬ IsConstantTT w := by
              intro hc
              have := (nonConstantProp_false_iff w).mpr hc
              rw [hnc] at this
              exact Bool.noConfusion this
            have hf : w ≠ List.replicate (2 ^ n) false := fun heq =>
              hnot ⟨false, by rw [hwlen]; exact heq⟩
            have ht : w ≠ List.replicate (2 ^ n) true := fun heq =>
              hnot ⟨true, by rw [hwlen]; exact heq⟩
            simp [hf, ht]
        simp only [List.filter_cons, hpred]
        rw [ih (fun u hu => hxs u (by simp [hu]))]
    exact hcongr (allBitstrings (2 ^ n)) (fun w hw => (mem_allBitstrings_iff (2 ^ n) w).mp hw)
  have hdisj : ∀ w ∈ allBitstrings (2 ^ n),
      !(decide (w = List.replicate (2 ^ n) false) &&
        decide (w = List.replicate (2 ^ n) true)) = true := by
    intro w _
    by_cases hf : w = List.replicate (2 ^ n) false
    · have hne : List.replicate (2 ^ n) false ≠ List.replicate (2 ^ n) true := by
        intro heq
        cases hm : 2 ^ n with
        | zero => omega
        | succ k =>
          rw [hm, List.replicate_succ, List.replicate_succ] at heq
          injection heq with h0 _
          exact Bool.noConfusion h0
      simp [hf, hne]
    · simp [hf]
  have hlen_const : ((allBitstrings (2 ^ n)).filter (fun w => !nonConstantProp w)).length = 2 := by
    rw [hconst_eq, filter_or_disjoint_length _ _ _ hdisj,
        filter_eq_replicate_count (2 ^ n) false,
        filter_eq_replicate_count (2 ^ n) true]
  omega

/-- Non-Vacuity Theorem: For every `n ≥ 1`, `nonConstantProp` is both
    large (density `≥ 1/2`) and useful against all constant functions. -/
public theorem natural_proof_nonvacuous (n : Nat) (hn : 1 ≤ n) :
    IsLarge nonConstantProp n 1 2 ∧ IsUsefulAgainst nonConstantProp n IsConstantTT := by
  refine ⟨⟨by omega, ?_⟩, ?_⟩
  · have hcnt := nonConstantProp_count n
    have hpow2 : 2 ≤ 2 ^ n := by
      have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
      simpa using this
    have h4 : 4 ≤ 2 ^ (2 ^ n) := by
      have : 2 ^ 2 ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by omega) hpow2
      simpa using this
    omega
  · intro tt _ hconst
    exact (nonConstantProp_false_iff tt).mpr hconst

end PVsNP
