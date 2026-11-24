/-
  SPDX-License-Identifier: Apache-2.0
  Copyright (c) 2026 Alexander S. Donahue (independent researcher, ORCID 0009-0006-8168-9648)

  PVsNP/Basic.lean
  Zero-dependency foundational helpers: exact finite lists of bitstrings,
  constructive pigeonhole on {0,1}^n, deterministic polynomial-vs-exponential bounds,
  and constructive bijective Cantor pairing on Nat.
-/
module

namespace PVsNP

/-- All bitstrings of length `n`, in canonical lexicographic order. -/
@[expose] public def allBitstrings : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    let rest := allBitstrings n
    rest.map (false :: ·) ++ rest.map (true :: ·)

public theorem allBitstrings_length (n : Nat) :
    (allBitstrings n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [allBitstrings, List.length_append, List.length_map, ih, Nat.pow_succ, Nat.mul_two]

public theorem mem_allBitstrings_iff (n : Nat) (w : List Bool) :
    w ∈ allBitstrings n ↔ w.length = n := by
  induction n generalizing w with
  | zero =>
    cases w with
    | nil => simp [allBitstrings]
    | cons b bs => simp [allBitstrings]
  | succ n ih =>
    cases w with
    | nil => simp [allBitstrings]
    | cons b bs =>
      cases b <;> simp [allBitstrings, ih]

private theorem nodup_map_of_inj {α β : Type} {f : α → β}
    (hf : ∀ x y, f x = f y → x = y) :
    ∀ {xs : List α}, xs.Nodup → (xs.map f).Nodup
  | [], _ => List.nodup_nil
  | a :: as, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj hf hnd.2⟩
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨b, hb, hfb⟩
    exact hnd.1 (hf b a hfb ▸ hb)

public theorem allBitstrings_nodup (n : Nat) :
    (allBitstrings n).Nodup := by
  induction n with
  | zero => simp [allBitstrings]
  | succ n ih =>
    simp only [allBitstrings]
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact nodup_map_of_inj (fun _ _ h => (List.cons.inj h).2) ih
    · exact nodup_map_of_inj (fun _ _ h => (List.cons.inj h).2) ih
    · intro x hx y hy hxy
      rw [List.mem_map] at hx hy
      rcases hx with ⟨a, _, rfl⟩
      rcases hy with ⟨b, _, rfl⟩
      cases hxy

/-- Pigeonhole on nodup lists: if `xs.Nodup` and `ys.length < xs.length`,
    some element of `xs` is not in `ys`. -/
public theorem exists_not_mem_of_length_lt {α : Type} [DecidableEq α]
    (xs ys : List α) (hnd : xs.Nodup) (hlt : ys.length < xs.length) :
    ∃ x ∈ xs, x ∉ ys := by
  induction xs generalizing ys with
  | nil => simp at hlt
  | cons a as ih =>
    rw [List.nodup_cons] at hnd
    by_cases ha : a ∈ ys
    · have hsub : (ys.erase a).length + 1 = ys.length := by
        rw [List.length_erase_of_mem ha]
        have hpos : 0 < ys.length := List.length_pos_of_mem ha
        omega
      have hlt' : (ys.erase a).length < as.length := by
        simp only [List.length_cons] at hlt
        omega
      rcases ih (ys.erase a) hnd.2 hlt' with ⟨x, hmem, hnot⟩
      refine ⟨x, List.mem_cons_of_mem a hmem, ?_⟩
      intro hxin
      have hne : x ≠ a := fun heq => hnd.1 (heq ▸ hmem)
      exact hnot ((List.mem_erase_of_ne hne).mpr hxin)
    · exact ⟨a, List.mem_cons_self, ha⟩

/-- Constructive finder: returns the first element of `xs` not in `ys`. -/
public def findNotMem {α : Type} [BEq α] (xs ys : List α) : Option α :=
  xs.find? (fun x => !ys.contains x)

public theorem findNotMem_some_of_length_lt {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
    (xs ys : List α) (hnd : xs.Nodup) (hlt : ys.length < xs.length) :
    ∃ x, findNotMem xs ys = some x ∧ x ∈ xs ∧ x ∉ ys := by
  rcases exists_not_mem_of_length_lt xs ys hnd hlt with ⟨w, hwxs, hwys⟩
  have hex : ∃ x ∈ xs, (!ys.contains x) = true := by
    refine ⟨w, hwxs, ?_⟩
    simp [hwys]
  have hne : findNotMem xs ys ≠ none := by
    intro hnone
    unfold findNotMem at hnone
    rw [List.find?_eq_none] at hnone
    rcases hex with ⟨x, hx, hpx⟩
    exact absurd hpx (hnone x hx)
  cases hfind : findNotMem xs ys with
  | none => exact absurd hfind hne
  | some x =>
    unfold findNotMem at hfind
    have hmem := List.mem_of_find?_eq_some hfind
    have hp := List.find?_some hfind
    refine ⟨x, rfl, hmem, ?_⟩
    simp at hp
    exact hp

/-- Corollary: constructive unqueried bitstring finder on `{0,1}^n`. -/
public def findUnqueried (n : Nat) (Q : List (List Bool)) : List Bool :=
  (findNotMem (allBitstrings n) Q).getD (List.replicate n false)

public theorem findUnqueried_spec (n : Nat) (Q : List (List Bool)) (hlt : Q.length < 2 ^ n) :
    (findUnqueried n Q).length = n ∧ findUnqueried n Q ∉ Q := by
  have hlt' : Q.length < (allBitstrings n).length := by
    rw [allBitstrings_length]; exact hlt
  rcases findNotMem_some_of_length_lt (allBitstrings n) Q (allBitstrings_nodup n) hlt' with
    ⟨x, hfind, hmem, hnot⟩
  unfold findUnqueried
  rw [hfind]
  exact ⟨(mem_allBitstrings_iff n x).mp hmem, hnot⟩

/-- Elementary bound: `k + 1 ≤ 2^k` for all `k`. -/
public theorem succ_le_two_pow (k : Nat) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_two]
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

/-- Elementary square-vs-exponential bound: `m * m ≤ 2^m` for `m ≥ 4`. -/
public theorem sq_le_two_pow (m : Nat) (hm : 4 ≤ m) : m * m ≤ 2 ^ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm4 : m < 4
    · have hm3 : m = 3 := by omega
      subst hm3; decide
    · have ih' := ih (by omega)
      rw [Nat.pow_succ, Nat.mul_two]
      have hlin : 2 * m + 1 ≤ m * m := by
        have : 4 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
        omega
      have hexp : (m + 1) * (m + 1) = m * m + (2 * m + 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
        omega
      omega

/-- Deterministic stage length `diagLength c M` strictly exceeding `M`
    and satisfying `(n + 1)^c + c < 2^n`. -/
public def diagLength (c M : Nat) : Nat :=
  (c + 1) * max (M + 1) (c + 4)

public theorem diagLength_gt (c M : Nat) : M < diagLength c M := by
  unfold diagLength
  have hkM : M + 1 ≤ max (M + 1) (c + 4) := Nat.le_max_left (M + 1) (c + 4)
  have h1 : 1 * max (M + 1) (c + 4) ≤ (c + 1) * max (M + 1) (c + 4) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

public theorem diagLength_exp_gt_poly (c M : Nat) :
    (diagLength c M + 1) ^ c + c < 2 ^ (diagLength c M) := by
  unfold diagLength
  let k := max (M + 1) (c + 4)
  show ((c + 1) * k + 1) ^ c + c < 2 ^ ((c + 1) * k)
  have hkc : c + 4 ≤ k := Nat.le_max_right (M + 1) (c + 4)
  have hn1_le : (c + 1) * k + 1 ≤ 2 ^ k := by
    have h2 : (c + 2) * k ≤ k * k := Nat.mul_le_mul_right k (by omega)
    have h3 : (c + 2) * k = (c + 1) * k + k := Nat.succ_mul (c + 1) k
    have h1 : (c + 1) * k + 1 ≤ k * k := by omega
    exact Nat.le_trans h1 (sq_le_two_pow k (by omega))
  have hpow_le : ((c + 1) * k + 1) ^ c ≤ (2 ^ k) ^ c := Nat.pow_le_pow_left hn1_le c
  rw [← Nat.pow_mul] at hpow_le
  have h2n : 2 ^ ((c + 1) * k) = 2 ^ (k * c) * 2 ^ k := by
    have hmul : (c + 1) * k = k * c + k := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    rw [hmul, Nat.pow_add]
  have h2k_ge : c + 2 ≤ 2 ^ k := by
    have := succ_le_two_pow k
    omega
  have hpos : 1 ≤ 2 ^ (k * c) := Nat.one_le_two_pow
  have hstep1 : 2 ^ (k * c) * (c + 2) ≤ 2 ^ ((c + 1) * k) := by
    rw [h2n]
    exact Nat.mul_le_mul_left (2 ^ (k * c)) h2k_ge
  have hmul2 : 2 ^ (k * c) * (c + 2) = 2 ^ (k * c) + 2 ^ (k * c) * (c + 1) := by
    have h1 : c + 2 = 1 + (c + 1) := by omega
    rw [h1, Nat.mul_add, Nat.mul_one]
  have hc_lt : c < 2 ^ (k * c) * (c + 1) := by
    have : 1 * (c + 1) ≤ 2 ^ (k * c) * (c + 1) := Nat.mul_le_mul_right (c + 1) hpos
    omega
  omega

/-- Triangular number helper: `(s + 1) * (s + 2) / 2 = s * (s + 1) / 2 + (s + 1)`. -/
private theorem tri_succ (s : Nat) :
    (s + 1) * (s + 2) / 2 = s * (s + 1) / 2 + (s + 1) := by
  have h1 : (s + 1) * (s + 2) = s * (s + 1) + 2 * (s + 1) := by
    rw [Nat.mul_comm (s + 1) (s + 2), Nat.add_mul, Nat.mul_comm s (s + 1)]
  rw [h1, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]

/-- Standard Cantor pairing and unpairing on `Nat`, bijective and constructive. -/
public def pairNat (a b : Nat) : Nat :=
  (a + b) * (a + b + 1) / 2 + b

/-- Bounded search unpairing: exact left inverse of `pairNat`. -/
public def unpairAux : Nat → Nat → Nat → Nat × Nat
  | 0, s, rem => (s - rem, rem)
  | fuel + 1, s, rem =>
    if rem ≤ s then (s - rem, rem)
    else unpairAux fuel (s + 1) (rem - (s + 1))

public def unpairNat (k : Nat) : Nat × Nat :=
  unpairAux k 0 k

private theorem unpairAux_spec (fuel s rem : Nat) (hfuel : rem ≤ fuel) :
    let p := unpairAux fuel s rem
    (p.1 + p.2) * (p.1 + p.2 + 1) / 2 + p.2 = s * (s + 1) / 2 + rem := by
  induction fuel generalizing s rem with
  | zero =>
    have hrem : rem = 0 := by omega
    subst hrem
    simp [unpairAux]
  | succ fuel ih =>
    unfold unpairAux
    by_cases h : rem ≤ s
    · simp only [h, ↓reduceIte]
      have hadd : s - rem + rem = s := by omega
      rw [hadd]
    · simp only [h, ↓reduceIte]
      have hfuel' : rem - (s + 1) ≤ fuel := by omega
      have hrec := ih (s + 1) (rem - (s + 1)) hfuel'
      have htri := tri_succ s
      have hsub : (s + 1) + (rem - (s + 1)) = rem := by omega
      have hcomb : (s + 1) * (s + 1 + 1) / 2 + (rem - (s + 1)) = s * (s + 1) / 2 + rem := by
        have hstep : (s + 1) * (s + 1 + 1) / 2 = s * (s + 1) / 2 + (s + 1) := htri
        rw [hstep]
        omega
      exact hrec.trans hcomb

private theorem tri_lt_of_lt {s1 s2 r1 r2 : Nat} (hlt : s1 < s2) (hr1 : r1 ≤ s1) :
    s1 * (s1 + 1) / 2 + r1 < s2 * (s2 + 1) / 2 + r2 := by
  have htri := tri_succ s1
  have hle : s1 + 1 ≤ s2 := hlt
  have hmul : (s1 + 1) * (s1 + 2) ≤ s2 * (s2 + 1) :=
    Nat.mul_le_mul hle (by omega)
  have hdiv : (s1 + 1) * (s1 + 2) / 2 ≤ s2 * (s2 + 1) / 2 :=
    Nat.div_le_div_right hmul
  omega

private theorem pairNat_injective {a1 b1 a2 b2 : Nat}
    (h : pairNat a1 b1 = pairNat a2 b2) : a1 = a2 ∧ b1 = b2 := by
  unfold pairNat at h
  have hsum : a1 + b1 = a2 + b2 := by
    rcases Nat.lt_trichotomy (a1 + b1) (a2 + b2) with hlt | heq | hgt
    · have := tri_lt_of_lt (r1 := b1) (r2 := b2) hlt (by omega)
      omega
    · exact heq
    · have := tri_lt_of_lt (r1 := b2) (r2 := b1) hgt (by omega)
      omega
  rw [hsum] at h
  omega

public theorem unpair_pair (a b : Nat) : unpairNat (pairNat a b) = (a, b) := by
  have hspec := unpairAux_spec (pairNat a b) 0 (pairNat a b) (Nat.le_refl _)
  simp only [Nat.zero_mul, Nat.zero_div, Nat.zero_add] at hspec
  have heq : pairNat (unpairNat (pairNat a b)).1 (unpairNat (pairNat a b)).2 = pairNat a b := hspec
  have hinj := pairNat_injective heq
  cases hp : unpairNat (pairNat a b) with
  | mk u v =>
    rw [hp] at hinj
    exact Prod.ext hinj.1 hinj.2

public theorem snd_unpair_le (k : Nat) : (unpairNat k).2 ≤ k := by
  have haux : ∀ fuel s rem, rem ≤ fuel → (unpairAux fuel s rem).2 ≤ s + rem := by
    intro fuel
    induction fuel with
    | zero =>
      intro s rem h; simp [unpairAux]
    | succ fuel ih =>
      intro s rem h
      unfold unpairAux
      by_cases hle : rem ≤ s
      · simp [hle]
      · simp only [hle, ↓reduceIte]
        have := ih (s + 1) (rem - (s + 1)) (by omega)
        omega
  have := haux k 0 k (Nat.le_refl k)
  simpa [unpairNat] using this

end PVsNP
