/-
  SPDX-License-Identifier: Apache-2.0
  Copyright (c) 2026 Alexander S. Donahue (independent researcher, ORCID 0009-0006-8168-9648)

  PVsNP/RelativizationSep.lean
  Baker–Gill–Solovay (1975) Separation Oracle:
    ∃ B : Oracle, ∃ L : Language, InNP B L ∧ ¬ InP B L.

  Fully constructive (zero Classical.choice needed in the oracle construction!),
  using explicit 4-tape Oracle Turing Machines from `PVsNP.OTM`.
-/
module

public import PVsNP.OTM

namespace PVsNP

/-- Unary oracle witness language `L_B(x) = true ↔ ∃ w, |w| = |x| ∧ B w = true`. -/
@[expose] public def unaryWitnessLang (B : Oracle) : Language :=
  fun x => (allBitstrings x.length).any B

public theorem unaryWitnessLang_iff (B : Oracle) (x : List Bool) :
    unaryWitnessLang B x = true ↔ ∃ w : List Bool, w.length = x.length ∧ B w = true := by
  unfold unaryWitnessLang
  rw [List.any_eq_true]
  constructor
  · rintro ⟨w, hmem, hBw⟩
    exact ⟨w, (mem_allBitstrings_iff x.length w).mp hmem, hBw⟩
  · rintro ⟨w, hlen, hBw⟩
    exact ⟨w, (mem_allBitstrings_iff x.length w).mpr hlen, hBw⟩

-- ============================================================================
-- Explicit 4-Tape Verifier OTM proving `unaryWitnessLang B ∈ InNP B`
-- ============================================================================

/-- Explicit 4-tape verifier for `unaryWitnessLang B` on input `x # w`:
    checks `|w| = |x|` via sentinel `.sep` + unary marks on `w1Tape`, copies `w` onto
    `qTape`, queries `B w`, and accepts iff `B w = true`. -/
public def unaryWitnessVerifier : OTM :=
  { rules := [
      { state := 0, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .any,
        act := .step 1 .stay (some .sep) .right none .stay none .stay },
      { state := 1, inPat := .exact .zero, w1Pat := .any, w2Pat := .any, qPat := .any,
        act := .step 1 .right (some .one) .right none .stay none .stay },
      { state := 1, inPat := .exact .one,  w1Pat := .any, w2Pat := .any, qPat := .any,
        act := .step 1 .right (some .one) .right none .stay none .stay },
      { state := 1, inPat := .exact .sep,  w1Pat := .any, w2Pat := .any, qPat := .any,
        act := .step 2 .right none .left none .stay none .stay },
      { state := 2, inPat := .exact .zero, w1Pat := .exact .one, w2Pat := .any, qPat := .any,
        act := .step 2 .right none .left none .stay (some .zero) .right },
      { state := 2, inPat := .exact .one,  w1Pat := .exact .one, w2Pat := .any, qPat := .any,
        act := .step 2 .right none .left none .stay (some .one)  .right },
      { state := 2, inPat := .exact .blank, w1Pat := .exact .sep, w2Pat := .any, qPat := .any,
        act := .step 3 .stay none .stay none .stay none .stay },
      { state := 3, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .any,
        act := .query 4 5 },
      { state := 4, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .any,
        act := .haltAccept },
      { state := 5, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .any,
        act := .haltReject }
    ] }

private def markedOnes (k : Nat) : Nat → Sym :=
  fun i => if i == 0 then Sym.sep else if i ≤ k then Sym.one else Sym.blank

private def tapeWritePrefix (w : List Bool) (k : Nat) : Nat → Sym :=
  fun i => if i < k then (if w.getD i false then Sym.one else Sym.zero) else Sym.blank

private theorem readQuery_tapeWritePrefix (w : List Bool) :
    ∀ k ≤ w.length, readQuery (tapeWritePrefix w k) k = w.take k := by
  intro k hk
  unfold readQuery
  induction k with
  | zero => simp [readQueryAux]
  | succ k ih =>
    have hlt : k < w.length := by omega
    simp only [readQueryAux]
    have hcongr : readQueryAux (tapeWritePrefix w (k + 1)) k = readQueryAux (tapeWritePrefix w k) k := by
      apply readQueryAux_congr
      intro i hi
      unfold tapeWritePrefix
      have h1 : i < k := hi
      have h2 : i < k + 1 := by omega
      simp [h1, h2]
    rw [hcongr, ih (by omega)]
    have hlast : (tapeWritePrefix w (k + 1) k == Sym.one) = w[k] := by
      unfold tapeWritePrefix
      simp only [Nat.lt_succ_self, ↓reduceIte, List.getD_eq_getElem?_getD,
                 List.getElem?_eq_getElem hlt, Option.getD_some]
      cases w[k] <;> decide
    rw [hlast]
    exact (List.take_succ_eq_append_getElem hlt).symm

private theorem uwv_in_at_lt (x w : List Bool) (i : Nat) (hi : i < x.length) :
    tapeOfList (encodePair x w) i = if x[i] then Sym.one else Sym.zero := by
  unfold tapeOfList encodePair
  rw [List.append_assoc]
  have hlen : (encodeBits x).length = x.length := List.length_map ..
  have hlt : i < (encodeBits x).length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
  unfold encodeBits; simp [hi]

private theorem uwv_in_at_eq (x w : List Bool) :
    tapeOfList (encodePair x w) x.length = Sym.sep := by
  unfold tapeOfList encodePair
  rw [List.append_assoc]
  have hlen : (encodeBits x).length = x.length := List.length_map ..
  have hle : (encodeBits x).length ≤ x.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hle, hlen, Nat.sub_self]
  rfl

private theorem uwv_in_at_w (x w : List Bool) (j : Nat) (hj : j < w.length) :
    tapeOfList (encodePair x w) (x.length + 1 + j) = if w[j] then Sym.one else Sym.zero := by
  unfold tapeOfList encodePair
  rw [List.append_assoc]
  have hlen : (encodeBits x).length = x.length := List.length_map ..
  have hle : (encodeBits x).length ≤ x.length + 1 + j := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hle]
  have hsub : x.length + 1 + j - (encodeBits x).length = j + 1 := by omega
  rw [hsub]
  simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
  unfold encodeBits; simp [hj]

private theorem uwv_in_at_end (x w : List Bool) :
    tapeOfList (encodePair x w) (x.length + 1 + w.length) = Sym.blank := by
  unfold tapeOfList encodePair
  simp only [List.getD_eq_getElem?_getD]
  have hnone : (encodeBits x ++ [Sym.sep] ++ encodeBits w)[x.length + 1 + w.length]? = none := by
    rw [List.getElem?_eq_none]
    simp only [List.length_append, List.length_singleton, encodeBits, List.length_map]
    omega
  rw [hnone]; rfl

private theorem uwv_phase1 (B : Oracle) (x w : List Bool) :
    ∀ k ≤ x.length,
    run B unaryWitnessVerifier (1 + k) (initConfig (encodePair x w)) =
    { (initConfig (encodePair x w)) with
      state := 1
      inHead := k
      w1Tape := markedOnes k
      w1Head := 1 + k } := by
  intro k hk
  induction k with
  | zero =>
    rw [Nat.add_zero, run_succ, run_zero]
    have hact : findAction unaryWitnessVerifier.rules 0
        (tapeOfList (encodePair x w) 0) (blankTape 0) (blankTape 0) (blankTape 0) =
        Action.step 1 Dir.stay (some Sym.sep) Dir.right none Dir.stay none Dir.stay := by
      simp only [blankTape]
      cases (tapeOfList (encodePair x w) 0) <;> rfl
    rw [stepLog_eq_step B unaryWitnessVerifier _ rfl hact]
    have hwt : writeOpt blankTape 0 (some Sym.sep) = markedOnes 0 := by
      funext i
      unfold writeOpt blankTape markedOnes
      cases i <;> rfl
    simp only [initConfig, moveHead]
    rw [hwt]
    rfl
  | succ k ih =>
    have hlt : k < x.length := by omega
    rw [show 1 + (k + 1) = (1 + k) + 1 from by omega, run_add, ih (by omega), run_succ, run_zero]
    have hsym := uwv_in_at_lt x w k hlt
    have hact : findAction unaryWitnessVerifier.rules 1
        (tapeOfList (encodePair x w) k) (markedOnes k (1 + k)) (blankTape 0) (blankTape 0) =
        Action.step 1 Dir.right (some Sym.one) Dir.right none Dir.stay none Dir.stay := by
      rw [hsym]; simp only [blankTape]
      cases x[k] <;> cases (markedOnes k (1 + k)) <;> decide
    rw [stepLog_eq_step B unaryWitnessVerifier _ rfl hact]
    have hwt : writeOpt (markedOnes k) (1 + k) (some Sym.one) = markedOnes (k + 1) := by
      funext i
      unfold writeOpt markedOnes
      by_cases hi : i = 1 + k
      · subst hi
        have hne0 : (1 + k == 0) = false := beq_false_of_ne (by omega)
        simp [hne0]; omega
      · have hbeq : (i == 1 + k) = false := beq_false_of_ne hi
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        by_cases hi0 : i = 0
        · subst hi0; rfl
        · have hbeq0 : (i == 0) = false := beq_false_of_ne hi0
          simp only [hbeq0, Bool.false_eq_true, ↓reduceIte]
          have hiff : (i ≤ k) ↔ (i ≤ k + 1) := by omega
          by_cases hle : i ≤ k <;> simp [hle, show (i ≤ k + 1) ↔ (i ≤ k) from hiff.symm]
    rw [hwt]
    simp only [moveHead, writeOpt]

private theorem uwv_phase2 (B : Oracle) (x w : List Bool) :
    ∀ j ≤ min x.length w.length,
    run B unaryWitnessVerifier j
      { (initConfig (encodePair x w)) with
        state := 2
        inHead := x.length + 1
        w1Tape := markedOnes x.length
        w1Head := x.length } =
    { (initConfig (encodePair x w)) with
      state := 2
      inHead := x.length + 1 + j
      w1Tape := markedOnes x.length
      w1Head := x.length - j
      qTape := tapeWritePrefix w j
      qHead := j } := by
  intro j hj
  induction j with
  | zero =>
    rw [run_zero]
    have hq : tapeWritePrefix w 0 = blankTape := by funext i; simp [tapeWritePrefix, blankTape]
    simp [hq, initConfig]
  | succ j ih =>
    have hjx : j < x.length := by omega
    have hjw : j < w.length := by omega
    rw [run_add B _ j 1, ih (by omega), run_succ, run_zero]
    have hsym := uwv_in_at_w x w j hjw
    have hw1 : markedOnes x.length (x.length - j) = Sym.one := by
      unfold markedOnes
      have hne0 : (x.length - j == 0) = false := beq_false_of_ne (by omega)
      have hle : x.length - j ≤ x.length := by omega
      simp [hne0, hle]
    have hact : findAction unaryWitnessVerifier.rules 2
        (tapeOfList (encodePair x w) (x.length + 1 + j))
        (markedOnes x.length (x.length - j)) (blankTape 0) (tapeWritePrefix w j j) =
        Action.step 2 Dir.right none Dir.left none Dir.stay
          (some (if w[j] then Sym.one else Sym.zero)) Dir.right := by
      rw [hsym, hw1]; simp only [blankTape]
      cases w[j] <;> cases (tapeWritePrefix w j j) <;> decide
    rw [stepLog_eq_step B unaryWitnessVerifier _ rfl hact]
    have hqt : writeOpt (tapeWritePrefix w j) j (some (if w[j] then Sym.one else Sym.zero)) =
        tapeWritePrefix w (j + 1) := by
      funext i
      unfold writeOpt tapeWritePrefix
      by_cases hi : i = j
      · subst hi
        simp [List.getD_eq_getElem?_getD, hjw]
      · have hbeq : (i == j) = false := beq_false_of_ne hi
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        have hiff : (i < j) ↔ (i < j + 1) := by omega
        by_cases hlt : i < j <;> simp [hlt, show (i < j + 1) ↔ (i < j) from hiff.symm]
    rw [hqt]
    simp only [moveHead, writeOpt]
    have ha1 : x.length + 1 + j + 1 = x.length + 1 + (j + 1) := by omega
    have ha2 : x.length - j - 1 = x.length - (j + 1) := by omega
    rw [ha1, ha2]

private theorem uwv_to_phase2 (B : Oracle) (x w : List Bool) :
    run B unaryWitnessVerifier (x.length + 2) (initConfig (encodePair x w)) =
    { (initConfig (encodePair x w)) with
      state := 2
      inHead := x.length + 1
      w1Tape := markedOnes x.length
      w1Head := x.length } := by
  rw [show x.length + 2 = (1 + x.length) + 1 from by omega, run_add,
      uwv_phase1 B x w x.length (Nat.le_refl _), run_succ, run_zero]
  have hsep := uwv_in_at_eq x w
  have hact : findAction unaryWitnessVerifier.rules 1
      (tapeOfList (encodePair x w) x.length) (markedOnes x.length (1 + x.length))
      (blankTape 0) (blankTape 0) =
      Action.step 2 Dir.right none Dir.left none Dir.stay none Dir.stay := by
    rw [hsep]; simp only [blankTape]
    cases (markedOnes x.length (1 + x.length)) <;> rfl
  rw [stepLog_eq_step B unaryWitnessVerifier _ rfl hact]
  simp only [moveHead, writeOpt]
  have hsub : 1 + x.length - 1 = x.length := by omega
  rw [hsub]

private theorem uwv_result_eq_len (B : Oracle) (x w : List Bool) (hlen : w.length = x.length) :
    (run B unaryWitnessVerifier (2 * x.length + 5) (initConfig (encodePair x w))).halted =
    some (B w) := by
  have hsplit : 2 * x.length + 5 = (x.length + 2) + x.length + 3 := by omega
  rw [hsplit, run_add, run_add, uwv_to_phase2]
  rw [uwv_phase2 B x w x.length (by omega)]
  rw [run_succ, run_succ, run_succ, run_zero]
  have hend : tapeOfList (encodePair x w) (x.length + 1 + x.length) = Sym.blank := by
    have h0 := uwv_in_at_end x w
    rwa [hlen] at h0
  have hw1 : markedOnes x.length (x.length - x.length) = Sym.sep := by
    simp [markedOnes]
  have hact3 : findAction unaryWitnessVerifier.rules 2
      (tapeOfList (encodePair x w) (x.length + 1 + x.length))
      (markedOnes x.length (x.length - x.length)) (blankTape 0)
      (tapeWritePrefix w x.length x.length) =
      Action.step 3 Dir.stay none Dir.stay none Dir.stay none Dir.stay := by
    rw [hend, hw1]; simp only [blankTape]
    cases (tapeWritePrefix w x.length x.length) <;> rfl
  have hs3 :
      (stepLog B unaryWitnessVerifier
        { (initConfig (encodePair x w)) with
          state := 2
          inHead := x.length + 1 + x.length
          w1Tape := markedOnes x.length
          w1Head := x.length - x.length
          qTape := tapeWritePrefix w x.length
          qHead := x.length }).1 =
      { (initConfig (encodePair x w)) with
        state := 3
        inHead := x.length + 1 + x.length
        w1Tape := markedOnes x.length
        w1Head := x.length - x.length
        qTape := tapeWritePrefix w x.length
        qHead := x.length } := by
    rw [stepLog_eq_step B unaryWitnessVerifier _ rfl hact3]
    rfl
  rw [hs3]
  have hactQ : findAction unaryWitnessVerifier.rules 3
      (tapeOfList (encodePair x w) (x.length + 1 + x.length))
      (markedOnes x.length (x.length - x.length)) (blankTape 0)
      (tapeWritePrefix w x.length x.length) = Action.query 4 5 := by
    rw [hend, hw1]; simp only [blankTape]
    cases (tapeWritePrefix w x.length x.length) <;> rfl
  have hread : readQuery (tapeWritePrefix w x.length) x.length = w := by
    rw [readQuery_tapeWritePrefix w x.length (by omega), ← hlen, List.take_length]
  have hsQ :
      (stepLog B unaryWitnessVerifier
        { (initConfig (encodePair x w)) with
          state := 3
          inHead := x.length + 1 + x.length
          w1Tape := markedOnes x.length
          w1Head := x.length - x.length
          qTape := tapeWritePrefix w x.length
          qHead := x.length }).1 =
      { (initConfig (encodePair x w)) with
        state := if B w then 4 else 5
        inHead := x.length + 1 + x.length
        w1Tape := markedOnes x.length
        w1Head := x.length - x.length
        qTape := blankTape
        qHead := 0 } := by
    rw [stepLog_eq_query B unaryWitnessVerifier _ rfl hactQ, hread]
  rw [hsQ]
  cases hBw : B w
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hactR : findAction unaryWitnessVerifier.rules 5
        (tapeOfList (encodePair x w) (x.length + 1 + x.length))
        (markedOnes x.length (x.length - x.length)) (blankTape 0) (blankTape 0) =
        Action.haltReject := by
      rw [hend, hw1]; rfl
    rw [stepLog_eq_haltReject B unaryWitnessVerifier _ rfl hactR]
  · simp only [↓reduceIte]
    have hactA : findAction unaryWitnessVerifier.rules 4
        (tapeOfList (encodePair x w) (x.length + 1 + x.length))
        (markedOnes x.length (x.length - x.length)) (blankTape 0) (blankTape 0) =
        Action.haltAccept := by
      rw [hend, hw1]; rfl
    rw [stepLog_eq_haltAccept B unaryWitnessVerifier _ rfl hactA]

private theorem uwv_reject_ne_len (B : Oracle) (x w : List Bool) (hne : w.length ≠ x.length) :
    (run B unaryWitnessVerifier (x.length + 2 + min x.length w.length + 1)
      (initConfig (encodePair x w))).halted = some false := by
  rw [run_add, run_add, uwv_to_phase2, uwv_phase2 B x w (min x.length w.length) (Nat.le_refl _)]
  rw [run_succ, run_zero]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hmin : min x.length w.length = w.length := Nat.min_eq_right (by omega)
    rw [hmin]
    have hend := uwv_in_at_end x w
    have hw1 : markedOnes x.length (x.length - w.length) = Sym.one := by
      unfold markedOnes
      have hne0 : (x.length - w.length == 0) = false := beq_false_of_ne (by omega)
      have hle : x.length - w.length ≤ x.length := by omega
      simp [hne0, hle]
    have hact : findAction unaryWitnessVerifier.rules 2
        (tapeOfList (encodePair x w) (x.length + 1 + w.length))
        (markedOnes x.length (x.length - w.length)) (blankTape 0)
        (tapeWritePrefix w w.length w.length) = Action.haltReject := by
      rw [hend, hw1]; simp only [blankTape]
      cases (tapeWritePrefix w w.length w.length) <;> decide
    rw [stepLog_eq_haltReject B unaryWitnessVerifier _ rfl hact]
  · have hmin : min x.length w.length = x.length := Nat.min_eq_left (by omega)
    rw [hmin]
    have hsym := uwv_in_at_w x w x.length hgt
    have hw1 : markedOnes x.length (x.length - x.length) = Sym.sep := by
      simp [markedOnes]
    have hact : findAction unaryWitnessVerifier.rules 2
        (tapeOfList (encodePair x w) (x.length + 1 + x.length))
        (markedOnes x.length (x.length - x.length)) (blankTape 0)
        (tapeWritePrefix w x.length x.length) = Action.haltReject := by
      rw [hsym, hw1]; simp only [blankTape]
      cases w[x.length] <;> cases (tapeWritePrefix w x.length x.length) <;> decide
    rw [stepLog_eq_haltReject B unaryWitnessVerifier _ rfl hact]

private theorem poly_slack_uwv (n : Nat) : 2 * n + 5 ≤ polyBound 5 n := by
  unfold polyBound
  cases n with
  | zero => decide
  | succ k =>
    have h5 : (k + 2) ^ 5 = (k + 2) ^ 4 * (k + 2) := Nat.pow_succ (k + 2) 4
    have h16 : 16 ≤ (k + 2) ^ 4 := by
      have : 2 ^ 4 ≤ (k + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      have h24 : 2 ^ 4 = 16 := rfl
      omega
    have hmul : 16 * (k + 2) ≤ (k + 2) ^ 4 * (k + 2) := Nat.mul_le_mul_right (k + 2) h16
    have heq : k + 1 + 1 = k + 2 := by omega
    rw [heq, h5]
    omega

/-- For EVERY oracle `B`, `unaryWitnessLang B ∈ NP^B`. -/
public theorem unaryWitnessLang_in_np (B : Oracle) : InNP B (unaryWitnessLang B) := by
  refine ⟨unaryWitnessVerifier, 5, 1, ?_⟩
  intro x
  rw [unaryWitnessLang_iff]
  constructor
  · rintro ⟨w, hlen, hBw⟩
    refine ⟨w, ?_, ?_⟩
    · unfold polyBound; rw [Nat.pow_one]; omega
    · have hres := uwv_result_eq_len B x w hlen
      rw [hBw] at hres
      exact run_halted_mono B unaryWitnessVerifier (poly_slack_uwv x.length) _ true hres
  · rintro ⟨w, _, hw⟩
    by_cases hlen : w.length = x.length
    · have hres := uwv_result_eq_len B x w hlen
      have hmono := run_halted_mono B unaryWitnessVerifier (poly_slack_uwv x.length) _ (B w) hres
      rw [hmono] at hw
      exact ⟨w, hlen, Option.some.inj hw⟩
    · have hrej := uwv_reject_ne_len B x w hlen
      have hle : x.length + 2 + min x.length w.length + 1 ≤ polyBound 5 x.length := by
        have hmin : min x.length w.length ≤ x.length := Nat.min_le_left ..
        have := poly_slack_uwv x.length
        omega
      have hmono := run_halted_mono B unaryWitnessVerifier hle _ false hrej
      rw [hmono] at hw
      cases hw

-- ============================================================================
-- Constructive Stage-by-Stage Diagonalization Oracle `B` (`P^B ≠ NP^B`)
-- ============================================================================

public structure DiagStage where
  oracle : Oracle
  floor : Nat

/-- Helper: execute one diagonalization stage against a decoded `(M, c)` pair. -/
public def diagStepMachine (M : OTM) (c : Nat) (st : DiagStage) : DiagStage :=
  let n := diagLength c st.floor
  let T := polyBound c n
  let inp := encodeBits (List.replicate n true)
  let res := runLog st.oracle M T (initConfig inp)
  let nextFloor := max n T
  if res.1.halted == some true then
    { oracle := st.oracle, floor := nextFloor }
  else
    let wStar := findUnqueried n res.2
    { oracle := fun u => if u == wStar then true else st.oracle u,
      floor := nextFloor }

/-- Stage `i` of Baker–Gill–Solovay diagonalization against the `i`-th `(OTM, c)` pair. -/
public def diagStep (i : Nat) (st : DiagStage) : DiagStage :=
  let p := unpairNat i
  match decodeOTM p.1 with
  | none => { oracle := st.oracle, floor := st.floor + 1 }
  | some M => diagStepMachine M p.2 st

/-- Stage `s` of the BGS diagonalization (`s = 0` is the empty oracle). -/
public def diagState : Nat → DiagStage
  | 0 => { oracle := fun _ => false, floor := 0 }
  | s + 1 => diagStep s (diagState s)

private theorem diagStepMachine_floor (M : OTM) (c : Nat) (st : DiagStage) :
    (diagStepMachine M c st).floor = max (diagLength c st.floor) (polyBound c (diagLength c st.floor)) := by
  dsimp only [diagStepMachine]
  split <;> rfl

private theorem diagStepMachine_qlen_lt (M : OTM) (c : Nat) (st : DiagStage) :
    (runLog st.oracle M (polyBound c (diagLength c st.floor))
      (initConfig (encodeBits (List.replicate (diagLength c st.floor) true)))).2.length <
    2 ^ (diagLength c st.floor) := by
  have hcnt := runLog_query_count st.oracle M (polyBound c (diagLength c st.floor))
    (initConfig (encodeBits (List.replicate (diagLength c st.floor) true)))
  have hexp : polyBound c (diagLength c st.floor) < 2 ^ (diagLength c st.floor) :=
    diagLength_exp_gt_poly c st.floor
  omega

private theorem diagState_floor_mono (s : Nat) :
    (diagState s).floor < (diagState (s + 1)).floor := by
  change (diagState s).floor < (diagStep s (diagState s)).floor
  dsimp only [diagStep]
  cases h : decodeOTM (unpairNat s).1 with
  | none =>
    simp only []
    omega
  | some M =>
    rw [diagStepMachine_floor]
    have hgt := diagLength_gt (unpairNat s).2 (diagState s).floor
    have hle : diagLength (unpairNat s).2 (diagState s).floor ≤
        max (diagLength (unpairNat s).2 (diagState s).floor)
            (polyBound (unpairNat s).2 (diagLength (unpairNat s).2 (diagState s).floor)) :=
      Nat.le_max_left ..
    omega

private theorem diagState_floor_ge (s : Nat) : s ≤ (diagState s).floor := by
  induction s with
  | zero => exact Nat.le_refl 0
  | succ s ih =>
    have hlt := diagState_floor_mono s
    omega

private theorem diagState_floor_le_of_le {s1 s2 : Nat} (hle : s1 ≤ s2) :
    (diagState s1).floor ≤ (diagState s2).floor := by
  induction s2 with
  | zero =>
    have h0 : s1 = 0 := by omega
    subst h0; exact Nat.le_refl _
  | succ s2 ih =>
    by_cases heq : s1 = s2 + 1
    · subst heq; exact Nat.le_refl _
    · have h1 := ih (by omega)
      have h2 := diagState_floor_mono s2
      omega

private theorem diagState_step_preserves_le (s : Nat) (u : List Bool)
    (hle : u.length ≤ (diagState s).floor) :
    (diagState (s + 1)).oracle u = (diagState s).oracle u := by
  change (diagStep s (diagState s)).oracle u = (diagState s).oracle u
  dsimp only [diagStep]
  cases h : decodeOTM (unpairNat s).1 with
  | none => rfl
  | some M =>
    dsimp only [diagStepMachine]
    split
    · rfl
    · let Q := (runLog (diagState s).oracle M
        (polyBound (unpairNat s).2 (diagLength (unpairNat s).2 (diagState s).floor))
        (initConfig (encodeBits (List.replicate (diagLength (unpairNat s).2 (diagState s).floor) true)))).2
      have hspec := findUnqueried_spec (diagLength (unpairNat s).2 (diagState s).floor) Q
        (diagStepMachine_qlen_lt M (unpairNat s).2 (diagState s))
      have hgt := diagLength_gt (unpairNat s).2 (diagState s).floor
      have hne : u ≠ findUnqueried (diagLength (unpairNat s).2 (diagState s).floor) Q := by
        intro heq
        rw [heq, hspec.1] at hle
        omega
      simp [Q, hne]

private theorem diagState_preserves_le (s1 s2 : Nat) (hle : s1 ≤ s2) (u : List Bool)
    (hu : u.length ≤ (diagState s1).floor) :
    (diagState s2).oracle u = (diagState s1).oracle u := by
  induction s2 with
  | zero =>
    have h0 : s1 = 0 := by omega
    subst h0; rfl
  | succ s2 ih =>
    by_cases heq : s1 = s2 + 1
    · subst heq; rfl
    · have hle1 : s1 ≤ s2 := by omega
      have hfl : (diagState s1).floor ≤ (diagState s2).floor := diagState_floor_le_of_le hle1
      rw [diagState_step_preserves_le s2 u (Nat.le_trans hu hfl)]
      exact ih hle1

private theorem diagState_zero_gt_floor (s : Nat) (u : List Bool)
    (hgt : (diagState s).floor < u.length) :
    (diagState s).oracle u = false := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have hfl_lt := diagState_floor_mono s
    have hprev := ih (by omega)
    change (diagStep s (diagState s)).floor < u.length at hgt
    change (diagStep s (diagState s)).oracle u = false
    dsimp only [diagStep] at hgt ⊢
    cases h : decodeOTM (unpairNat s).1 with
    | none => exact hprev
    | some M =>
      rw [h, diagStepMachine_floor] at hgt
      dsimp only [diagStepMachine]
      split
      · exact hprev
      · let Q := (runLog (diagState s).oracle M
          (polyBound (unpairNat s).2 (diagLength (unpairNat s).2 (diagState s).floor))
          (initConfig (encodeBits (List.replicate (diagLength (unpairNat s).2 (diagState s).floor) true)))).2
        have hspec := findUnqueried_spec (diagLength (unpairNat s).2 (diagState s).floor) Q
          (diagStepMachine_qlen_lt M (unpairNat s).2 (diagState s))
        have hle_max : diagLength (unpairNat s).2 (diagState s).floor ≤
            max (diagLength (unpairNat s).2 (diagState s).floor)
                (polyBound (unpairNat s).2 (diagLength (unpairNat s).2 (diagState s).floor)) :=
          Nat.le_max_left ..
        have hne : u ≠ findUnqueried (diagLength (unpairNat s).2 (diagState s).floor) Q := by
          intro heq
          rw [heq, hspec.1] at hgt
          omega
        simp [Q, hne, hprev]

/-- The constructive Baker–Gill–Solovay separation oracle `B_sep`. -/
public def bgsSepOracle : Oracle :=
  fun u => (diagState u.length).oracle u

public theorem bgsSepOracle_eq_stage (s : Nat) (u : List Bool)
    (hu : u.length ≤ (diagState s).floor) :
    bgsSepOracle u = (diagState s).oracle u := by
  unfold bgsSepOracle
  rcases Nat.le_total u.length s with hle | hge
  · exact (diagState_preserves_le u.length s hle u (diagState_floor_ge u.length)).symm
  · exact diagState_preserves_le s u.length hge u hu

/-- Headline Theorem (Baker–Gill–Solovay 1975, Separation Oracle):
    There exists a computable oracle `B` and a language `L ∈ NP^B` such that `L ∉ P^B`. -/
public theorem bgs_oracle_separation :
    ∃ B : Oracle, ∃ L : Language, InNP B L ∧ ¬ InP B L := by
  refine ⟨bgsSepOracle, unaryWitnessLang bgsSepOracle, unaryWitnessLang_in_np bgsSepOracle, ?_⟩
  rintro ⟨M, c, hdec⟩
  let i := pairNat (encodeOTM M) c
  let st := diagState i
  let n := diagLength c st.floor
  let T := polyBound c n
  let x := List.replicate n true
  have hxlen : x.length = n := List.length_replicate
  have hunp : unpairNat i = (encodeOTM M, c) := unpair_pair (encodeOTM M) c
  have hdecM : decodeOTM (encodeOTM M) = some M := decode_encodeOTM M
  have hstage_eq_step : diagState (i + 1) = diagStepMachine M c st := by
    unfold diagState diagStep
    rw [hunp]
    simp [hdecM, st]
  have hnextFloor : (diagState (i + 1)).floor = max n T := by
    rw [hstage_eq_step, diagStepMachine_floor]
  have hqlen_lt : (runLog st.oracle M T (initConfig (encodeBits x))).2.length < 2 ^ n :=
    diagStepMachine_qlen_lt M c st
  -- Stage `i` oracle agrees with `bgsSepOracle` on all queries made by M at stage `i`!
  have hrun_agree :
      run bgsSepOracle M T (initConfig (encodeBits x)) =
      run st.oracle M T (initConfig (encodeBits x)) := by
    have hlog := runLog_oracle_agree st.oracle bgsSepOracle M T (initConfig (encodeBits x)) (by
      intro q hq
      have hqlen := runLog_query_len st.oracle M T (initConfig (encodeBits x)) q hq
      simp only [initConfig, Nat.zero_add] at hqlen
      have hq_le_next : q.length ≤ (diagState (i + 1)).floor := by
        rw [hnextFloor]
        exact Nat.le_trans hqlen (Nat.le_max_right n T)
      rw [bgsSepOracle_eq_stage (i + 1) q hq_le_next, hstage_eq_step]
      dsimp only [diagStepMachine]
      split
      · rfl
      · have hspec := findUnqueried_spec n (runLog st.oracle M T (initConfig (encodeBits x))).2 hqlen_lt
        have hne : q ≠ findUnqueried n (runLog st.oracle M T (initConfig (encodeBits x))).2 := by
          intro heq; rw [heq] at hq; exact hspec.2 hq
        have hbeq : (q == findUnqueried (diagLength c st.floor)
            (runLog st.oracle M (polyBound c (diagLength c st.floor))
              (initConfig (encodeBits (List.replicate (diagLength c st.floor) true)))).2) = false :=
          beq_false_of_ne hne
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte])
    exact (congrArg Prod.fst hlog).symm
  -- Compare `M`'s decision on `x = 1^n` against `unaryWitnessLang bgsSepOracle x`!
  have hMdec := hdec x
  rw [hxlen] at hMdec
  change (run bgsSepOracle M T (initConfig (encodeBits x))).halted =
         some (unaryWitnessLang bgsSepOracle x) at hMdec
  rw [hrun_agree] at hMdec
  by_cases hacc : (run st.oracle M T (initConfig (encodeBits x))).halted = some true
  · -- Case 1: M accepted `1^n`, so NO length-n string was added to `bgsSepOracle`!
    rw [hacc] at hMdec
    have hLtrue : unaryWitnessLang bgsSepOracle x = true := (Option.some.inj hMdec).symm
    rw [unaryWitnessLang_iff] at hLtrue
    rcases hLtrue with ⟨w, hwlen, hBw⟩
    rw [hxlen] at hwlen
    have hw_le : w.length ≤ (diagState (i + 1)).floor := by
      rw [hnextFloor, hwlen]; exact Nat.le_max_left n T
    rw [bgsSepOracle_eq_stage (i + 1) w hw_le, hstage_eq_step] at hBw
    have hor : (diagStepMachine M c st).oracle = st.oracle := by
      unfold diagStepMachine
      have hcond : ((runLog st.oracle M (polyBound c (diagLength c st.floor))
          (initConfig (encodeBits (List.replicate (diagLength c st.floor) true)))).1.halted == some true) = true :=
        beq_iff_eq.mpr hacc
      simp only [hcond, ↓reduceIte]
    rw [hor] at hBw
    have hzero : st.oracle w = false :=
      diagState_zero_gt_floor i w (by rw [hwlen]; exact diagLength_gt c st.floor)
    rw [hzero] at hBw
    cases hBw
  · -- Case 2: M did not accept `1^n`, so `wStar` of length `n` WAS added to `bgsSepOracle`!
    let wStar := findUnqueried n (runLog st.oracle M T (initConfig (encodeBits x))).2
    have hspec := findUnqueried_spec n (runLog st.oracle M T (initConfig (encodeBits x))).2 hqlen_lt
    have hw_le : wStar.length ≤ (diagState (i + 1)).floor := by
      rw [hnextFloor, hspec.1]; exact Nat.le_max_left n T
    have hBwStar : bgsSepOracle wStar = true := by
      rw [bgsSepOracle_eq_stage (i + 1) wStar hw_le, hstage_eq_step]
      have hor : (diagStepMachine M c st).oracle = (fun u => if u == wStar then true else st.oracle u) := by
        unfold diagStepMachine
        have hcond : ((runLog st.oracle M (polyBound c (diagLength c st.floor))
            (initConfig (encodeBits (List.replicate (diagLength c st.floor) true)))).1.halted == some true) = false :=
          beq_false_of_ne hacc
        simp only [hcond, Bool.false_eq_true, ↓reduceIte, wStar, n, T, x]
      rw [hor]
      simp
    have hLtrue : unaryWitnessLang bgsSepOracle x = true :=
      (unaryWitnessLang_iff bgsSepOracle x).mpr ⟨wStar, by rw [hxlen]; exact hspec.1, hBwStar⟩
    rw [hLtrue] at hMdec
    exact hacc hMdec

end PVsNP
