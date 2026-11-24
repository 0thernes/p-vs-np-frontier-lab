/-
  SPDX-License-Identifier: Apache-2.0
  Copyright (c) 2026 Alexander S. Donahue (independent researcher, ORCID 0009-0006-8168-9648)

  PVsNP/RelativizationCol.lean
  Baker–Gill–Solovay (1975) Collapse Oracle:
    ∃ A : Oracle, ∀ L : Language, InP A L ↔ InNP A L.

  Uses a well-founded length-recursive canonical NP^A oracle `bgsColOracle`
  and an explicit 4-tape polynomial-time Oracle Turing Machine `collapseDecider V c d`
  that constructs the exact padded query ⟨V, d, x, 1^{t+1}⟩ with length > t = polyBound c |x|.
-/
module

public import PVsNP.OTM

namespace PVsNP

-- ============================================================================
-- Part 1: Self-Delimiting Collapse Query Encoding & Decoding
-- ============================================================================

@[expose] public section

def doubleBits : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: doubleBits bs

def encodeColQuery (vCode d t : Nat) (x : List Bool) : List Bool :=
  List.replicate vCode true ++ [false] ++
  List.replicate d true ++ [false] ++
  doubleBits x ++ [false, false] ++
  List.replicate (t + 1) true

def readUnary : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest =>
    match readUnary rest with
    | none => none
    | some (k, rem) => some (k + 1, rem)

def readDoubled : List Bool → Option (List Bool × List Bool)
  | false :: false :: rest => some ([], rest)
  | true :: b :: rest =>
    match readDoubled rest with
    | none => none
    | some (xs, rem) => some (b :: xs, rem)
  | _ => none

def readAllOnes : List Bool → Option Nat
  | [] => some 0
  | true :: rest => (readAllOnes rest).map (· + 1)
  | false :: _ => none

def decodeColQuery (q : List Bool) : Option (Nat × Nat × Nat × List Bool) :=
  match readUnary q with
  | none => none
  | some (vCode, r1) =>
    match readUnary r1 with
    | none => none
    | some (d, r2) =>
      match readDoubled r2 with
      | none => none
      | some (x, r3) =>
        match readAllOnes r3 with
        | some (t + 1) => some (vCode, d, t, x)
        | _ => none

end

private theorem readUnary_replicate (n : Nat) (rest : List Bool) :
    readUnary (List.replicate n true ++ false :: rest) = some (n, rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, readUnary, ih]

private theorem readDoubled_doubleBits (x rest : List Bool) :
    readDoubled (doubleBits x ++ false :: false :: rest) = some (x, rest) := by
  induction x with
  | nil => rfl
  | cons b bs ih =>
    simp only [doubleBits, List.cons_append, readDoubled, ih]

private theorem readAllOnes_replicate (n : Nat) :
    readAllOnes (List.replicate n true) = some n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, readAllOnes, ih, Option.map_some]

public theorem decode_encodeColQuery (vCode d t : Nat) (x : List Bool) :
    decodeColQuery (encodeColQuery vCode d t x) = some (vCode, d, t, x) := by
  unfold decodeColQuery encodeColQuery
  have h1 :
      List.replicate vCode true ++ [false] ++ List.replicate d true ++ [false] ++
        doubleBits x ++ [false, false] ++ List.replicate (t + 1) true =
      List.replicate vCode true ++
        (false :: (List.replicate d true ++
          (false :: (doubleBits x ++ (false :: false :: List.replicate (t + 1) true))))) := by
    simp [List.append_assoc]
  rw [h1, readUnary_replicate]
  dsimp only
  rw [readUnary_replicate]
  dsimp only
  rw [readDoubled_doubleBits]
  dsimp only
  rw [readAllOnes_replicate]

private theorem doubleBits_length (x : List Bool) : (doubleBits x).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons b bs ih => simp [doubleBits, ih]; omega

public theorem encodeColQuery_length_gt (vCode d t : Nat) (x : List Bool) :
    t < (encodeColQuery vCode d t x).length := by
  unfold encodeColQuery
  simp only [List.length_append, List.length_replicate,
             List.length_cons, List.length_nil, doubleBits_length]
  omega

-- ============================================================================
-- Part 2: Well-Founded Length-Recursive Collapse Oracle `bgsColOracle`
-- ============================================================================

/-- All bitstrings of length `≤ B`. -/
public def allBitstringsUpTo : Nat → List (List Bool)
  | 0 => allBitstrings 0
  | k + 1 => allBitstrings (k + 1) ++ allBitstringsUpTo k

public theorem mem_allBitstringsUpTo_iff (B : Nat) (w : List Bool) :
    w ∈ allBitstringsUpTo B ↔ w.length ≤ B := by
  induction B with
  | zero =>
    simp [allBitstringsUpTo, mem_allBitstrings_iff]
  | succ k ih =>
    simp only [allBitstringsUpTo, List.mem_append, mem_allBitstrings_iff, ih]
    omega

/-- Length-recursive canonical `NP^A` oracle `bgsColOracle`.
    Every query made by `V` in `t` steps has length `≤ t < q.length`,
    making the recursion well-founded on `q.length`. -/
public def bgsColOracle (q : List Bool) : Bool :=
  match decodeColQuery q with
  | none => false
  | some (vCode, d, t, x) =>
    if _ht : t < q.length then
      match decodeOTM vCode with
      | none => false
      | some V =>
        let Oprev : Oracle := fun u =>
          if _hu : u.length < q.length then bgsColOracle u else false
        (allBitstringsUpTo (polyBound d x.length)).any (fun w =>
          (run Oprev V t (initConfig (encodePair x w))).halted == some true)
    else false
termination_by q.length

public theorem bgsColOracle_spec (V : OTM) (d t : Nat) (x : List Bool) :
    bgsColOracle (encodeColQuery (encodeOTM V) d t x) = true ↔
      ∃ w : List Bool, w.length ≤ polyBound d x.length ∧
        (run bgsColOracle V t (initConfig (encodePair x w))).halted = some true := by
  let q := encodeColQuery (encodeOTM V) d t x
  have hlt : t < q.length := encodeColQuery_length_gt (encodeOTM V) d t x
  have hdec : decodeColQuery q = some (encodeOTM V, d, t, x) :=
    decode_encodeColQuery (encodeOTM V) d t x
  have hV : decodeOTM (encodeOTM V) = some V := decode_encodeOTM V
  let Oprev : Oracle := fun u => if _hu : u.length < q.length then bgsColOracle u else false
  have hunfold : bgsColOracle q =
      (allBitstringsUpTo (polyBound d x.length)).any (fun w =>
        (run Oprev V t (initConfig (encodePair x w))).halted == some true) := by
    rw [bgsColOracle]
    simp only [hdec, hlt, ↓reduceDIte, hV, Oprev]
  rw [hunfold, List.any_eq_true]
  have hagree : ∀ w : List Bool,
      run Oprev V t (initConfig (encodePair x w)) =
      run bgsColOracle V t (initConfig (encodePair x w)) := by
    intro w
    apply run_oracle_agree_le Oprev bgsColOracle V t (encodePair x w)
    intro u hu
    have hult : u.length < q.length := by omega
    simp [Oprev, hult]
  constructor
  · rintro ⟨w, hmem, hacc⟩
    rw [hagree w] at hacc
    exact ⟨w, (mem_allBitstringsUpTo_iff ..).mp hmem, beq_iff_eq.mp hacc⟩
  · rintro ⟨w, hlen, hacc⟩
    refine ⟨w, (mem_allBitstringsUpTo_iff ..).mpr hlen, ?_⟩
    rw [hagree w]
    exact beq_iff_eq.mpr hacc

-- ============================================================================
-- Part 3: Explicit 4-Tape Polynomial-Time Query-Constructing OTM `collapseDecider`
-- ============================================================================

private def colMarkedOnes (k : Nat) : Nat → Sym :=
  fun i => if i == 0 then Sym.sep else if i ≤ k then Sym.one else Sym.blank

private def qTapeFromBits (bs : List Bool) : Nat → Sym :=
  fun i => if i < bs.length then (if bs.getD i false then Sym.one else Sym.zero) else Sym.blank

private theorem readQuery_qTapeFromBits (bs : List Bool) :
    readQuery (qTapeFromBits bs) bs.length = bs := by
  have haux : ∀ k ≤ bs.length, readQueryAux (qTapeFromBits bs) k = bs.take k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hlt : k < bs.length := by omega
      simp only [readQueryAux, ih (by omega)]
      have hlast : (qTapeFromBits bs k == Sym.one) = bs[k] := by
        unfold qTapeFromBits
        simp only [hlt, ↓reduceIte, List.getD_eq_getElem?_getD,
                   List.getElem?_eq_getElem hlt, Option.getD_some]
        cases bs[k] <;> decide
      rw [hlast]
      exact (List.take_succ_eq_append_getElem hlt).symm
  unfold readQuery
  rw [haux bs.length (Nat.le_refl _), List.take_length]

private def mulRoundRules (base next : Nat) : List Rule := [
  { state := base, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step (base + 1) .stay none .left none .stay none .stay },
  { state := base + 1, inPat := .any, w1Pat := .exact .one, w2Pat := .any, qPat := .any,
    act := .step (base + 2) .stay (some .blank) .stay none .stay none .stay },
  { state := base + 1, inPat := .any, w1Pat := .exact .sep, w2Pat := .any, qPat := .any,
    act := .step (base + 4) .stay none .right none .left none .stay },
  { state := base + 2, inPat := .exact .zero, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step (base + 2) .right none .stay (some .one) .right none .right },
  { state := base + 2, inPat := .exact .one,  w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step (base + 2) .right none .stay (some .one) .right none .right },
  { state := base + 2, inPat := .exact .blank, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step (base + 3) .stay none .stay (some .one) .right none .stay },
  { state := base + 3, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .exact .blank,
    act := .step (base + 3) .left none .stay none .stay none .left },
  { state := base + 3, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .exact .sep,
    act := .step (base + 1) .stay none .left none .stay none .stay },
  { state := base + 4, inPat := .any, w1Pat := .any, w2Pat := .exact .one, qPat := .any,
    act := .step (base + 4) .stay (some .one) .right (some .blank) .left none .stay },
  { state := base + 4, inPat := .any, w1Pat := .any, w2Pat := .exact .sep, qPat := .any,
    act := .step next .stay none .stay none .right none .stay }
]

private def allMulRounds (c : Nat) : List Rule :=
  (List.range c).flatMap (fun j => mulRoundRules (2 + 5 * j) (2 + 5 * (j + 1)))

private def writeBitsRules (base : Nat) : List Bool → List Rule
  | [] => []
  | b :: bs =>
    { state := base, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .any,
      act := .step (base + 1) .stay none .stay none .stay (some (if b then .one else .zero)) .right } ::
    writeBitsRules (base + 1) bs

private def colPrefBits (V : OTM) (d : Nat) : List Bool :=
  List.replicate (encodeOTM V) true ++ [false] ++ List.replicate d true ++ [false]

private def colInitRules : List Rule := [
  { state := 0, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step 1 .stay (some .sep) .right (some .sep) .right (some .sep) .stay },
  { state := 1, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step 2 .stay (some .one) .right none .stay none .stay }
]

private def colXRules (sX : Nat) : List Rule := [
  { state := sX, inPat := .exact .zero, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step (sX + 1) .stay none .stay none .stay (some .one) .right },
  { state := sX, inPat := .exact .one,  w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step (sX + 2) .stay none .stay none .stay (some .one) .right },
  { state := sX, inPat := .exact .blank, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step (sX + 3) .stay none .stay none .stay (some .zero) .right },
  { state := sX + 1, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step sX .right none .stay none .stay (some .zero) .right },
  { state := sX + 2, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step sX .right none .stay none .stay (some .one) .right },
  { state := sX + 3, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step (sX + 4) .stay none .left none .stay (some .zero) .right }
]

private def colDrainRules (sDrain : Nat) : List Rule := [
  { state := sDrain, inPat := .any, w1Pat := .exact .one, w2Pat := .any, qPat := .any,
    act := .step sDrain .stay none .left none .stay (some .one) .right },
  { state := sDrain, inPat := .any, w1Pat := .exact .sep, w2Pat := .any, qPat := .any,
    act := .step (sDrain + 1) .stay none .stay none .stay none .stay }
]

private def colTailRules (sQuery : Nat) : List Rule := [
  { state := sQuery, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .query (sQuery + 1) (sQuery + 2) },
  { state := sQuery + 1, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .haltAccept },
  { state := sQuery + 2, inPat := .any, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .haltReject }
]

/-- Explicit 4-tape polynomial-time decider `collapseDecider V c d` for an `NP^A` language
    with verifier `V`, time exponent `c`, and witness exponent `d`. -/
public def collapseDecider (V : OTM) (c d : Nat) : OTM :=
  let sMulEnd := 2 + 5 * c
  let sX := sMulEnd + (colPrefBits V d).length
  let sDrain := sX + 4
  let sPad := sDrain + 1
  let sQuery := sPad + (c + 1)
  { rules := colInitRules ++ allMulRounds c ++ writeBitsRules sMulEnd (colPrefBits V d) ++
             colXRules sX ++ colDrainRules sDrain ++
             writeBitsRules sPad (List.replicate (c + 1) true) ++ colTailRules sQuery }

-- ============================================================================
-- Helper Lemmas for Rule Lookup in Disjoint State Blocks
-- ============================================================================

private theorem findAction_cons_rule (r : Rule) (rs : List Rule) (st : Nat) (sIn sW1 sW2 sQ : Sym) :
    findAction (r :: rs) st sIn sW1 sW2 sQ =
    if (r.state == st && r.inPat.matches sIn && r.w1Pat.matches sW1 &&
        r.w2Pat.matches sW2 && r.qPat.matches sQ)
    then r.act
    else findAction rs st sIn sW1 sW2 sQ := by
  unfold findAction
  simp only [List.find?_cons]
  cases (r.state == st && r.inPat.matches sIn && r.w1Pat.matches sW1 &&
         r.w2Pat.matches sW2 && r.qPat.matches sQ) <;> rfl

private theorem findAction_append_left (r1 r2 : List Rule) (st : Nat) (sIn sW1 sW2 sQ : Sym)
    (hnone : ∀ r ∈ r1, r.state ≠ st) :
    findAction (r1 ++ r2) st sIn sW1 sW2 sQ = findAction r2 st sIn sW1 sW2 sQ := by
  unfold findAction
  rw [List.find?_append]
  have h1 : r1.find? (fun r =>
      r.state == st && r.inPat.matches sIn && r.w1Pat.matches sW1 &&
      r.w2Pat.matches sW2 && r.qPat.matches sQ) = none := by
    rw [List.find?_eq_none]
    intro r hr htrue
    simp only [Bool.and_eq_true] at htrue
    exact hnone r hr (beq_iff_eq.mp htrue.1.1.1.1)
  rw [h1, Option.none_or]

private theorem findAction_append_right (r1 r2 : List Rule) (st : Nat) (sIn sW1 sW2 sQ : Sym)
    (hnone : ∀ r ∈ r2, r.state ≠ st) :
    findAction (r1 ++ r2) st sIn sW1 sW2 sQ = findAction r1 st sIn sW1 sW2 sQ := by
  unfold findAction
  rw [List.find?_append]
  have h2 : r2.find? (fun r =>
      r.state == st && r.inPat.matches sIn && r.w1Pat.matches sW1 &&
      r.w2Pat.matches sW2 && r.qPat.matches sQ) = none := by
    rw [List.find?_eq_none]
    intro r hr htrue
    simp only [Bool.and_eq_true] at htrue
    exact hnone r hr (beq_iff_eq.mp htrue.1.1.1.1)
  rw [h2]
  cases r1.find? (fun r =>
      r.state == st && r.inPat.matches sIn && r.w1Pat.matches sW1 &&
      r.w2Pat.matches sW2 && r.qPat.matches sQ) <;> rfl

private theorem mem_mulRoundRules_state (base next : Nat) (r : Rule)
    (hr : r ∈ mulRoundRules base next) :
    base ≤ r.state ∧ r.state < base + 5 := by
  simp only [mulRoundRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [] <;> omega

private theorem mem_allMulRounds_state (c : Nat) (r : Rule)
    (hr : r ∈ allMulRounds c) :
    2 ≤ r.state ∧ r.state < 2 + 5 * c := by
  unfold allMulRounds at hr
  rw [List.mem_flatMap] at hr
  rcases hr with ⟨j, hj, hrm⟩
  rw [List.mem_range] at hj
  have ⟨h1, h2⟩ := mem_mulRoundRules_state (2 + 5 * j) (2 + 5 * (j + 1)) r hrm
  omega

private theorem mem_writeBitsRules_state (base : Nat) (bs : List Bool) (r : Rule)
    (hr : r ∈ writeBitsRules base bs) :
    base ≤ r.state ∧ r.state < base + bs.length := by
  induction bs generalizing base with
  | nil => simp [writeBitsRules] at hr
  | cons b bs ih =>
    simp only [writeBitsRules, List.mem_cons] at hr
    rcases hr with rfl | hrest
    · simp
    · have ⟨h1, h2⟩ := ih (base + 1) hrest
      simp only [List.length_cons]
      omega

private theorem mem_colInit_range (r : Rule) (hr : r ∈ colInitRules) : r.state < 2 := by
  simp only [colInitRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> decide

private theorem mem_colX_range (sX : Nat) (r : Rule) (hr : r ∈ colXRules sX) :
    sX ≤ r.state ∧ r.state < sX + 4 := by
  simp only [colXRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

private theorem mem_colDrain_range (sDrain : Nat) (r : Rule) (hr : r ∈ colDrainRules sDrain) :
    r.state = sDrain := by
  simp only [colDrainRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rfl

private theorem mem_colTail_range (sQuery : Nat) (r : Rule) (hr : r ∈ colTailRules sQuery) :
    sQuery ≤ r.state ∧ r.state < sQuery + 3 := by
  simp only [colTailRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega

-- Direct symbolic evaluation lemmas for each small rule block (zero free-variable `decide` issues!)
private theorem beq_nat_false_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false := beq_false_of_ne h

private theorem sym_beq_eq (a b : Sym) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> rfl

private theorem findAction_mulRound_0 (base next : Nat) (sIn sW1 sW2 sQ : Sym) :
    findAction (mulRoundRules base next) base sIn sW1 sW2 sQ =
    Action.step (base + 1) .stay none .left none .stay none .stay := by
  unfold mulRoundRules
  rw [findAction_cons_rule]
  simp [SymPat.matches]

private theorem findAction_mulRound_1_one (base next : Nat) (sIn sW2 sQ : Sym) :
    findAction (mulRoundRules base next) (base + 1) sIn Sym.one sW2 sQ =
    Action.step (base + 2) .stay (some .blank) .stay none .stay none .stay := by
  unfold mulRoundRules
  rw [findAction_cons_rule, findAction_cons_rule]
  have h01 : (base == base + 1) = false := beq_false_of_ne (by omega)
  simp [h01, SymPat.matches, sym_beq_eq]

private theorem findAction_mulRound_1_sep (base next : Nat) (sIn sW2 sQ : Sym) :
    findAction (mulRoundRules base next) (base + 1) sIn Sym.sep sW2 sQ =
    Action.step (base + 4) .stay none .right none .left none .stay := by
  unfold mulRoundRules
  rw [findAction_cons_rule, findAction_cons_rule, findAction_cons_rule]
  have h01 : (base == base + 1) = false := beq_false_of_ne (by omega)
  simp [h01, SymPat.matches, sym_beq_eq]

private theorem findAction_mulRound_2_bit (base next : Nat) (b : Bool) (sW1 sW2 sQ : Sym) :
    findAction (mulRoundRules base next) (base + 2) (if b then Sym.one else Sym.zero) sW1 sW2 sQ =
    Action.step (base + 2) .right none .stay (some .one) .right none .right := by
  unfold mulRoundRules
  rw [findAction_cons_rule, findAction_cons_rule, findAction_cons_rule,
      findAction_cons_rule, findAction_cons_rule]
  have h02 : (base == base + 2) = false := beq_false_of_ne (by omega)
  have h12 : (base + 1 == base + 2) = false := beq_false_of_ne (by omega)
  cases b <;> simp [h02, h12, SymPat.matches, sym_beq_eq]

private theorem findAction_mulRound_2_blank (base next : Nat) (sW1 sW2 sQ : Sym) :
    findAction (mulRoundRules base next) (base + 2) Sym.blank sW1 sW2 sQ =
    Action.step (base + 3) .stay none .stay (some .one) .right none .stay := by
  unfold mulRoundRules
  rw [findAction_cons_rule, findAction_cons_rule, findAction_cons_rule,
      findAction_cons_rule, findAction_cons_rule, findAction_cons_rule]
  have h02 : (base == base + 2) = false := beq_false_of_ne (by omega)
  have h12 : (base + 1 == base + 2) = false := beq_false_of_ne (by omega)
  simp [h02, h12, SymPat.matches, sym_beq_eq]

private theorem findAction_mulRound_3_blank (base next : Nat) (sIn sW1 sW2 : Sym) :
    findAction (mulRoundRules base next) (base + 3) sIn sW1 sW2 Sym.blank =
    Action.step (base + 3) .left none .stay none .stay none .left := by
  unfold mulRoundRules
  rw [findAction_cons_rule, findAction_cons_rule, findAction_cons_rule,
      findAction_cons_rule, findAction_cons_rule, findAction_cons_rule,
      findAction_cons_rule]
  have h03 : (base == base + 3) = false := beq_false_of_ne (by omega)
  have h13 : (base + 1 == base + 3) = false := beq_false_of_ne (by omega)
  have h23 : (base + 2 == base + 3) = false := beq_false_of_ne (by omega)
  simp [h03, h13, h23, SymPat.matches, sym_beq_eq]

private theorem findAction_mulRound_3_sep (base next : Nat) (sIn sW1 sW2 : Sym) :
    findAction (mulRoundRules base next) (base + 3) sIn sW1 sW2 Sym.sep =
    Action.step (base + 1) .stay none .left none .stay none .stay := by
  unfold mulRoundRules
  rw [findAction_cons_rule, findAction_cons_rule, findAction_cons_rule,
      findAction_cons_rule, findAction_cons_rule, findAction_cons_rule,
      findAction_cons_rule, findAction_cons_rule]
  have h03 : (base == base + 3) = false := beq_false_of_ne (by omega)
  have h13 : (base + 1 == base + 3) = false := beq_false_of_ne (by omega)
  have h23 : (base + 2 == base + 3) = false := beq_false_of_ne (by omega)
  simp [h03, h13, h23, SymPat.matches, sym_beq_eq]

private theorem findAction_mulRound_4_one (base next : Nat) (sIn sW1 sQ : Sym) :
    findAction (mulRoundRules base next) (base + 4) sIn sW1 Sym.one sQ =
    Action.step (base + 4) .stay (some .one) .right (some .blank) .left none .stay := by
  unfold mulRoundRules
  rw [findAction_cons_rule, findAction_cons_rule, findAction_cons_rule,
      findAction_cons_rule, findAction_cons_rule, findAction_cons_rule,
      findAction_cons_rule, findAction_cons_rule, findAction_cons_rule]
  have h04 : (base == base + 4) = false := beq_false_of_ne (by omega)
  have h14 : (base + 1 == base + 4) = false := beq_false_of_ne (by omega)
  have h24 : (base + 2 == base + 4) = false := beq_false_of_ne (by omega)
  have h34 : (base + 3 == base + 4) = false := beq_false_of_ne (by omega)
  simp [h04, h14, h24, h34, SymPat.matches, sym_beq_eq]

private theorem findAction_mulRound_4_sep (base next : Nat) (sIn sW1 sQ : Sym) :
    findAction (mulRoundRules base next) (base + 4) sIn sW1 Sym.sep sQ =
    Action.step next .stay none .stay none .right none .stay := by
  unfold mulRoundRules
  rw [findAction_cons_rule, findAction_cons_rule, findAction_cons_rule,
      findAction_cons_rule, findAction_cons_rule, findAction_cons_rule,
      findAction_cons_rule, findAction_cons_rule, findAction_cons_rule,
      findAction_cons_rule]
  have h04 : (base == base + 4) = false := beq_false_of_ne (by omega)
  have h14 : (base + 1 == base + 4) = false := beq_false_of_ne (by omega)
  have h24 : (base + 2 == base + 4) = false := beq_false_of_ne (by omega)
  have h34 : (base + 3 == base + 4) = false := beq_false_of_ne (by omega)
  simp [h04, h14, h24, h34, SymPat.matches, sym_beq_eq]

private theorem findAction_colX_0_zero (sX : Nat) (sW1 sW2 sQ : Sym) :
    findAction (colXRules sX) sX Sym.zero sW1 sW2 sQ =
    Action.step (sX + 1) .stay none .stay none .stay (some .one) .right := by
  unfold colXRules; rw [findAction_cons_rule]; simp [SymPat.matches, sym_beq_eq]

private theorem findAction_colX_0_one (sX : Nat) (sW1 sW2 sQ : Sym) :
    findAction (colXRules sX) sX Sym.one sW1 sW2 sQ =
    Action.step (sX + 2) .stay none .stay none .stay (some .one) .right := by
  unfold colXRules; rw [findAction_cons_rule, findAction_cons_rule]; simp [SymPat.matches, sym_beq_eq]

private theorem findAction_colX_0_blank (sX : Nat) (sW1 sW2 sQ : Sym) :
    findAction (colXRules sX) sX Sym.blank sW1 sW2 sQ =
    Action.step (sX + 3) .stay none .stay none .stay (some .zero) .right := by
  unfold colXRules
  rw [findAction_cons_rule, findAction_cons_rule, findAction_cons_rule]
  simp [SymPat.matches, sym_beq_eq]

private theorem findAction_colX_1 (sX : Nat) (sIn sW1 sW2 sQ : Sym) :
    findAction (colXRules sX) (sX + 1) sIn sW1 sW2 sQ =
    Action.step sX .right none .stay none .stay (some .zero) .right := by
  unfold colXRules
  rw [findAction_cons_rule, findAction_cons_rule, findAction_cons_rule, findAction_cons_rule]
  have h01 : (sX == sX + 1) = false := beq_false_of_ne (by omega)
  simp [h01, SymPat.matches, sym_beq_eq]

private theorem findAction_colX_2 (sX : Nat) (sIn sW1 sW2 sQ : Sym) :
    findAction (colXRules sX) (sX + 2) sIn sW1 sW2 sQ =
    Action.step sX .right none .stay none .stay (some .one) .right := by
  unfold colXRules
  rw [findAction_cons_rule, findAction_cons_rule, findAction_cons_rule,
      findAction_cons_rule, findAction_cons_rule]
  have h02 : (sX == sX + 2) = false := beq_false_of_ne (by omega)
  have h12 : (sX + 1 == sX + 2) = false := beq_false_of_ne (by omega)
  simp [h02, h12, SymPat.matches, sym_beq_eq]

private theorem findAction_colX_3 (sX : Nat) (sIn sW1 sW2 sQ : Sym) :
    findAction (colXRules sX) (sX + 3) sIn sW1 sW2 sQ =
    Action.step (sX + 4) .stay none .left none .stay (some .zero) .right := by
  unfold colXRules
  rw [findAction_cons_rule, findAction_cons_rule, findAction_cons_rule,
      findAction_cons_rule, findAction_cons_rule, findAction_cons_rule]
  have h03 : (sX == sX + 3) = false := beq_false_of_ne (by omega)
  have h13 : (sX + 1 == sX + 3) = false := beq_false_of_ne (by omega)
  have h23 : (sX + 2 == sX + 3) = false := beq_false_of_ne (by omega)
  simp [h03, h13, h23, SymPat.matches, sym_beq_eq]

private theorem findAction_colDrain_one (sDrain : Nat) (sIn sW2 sQ : Sym) :
    findAction (colDrainRules sDrain) sDrain sIn Sym.one sW2 sQ =
    Action.step sDrain .stay none .left none .stay (some .one) .right := by
  unfold colDrainRules; rw [findAction_cons_rule]; simp [SymPat.matches, sym_beq_eq]

private theorem findAction_colDrain_sep (sDrain : Nat) (sIn sW2 sQ : Sym) :
    findAction (colDrainRules sDrain) sDrain sIn Sym.sep sW2 sQ =
    Action.step (sDrain + 1) .stay none .stay none .stay none .stay := by
  unfold colDrainRules; rw [findAction_cons_rule, findAction_cons_rule]; simp [SymPat.matches, sym_beq_eq]

private theorem findAction_colTail_0 (sQuery : Nat) (sIn sW1 sW2 sQ : Sym) :
    findAction (colTailRules sQuery) sQuery sIn sW1 sW2 sQ =
    Action.query (sQuery + 1) (sQuery + 2) := by
  unfold colTailRules; rw [findAction_cons_rule]; simp [SymPat.matches]

private theorem findAction_colTail_1 (sQuery : Nat) (sIn sW1 sW2 sQ : Sym) :
    findAction (colTailRules sQuery) (sQuery + 1) sIn sW1 sW2 sQ = Action.haltAccept := by
  unfold colTailRules; rw [findAction_cons_rule, findAction_cons_rule]
  have h01 : (sQuery == sQuery + 1) = false := beq_false_of_ne (by omega)
  simp [h01, SymPat.matches]

private theorem findAction_colTail_2 (sQuery : Nat) (sIn sW1 sW2 sQ : Sym) :
    findAction (colTailRules sQuery) (sQuery + 2) sIn sW1 sW2 sQ = Action.haltReject := by
  unfold colTailRules; rw [findAction_cons_rule, findAction_cons_rule, findAction_cons_rule]
  have h02 : (sQuery == sQuery + 2) = false := beq_false_of_ne (by omega)
  have h12 : (sQuery + 1 == sQuery + 2) = false := beq_false_of_ne (by omega)
  simp [h02, h12, SymPat.matches]

private theorem findAction_writeBitsRules (base : Nat) (bs : List Bool) (i : Nat)
    (hi : i < bs.length) (sIn sW1 sW2 sQ : Sym) :
    findAction (writeBitsRules base bs) (base + i) sIn sW1 sW2 sQ =
    Action.step (base + i + 1) .stay none .stay none .stay
      (some (if bs[i] then .one else .zero)) .right := by
  induction bs generalizing base i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero =>
      simp only [writeBitsRules, Nat.add_zero, List.getElem_cons_zero]
      rw [findAction_cons_rule]
      simp [SymPat.matches]
    | succ i =>
      simp only [writeBitsRules]
      have hne : base ≠ base + (i + 1) := by omega
      rw [findAction_cons_rule]
      have hbeq : (base == base + (i + 1)) = false := beq_false_of_ne hne
      simp only [hbeq, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      have heq : base + (i + 1) = (base + 1) + i := by omega
      rw [heq, ih (base + 1) i (by simp at hi; omega)]
      simp

private theorem findAction_allMulRounds (c j : Nat) (hj : j < c) (off : Nat) (hoff : off < 5)
    (sIn sW1 sW2 sQ : Sym) :
    findAction (allMulRounds c) (2 + 5 * j + off) sIn sW1 sW2 sQ =
    findAction (mulRoundRules (2 + 5 * j) (2 + 5 * (j + 1))) (2 + 5 * j + off) sIn sW1 sW2 sQ := by
  have haux : ∀ k, j < k →
      findAction ((List.range k).flatMap (fun m => mulRoundRules (2 + 5 * m) (2 + 5 * (m + 1))))
        (2 + 5 * j + off) sIn sW1 sW2 sQ =
      findAction (mulRoundRules (2 + 5 * j) (2 + 5 * (j + 1))) (2 + 5 * j + off) sIn sW1 sW2 sQ := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      by_cases hjk : j = k
      · subst hjk
        rw [findAction_append_left]
        intro r hr
        have ⟨_, h2⟩ := mem_allMulRounds_state j r hr
        omega
      · rw [findAction_append_right]
        · exact ih (by omega)
        · intro r hr
          have ⟨h1, _⟩ := mem_mulRoundRules_state (2 + 5 * k) (2 + 5 * (k + 1)) r hr
          omega
  exact haux c hj

private theorem collapseDecider_rules_eq (V : OTM) (c d : Nat) :
    let sMulEnd := 2 + 5 * c
    let sX := sMulEnd + (colPrefBits V d).length
    let sDrain := sX + 4
    let sPad := sDrain + 1
    let sQuery := sPad + (c + 1)
    (collapseDecider V c d).rules =
      colInitRules ++ allMulRounds c ++ writeBitsRules sMulEnd (colPrefBits V d) ++
      colXRules sX ++ colDrainRules sDrain ++
      writeBitsRules sPad (List.replicate (c + 1) true) ++ colTailRules sQuery := rfl

private theorem colDec_lookup_0 (V : OTM) (c d : Nat) (sIn sW1 sW2 sQ : Sym) :
    findAction (collapseDecider V c d).rules 0 sIn sW1 sW2 sQ =
    Action.step 1 .stay (some .sep) .right (some .sep) .right (some .sep) .stay := by
  rw [collapseDecider_rules_eq]
  simp only [List.append_assoc, colInitRules, List.cons_append]
  rw [findAction_cons_rule]
  simp [SymPat.matches]

private theorem colDec_lookup_1 (V : OTM) (c d : Nat) (sIn sW1 sW2 sQ : Sym) :
    findAction (collapseDecider V c d).rules 1 sIn sW1 sW2 sQ =
    Action.step 2 .stay (some .one) .right none .stay none .stay := by
  rw [collapseDecider_rules_eq]
  simp only [List.append_assoc, colInitRules, List.cons_append]
  rw [findAction_cons_rule, findAction_cons_rule]
  simp [SymPat.matches]

private theorem colDec_lookup_mul (V : OTM) (c d j off : Nat) (hj : j < c) (hoff : off < 5)
    (sIn sW1 sW2 sQ : Sym) :
    findAction (collapseDecider V c d).rules (2 + 5 * j + off) sIn sW1 sW2 sQ =
    findAction (mulRoundRules (2 + 5 * j) (2 + 5 * (j + 1))) (2 + 5 * j + off) sIn sW1 sW2 sQ := by
  rw [collapseDecider_rules_eq]
  simp only [List.append_assoc]
  rw [findAction_append_left colInitRules _ _ _ _ _ _ (by intro r hr; have := mem_colInit_range r hr; omega)]
  rw [findAction_append_right (allMulRounds c) _ _ _ _ _ _ (by
    intro r hr
    simp only [List.mem_append] at hr
    rcases hr with h | h | h | h | h
    · have := (mem_writeBitsRules_state _ _ r h).1; omega
    · have := (mem_colX_range _ r h).1; omega
    · have := mem_colDrain_range _ r h; omega
    · have := (mem_writeBitsRules_state _ _ r h).1; omega
    · have := (mem_colTail_range _ r h).1; omega)]
  exact findAction_allMulRounds c j hj off hoff sIn sW1 sW2 sQ

private theorem colDec_lookup_pref (V : OTM) (c d i : Nat) (hi : i < (colPrefBits V d).length)
    (sIn sW1 sW2 sQ : Sym) :
    findAction (collapseDecider V c d).rules (2 + 5 * c + i) sIn sW1 sW2 sQ =
    Action.step (2 + 5 * c + i + 1) .stay none .stay none .stay
      (some (if (colPrefBits V d)[i] then .one else .zero)) .right := by
  rw [collapseDecider_rules_eq]
  simp only [List.append_assoc]
  rw [findAction_append_left colInitRules _ _ _ _ _ _ (by intro r hr; have := mem_colInit_range r hr; omega)]
  rw [findAction_append_left (allMulRounds c) _ _ _ _ _ _ (by intro r hr; have := (mem_allMulRounds_state c r hr).2; omega)]
  rw [findAction_append_right (writeBitsRules (2 + 5 * c) (colPrefBits V d)) _ _ _ _ _ _ (by
    intro r hr
    simp only [List.mem_append] at hr
    rcases hr with h | h | h | h
    · have := (mem_colX_range _ r h).1; omega
    · have := mem_colDrain_range _ r h; omega
    · have := (mem_writeBitsRules_state _ _ r h).1; omega
    · have := (mem_colTail_range _ r h).1; omega)]
  exact findAction_writeBitsRules (2 + 5 * c) (colPrefBits V d) i hi sIn sW1 sW2 sQ

private theorem colDec_lookup_x (V : OTM) (c d off : Nat) (hoff : off < 4) (sIn sW1 sW2 sQ : Sym) :
    let sX := 2 + 5 * c + (colPrefBits V d).length
    findAction (collapseDecider V c d).rules (sX + off) sIn sW1 sW2 sQ =
    findAction (colXRules sX) (sX + off) sIn sW1 sW2 sQ := by
  dsimp only
  rw [collapseDecider_rules_eq]
  simp only [List.append_assoc]
  rw [findAction_append_left colInitRules _ _ _ _ _ _ (by intro r hr; have := mem_colInit_range r hr; omega)]
  rw [findAction_append_left (allMulRounds c) _ _ _ _ _ _ (by intro r hr; have := (mem_allMulRounds_state c r hr).2; omega)]
  rw [findAction_append_left (writeBitsRules _ _) _ _ _ _ _ _ (by intro r hr; have := (mem_writeBitsRules_state _ _ r hr).2; omega)]
  rw [findAction_append_right (colXRules _) _ _ _ _ _ _ (by
    intro r hr
    simp only [List.mem_append] at hr
    rcases hr with h | h | h
    · have := mem_colDrain_range _ r h; omega
    · have := (mem_writeBitsRules_state _ _ r h).1; omega
    · have := (mem_colTail_range _ r h).1; omega)]

private theorem colDec_lookup_drain (V : OTM) (c d : Nat) (sIn sW1 sW2 sQ : Sym) :
    let sDrain := 2 + 5 * c + (colPrefBits V d).length + 4
    findAction (collapseDecider V c d).rules sDrain sIn sW1 sW2 sQ =
    findAction (colDrainRules sDrain) sDrain sIn sW1 sW2 sQ := by
  dsimp only
  rw [collapseDecider_rules_eq]
  simp only [List.append_assoc]
  rw [findAction_append_left colInitRules _ _ _ _ _ _ (by intro r hr; have := mem_colInit_range r hr; omega)]
  rw [findAction_append_left (allMulRounds c) _ _ _ _ _ _ (by intro r hr; have := (mem_allMulRounds_state c r hr).2; omega)]
  rw [findAction_append_left (writeBitsRules _ _) _ _ _ _ _ _ (by intro r hr; have := (mem_writeBitsRules_state _ _ r hr).2; omega)]
  rw [findAction_append_left (colXRules _) _ _ _ _ _ _ (by intro r hr; have := (mem_colX_range _ r hr).2; omega)]
  rw [findAction_append_right (colDrainRules _) _ _ _ _ _ _ (by
    intro r hr
    simp only [List.mem_append] at hr
    rcases hr with h | h
    · have := (mem_writeBitsRules_state _ _ r h).1; omega
    · have := (mem_colTail_range _ r h).1; omega)]

private theorem colDec_lookup_pad (V : OTM) (c d i : Nat) (hi : i < (List.replicate (c + 1) true).length)
    (sIn sW1 sW2 sQ : Sym) :
    let sPad := 2 + 5 * c + (colPrefBits V d).length + 5
    findAction (collapseDecider V c d).rules (sPad + i) sIn sW1 sW2 sQ =
    Action.step (sPad + i + 1) .stay none .stay none .stay
      (some (if (List.replicate (c + 1) true)[i] then .one else .zero)) .right := by
  dsimp only
  rw [collapseDecider_rules_eq]
  simp only [List.append_assoc]
  rw [findAction_append_left colInitRules _ _ _ _ _ _ (by intro r hr; have := mem_colInit_range r hr; omega)]
  rw [findAction_append_left (allMulRounds c) _ _ _ _ _ _ (by intro r hr; have := (mem_allMulRounds_state c r hr).2; omega)]
  rw [findAction_append_left (writeBitsRules _ _) _ _ _ _ _ _ (by intro r hr; have := (mem_writeBitsRules_state _ _ r hr).2; omega)]
  rw [findAction_append_left (colXRules _) _ _ _ _ _ _ (by intro r hr; have := (mem_colX_range _ r hr).2; omega)]
  rw [findAction_append_left (colDrainRules _) _ _ _ _ _ _ (by intro r hr; have := mem_colDrain_range _ r hr; omega)]
  rw [findAction_append_right (writeBitsRules _ _) _ _ _ _ _ _ (by
    intro r hr
    have := (mem_colTail_range _ r hr).1
    simp only [List.length_replicate] at hi
    omega)]
  exact findAction_writeBitsRules _ (List.replicate (c + 1) true) i hi sIn sW1 sW2 sQ

private theorem colDec_lookup_tail (V : OTM) (c d off : Nat) (hoff : off < 3) (sIn sW1 sW2 sQ : Sym) :
    let sQuery := 2 + 5 * c + (colPrefBits V d).length + 5 + (c + 1)
    findAction (collapseDecider V c d).rules (sQuery + off) sIn sW1 sW2 sQ =
    findAction (colTailRules sQuery) (sQuery + off) sIn sW1 sW2 sQ := by
  dsimp only
  rw [collapseDecider_rules_eq]
  simp only [List.append_assoc]
  rw [findAction_append_left colInitRules _ _ _ _ _ _ (by intro r hr; have := mem_colInit_range r hr; omega)]
  rw [findAction_append_left (allMulRounds c) _ _ _ _ _ _ (by intro r hr; have := (mem_allMulRounds_state c r hr).2; omega)]
  rw [findAction_append_left (writeBitsRules _ _) _ _ _ _ _ _ (by intro r hr; have := (mem_writeBitsRules_state _ _ r hr).2; omega)]
  rw [findAction_append_left (colXRules _) _ _ _ _ _ _ (by intro r hr; have := (mem_colX_range _ r hr).2; omega)]
  rw [findAction_append_left (colDrainRules _) _ _ _ _ _ _ (by intro r hr; have := mem_colDrain_range _ r hr; omega)]
  rw [findAction_append_left (writeBitsRules _ _) _ _ _ _ _ _ (by
    intro r hr
    have := (mem_writeBitsRules_state _ _ r hr).2
    simp only [List.length_replicate] at this
    omega)]

-- ============================================================================
-- Part 4: Exact Phase Execution Proofs
-- ============================================================================

private theorem run_writeBits_block (O : Oracle) (M : OTM) (base : Nat) (bs : List Bool)
    (hblock : ∀ i (hi : i < bs.length), ∀ sIn sW1 sW2 sQ,
      findAction M.rules (base + i) sIn sW1 sW2 sQ =
      Action.step (base + i + 1) .stay none .stay none .stay
        (some (if bs[i]'hi then .one else .zero)) .right)
    (cfg : Config) (pref : List Bool)
    (hst : cfg.state = base) (hh : cfg.halted = none)
    (hqh : cfg.qHead = pref.length)
    (hqt : ∀ idx < pref.length, cfg.qTape idx = if pref.getD idx false then Sym.one else Sym.zero) :
    let cfgF := run O M bs.length cfg
    cfgF.state = base + bs.length ∧
    cfgF.halted = none ∧
    cfgF.inTape = cfg.inTape ∧ cfgF.inHead = cfg.inHead ∧
    cfgF.w1Tape = cfg.w1Tape ∧ cfgF.w1Head = cfg.w1Head ∧
    cfgF.w2Tape = cfg.w2Tape ∧ cfgF.w2Head = cfg.w2Head ∧
    cfgF.qHead = (pref ++ bs).length ∧
    ∀ idx < (pref ++ bs).length,
      cfgF.qTape idx = if (pref ++ bs).getD idx false then Sym.one else Sym.zero := by
  induction bs generalizing base cfg pref with
  | nil =>
    dsimp only
    rw [List.length_nil, Nat.add_zero, run_zero, List.append_nil]
    exact ⟨hst, hh, rfl, rfl, rfl, rfl, rfl, rfl, hqh, hqt⟩
  | cons b bs ih =>
    dsimp only
    rw [List.length_cons, show bs.length + 1 = 1 + bs.length from by omega, run_add, run_succ, run_zero]
    have hact0 := hblock 0 (by simp) (cfg.inTape cfg.inHead) (cfg.w1Tape cfg.w1Head)
      (cfg.w2Tape cfg.w2Head) (cfg.qTape cfg.qHead)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hact0
    rw [← hst] at hact0
    rw [stepLog_eq_step O M cfg hh hact0, hst]
    have hwn : ∀ t p, writeOpt t p none = t := fun _ _ => rfl
    simp only [moveHead, hwn]
    have hblock' : ∀ i (hi : i < bs.length), ∀ sIn sW1 sW2 sQ,
        findAction M.rules (base + 1 + i) sIn sW1 sW2 sQ =
        Action.step (base + 1 + i + 1) .stay none .stay none .stay
          (some (if bs[i]'hi then .one else .zero)) .right := by
      intro i hi sIn sW1 sW2 sQ
      have h := hblock (i + 1) (by simp; omega) sIn sW1 sW2 sQ
      have ha : base + (i + 1) = base + 1 + i := by omega
      rw [ha] at h
      simpa using h
    have hqt' : ∀ idx < (pref ++ [b]).length,
        writeOpt cfg.qTape cfg.qHead (some (if b then Sym.one else Sym.zero)) idx =
        if (pref ++ [b]).getD idx false then Sym.one else Sym.zero := by
      intro idx hidx
      unfold writeOpt
      rw [hqh]
      simp only [List.length_append, List.length_singleton] at hidx
      by_cases heq : idx = pref.length
      · subst heq
        simp only [beq_self_eq_true, ↓reduceIte, List.getD_eq_getElem?_getD,
                   List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
                   List.getElem?_cons_zero, Option.getD_some]
      · have hbeq : (idx == pref.length) = false := beq_false_of_ne heq
        have hlt : idx < pref.length := by omega
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.getD_eq_getElem?_getD,
                   List.getElem?_append_left hlt]
        have := hqt idx hlt
        simpa [List.getD_eq_getElem?_getD] using this
    have hrec := ih (base + 1) hblock'
      { cfg with
          state := base + 1
          qTape := writeOpt cfg.qTape cfg.qHead (some (if b then Sym.one else Sym.zero))
          qHead := cfg.qHead + 1 }
      (pref ++ [b]) rfl hh (by simp [hqh]) hqt'
    dsimp only at hrec
    simp only [List.append_assoc, List.singleton_append] at hrec ⊢
    refine ⟨by omega, hrec.2.1, hrec.2.2.1, hrec.2.2.2.1, hrec.2.2.2.2.1,
            hrec.2.2.2.2.2.1, hrec.2.2.2.2.2.2.1, hrec.2.2.2.2.2.2.2.1,
            hrec.2.2.2.2.2.2.2.2.1, hrec.2.2.2.2.2.2.2.2.2⟩

private theorem col_in_at_lt (x : List Bool) (i : Nat) (hi : i < x.length) :
    tapeOfList (encodeBits x) i = if x[i] then Sym.one else Sym.zero := by
  unfold tapeOfList encodeBits
  simp [List.getD_eq_getElem?_getD, hi]

private theorem col_in_at_end (x : List Bool) :
    tapeOfList (encodeBits x) x.length = Sym.blank := by
  unfold tapeOfList encodeBits
  simp [List.getD_eq_getElem?_getD]

private theorem writeOpt_colMarkedOnes_succ (k : Nat) :
    writeOpt (colMarkedOnes k) (k + 1) (some Sym.one) = colMarkedOnes (k + 1) := by
  funext i
  unfold writeOpt colMarkedOnes
  by_cases hi : i = k + 1
  · subst hi
    have h0 : (k + 1 == 0) = false := beq_false_of_ne (by omega)
    simp [h0]
  · have hbeq : (i == k + 1) = false := beq_false_of_ne hi
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : i = 0
    · subst h0; rfl
    · have hb0 : (i == 0) = false := beq_false_of_ne h0
      simp only [hb0, Bool.false_eq_true, ↓reduceIte]
      have hiff : (i ≤ k) ↔ (i ≤ k + 1) := by omega
      by_cases hle : i ≤ k <;> simp [hle, show (i ≤ k + 1) ↔ (i ≤ k) from hiff.symm]

private theorem writeOpt_colMarkedOnes_erase (k : Nat) :
    writeOpt (colMarkedOnes (k + 1)) (k + 1) (some Sym.blank) = colMarkedOnes k := by
  funext i
  unfold writeOpt colMarkedOnes
  by_cases hi : i = k + 1
  · subst hi
    have h0 : (k + 1 == 0) = false := beq_false_of_ne (by omega)
    have hle : ¬ (k + 1 ≤ k) := by omega
    simp [h0, hle]
  · have hbeq : (i == k + 1) = false := beq_false_of_ne hi
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : i = 0
    · subst h0; rfl
    · have hb0 : (i == 0) = false := beq_false_of_ne h0
      simp only [hb0, Bool.false_eq_true, ↓reduceIte]
      have hiff : (i ≤ k + 1) ↔ (i ≤ k) := by omega
      by_cases hle : i ≤ k <;> simp [hle, show (i ≤ k + 1) ↔ (i ≤ k) from hiff]

private theorem run_mulRound_inner_fwd (O : Oracle) (M : OTM) (base next : Nat) (x : List Bool)
    (hblock : ∀ off < 5, ∀ sIn sW1 sW2 sQ,
      findAction M.rules (base + off) sIn sW1 sW2 sQ =
      findAction (mulRoundRules base next) (base + off) sIn sW1 sW2 sQ)
    (w1T : Nat → Sym) (w1H : Nat) (acc : Nat) :
    ∀ k ≤ x.length,
    run O M k
      { state := base + 2, inTape := tapeOfList (encodeBits x), inHead := 0,
        w1Tape := w1T, w1Head := w1H,
        w2Tape := colMarkedOnes acc, w2Head := acc + 1,
        qTape := colMarkedOnes 0, qHead := 0, halted := none } =
    { state := base + 2, inTape := tapeOfList (encodeBits x), inHead := k,
      w1Tape := w1T, w1Head := w1H,
      w2Tape := colMarkedOnes (acc + k), w2Head := acc + k + 1,
      qTape := colMarkedOnes 0, qHead := k, halted := none } := by
  intro k hk
  induction k with
  | zero => simp [run_zero]
  | succ k ih =>
    rw [run_add O M k 1, ih (by omega), run_succ, run_zero]
    have hsym := col_in_at_lt x k (by omega)
    have hact : findAction M.rules (base + 2)
        (tapeOfList (encodeBits x) k) (w1T w1H)
        (colMarkedOnes (acc + k) (acc + k + 1)) (colMarkedOnes 0 k) =
        Action.step (base + 2) .right none .stay (some .one) .right none .right := by
      rw [hblock 2 (by decide), hsym]
      exact findAction_mulRound_2_bit base next x[k] ..
    rw [stepLog_eq_step O M _ rfl hact, writeOpt_colMarkedOnes_succ]
    simp only [moveHead, writeOpt]
    have h1 : acc + k + 1 = acc + (k + 1) := by omega
    rw [h1]

private theorem run_mulRound_inner_rev (O : Oracle) (M : OTM) (base next : Nat) (x : List Bool)
    (hblock : ∀ off < 5, ∀ sIn sW1 sW2 sQ,
      findAction M.rules (base + off) sIn sW1 sW2 sQ =
      findAction (mulRoundRules base next) (base + off) sIn sW1 sW2 sQ)
    (w1T : Nat → Sym) (w1H : Nat) (w2T : Nat → Sym) (w2H : Nat) :
    ∀ k : Nat,
    run O M k
      { state := base + 3, inTape := tapeOfList (encodeBits x), inHead := k,
        w1Tape := w1T, w1Head := w1H,
        w2Tape := w2T, w2Head := w2H,
        qTape := colMarkedOnes 0, qHead := k, halted := none } =
    { state := base + 3, inTape := tapeOfList (encodeBits x), inHead := 0,
      w1Tape := w1T, w1Head := w1H,
      w2Tape := w2T, w2Head := w2H,
      qTape := colMarkedOnes 0, qHead := 0, halted := none } := by
  intro k
  induction k with
  | zero => rw [run_zero]
  | succ k ih =>
    rw [run_succ]
    have hq : colMarkedOnes 0 (k + 1) = Sym.blank := by
      unfold colMarkedOnes
      have h0 : (k + 1 == 0) = false := beq_false_of_ne (by omega)
      simp [h0]
    have hact : findAction M.rules (base + 3)
        (tapeOfList (encodeBits x) (k + 1)) (w1T w1H) (w2T w2H) (colMarkedOnes 0 (k + 1)) =
        Action.step (base + 3) .left none .stay none .stay none .left := by
      rw [hblock 3 (by decide), hq]
      exact findAction_mulRound_3_blank base next ..
    rw [stepLog_eq_step O M _ rfl hact]
    simp only [moveHead, writeOpt, Nat.add_sub_cancel]
    exact ih

private theorem run_mulRound_outer (O : Oracle) (M : OTM) (base next : Nat) (x : List Bool)
    (hblock : ∀ off < 5, ∀ sIn sW1 sW2 sQ,
      findAction M.rules (base + off) sIn sW1 sW2 sQ =
      findAction (mulRoundRules base next) (base + off) sIn sW1 sW2 sQ) :
    ∀ m acc : Nat,
    run O M (m * (2 * x.length + 3))
      { state := base + 1, inTape := tapeOfList (encodeBits x), inHead := 0,
        w1Tape := colMarkedOnes m, w1Head := m,
        w2Tape := colMarkedOnes acc, w2Head := acc + 1,
        qTape := colMarkedOnes 0, qHead := 0, halted := none } =
    { state := base + 1, inTape := tapeOfList (encodeBits x), inHead := 0,
      w1Tape := colMarkedOnes 0, w1Head := 0,
      w2Tape := colMarkedOnes (acc + m * (x.length + 1)), w2Head := acc + m * (x.length + 1) + 1,
      qTape := colMarkedOnes 0, qHead := 0, halted := none } := by
  intro m
  induction m with
  | zero =>
    intro acc; simp [run_zero]
  | succ m ih =>
    intro acc
    have hsplit : (m + 1) * (2 * x.length + 3) =
        (1 + x.length + 1 + x.length + 1) + m * (2 * x.length + 3) := by
      rw [Nat.succ_mul]; omega
    rw [hsplit,
        run_add O M (1 + x.length + 1 + x.length + 1) (m * (2 * x.length + 3)),
        run_add O M (1 + x.length + 1 + x.length) 1,
        run_add O M (1 + x.length + 1) x.length,
        run_add O M (1 + x.length) 1,
        run_add O M 1 x.length]
    have hs1 :
        run O M 1
          { state := base + 1, inTape := tapeOfList (encodeBits x), inHead := 0,
            w1Tape := colMarkedOnes (m + 1), w1Head := m + 1,
            w2Tape := colMarkedOnes acc, w2Head := acc + 1,
            qTape := colMarkedOnes 0, qHead := 0, halted := none } =
        { state := base + 2, inTape := tapeOfList (encodeBits x), inHead := 0,
          w1Tape := colMarkedOnes m, w1Head := m + 1,
          w2Tape := colMarkedOnes acc, w2Head := acc + 1,
          qTape := colMarkedOnes 0, qHead := 0, halted := none } := by
      rw [run_succ, run_zero]
      have hw1 : colMarkedOnes (m + 1) (m + 1) = Sym.one := by
        unfold colMarkedOnes
        have h0 : (m + 1 == 0) = false := beq_false_of_ne (by omega)
        simp [h0]
      have hact1 : findAction M.rules (base + 1)
          (tapeOfList (encodeBits x) 0) (colMarkedOnes (m + 1) (m + 1))
          (colMarkedOnes acc (acc + 1)) (colMarkedOnes 0 0) =
          Action.step (base + 2) .stay (some .blank) .stay none .stay none .stay := by
        rw [hblock 1 (by decide), hw1]
        exact findAction_mulRound_1_one base next ..
      rw [stepLog_eq_step O M _ rfl hact1, writeOpt_colMarkedOnes_erase]
      simp only [moveHead, writeOpt]
    rw [hs1]
    rw [run_mulRound_inner_fwd O M base next x hblock (colMarkedOnes m) (m + 1) acc x.length (Nat.le_refl _)]
    have hs2 :
        run O M 1
          { state := base + 2, inTape := tapeOfList (encodeBits x), inHead := x.length,
            w1Tape := colMarkedOnes m, w1Head := m + 1,
            w2Tape := colMarkedOnes (acc + x.length), w2Head := acc + x.length + 1,
            qTape := colMarkedOnes 0, qHead := x.length, halted := none } =
        { state := base + 3, inTape := tapeOfList (encodeBits x), inHead := x.length,
          w1Tape := colMarkedOnes m, w1Head := m + 1,
          w2Tape := colMarkedOnes (acc + x.length + 1), w2Head := acc + x.length + 1 + 1,
          qTape := colMarkedOnes 0, qHead := x.length, halted := none } := by
      rw [run_succ, run_zero]
      have hend := col_in_at_end x
      have hact2 : findAction M.rules (base + 2)
          (tapeOfList (encodeBits x) x.length) (colMarkedOnes m (m + 1))
          (colMarkedOnes (acc + x.length) (acc + x.length + 1)) (colMarkedOnes 0 x.length) =
          Action.step (base + 3) .stay none .stay (some .one) .right none .stay := by
        rw [hblock 2 (by decide), hend]
        exact findAction_mulRound_2_blank base next ..
      rw [stepLog_eq_step O M _ rfl hact2, writeOpt_colMarkedOnes_succ]
      simp only [moveHead, writeOpt]
    rw [hs2]
    rw [run_mulRound_inner_rev O M base next x hblock (colMarkedOnes m) (m + 1)
          (colMarkedOnes (acc + x.length + 1)) (acc + x.length + 1 + 1) x.length]
    have hs3 :
        run O M 1
          { state := base + 3, inTape := tapeOfList (encodeBits x), inHead := 0,
            w1Tape := colMarkedOnes m, w1Head := m + 1,
            w2Tape := colMarkedOnes (acc + x.length + 1), w2Head := acc + x.length + 1 + 1,
            qTape := colMarkedOnes 0, qHead := 0, halted := none } =
        { state := base + 1, inTape := tapeOfList (encodeBits x), inHead := 0,
          w1Tape := colMarkedOnes m, w1Head := m,
          w2Tape := colMarkedOnes (acc + x.length + 1), w2Head := acc + x.length + 1 + 1,
          qTape := colMarkedOnes 0, qHead := 0, halted := none } := by
      rw [run_succ, run_zero]
      have hq0 : colMarkedOnes 0 0 = Sym.sep := rfl
      have hact3 : findAction M.rules (base + 3)
          (tapeOfList (encodeBits x) 0) (colMarkedOnes m (m + 1))
          (colMarkedOnes (acc + x.length + 1) (acc + x.length + 1 + 1)) (colMarkedOnes 0 0) =
          Action.step (base + 1) .stay none .left none .stay none .stay := by
        rw [hblock 3 (by decide), hq0]
        exact findAction_mulRound_3_sep base next ..
      rw [stepLog_eq_step O M _ rfl hact3]
      simp only [moveHead, writeOpt, Nat.add_sub_cancel]
    rw [hs3]
    rw [ih (acc + x.length + 1)]
    have heq : acc + x.length + 1 + m * (x.length + 1) = acc + (m + 1) * (x.length + 1) := by
      rw [Nat.succ_mul]; omega
    rw [heq]

private theorem run_mulRound_copyback (O : Oracle) (M : OTM) (base next : Nat) (x : List Bool)
    (hblock : ∀ off < 5, ∀ sIn sW1 sW2 sQ,
      findAction M.rules (base + off) sIn sW1 sW2 sQ =
      findAction (mulRoundRules base next) (base + off) sIn sW1 sW2 sQ) :
    ∀ k a : Nat,
    run O M k
      { state := base + 4, inTape := tapeOfList (encodeBits x), inHead := 0,
        w1Tape := colMarkedOnes a, w1Head := a + 1,
        w2Tape := colMarkedOnes k, w2Head := k,
        qTape := colMarkedOnes 0, qHead := 0, halted := none } =
    { state := base + 4, inTape := tapeOfList (encodeBits x), inHead := 0,
      w1Tape := colMarkedOnes (a + k), w1Head := a + k + 1,
      w2Tape := colMarkedOnes 0, w2Head := 0,
      qTape := colMarkedOnes 0, qHead := 0, halted := none } := by
  intro k
  induction k with
  | zero => intro a; simp [run_zero]
  | succ k ih =>
    intro a
    rw [run_succ]
    have hw2 : colMarkedOnes (k + 1) (k + 1) = Sym.one := by
      unfold colMarkedOnes
      have h0 : (k + 1 == 0) = false := beq_false_of_ne (by omega)
      simp [h0]
    have hact : findAction M.rules (base + 4)
        (tapeOfList (encodeBits x) 0) (colMarkedOnes a (a + 1))
        (colMarkedOnes (k + 1) (k + 1)) (colMarkedOnes 0 0) =
        Action.step (base + 4) .stay (some .one) .right (some .blank) .left none .stay := by
      rw [hblock 4 (by decide), hw2]
      exact findAction_mulRound_4_one base next ..
    rw [stepLog_eq_step O M _ rfl hact, writeOpt_colMarkedOnes_succ, writeOpt_colMarkedOnes_erase]
    simp only [moveHead, writeOpt, Nat.add_sub_cancel]
    rw [ih (a + 1)]
    have heq : a + 1 + k = a + (k + 1) := by omega
    rw [heq]

private theorem run_mulRound_full (O : Oracle) (M : OTM) (base next : Nat) (x : List Bool) (m : Nat)
    (hblock : ∀ off < 5, ∀ sIn sW1 sW2 sQ,
      findAction M.rules (base + off) sIn sW1 sW2 sQ =
      findAction (mulRoundRules base next) (base + off) sIn sW1 sW2 sQ) :
    run O M (1 + m * (2 * x.length + 3) + 1 + m * (x.length + 1) + 1)
      { state := base, inTape := tapeOfList (encodeBits x), inHead := 0,
        w1Tape := colMarkedOnes m, w1Head := m + 1,
        w2Tape := colMarkedOnes 0, w2Head := 1,
        qTape := colMarkedOnes 0, qHead := 0, halted := none } =
    { state := next, inTape := tapeOfList (encodeBits x), inHead := 0,
      w1Tape := colMarkedOnes (m * (x.length + 1)), w1Head := m * (x.length + 1) + 1,
      w2Tape := colMarkedOnes 0, w2Head := 1,
      qTape := colMarkedOnes 0, qHead := 0, halted := none } := by
  rw [run_add O M (1 + m * (2 * x.length + 3) + 1 + m * (x.length + 1)) 1,
      run_add O M (1 + m * (2 * x.length + 3) + 1) (m * (x.length + 1)),
      run_add O M (1 + m * (2 * x.length + 3)) 1,
      run_add O M 1 (m * (2 * x.length + 3))]
  have hs0 :
      run O M 1
        { state := base, inTape := tapeOfList (encodeBits x), inHead := 0,
          w1Tape := colMarkedOnes m, w1Head := m + 1,
          w2Tape := colMarkedOnes 0, w2Head := 1,
          qTape := colMarkedOnes 0, qHead := 0, halted := none } =
      { state := base + 1, inTape := tapeOfList (encodeBits x), inHead := 0,
        w1Tape := colMarkedOnes m, w1Head := m,
        w2Tape := colMarkedOnes 0, w2Head := 1,
        qTape := colMarkedOnes 0, qHead := 0, halted := none } := by
    rw [run_succ, run_zero]
    have hact0 : findAction M.rules base
        (tapeOfList (encodeBits x) 0) (colMarkedOnes m (m + 1))
        (colMarkedOnes 0 1) (colMarkedOnes 0 0) =
        Action.step (base + 1) .stay none .left none .stay none .stay := by
      have h0 := hblock 0 (by decide)
        (tapeOfList (encodeBits x) 0) (colMarkedOnes m (m + 1))
        (colMarkedOnes 0 1) (colMarkedOnes 0 0)
      rw [Nat.add_zero] at h0
      rw [h0]
      exact findAction_mulRound_0 base next ..
    rw [stepLog_eq_step O M _ rfl hact0]
    simp only [moveHead, writeOpt, Nat.add_sub_cancel]
  rw [hs0]
  rw [run_mulRound_outer O M base next x hblock m 0]
  simp only [Nat.zero_add]
  have hs1 :
      run O M 1
        { state := base + 1, inTape := tapeOfList (encodeBits x), inHead := 0,
          w1Tape := colMarkedOnes 0, w1Head := 0,
          w2Tape := colMarkedOnes (m * (x.length + 1)), w2Head := m * (x.length + 1) + 1,
          qTape := colMarkedOnes 0, qHead := 0, halted := none } =
      { state := base + 4, inTape := tapeOfList (encodeBits x), inHead := 0,
        w1Tape := colMarkedOnes 0, w1Head := 1,
        w2Tape := colMarkedOnes (m * (x.length + 1)), w2Head := m * (x.length + 1),
        qTape := colMarkedOnes 0, qHead := 0, halted := none } := by
    rw [run_succ, run_zero]
    have hw1sep : colMarkedOnes 0 0 = Sym.sep := rfl
    have hact1 : findAction M.rules (base + 1)
        (tapeOfList (encodeBits x) 0) (colMarkedOnes 0 0)
        (colMarkedOnes (m * (x.length + 1)) (m * (x.length + 1) + 1)) (colMarkedOnes 0 0) =
        Action.step (base + 4) .stay none .right none .left none .stay := by
      rw [hblock 1 (by decide), hw1sep]
      exact findAction_mulRound_1_sep base next ..
    rw [stepLog_eq_step O M _ rfl hact1]
    simp only [moveHead, writeOpt, Nat.add_sub_cancel]
  rw [hs1]
  rw [run_mulRound_copyback O M base next x hblock (m * (x.length + 1)) 0]
  simp only [Nat.zero_add]
  rw [run_succ, run_zero]
  have hw2sep : colMarkedOnes 0 0 = Sym.sep := rfl
  have hact4 : findAction M.rules (base + 4)
      (tapeOfList (encodeBits x) 0)
      (colMarkedOnes (m * (x.length + 1)) (m * (x.length + 1) + 1))
      (colMarkedOnes 0 0) (colMarkedOnes 0 0) =
      Action.step next .stay none .stay none .right none .stay := by
    rw [hblock 4 (by decide), hw2sep]
    exact findAction_mulRound_4_sep base next ..
  rw [stepLog_eq_step O M _ rfl hact4]
  simp only [moveHead, writeOpt]

private def mulPhaseSteps (n : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => mulPhaseSteps n j + (1 + (n + 1) ^ j * (2 * n + 3) + 1 + (n + 1) ^ j * (n + 1) + 1)

private theorem mulPhaseSteps_le (n c : Nat) :
    mulPhaseSteps n c ≤ 4 * c * (n + 1) ^ c + 3 * c := by
  induction c with
  | zero => simp [mulPhaseSteps]
  | succ c ih =>
    unfold mulPhaseSteps
    have hpow_le : (n + 1) ^ c ≤ (n + 1) ^ (c + 1) := by
      rw [Nat.pow_succ]
      exact Nat.le_mul_of_pos_right _ (by omega)
    have hstep_le : (n + 1) ^ c * (2 * n + 3) + (n + 1) ^ c * (n + 1) ≤ 4 * (n + 1) ^ (c + 1) := by
      have h23 : 2 * n + 3 ≤ 3 * (n + 1) := by omega
      have h1 : (n + 1) ^ c * (2 * n + 3) ≤ (n + 1) ^ c * (3 * (n + 1)) :=
        Nat.mul_le_mul_left _ h23
      have hpow : (n + 1) ^ (c + 1) = (n + 1) ^ c * (n + 1) := Nat.pow_succ ..
      have h3 : (n + 1) ^ c * (3 * (n + 1)) = 3 * ((n + 1) ^ c * (n + 1)) := by
        rw [Nat.mul_left_comm]
      omega
    have hprev_le : 4 * c * (n + 1) ^ c ≤ 4 * c * (n + 1) ^ (c + 1) :=
      Nat.mul_le_mul_left (4 * c) hpow_le
    have hmul_succ : 4 * (c + 1) * (n + 1) ^ (c + 1) =
        4 * c * (n + 1) ^ (c + 1) + 4 * (n + 1) ^ (c + 1) := by
      rw [Nat.mul_add, Nat.add_mul]
    omega

private theorem colDec_phase_init_and_mul (O : Oracle) (V : OTM) (c d : Nat) (x : List Bool) :
    run O (collapseDecider V c d) (2 + mulPhaseSteps x.length c) (initConfig (encodeBits x)) =
    { state := 2 + 5 * c, inTape := tapeOfList (encodeBits x), inHead := 0,
      w1Tape := colMarkedOnes ((x.length + 1) ^ c), w1Head := (x.length + 1) ^ c + 1,
      w2Tape := colMarkedOnes 0, w2Head := 1,
      qTape := colMarkedOnes 0, qHead := 0, halted := none } := by
  rw [run_add]
  have hinit :
      run O (collapseDecider V c d) 2 (initConfig (encodeBits x)) =
      { state := 2, inTape := tapeOfList (encodeBits x), inHead := 0,
        w1Tape := colMarkedOnes 1, w1Head := 2,
        w2Tape := colMarkedOnes 0, w2Head := 1,
        qTape := colMarkedOnes 0, qHead := 0, halted := none } := by
    rw [run_succ, run_succ, run_zero]
    have hact0 := colDec_lookup_0 V c d
      (tapeOfList (encodeBits x) 0) (blankTape 0) (blankTape 0) (blankTape 0)
    have hs0 :
        (stepLog O (collapseDecider V c d) (initConfig (encodeBits x))).1 =
        { state := 1, inTape := tapeOfList (encodeBits x), inHead := 0,
          w1Tape := colMarkedOnes 0, w1Head := 1,
          w2Tape := colMarkedOnes 0, w2Head := 1,
          qTape := colMarkedOnes 0, qHead := 0, halted := none } := by
      rw [stepLog_eq_step O (collapseDecider V c d) (initConfig (encodeBits x)) rfl hact0]
      have hw0 : writeOpt blankTape 0 (some Sym.sep) = colMarkedOnes 0 := by
        funext i; unfold writeOpt blankTape colMarkedOnes; cases i <;> rfl
      simp only [initConfig, moveHead, hw0]
    rw [hs0]
    have hact1 := colDec_lookup_1 V c d
      (tapeOfList (encodeBits x) 0) (colMarkedOnes 0 1) (colMarkedOnes 0 1) (colMarkedOnes 0 0)
    rw [stepLog_eq_step O (collapseDecider V c d) _ rfl hact1]
    rw [writeOpt_colMarkedOnes_succ 0]
    simp only [moveHead, writeOpt]
  rw [hinit]
  have hloop : ∀ j ≤ c,
      run O (collapseDecider V c d) (mulPhaseSteps x.length j)
        { state := 2, inTape := tapeOfList (encodeBits x), inHead := 0,
          w1Tape := colMarkedOnes 1, w1Head := 2,
          w2Tape := colMarkedOnes 0, w2Head := 1,
          qTape := colMarkedOnes 0, qHead := 0, halted := none } =
      { state := 2 + 5 * j, inTape := tapeOfList (encodeBits x), inHead := 0,
        w1Tape := colMarkedOnes ((x.length + 1) ^ j), w1Head := (x.length + 1) ^ j + 1,
        w2Tape := colMarkedOnes 0, w2Head := 1,
        qTape := colMarkedOnes 0, qHead := 0, halted := none } := by
    intro j hj
    induction j with
    | zero => simp [mulPhaseSteps, run_zero]
    | succ j ih =>
      unfold mulPhaseSteps
      rw [run_add, ih (by omega)]
      have hround := run_mulRound_full O (collapseDecider V c d) (2 + 5 * j) (2 + 5 * (j + 1)) x
        ((x.length + 1) ^ j) (fun off hoff => colDec_lookup_mul V c d j off (by omega) hoff)
      rw [hround, ← Nat.pow_succ]
  exact hloop c (Nat.le_refl c)

private theorem colDec_phase_x (O : Oracle) (V : OTM) (c d : Nat) (x : List Bool)
    (w1T : Nat → Sym) (w1H : Nat) (w2T : Nat → Sym) (w2H : Nat) :
    ∀ k ≤ x.length, ∀ qT : Nat → Sym, ∀ pref : List Bool,
    (∀ idx < pref.length, qT idx = if pref.getD idx false then Sym.one else Sym.zero) →
    let sX := 2 + 5 * c + (colPrefBits V d).length
    let cfgF := run O (collapseDecider V c d) (2 * k)
      { state := sX, inTape := tapeOfList (encodeBits x), inHead := 0,
        w1Tape := w1T, w1Head := w1H, w2Tape := w2T, w2Head := w2H,
        qTape := qT, qHead := pref.length, halted := none }
    cfgF.state = sX ∧ cfgF.halted = none ∧
    cfgF.inTape = tapeOfList (encodeBits x) ∧ cfgF.inHead = k ∧
    cfgF.w1Tape = w1T ∧ cfgF.w1Head = w1H ∧
    cfgF.w2Tape = w2T ∧ cfgF.w2Head = w2H ∧
    cfgF.qHead = (pref ++ doubleBits (x.take k)).length ∧
    ∀ idx < (pref ++ doubleBits (x.take k)).length,
      cfgF.qTape idx = if (pref ++ doubleBits (x.take k)).getD idx false then Sym.one else Sym.zero := by
  intro k hk
  induction k with
  | zero =>
    intro qT pref hqt
    dsimp only
    rw [Nat.mul_zero, run_zero, List.take_zero, show doubleBits [] = [] from rfl, List.append_nil]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hqt⟩
  | succ k ih =>
    intro qT pref hqt
    dsimp only
    rw [show 2 * (k + 1) = 2 * k + 2 from by omega, run_add]
    have hprev := ih (by omega) qT pref hqt
    dsimp only at hprev
    rcases hprev with ⟨hst, hhalt, hinT, hinH, hw1T, hw1H, hw2T, hw2H, hqH, hqT⟩
    let sX := 2 + 5 * c + (colPrefBits V d).length
    let cfgK := run O (collapseDecider V c d) (2 * k)
      { state := sX, inTape := tapeOfList (encodeBits x), inHead := 0,
        w1Tape := w1T, w1Head := w1H, w2Tape := w2T, w2Head := w2H,
        qTape := qT, qHead := pref.length, halted := none }
    let prefK := pref ++ doubleBits (x.take k)
    change (run O (collapseDecider V c d) 2 cfgK).state = sX ∧ _
    rw [run_succ, run_succ, run_zero]
    have hlt : k < x.length := by omega
    have hsym : cfgK.inTape cfgK.inHead = if x[k] then Sym.one else Sym.zero := by
      rw [hinT, hinH]; exact col_in_at_lt x k hlt
    have htake : doubleBits (x.take (k + 1)) = doubleBits (x.take k) ++ [true, x[k]] := by
      rw [List.take_succ_eq_append_getElem hlt]
      have hdb_app : ∀ xs ys, doubleBits (xs ++ ys) = doubleBits xs ++ doubleBits ys := by
        intro xs ys; induction xs with | nil => rfl | cons a as iha => simp [doubleBits, iha]
      rw [hdb_app]; rfl
    have hpref_next : pref ++ doubleBits (x.take (k + 1)) = prefK ++ [true, x[k]] := by
      rw [htake, ← List.append_assoc]
    cases hxk : x[k]
    · simp only [hxk, Bool.false_eq_true, ↓reduceIte] at hsym
      have hact1 : findAction (collapseDecider V c d).rules cfgK.state
          (cfgK.inTape cfgK.inHead) (cfgK.w1Tape cfgK.w1Head)
          (cfgK.w2Tape cfgK.w2Head) (cfgK.qTape cfgK.qHead) =
          Action.step (sX + 1) .stay none .stay none .stay (some .one) .right := by
        have hlu := colDec_lookup_x V c d 0 (by decide)
          (cfgK.inTape cfgK.inHead) (cfgK.w1Tape cfgK.w1Head) (cfgK.w2Tape cfgK.w2Head) (cfgK.qTape cfgK.qHead)
        simp only [Nat.add_zero] at hlu
        rw [hst, hlu, hsym]
        exact findAction_colX_0_zero sX ..
      rw [stepLog_eq_step O (collapseDecider V c d) cfgK hhalt hact1]
      let cfgK1 : Config :=
        { cfgK with
            state := sX + 1
            inHead := moveHead cfgK.inHead Dir.stay
            w1Tape := writeOpt cfgK.w1Tape cfgK.w1Head none
            w1Head := moveHead cfgK.w1Head Dir.stay
            w2Tape := writeOpt cfgK.w2Tape cfgK.w2Head none
            w2Head := moveHead cfgK.w2Head Dir.stay
            qTape := writeOpt cfgK.qTape cfgK.qHead (some Sym.one)
            qHead := moveHead cfgK.qHead Dir.right }
      have hact2 : findAction (collapseDecider V c d).rules cfgK1.state
          (cfgK1.inTape cfgK1.inHead) (cfgK1.w1Tape cfgK1.w1Head)
          (cfgK1.w2Tape cfgK1.w2Head) (cfgK1.qTape cfgK1.qHead) =
          Action.step sX .right none .stay none .stay (some .zero) .right := by
        dsimp only [cfgK1]
        rw [colDec_lookup_x V c d 1 (by decide)]
        exact findAction_colX_1 sX ..
      have hhalt1 : cfgK1.halted = none := hhalt
      rw [stepLog_eq_step O (collapseDecider V c d) cfgK1 hhalt1 hact2]
      dsimp only [cfgK1, cfgK, sX]
      have hqH' : (run O (collapseDecider V c d) (2 * k)
          { state := 2 + 5 * c + (colPrefBits V d).length, inTape := tapeOfList (encodeBits x), inHead := 0,
            w1Tape := w1T, w1Head := w1H, w2Tape := w2T, w2Head := w2H, qTape := qT, qHead := pref.length,
            halted := none }).qHead = prefK.length := hqH
      refine ⟨rfl, hhalt, hinT, by simp [moveHead, hinH], hw1T, hw1H, hw2T, hw2H, ?_, ?_⟩
      · rw [hpref_next]; simp only [moveHead, hqH', List.length_append, List.length_cons, List.length_nil]
      · intro idx hidx
        rw [hpref_next] at hidx ⊢
        simp only [List.length_append, List.length_cons, List.length_nil] at hidx
        unfold writeOpt; simp only [moveHead, hqH']
        by_cases h2 : idx = prefK.length + 1
        · subst h2
          simp only [beq_self_eq_true, ↓reduceIte]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_succ _),
              show prefK.length + 1 - prefK.length = 1 from by omega]
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, hxk]
          rfl
        · have hb2 : (idx == prefK.length + 1) = false := beq_false_of_ne h2
          simp only [hb2, Bool.false_eq_true, ↓reduceIte]
          by_cases h1 : idx = prefK.length
          · subst h1
            simp only [beq_self_eq_true, ↓reduceIte]
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
            rfl
          · have hb1 : (idx == prefK.length) = false := beq_false_of_ne h1
            have hidx_lt : idx < prefK.length := by omega
            simp only [hb1, Bool.false_eq_true, ↓reduceIte, List.getD_eq_getElem?_getD,
                       List.getElem?_append_left hidx_lt]
            have := hqT idx hidx_lt
            simpa [prefK, List.getD_eq_getElem?_getD] using this
    · simp only [hxk, ↓reduceIte] at hsym
      have hact1 : findAction (collapseDecider V c d).rules cfgK.state
          (cfgK.inTape cfgK.inHead) (cfgK.w1Tape cfgK.w1Head)
          (cfgK.w2Tape cfgK.w2Head) (cfgK.qTape cfgK.qHead) =
          Action.step (sX + 2) .stay none .stay none .stay (some .one) .right := by
        have hlu := colDec_lookup_x V c d 0 (by decide)
          (cfgK.inTape cfgK.inHead) (cfgK.w1Tape cfgK.w1Head) (cfgK.w2Tape cfgK.w2Head) (cfgK.qTape cfgK.qHead)
        simp only [Nat.add_zero] at hlu
        rw [hst, hlu, hsym]
        exact findAction_colX_0_one sX ..
      rw [stepLog_eq_step O (collapseDecider V c d) cfgK hhalt hact1]
      let cfgK1 : Config :=
        { cfgK with
            state := sX + 2
            inHead := moveHead cfgK.inHead Dir.stay
            w1Tape := writeOpt cfgK.w1Tape cfgK.w1Head none
            w1Head := moveHead cfgK.w1Head Dir.stay
            w2Tape := writeOpt cfgK.w2Tape cfgK.w2Head none
            w2Head := moveHead cfgK.w2Head Dir.stay
            qTape := writeOpt cfgK.qTape cfgK.qHead (some Sym.one)
            qHead := moveHead cfgK.qHead Dir.right }
      have hact2 : findAction (collapseDecider V c d).rules cfgK1.state
          (cfgK1.inTape cfgK1.inHead) (cfgK1.w1Tape cfgK1.w1Head)
          (cfgK1.w2Tape cfgK1.w2Head) (cfgK1.qTape cfgK1.qHead) =
          Action.step sX .right none .stay none .stay (some .one) .right := by
        dsimp only [cfgK1]
        rw [colDec_lookup_x V c d 2 (by decide)]
        exact findAction_colX_2 sX ..
      have hhalt1 : cfgK1.halted = none := hhalt
      rw [stepLog_eq_step O (collapseDecider V c d) cfgK1 hhalt1 hact2]
      dsimp only [cfgK1, cfgK, sX]
      have hqH' : (run O (collapseDecider V c d) (2 * k)
          { state := 2 + 5 * c + (colPrefBits V d).length, inTape := tapeOfList (encodeBits x), inHead := 0,
            w1Tape := w1T, w1Head := w1H, w2Tape := w2T, w2Head := w2H, qTape := qT, qHead := pref.length,
            halted := none }).qHead = prefK.length := hqH
      refine ⟨rfl, hhalt, hinT, by simp [moveHead, hinH], hw1T, hw1H, hw2T, hw2H, ?_, ?_⟩
      · rw [hpref_next]; simp only [moveHead, hqH', List.length_append, List.length_cons, List.length_nil]
      · intro idx hidx
        rw [hpref_next] at hidx ⊢
        simp only [List.length_append, List.length_cons, List.length_nil] at hidx
        unfold writeOpt; simp only [moveHead, hqH']
        by_cases h2 : idx = prefK.length + 1
        · subst h2
          simp only [beq_self_eq_true, ↓reduceIte]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_succ _),
              show prefK.length + 1 - prefK.length = 1 from by omega]
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, hxk]
          rfl
        · have hb2 : (idx == prefK.length + 1) = false := beq_false_of_ne h2
          simp only [hb2, Bool.false_eq_true, ↓reduceIte]
          by_cases h1 : idx = prefK.length
          · subst h1
            simp only [beq_self_eq_true, ↓reduceIte]
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
            rfl
          · have hb1 : (idx == prefK.length) = false := beq_false_of_ne h1
            have hidx_lt : idx < prefK.length := by omega
            simp only [hb1, Bool.false_eq_true, ↓reduceIte, List.getD_eq_getElem?_getD,
                       List.getElem?_append_left hidx_lt]
            have := hqT idx hidx_lt
            simpa [prefK, List.getD_eq_getElem?_getD] using this

private theorem colDec_phase_drain (O : Oracle) (V : OTM) (c d : Nat) (m : Nat) :
    ∀ k ≤ m, ∀ cfg : Config, ∀ pref : List Bool,
    cfg.state = 2 + 5 * c + (colPrefBits V d).length + 4 →
    cfg.halted = none →
    cfg.w1Tape = colMarkedOnes m → cfg.w1Head = k →
    cfg.qHead = pref.length →
    (∀ idx < pref.length, cfg.qTape idx = if pref.getD idx false then Sym.one else Sym.zero) →
    let cfgF := run O (collapseDecider V c d) k cfg
    cfgF.state = 2 + 5 * c + (colPrefBits V d).length + 4 ∧ cfgF.halted = none ∧
    cfgF.w1Tape = colMarkedOnes m ∧ cfgF.w1Head = 0 ∧
    cfgF.qHead = (pref ++ List.replicate k true).length ∧
    ∀ idx < (pref ++ List.replicate k true).length,
      cfgF.qTape idx = if (pref ++ List.replicate k true).getD idx false then Sym.one else Sym.zero := by
  intro k hk
  induction k with
  | zero =>
    intro cfg pref hst hh hw1T hw1H hqH hqT
    simp only [run_zero, List.replicate_zero, List.append_nil]
    exact ⟨hst, hh, hw1T, hw1H, hqH, hqT⟩
  | succ k ih =>
    intro cfg pref hst hh hw1T hw1H hqH hqT
    dsimp only
    rw [run_succ]
    have hw1 : cfg.w1Tape cfg.w1Head = Sym.one := by
      rw [hw1T, hw1H]
      unfold colMarkedOnes
      have h0 : (k + 1 == 0) = false := beq_false_of_ne (by omega)
      simp [h0, hk]
    have hact : findAction (collapseDecider V c d).rules cfg.state
        (cfg.inTape cfg.inHead) (cfg.w1Tape cfg.w1Head)
        (cfg.w2Tape cfg.w2Head) (cfg.qTape cfg.qHead) =
        Action.step (2 + 5 * c + (colPrefBits V d).length + 4) .stay none .left none .stay (some .one) .right := by
      rw [hst, colDec_lookup_drain, hw1]
      exact findAction_colDrain_one ..
    rw [stepLog_eq_step O (collapseDecider V c d) cfg hh hact]
    have hqt' : ∀ idx < (pref ++ [true]).length,
        writeOpt cfg.qTape cfg.qHead (some Sym.one) idx =
        if (pref ++ [true]).getD idx false then Sym.one else Sym.zero := by
      intro idx hidx
      unfold writeOpt; rw [hqH]
      simp only [List.length_append, List.length_singleton] at hidx
      by_cases heq : idx = pref.length
      · subst heq; simp [List.getD_eq_getElem?_getD]
      · have hb : (idx == pref.length) = false := beq_false_of_ne heq
        have hlt : idx < pref.length := by omega
        simp only [hb, Bool.false_eq_true, ↓reduceIte, List.getD_eq_getElem?_getD,
                   List.getElem?_append_left hlt]
        have := hqT idx hlt
        simpa [List.getD_eq_getElem?_getD] using this
    have hrec := ih (by omega)
      { cfg with
          state := 2 + 5 * c + (colPrefBits V d).length + 4
          inHead := moveHead cfg.inHead Dir.stay
          w1Tape := writeOpt cfg.w1Tape cfg.w1Head none
          w1Head := moveHead cfg.w1Head Dir.left
          w2Tape := writeOpt cfg.w2Tape cfg.w2Head none
          w2Head := moveHead cfg.w2Head Dir.stay
          qTape := writeOpt cfg.qTape cfg.qHead (some Sym.one)
          qHead := moveHead cfg.qHead Dir.right }
      (pref ++ [true]) rfl hh hw1T (by simp [moveHead, hw1H]) (by simp [moveHead, hqH]) hqt'
    have hrep : pref ++ [true] ++ List.replicate k true = pref ++ List.replicate (k + 1) true := by
      rw [List.append_assoc, List.singleton_append, ← List.replicate_succ]
    simpa [hrep] using hrec

private def colDecExactSteps (V : OTM) (c d n : Nat) : Nat :=
  (2 + mulPhaseSteps n c) +
  (colPrefBits V d).length +
  (2 * n + 2) +
  ((n + 1) ^ c + 1) +
  (c + 1) + 2

private theorem colDec_exact_output (O : Oracle) (V : OTM) (c d : Nat) (x : List Bool) :
    (run O (collapseDecider V c d) (colDecExactSteps V c d x.length)
      (initConfig (encodeBits x))).halted =
    some (O (encodeColQuery (encodeOTM V) d (polyBound c x.length) x)) := by
  unfold colDecExactSteps
  rw [run_add O (collapseDecider V c d) _ 2,
      run_add O (collapseDecider V c d) _ (c + 1),
      run_add O (collapseDecider V c d) _ ((x.length + 1) ^ c + 1),
      run_add O (collapseDecider V c d) _ (2 * x.length + 2),
      run_add O (collapseDecider V c d) _ (colPrefBits V d).length]
  rw [colDec_phase_init_and_mul O V c d x]
  let cfgM : Config :=
    { state := 2 + 5 * c, inTape := tapeOfList (encodeBits x), inHead := 0,
      w1Tape := colMarkedOnes ((x.length + 1) ^ c), w1Head := (x.length + 1) ^ c + 1,
      w2Tape := colMarkedOnes 0, w2Head := 1,
      qTape := colMarkedOnes 0, qHead := 0, halted := none }
  have hpref := run_writeBits_block O (collapseDecider V c d) (2 + 5 * c) (colPrefBits V d)
    (fun i hi => colDec_lookup_pref V c d i hi)
    cfgM [] rfl rfl rfl (by intro idx hidx; simp at hidx)
  dsimp only at hpref
  simp only [List.nil_append] at hpref
  rcases hpref with ⟨hpSt, hpH, hpInT, hpInH, hpW1T, hpW1H, hpW2T, hpW2H, hpQH, hpQT⟩
  let cfgP := run O (collapseDecider V c d) (colPrefBits V d).length cfgM
  have hcfgP_eq : cfgP =
      { state := 2 + 5 * c + (colPrefBits V d).length, inTape := tapeOfList (encodeBits x), inHead := 0,
        w1Tape := colMarkedOnes ((x.length + 1) ^ c), w1Head := (x.length + 1) ^ c + 1,
        w2Tape := colMarkedOnes 0, w2Head := 1,
        qTape := cfgP.qTape, qHead := (colPrefBits V d).length, halted := none } := by
    have heta : cfgP =
        Config.mk cfgP.state cfgP.inTape cfgP.inHead cfgP.w1Tape cfgP.w1Head
          cfgP.w2Tape cfgP.w2Head cfgP.qTape cfgP.qHead cfgP.halted := rfl
    rw [heta, hpSt, hpInT, hpInH, hpW1T, hpW1H, hpW2T, hpW2H, hpQH, hpH]
  change (run O (collapseDecider V c d) 2
    (run O (collapseDecider V c d) (c + 1)
      (run O (collapseDecider V c d) ((x.length + 1) ^ c + 1)
        (run O (collapseDecider V c d) (2 * x.length + 2) cfgP)))).halted = _
  rw [run_add O _ (2 * x.length) 2, hcfgP_eq]
  have hx := colDec_phase_x O V c d x
    (colMarkedOnes ((x.length + 1) ^ c)) ((x.length + 1) ^ c + 1)
    (colMarkedOnes 0) 1 x.length (Nat.le_refl _) cfgP.qTape (colPrefBits V d) hpQT
  dsimp only at hx
  rw [List.take_length] at hx
  rcases hx with ⟨hxSt, hxH, hxInT, hxInH, hxW1T, hxW1H, hxW2T, hxW2H, hxQH, hxQT⟩
  let sX := 2 + 5 * c + (colPrefBits V d).length
  let cfgX := run O (collapseDecider V c d) (2 * x.length)
    { state := sX, inTape := tapeOfList (encodeBits x), inHead := 0,
      w1Tape := colMarkedOnes ((x.length + 1) ^ c), w1Head := (x.length + 1) ^ c + 1,
      w2Tape := colMarkedOnes 0, w2Head := 1,
      qTape := cfgP.qTape, qHead := (colPrefBits V d).length, halted := none }
  let prefX := colPrefBits V d ++ doubleBits x
  have hterm :
      let cfgT := run O (collapseDecider V c d) 2 cfgX
      cfgT.state = sX + 4 ∧ cfgT.halted = none ∧
      cfgT.w1Tape = colMarkedOnes ((x.length + 1) ^ c) ∧ cfgT.w1Head = (x.length + 1) ^ c ∧
      cfgT.qHead = (prefX ++ [false, false]).length ∧
      ∀ idx < (prefX ++ [false, false]).length,
        cfgT.qTape idx = if (prefX ++ [false, false]).getD idx false then Sym.one else Sym.zero := by
    dsimp only
    rw [run_succ, run_succ, run_zero]
    have hend : cfgX.inTape cfgX.inHead = Sym.blank := by
      rw [hxInT, hxInH]; exact col_in_at_end x
    have hact1 : findAction (collapseDecider V c d).rules cfgX.state
        (cfgX.inTape cfgX.inHead) (cfgX.w1Tape cfgX.w1Head)
        (cfgX.w2Tape cfgX.w2Head) (cfgX.qTape cfgX.qHead) =
        Action.step (sX + 3) .stay none .stay none .stay (some .zero) .right := by
      have hlu := colDec_lookup_x V c d 0 (by decide)
        (cfgX.inTape cfgX.inHead) (cfgX.w1Tape cfgX.w1Head) (cfgX.w2Tape cfgX.w2Head) (cfgX.qTape cfgX.qHead)
      simp only [Nat.add_zero] at hlu
      rw [hxSt, hlu, hend]
      exact findAction_colX_0_blank sX ..
    rw [stepLog_eq_step O (collapseDecider V c d) cfgX hxH hact1]
    let cfgX1 : Config :=
      { cfgX with
          state := sX + 3
          inHead := moveHead cfgX.inHead Dir.stay
          w1Tape := writeOpt cfgX.w1Tape cfgX.w1Head none
          w1Head := moveHead cfgX.w1Head Dir.stay
          w2Tape := writeOpt cfgX.w2Tape cfgX.w2Head none
          w2Head := moveHead cfgX.w2Head Dir.stay
          qTape := writeOpt cfgX.qTape cfgX.qHead (some Sym.zero)
          qHead := moveHead cfgX.qHead Dir.right }
    have hact2 : findAction (collapseDecider V c d).rules cfgX1.state
        (cfgX1.inTape cfgX1.inHead) (cfgX1.w1Tape cfgX1.w1Head)
        (cfgX1.w2Tape cfgX1.w2Head) (cfgX1.qTape cfgX1.qHead) =
        Action.step (sX + 4) .stay none .left none .stay (some .zero) .right := by
      dsimp only [cfgX1]
      rw [colDec_lookup_x V c d 3 (by decide)]
      exact findAction_colX_3 sX ..
    have hxH1 : cfgX1.halted = none := hxH
    rw [stepLog_eq_step O (collapseDecider V c d) cfgX1 hxH1 hact2]
    dsimp only [cfgX1, cfgX, sX]
    have hxQH' : (run O (collapseDecider V c d) (2 * x.length)
        { state := 2 + 5 * c + (colPrefBits V d).length, inTape := tapeOfList (encodeBits x), inHead := 0,
          w1Tape := colMarkedOnes ((x.length + 1) ^ c), w1Head := (x.length + 1) ^ c + 1,
          w2Tape := colMarkedOnes 0, w2Head := 1, qTape := cfgP.qTape,
          qHead := (colPrefBits V d).length, halted := none }).qHead = prefX.length := hxQH
    refine ⟨rfl, hxH, hxW1T, by simp [moveHead, hxW1H],
            by simp only [moveHead, hxQH', List.length_append, List.length_cons, List.length_nil], ?_⟩
    intro idx hidx
    simp only [List.length_append, List.length_cons, List.length_nil] at hidx
    unfold writeOpt; simp only [moveHead, hxQH']
    by_cases h2 : idx = prefX.length + 1
    · subst h2
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_succ _),
          show prefX.length + 1 - prefX.length = 1 from by omega]
      rfl
    · have hb2 : (idx == prefX.length + 1) = false := beq_false_of_ne h2
      simp only [hb2, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : idx = prefX.length
      · subst h1
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      · have hb1 : (idx == prefX.length) = false := beq_false_of_ne h1
        have hlt : idx < prefX.length := by omega
        simp only [hb1, Bool.false_eq_true, ↓reduceIte, List.getD_eq_getElem?_getD,
                   List.getElem?_append_left hlt]
        have := hxQT idx hlt
        simpa [prefX, List.getD_eq_getElem?_getD] using this
  dsimp only at hterm
  rcases hterm with ⟨htSt, htH, htW1T, htW1H, htQH, htQT⟩
  let cfgT := run O (collapseDecider V c d) 2 cfgX
  change (run O (collapseDecider V c d) 2
    (run O (collapseDecider V c d) (c + 1)
      (run O (collapseDecider V c d) ((x.length + 1) ^ c + 1) cfgT))).halted = _
  rw [run_add O _ ((x.length + 1) ^ c) 1]
  have hdrain := colDec_phase_drain O V c d ((x.length + 1) ^ c) ((x.length + 1) ^ c) (Nat.le_refl _)
    cfgT (prefX ++ [false, false]) htSt htH htW1T htW1H htQH htQT
  dsimp only at hdrain
  rcases hdrain with ⟨hdSt, hdH, hdW1T, hdW1H, hdQH, hdQT⟩
  let cfgD := run O (collapseDecider V c d) ((x.length + 1) ^ c) cfgT
  change (run O (collapseDecider V c d) 2
    (run O (collapseDecider V c d) (c + 1)
      (run O (collapseDecider V c d) 1 cfgD))).halted = _
  let cfgPad0 : Config :=
    { cfgD with
        state := sX + 5
        inHead := moveHead cfgD.inHead Dir.stay
        w1Tape := writeOpt cfgD.w1Tape cfgD.w1Head none
        w1Head := moveHead cfgD.w1Head Dir.stay
        w2Tape := writeOpt cfgD.w2Tape cfgD.w2Head none
        w2Head := moveHead cfgD.w2Head Dir.stay
        qTape := writeOpt cfgD.qTape cfgD.qHead none
        qHead := moveHead cfgD.qHead Dir.stay }
  have hsD : run O (collapseDecider V c d) 1 cfgD = cfgPad0 := by
    rw [run_succ, run_zero]
    have hw1sep : cfgD.w1Tape cfgD.w1Head = Sym.sep := by rw [hdW1T, hdW1H]; rfl
    have hactD : findAction (collapseDecider V c d).rules cfgD.state
        (cfgD.inTape cfgD.inHead) (cfgD.w1Tape cfgD.w1Head)
        (cfgD.w2Tape cfgD.w2Head) (cfgD.qTape cfgD.qHead) =
        Action.step (sX + 5) .stay none .stay none .stay none .stay := by
      rw [hdSt, colDec_lookup_drain, hw1sep]
      exact findAction_colDrain_sep ..
    rw [stepLog_eq_step O (collapseDecider V c d) cfgD hdH hactD]
  rw [hsD]
  let prefD := prefX ++ [false, false] ++ List.replicate ((x.length + 1) ^ c) true
  have hpad := run_writeBits_block O (collapseDecider V c d)
    (sX + 5) (List.replicate (c + 1) true)
    (fun i hi => colDec_lookup_pad V c d i hi)
    cfgPad0 prefD rfl hdH (by dsimp only [cfgPad0, cfgD, moveHead]; exact hdQH) (by
      intro idx hidx; simp only [cfgPad0, cfgD, writeOpt]; exact hdQT idx hidx)
  dsimp only at hpad
  simp only [List.length_replicate] at hpad
  rcases hpad with ⟨hpdSt, hpdH, _, _, _, _, _, _, hpdQH, hpdQT⟩
  let cfgQ := run O (collapseDecider V c d) (c + 1) cfgPad0
  have hqStr : prefD ++ List.replicate (c + 1) true =
      encodeColQuery (encodeOTM V) d (polyBound c x.length) x := by
    unfold encodeColQuery polyBound
    simp only [prefD, prefX, colPrefBits, List.append_assoc]
    congr 1; congr 1; congr 1; congr 1; congr 1; congr 1
    have hrep_add : ∀ a b : Nat, List.replicate a true ++ List.replicate b true = List.replicate (a + b) true := by
      intro a b; induction a with
      | zero => simp
      | succ a iha => rw [List.replicate_succ, List.cons_append, iha, Nat.succ_add, List.replicate_succ]
    rw [hrep_add]
    have hsum : (x.length + 1) ^ c + (c + 1) = (x.length + 1) ^ c + c + 1 := by omega
    rw [hsum]
  change (run O (collapseDecider V c d) 2 cfgQ).halted = _
  rw [run_succ, run_succ, run_zero]
  let sQ := sX + 5 + (c + 1)
  have hactQ : findAction (collapseDecider V c d).rules cfgQ.state
      (cfgQ.inTape cfgQ.inHead) (cfgQ.w1Tape cfgQ.w1Head)
      (cfgQ.w2Tape cfgQ.w2Head) (cfgQ.qTape cfgQ.qHead) =
      Action.query (sQ + 1) (sQ + 2) := by
    have hlu := colDec_lookup_tail V c d 0 (by decide)
      (cfgQ.inTape cfgQ.inHead) (cfgQ.w1Tape cfgQ.w1Head) (cfgQ.w2Tape cfgQ.w2Head) (cfgQ.qTape cfgQ.qHead)
    simp only [Nat.add_zero] at hlu
    rw [hpdSt, hlu]
    exact findAction_colTail_0 sQ ..
  rw [stepLog_eq_query O (collapseDecider V c d) cfgQ hpdH hactQ]
  have hread : readQuery cfgQ.qTape cfgQ.qHead =
      encodeColQuery (encodeOTM V) d (polyBound c x.length) x := by
    rw [hpdQH, ← hqStr]
    have hcongr : readQuery cfgQ.qTape (prefD ++ List.replicate (c + 1) true).length =
        readQuery (qTapeFromBits (prefD ++ List.replicate (c + 1) true))
          (prefD ++ List.replicate (c + 1) true).length := by
      unfold readQuery
      apply readQueryAux_congr
      intro i hi
      rw [hpdQT i hi]
      unfold qTapeFromBits
      simp only [hi, ↓reduceIte, List.getD_eq_getElem?_getD]
    rw [hcongr, readQuery_qTapeFromBits]
  rw [hread]
  cases hO : O (encodeColQuery (encodeOTM V) d (polyBound c x.length) x)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    let cfgQR : Config := { cfgQ with state := sQ + 2, qTape := blankTape, qHead := 0 }
    have hactR : findAction (collapseDecider V c d).rules cfgQR.state
        (cfgQR.inTape cfgQR.inHead) (cfgQR.w1Tape cfgQR.w1Head)
        (cfgQR.w2Tape cfgQR.w2Head) (cfgQR.qTape cfgQR.qHead) = Action.haltReject := by
      dsimp only [cfgQR]
      rw [colDec_lookup_tail V c d 2 (by decide)]
      exact findAction_colTail_2 sQ ..
    have hQRh : cfgQR.halted = none := hpdH
    rw [stepLog_eq_haltReject O (collapseDecider V c d) cfgQR hQRh hactR]
  · simp only [↓reduceIte]
    let cfgQA : Config := { cfgQ with state := sQ + 1, qTape := blankTape, qHead := 0 }
    have hactA : findAction (collapseDecider V c d).rules cfgQA.state
        (cfgQA.inTape cfgQA.inHead) (cfgQA.w1Tape cfgQA.w1Head)
        (cfgQA.w2Tape cfgQA.w2Head) (cfgQA.qTape cfgQA.qHead) = Action.haltAccept := by
      dsimp only [cfgQA]
      rw [colDec_lookup_tail V c d 1 (by decide)]
      exact findAction_colTail_1 sQ ..
    have hQAh : cfgQA.halted = none := hpdH
    rw [stepLog_eq_haltAccept O (collapseDecider V c d) cfgQA hQAh hactA]

private theorem colDecExactSteps_le_poly (V : OTM) (c d n : Nat) :
    let K := 7 * c + 10 + (colPrefBits V d).length
    colDecExactSteps V c d n ≤ polyBound (c + 1 + K) n := by
  dsimp only
  let K := 7 * c + 10 + (colPrefBits V d).length
  change colDecExactSteps V c d n ≤ polyBound (c + 1 + K) n
  unfold colDecExactSteps polyBound
  have hm := mulPhaseSteps_le n c
  have hpow_le : (n + 1) ^ c ≤ (n + 1) ^ (c + 1) := by
    rw [Nat.pow_succ]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hn_le : n + 1 ≤ (n + 1) ^ (c + 1) := by
    have : (n + 1) ^ 1 ≤ (n + 1) ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    simpa using this
  cases n with
  | zero =>
    have h01 : (0 + 1) ^ c = 1 := by simp
    have h02 : (0 + 1) ^ (c + 1 + K) = 1 := by simp
    rw [h01] at hm ⊢
    rw [h02]
    omega
  | succ k =>
    have heq : k + 1 + 1 = k + 2 := by omega
    rw [heq] at hm hpow_le hn_le ⊢
    have h2K : K + 1 ≤ 2 ^ K := succ_le_two_pow K
    have hbaseK : 2 ^ K ≤ (k + 2) ^ K := Nat.pow_le_pow_left (by omega) K
    have hge : K + 1 ≤ (k + 2) ^ K := Nat.le_trans h2K hbaseK
    have hsplit : (k + 2) ^ (c + 1 + K) = (k + 2) ^ (c + 1) * (k + 2) ^ K := Nat.pow_add ..
    have hbig : (k + 2) ^ (c + 1) * (K + 1) ≤ (k + 2) ^ (c + 1 + K) := by
      rw [hsplit]
      exact Nat.mul_le_mul_left _ hge
    have hmul : (k + 2) ^ (c + 1) * (K + 1) = K * (k + 2) ^ (c + 1) + (k + 2) ^ (c + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
    have hKpow : (4 * c + 3) * (k + 2) ^ (c + 1) ≤ K * (k + 2) ^ (c + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4c : 4 * c * (k + 2) ^ c ≤ 4 * c * (k + 2) ^ (c + 1) :=
      Nat.mul_le_mul_left (4 * c) hpow_le
    have h4c3 : (4 * c + 3) * (k + 2) ^ (c + 1) =
        4 * c * (k + 2) ^ (c + 1) + 3 * (k + 2) ^ (c + 1) := by
      rw [Nat.add_mul]
    have h2n : 2 * (k + 1) ≤ 2 * (k + 2) ^ (c + 1) := by omega
    omega

/-- Headline Theorem (Baker–Gill–Solovay 1975, Collapse Oracle):
    There exists a computable oracle `A` such that `P^A = NP^A`. -/
public theorem bgs_oracle_collapse :
    ∃ A : Oracle, ∀ L : Language, InP A L ↔ InNP A L := by
  refine ⟨bgsColOracle, fun L => ⟨p_subset_np bgsColOracle L, ?_⟩⟩
  rintro ⟨V, c, d, hV⟩
  let K := 7 * c + 10 + (colPrefBits V d).length
  refine ⟨collapseDecider V c d, c + 1 + K, ?_⟩
  intro x
  have hrun := colDec_exact_output bgsColOracle V c d x
  have hmono := run_halted_mono bgsColOracle (collapseDecider V c d)
    (colDecExactSteps_le_poly V c d x.length) _ _ hrun
  rw [hmono]
  congr 1
  have hiff : bgsColOracle (encodeColQuery (encodeOTM V) d (polyBound c x.length) x) = true ↔ L x = true := by
    rw [bgsColOracle_spec, ← hV x]
  cases hA : bgsColOracle (encodeColQuery (encodeOTM V) d (polyBound c x.length) x) <;>
  cases hL : L x
  · rfl
  · exact absurd (hiff.mpr hL) (by rw [hA]; decide)
  · exact absurd (hiff.mp hA) (by rw [hL]; decide)
  · rfl

end PVsNP
