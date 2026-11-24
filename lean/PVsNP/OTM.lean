/-
  SPDX-License-Identifier: Apache-2.0
  Copyright (c) 2026 Alexander S. Donahue (independent researcher, ORCID 0009-0006-8168-9648)

  PVsNP/OTM.lean
  Explicit 4-tape Oracle Turing Machine model (read-only input tape, two read/write
  work tapes, one oracle query tape), exact step/query-log semantics, complexity
  classes `InP` and `InNP`, non-vacuity (`P^O ⊆ NP^O`), and bijective `OTM ↔ Nat` coding.
-/
module

public import PVsNP.Basic

namespace PVsNP
@[expose] public section

/-- An oracle is an arbitrary Boolean predicate on binary strings. -/
abbrev Oracle := List Bool → Bool

/-- A decision problem (language) is a Boolean predicate on binary strings. -/
public abbrev Language := List Bool → Bool

/-- Explicit 4-symbol tape alphabet: blank, 0, 1, and pair separator `#`. -/
public inductive Sym where
  | blank
  | zero
  | one
  | sep
  deriving DecidableEq, Repr, BEq

/-- Symbol match pattern (finite syntactic sugar over `Sym`). -/
public inductive SymPat where
  | any
  | exact (s : Sym)
  deriving DecidableEq, Repr, BEq

def SymPat.matches : SymPat → Sym → Bool
  | .any, _ => true
  | .exact s, t => s == t

/-- Tape head movement direction. -/
public inductive Dir where
  | left
  | stay
  | right
  deriving DecidableEq, Repr, BEq

def moveHead (pos : Nat) : Dir → Nat
  | .left => pos - 1
  | .stay => pos
  | .right => pos + 1

public theorem moveHead_le_succ (pos : Nat) (d : Dir) : moveHead pos d ≤ pos + 1 := by
  cases d <;> simp [moveHead] <;> omega

/-- Transition action for a 4-tape Oracle Turing Machine. -/
public inductive Action where
  | haltAccept
  | haltReject
  | step (nextState : Nat) (inDir : Dir)
         (w1Write : Option Sym) (w1Dir : Dir)
         (w2Write : Option Sym) (w2Dir : Dir)
         (qWrite : Option Sym) (qDir : Dir)
  | query (yesState : Nat) (noState : Nat)
  deriving DecidableEq, Repr, BEq

/-- One transition rule in a finite OTM table. -/
public structure Rule where
  state : Nat
  inPat : SymPat
  w1Pat : SymPat
  w2Pat : SymPat
  qPat : SymPat
  act : Action
  deriving DecidableEq, Repr, BEq

/-- Explicit finite 4-tape Oracle Turing Machine (start state is 0). -/
public structure OTM where
  rules : List Rule
  deriving DecidableEq, Repr, BEq

/-- Write an optional symbol to a one-sided infinite tape `Nat → Sym`. -/
def writeOpt (tape : Nat → Sym) (pos : Nat) : Option Sym → (Nat → Sym)
  | none => tape
  | some s => fun i => if i == pos then s else tape i

/-- Read the binary query string from cells `0 .. qHead - 1` of the query tape.
    (`Sym.one` reads as `true`; all other symbols read as `false`.) -/
def readQueryAux (tape : Nat → Sym) : Nat → List Bool
  | 0 => []
  | k + 1 => readQueryAux tape k ++ [tape k == Sym.one]

def readQuery (tape : Nat → Sym) (qHead : Nat) : List Bool :=
  readQueryAux tape qHead

public theorem readQuery_length (tape : Nat → Sym) (qHead : Nat) :
    (readQuery tape qHead).length = qHead := by
  unfold readQuery
  induction qHead with
  | zero => rfl
  | succ k ih =>
    simp [readQueryAux, List.length_append, ih]

public theorem readQueryAux_congr {t1 t2 : Nat → Sym} {k : Nat}
    (h : ∀ i < k, t1 i = t2 i) : readQueryAux t1 k = readQueryAux t2 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [readQueryAux]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

/-- Full machine configuration of a 4-tape OTM. -/
public structure Config where
  state : Nat
  inTape : Nat → Sym
  inHead : Nat
  w1Tape : Nat → Sym
  w1Head : Nat
  w2Tape : Nat → Sym
  w2Head : Nat
  qTape : Nat → Sym
  qHead : Nat
  halted : Option Bool

def blankTape : Nat → Sym := fun _ => Sym.blank

def tapeOfList (xs : List Sym) : Nat → Sym :=
  fun i => xs.getD i Sym.blank

def initConfig (inp : List Sym) : Config :=
  { state := 0
    inTape := tapeOfList inp
    inHead := 0
    w1Tape := blankTape
    w1Head := 0
    w2Tape := blankTape
    w2Head := 0
    qTape := blankTape
    qHead := 0
    halted := none }

def findAction (rules : List Rule) (st : Nat) (sIn sW1 sW2 sQ : Sym) : Action :=
  match rules.find? (fun r =>
      r.state == st && r.inPat.matches sIn && r.w1Pat.matches sW1 &&
      r.w2Pat.matches sW2 && r.qPat.matches sQ) with
  | some r => r.act
  | none => Action.haltReject

/-- Single step with optional logged oracle query. -/
def stepLog (O : Oracle) (M : OTM) (cfg : Config) : Config × Option (List Bool) :=
  match cfg.halted with
  | some _ => (cfg, none)
  | none =>
    let sIn := cfg.inTape cfg.inHead
    let sW1 := cfg.w1Tape cfg.w1Head
    let sW2 := cfg.w2Tape cfg.w2Head
    let sQ  := cfg.qTape  cfg.qHead
    match findAction M.rules cfg.state sIn sW1 sW2 sQ with
    | .haltAccept => ({ cfg with halted := some true }, none)
    | .haltReject => ({ cfg with halted := some false }, none)
    | .step ns inD w1W w1D w2W w2D qW qD =>
      ({ cfg with
          state  := ns
          inHead := moveHead cfg.inHead inD
          w1Tape := writeOpt cfg.w1Tape cfg.w1Head w1W
          w1Head := moveHead cfg.w1Head w1D
          w2Tape := writeOpt cfg.w2Tape cfg.w2Head w2W
          w2Head := moveHead cfg.w2Head w2D
          qTape  := writeOpt cfg.qTape  cfg.qHead  qW
          qHead  := moveHead cfg.qHead  qD }, none)
    | .query yS nS =>
      let q := readQuery cfg.qTape cfg.qHead
      let ans := O q
      ({ cfg with
          state := if ans then yS else nS
          qTape := blankTape
          qHead := 0 }, some q)

/-- Multi-step execution returning final configuration and list of all oracle queries made. -/
def runLog (O : Oracle) (M : OTM) : Nat → Config → Config × List (List Bool)
  | 0, cfg => (cfg, [])
  | t + 1, cfg =>
    let (cfg1, oq) := stepLog O M cfg
    let (cfgF, qs) := runLog O M t cfg1
    match oq with
    | none => (cfgF, qs)
    | some q => (cfgF, q :: qs)

def run (O : Oracle) (M : OTM) (t : Nat) (cfg : Config) : Config :=
  (runLog O M t cfg).1

public theorem run_zero (O : Oracle) (M : OTM) (cfg : Config) :
    run O M 0 cfg = cfg := rfl

public theorem run_succ (O : Oracle) (M : OTM) (t : Nat) (cfg : Config) :
    run O M (t + 1) cfg = run O M t (stepLog O M cfg).1 := by
  unfold run
  simp only [runLog]
  cases h : stepLog O M cfg with
  | mk c1 oq =>
    cases h2 : runLog O M t c1 with
    | mk cf qs =>
      cases oq <;> rfl

public theorem run_add (O : Oracle) (M : OTM) (t1 t2 : Nat) (cfg : Config) :
    run O M (t1 + t2) cfg = run O M t2 (run O M t1 cfg) := by
  induction t1 generalizing cfg with
  | zero =>
    rw [Nat.zero_add, run_zero]
  | succ t1 ih =>
    rw [Nat.succ_add, run_succ, run_succ, ih]

public theorem stepLog_halted (O : Oracle) (M : OTM) (cfg : Config) (b : Bool)
    (hh : cfg.halted = some b) :
    stepLog O M cfg = (cfg, none) := by
  unfold stepLog; rw [hh]

public theorem stepLog_none (O : Oracle) (M : OTM) (cfg : Config) (hh : cfg.halted = none) :
    stepLog O M cfg =
    match findAction M.rules cfg.state (cfg.inTape cfg.inHead) (cfg.w1Tape cfg.w1Head)
        (cfg.w2Tape cfg.w2Head) (cfg.qTape cfg.qHead) with
    | .haltAccept => ({ cfg with halted := some true }, none)
    | .haltReject => ({ cfg with halted := some false }, none)
    | .step ns inD w1W w1D w2W w2D qW qD =>
      ({ cfg with
          state  := ns
          inHead := moveHead cfg.inHead inD
          w1Tape := writeOpt cfg.w1Tape cfg.w1Head w1W
          w1Head := moveHead cfg.w1Head w1D
          w2Tape := writeOpt cfg.w2Tape cfg.w2Head w2W
          w2Head := moveHead cfg.w2Head w2D
          qTape  := writeOpt cfg.qTape  cfg.qHead  qW
          qHead  := moveHead cfg.qHead  qD }, none)
    | .query yS nS =>
      let q := readQuery cfg.qTape cfg.qHead
      ({ cfg with
          state := if O q then yS else nS
          qTape := blankTape
          qHead := 0 }, some q) := by
  unfold stepLog; rw [hh]

public theorem stepLog_eq_step (O : Oracle) (M : OTM) (cfg : Config)
    (hh : cfg.halted = none)
    {ns : Nat} {inD : Dir} {w1W : Option Sym} {w1D : Dir}
    {w2W : Option Sym} {w2D : Dir} {qW : Option Sym} {qD : Dir}
    (hact : findAction M.rules cfg.state (cfg.inTape cfg.inHead) (cfg.w1Tape cfg.w1Head)
              (cfg.w2Tape cfg.w2Head) (cfg.qTape cfg.qHead) =
            Action.step ns inD w1W w1D w2W w2D qW qD) :
    (stepLog O M cfg).1 =
    { cfg with
        state  := ns
        inHead := moveHead cfg.inHead inD
        w1Tape := writeOpt cfg.w1Tape cfg.w1Head w1W
        w1Head := moveHead cfg.w1Head w1D
        w2Tape := writeOpt cfg.w2Tape cfg.w2Head w2W
        w2Head := moveHead cfg.w2Head w2D
        qTape  := writeOpt cfg.qTape  cfg.qHead  qW
        qHead  := moveHead cfg.qHead  qD } := by
  rw [stepLog_none O M cfg hh, hact]

public theorem stepLog_eq_haltReject (O : Oracle) (M : OTM) (cfg : Config)
    (hh : cfg.halted = none)
    (hact : findAction M.rules cfg.state (cfg.inTape cfg.inHead) (cfg.w1Tape cfg.w1Head)
              (cfg.w2Tape cfg.w2Head) (cfg.qTape cfg.qHead) = Action.haltReject) :
    (stepLog O M cfg).1 = { cfg with halted := some false } := by
  rw [stepLog_none O M cfg hh, hact]

public theorem stepLog_eq_haltAccept (O : Oracle) (M : OTM) (cfg : Config)
    (hh : cfg.halted = none)
    (hact : findAction M.rules cfg.state (cfg.inTape cfg.inHead) (cfg.w1Tape cfg.w1Head)
              (cfg.w2Tape cfg.w2Head) (cfg.qTape cfg.qHead) = Action.haltAccept) :
    (stepLog O M cfg).1 = { cfg with halted := some true } := by
  rw [stepLog_none O M cfg hh, hact]

public theorem stepLog_eq_query (O : Oracle) (M : OTM) (cfg : Config)
    (hh : cfg.halted = none) {yS nS : Nat}
    (hact : findAction M.rules cfg.state (cfg.inTape cfg.inHead) (cfg.w1Tape cfg.w1Head)
              (cfg.w2Tape cfg.w2Head) (cfg.qTape cfg.qHead) = Action.query yS nS) :
    (stepLog O M cfg).1 =
    { cfg with
        state := if O (readQuery cfg.qTape cfg.qHead) then yS else nS
        qTape := blankTape
        qHead := 0 } := by
  rw [stepLog_none O M cfg hh, hact]

public theorem run_halted_preserved (O : Oracle) (M : OTM) (t : Nat) (cfg : Config)
    (b : Bool) (hh : cfg.halted = some b) :
    (run O M t cfg).halted = some b := by
  induction t generalizing cfg with
  | zero => exact hh
  | succ t ih =>
    rw [run_succ, stepLog_halted O M cfg b hh]
    exact ih cfg hh

public theorem run_halted_mono (O : Oracle) (M : OTM) {t1 t2 : Nat} (hle : t1 ≤ t2)
    (cfg : Config) (b : Bool) (hh : (run O M t1 cfg).halted = some b) :
    (run O M t2 cfg).halted = some b := by
  have hsplit : t2 = t1 + (t2 - t1) := by omega
  rw [hsplit, run_add]
  exact run_halted_preserved O M (t2 - t1) (run O M t1 cfg) b hh

/-- Query-count bound: at most `t` oracle queries can be issued in `t` steps. -/
public theorem runLog_query_count (O : Oracle) (M : OTM) (t : Nat) (cfg : Config) :
    (runLog O M t cfg).2.length ≤ t := by
  induction t generalizing cfg with
  | zero => simp [runLog]
  | succ t ih =>
    simp only [runLog]
    cases h : stepLog O M cfg with
    | mk cfg1 oq =>
      have hrec := ih cfg1
      cases h2 : runLog O M t cfg1 with
      | mk cf qs =>
        rw [h2] at hrec
        simp only at hrec
        cases oq with
        | none => exact Nat.le_trans hrec (Nat.le_succ t)
        | some q => simp only [List.length_cons]; omega

private theorem stepLog_qHead_le (O : Oracle) (M : OTM) (cfg : Config) :
    (stepLog O M cfg).1.qHead ≤ cfg.qHead + 1 ∧
    ∀ q, (stepLog O M cfg).2 = some q → q.length = cfg.qHead := by
  cases hh : cfg.halted with
  | some b =>
    rw [stepLog_halted O M cfg b hh]
    refine ⟨Nat.le_succ _, ?_⟩
    intro q h; cases h
  | none =>
    rw [stepLog_none O M cfg hh]
    cases findAction M.rules cfg.state (cfg.inTape cfg.inHead) (cfg.w1Tape cfg.w1Head)
        (cfg.w2Tape cfg.w2Head) (cfg.qTape cfg.qHead) with
    | haltAccept =>
      refine ⟨Nat.le_succ _, ?_⟩; intro q h; cases h
    | haltReject =>
      refine ⟨Nat.le_succ _, ?_⟩; intro q h; cases h
    | step _ _ _ _ _ _ _ qD =>
      refine ⟨moveHead_le_succ cfg.qHead qD, ?_⟩; intro q h; cases h
    | query _ _ =>
      refine ⟨Nat.zero_le _, ?_⟩
      intro q h
      injection h with hq
      rw [← hq, readQuery_length]

/-- Query-length bound: every query issued in `t` steps has length `≤ cfg.qHead + t`. -/
public theorem runLog_query_len (O : Oracle) (M : OTM) (t : Nat) (cfg : Config) :
    ∀ q ∈ (runLog O M t cfg).2, q.length ≤ cfg.qHead + t := by
  induction t generalizing cfg with
  | zero =>
    intro q hq; simp [runLog] at hq
  | succ t ih =>
    intro q hq
    simp only [runLog] at hq
    cases hs : stepLog O M cfg with
    | mk cfg1 oq =>
      rw [hs] at hq
      have ⟨hhead, hqlen⟩ := stepLog_qHead_le O M cfg
      rw [hs] at hhead hqlen
      simp only at hhead
      cases h2 : runLog O M t cfg1 with
      | mk cf qs =>
        rw [h2] at hq
        have ih' := ih cfg1
        rw [h2] at ih'
        cases oq with
        | none =>
          have hlen := ih' q hq
          omega
        | some q0 =>
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hmem
          · have h0 := hqlen q rfl
            omega
          · have hlen := ih' q hmem
            omega

/-- Oracle locality lemma: if two oracles agree on every query actually made by `M`
    under `O1` in `t` steps, then `M` produces the exact same configuration and query log under `O2`. -/
public theorem runLog_oracle_agree (O1 O2 : Oracle) (M : OTM) (t : Nat) (cfg : Config)
    (hagree : ∀ q ∈ (runLog O1 M t cfg).2, O1 q = O2 q) :
    runLog O1 M t cfg = runLog O2 M t cfg := by
  induction t generalizing cfg with
  | zero => rfl
  | succ t ih =>
    have hstep : stepLog O1 M cfg = stepLog O2 M cfg := by
      cases hh : cfg.halted with
      | some b =>
        rw [stepLog_halted O1 M cfg b hh, stepLog_halted O2 M cfg b hh]
      | none =>
        rw [stepLog_none O1 M cfg hh, stepLog_none O2 M cfg hh]
        cases hact : findAction M.rules cfg.state (cfg.inTape cfg.inHead) (cfg.w1Tape cfg.w1Head)
            (cfg.w2Tape cfg.w2Head) (cfg.qTape cfg.qHead) with
        | haltAccept => rfl
        | haltReject => rfl
        | step _ _ _ _ _ _ _ _ => rfl
        | query yS nS =>
          have hqmem : readQuery cfg.qTape cfg.qHead ∈ (runLog O1 M (t + 1) cfg).2 := by
            simp only [runLog]
            rw [stepLog_none O1 M cfg hh, hact]
            cases runLog O1 M t _ with
            | mk cf qs => exact List.mem_cons_self
          have heq := hagree _ hqmem
          simp [heq]
    simp only [runLog]
    rw [← hstep]
    cases hs : stepLog O1 M cfg with
    | mk cfg1 oq =>
      have hagree' : ∀ q ∈ (runLog O1 M t cfg1).2, O1 q = O2 q := by
        intro q hq
        apply hagree
        simp only [runLog]
        rw [hs]
        cases h2 : runLog O1 M t cfg1 with
        | mk cf qs =>
          rw [h2] at hq
          cases oq with
          | none => exact hq
          | some q0 => exact List.mem_cons_of_mem q0 hq
      rw [ih cfg1 hagree']

public theorem run_oracle_agree_le (O1 O2 : Oracle) (M : OTM) (t : Nat) (inp : List Sym)
    (hagree : ∀ q : List Bool, q.length ≤ t → O1 q = O2 q) :
    run O1 M t (initConfig inp) = run O2 M t (initConfig inp) := by
  have hlog := runLog_oracle_agree O1 O2 M t (initConfig inp) (by
    intro q hq
    have hlen := runLog_query_len O1 M t (initConfig inp) q hq
    simp [initConfig] at hlen
    exact hagree q hlen)
  exact congrArg Prod.fst hlog

/-- Input encodings for decision machines (`x`) and verifiers (`x # w`). -/
def encodeBits (xs : List Bool) : List Sym :=
  xs.map (fun b => if b then Sym.one else Sym.zero)

def encodePair (x w : List Bool) : List Sym :=
  encodeBits x ++ [Sym.sep] ++ encodeBits w

/-- Polynomial time bound `(n + 1)^c + c`. -/
def polyBound (c n : Nat) : Nat :=
  (n + 1) ^ c + c

/-- `M` decides language `L` relative to oracle `O` within polynomial bound `polyBound c`. -/
def DecidesInPoly (O : Oracle) (M : OTM) (L : Language) (c : Nat) : Prop :=
  ∀ x : List Bool, (run O M (polyBound c x.length) (initConfig (encodeBits x))).halted = some (L x)

/-- Complexity class `P^O`: languages decided by a polynomial-time deterministic 4-tape OTM. -/
def InP (O : Oracle) (L : Language) : Prop :=
  ∃ M : OTM, ∃ c : Nat, DecidesInPoly O M L c

/-- Complexity class `NP^O`: languages verified by a polynomial-time deterministic 4-tape OTM
    taking `(x # w)` with witness length bounded by `polyBound d |x|`. -/
def InNP (O : Oracle) (L : Language) : Prop :=
  ∃ V : OTM, ∃ c d : Nat, ∀ x : List Bool,
    L x = true ↔
      ∃ w : List Bool, w.length ≤ polyBound d x.length ∧
        (run O V (polyBound c x.length) (initConfig (encodePair x w))).halted = some true

-- ============================================================================
-- Non-Vacuity Theorem: `P^O ⊆ NP^O` for EVERY oracle `O` and EVERY language `L`!
-- ============================================================================

end

private def shiftAction (off : Nat) : Action → Action
  | .haltAccept => .haltAccept
  | .haltReject => .haltReject
  | .step ns inD w1W w1D w2W w2D qW qD => .step (ns + off) inD w1W w1D w2W w2D qW qD
  | .query yS nS => .query (yS + off) (nS + off)

private def shiftRule (off : Nat) (r : Rule) : Rule :=
  { r with state := r.state + off, act := shiftAction off r.act }

private def expandSepPat : SymPat → List SymPat
  | .exact .blank => [.exact .blank, .exact .sep]
  | .exact .sep => []
  | p => [p]

private def expandRuleSep (r : Rule) : List Rule :=
  (expandSepPat r.inPat).map (fun ip => { r with inPat := ip })

private def wrapPrefixRules : List Rule := [
  { state := 0, inPat := .exact .zero, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step 0 .right (some .one) .right none .stay none .stay },
  { state := 0, inPat := .exact .one,  w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step 0 .right (some .one) .right none .stay none .stay },
  { state := 0, inPat := .exact .sep,  w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step 1 .right none .stay none .stay none .stay },
  { state := 1, inPat := .exact .blank, w1Pat := .any, w2Pat := .any, qPat := .any,
    act := .step 2 .left none .left none .stay none .stay },
  { state := 2, inPat := .any, w1Pat := .exact .one, w2Pat := .any, qPat := .any,
    act := .step 2 .left (some .blank) .left none .stay none .stay },
  { state := 2, inPat := .any, w1Pat := .exact .blank, w2Pat := .any, qPat := .any,
    act := .step 3 .stay none .stay none .stay none .stay }
]

/-- Verifier wrapper `wrapDecisionAsVerifier M`: rejects any non-empty witness `w`,
    rewinds to cell 0 when `w = []`, and runs `M` shifted by +3 treating `.sep` as `.blank`. -/
public def wrapDecisionAsVerifier (M : OTM) : OTM :=
  { rules := wrapPrefixRules ++ (M.rules.flatMap expandRuleSep).map (shiftRule 3) }

private def mapSepToBlank (s : Sym) : Sym :=
  if s == Sym.sep then Sym.blank else s

private theorem findAction_shift_append (pref rest : List Rule)
    (hpref : ∀ r ∈ pref, r.state < 3) (st : Nat) (sIn sW1 sW2 sQ : Sym) :
    findAction (pref ++ rest.map (shiftRule 3)) (st + 3) sIn sW1 sW2 sQ =
    shiftAction 3 (findAction rest st sIn sW1 sW2 sQ) := by
  unfold findAction
  have hnone : pref.find? (fun r =>
      r.state == st + 3 && r.inPat.matches sIn && r.w1Pat.matches sW1 &&
      r.w2Pat.matches sW2 && r.qPat.matches sQ) = none := by
    rw [List.find?_eq_none]
    intro r hr htrue
    have hlt := hpref r hr
    simp only [Bool.and_eq_true] at htrue
    have heq : r.state = st + 3 := beq_iff_eq.mp htrue.1.1.1.1
    omega
  rw [List.find?_append, hnone, Option.none_or]
  induction rest with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.find?_cons]
    have hmatch :
        ((shiftRule 3 r).state == st + 3 && (shiftRule 3 r).inPat.matches sIn &&
          (shiftRule 3 r).w1Pat.matches sW1 && (shiftRule 3 r).w2Pat.matches sW2 &&
          (shiftRule 3 r).qPat.matches sQ) =
        (r.state == st && r.inPat.matches sIn && r.w1Pat.matches sW1 &&
          r.w2Pat.matches sW2 && r.qPat.matches sQ) := by
      simp only [shiftRule]
      have hst : (r.state + 3 == st + 3) = (r.state == st) := by
        cases h : (r.state == st)
        · simp at h; simp [h]
        · simp at h; simp [h]
      rw [hst]
    rw [hmatch]
    cases (r.state == st && r.inPat.matches sIn && r.w1Pat.matches sW1 &&
           r.w2Pat.matches sW2 && r.qPat.matches sQ) with
    | false => exact ih
    | true => rfl

private theorem findAction_cons (r : Rule) (rs : List Rule) (st : Nat) (sIn sW1 sW2 sQ : Sym) :
    findAction (r :: rs) st sIn sW1 sW2 sQ =
    if (r.state == st && r.inPat.matches sIn && r.w1Pat.matches sW1 &&
        r.w2Pat.matches sW2 && r.qPat.matches sQ)
    then r.act
    else findAction rs st sIn sW1 sW2 sQ := by
  unfold findAction
  simp only [List.find?_cons]
  cases (r.state == st && r.inPat.matches sIn && r.w1Pat.matches sW1 &&
         r.w2Pat.matches sW2 && r.qPat.matches sQ) <;> rfl

private theorem sym_beq_eq (a b : Sym) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> rfl

private theorem findAction_sepAsBlank (rules : List Rule) (st : Nat) (sIn sW1 sW2 sQ : Sym) :
    findAction (rules.flatMap expandRuleSep) st sIn sW1 sW2 sQ =
    findAction rules st (mapSepToBlank sIn) sW1 sW2 sQ := by
  induction rules with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨rst, rip, rw1, rw2, rq, ract⟩
    cases rip with
    | any =>
      change findAction ({ state := rst, inPat := SymPat.any, w1Pat := rw1, w2Pat := rw2, qPat := rq, act := ract } ::
                         rs.flatMap expandRuleSep) st sIn sW1 sW2 sQ = _
      rw [findAction_cons, findAction_cons, ih]
      simp [SymPat.matches]
    | exact ps =>
      cases ps with
      | blank =>
        change findAction ({ state := rst, inPat := SymPat.exact Sym.blank, w1Pat := rw1, w2Pat := rw2, qPat := rq, act := ract } ::
                           { state := rst, inPat := SymPat.exact Sym.sep, w1Pat := rw1, w2Pat := rw2, qPat := rq, act := ract } ::
                           rs.flatMap expandRuleSep) st sIn sW1 sW2 sQ = _
        rw [findAction_cons, findAction_cons, findAction_cons, ih]
        cases sIn <;> simp [SymPat.matches, mapSepToBlank, sym_beq_eq]
      | zero =>
        change findAction ({ state := rst, inPat := SymPat.exact Sym.zero, w1Pat := rw1, w2Pat := rw2, qPat := rq, act := ract } ::
                           rs.flatMap expandRuleSep) st sIn sW1 sW2 sQ = _
        rw [findAction_cons, findAction_cons, ih]
        cases sIn <;> simp [SymPat.matches, mapSepToBlank, sym_beq_eq]
      | one =>
        change findAction ({ state := rst, inPat := SymPat.exact Sym.one, w1Pat := rw1, w2Pat := rw2, qPat := rq, act := ract } ::
                           rs.flatMap expandRuleSep) st sIn sW1 sW2 sQ = _
        rw [findAction_cons, findAction_cons, ih]
        cases sIn <;> simp [SymPat.matches, mapSepToBlank, sym_beq_eq]
      | sep =>
        change findAction (rs.flatMap expandRuleSep) st sIn sW1 sW2 sQ = _
        rw [findAction_cons, ih]
        cases sIn <;> simp [SymPat.matches, mapSepToBlank, sym_beq_eq]

private theorem wrap_findAction_lt3 (M : OTM) (st : Nat) (sIn sW1 sW2 sQ : Sym) (hst : st < 3) :
    findAction (wrapDecisionAsVerifier M).rules st sIn sW1 sW2 sQ =
    findAction wrapPrefixRules st sIn sW1 sW2 sQ := by
  unfold wrapDecisionAsVerifier findAction
  rw [List.find?_append]
  have hnone : ((M.rules.flatMap expandRuleSep).map (shiftRule 3)).find? (fun r =>
      r.state == st && r.inPat.matches sIn && r.w1Pat.matches sW1 &&
      r.w2Pat.matches sW2 && r.qPat.matches sQ) = none := by
    rw [List.find?_eq_none]
    intro r hr htrue
    rw [List.mem_map] at hr
    rcases hr with ⟨r0, _, rfl⟩
    simp only [shiftRule, Bool.and_eq_true] at htrue
    have heq : r0.state + 3 = st := beq_iff_eq.mp htrue.1.1.1.1
    omega
  rw [hnone]
  cases wrapPrefixRules.find? (fun r =>
      r.state == st && r.inPat.matches sIn && r.w1Pat.matches sW1 &&
      r.w2Pat.matches sW2 && r.qPat.matches sQ) <;> rfl

private theorem wrap_phase3_sim (O : Oracle) (M : OTM) (t : Nat) (c1 c2 : Config)
    (hEq : c1.state = c2.state + 3 ∧ c1.inHead = c2.inHead ∧
           c1.w1Tape = c2.w1Tape ∧ c1.w1Head = c2.w1Head ∧
           c1.w2Tape = c2.w2Tape ∧ c1.w2Head = c2.w2Head ∧
           c1.qTape = c2.qTape ∧ c1.qHead = c2.qHead ∧
           c1.halted = c2.halted)
    (hmatch : ∀ i, mapSepToBlank (c1.inTape i) = c2.inTape i) :
    (run O (wrapDecisionAsVerifier M) t c1).halted = (run O M t c2).halted := by
  induction t generalizing c1 c2 with
  | zero =>
    rw [run_zero, run_zero]
    exact hEq.2.2.2.2.2.2.2.2
  | succ t ih =>
    rw [run_succ, run_succ]
    rcases hEq with ⟨hst, hin, hw1t, hw1h, hw2t, hw2h, hqt, hqh, hhalt⟩
    cases hhalt' : c2.halted with
    | some b =>
      rw [stepLog_halted O (wrapDecisionAsVerifier M) c1 b (by rw [hhalt, hhalt']),
          stepLog_halted O M c2 b hhalt']
      rw [run_halted_preserved _ _ _ _ b (by rw [hhalt, hhalt']),
          run_halted_preserved _ _ _ _ b hhalt']
    | none =>
      rw [stepLog_none O (wrapDecisionAsVerifier M) c1 (by rw [hhalt, hhalt']),
          stepLog_none O M c2 hhalt']
      simp only [wrapDecisionAsVerifier]
      rw [hst, hin, hw1t, hw1h, hw2t, hw2h, hqt, hqh]
      rw [findAction_shift_append _ _ (by intro r hr; simp [wrapPrefixRules] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
      rw [findAction_sepAsBlank, hmatch c2.inHead]
      cases findAction M.rules c2.state (c2.inTape c2.inHead) (c2.w1Tape c2.w1Head)
          (c2.w2Tape c2.w2Head) (c2.qTape c2.qHead) with
      | haltAccept =>
        simp only [shiftAction]
        rw [run_halted_preserved _ _ _ _ true rfl, run_halted_preserved _ _ _ _ true rfl]
      | haltReject =>
        simp only [shiftAction]
        rw [run_halted_preserved _ _ _ _ false rfl, run_halted_preserved _ _ _ _ false rfl]
      | step ns inD w1W w1D w2W w2D qW qD =>
        simp only [shiftAction]
        apply ih
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by rw [hhalt, hhalt']⟩
        · exact hmatch
      | query yS nS =>
        simp only [shiftAction]
        apply ih
        · exact ⟨by cases O (readQuery c2.qTape c2.qHead) <;> rfl,
                 rfl, rfl, rfl, rfl, rfl, rfl, rfl, by rw [hhalt, hhalt']⟩
        · exact hmatch

private theorem encodePair_at_lt (x w : List Bool) (i : Nat) (hi : i < x.length) :
    tapeOfList (encodePair x w) i = if x[i] then Sym.one else Sym.zero := by
  unfold tapeOfList encodePair
  rw [List.append_assoc]
  have hlen : (encodeBits x).length = x.length := List.length_map ..
  have hlt : i < (encodeBits x).length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
  unfold encodeBits
  simp [hi]

private theorem encodePair_at_eq (x w : List Bool) :
    tapeOfList (encodePair x w) x.length = Sym.sep := by
  unfold tapeOfList encodePair
  rw [List.append_assoc]
  have hlen : (encodeBits x).length = x.length := List.length_map ..
  have hle : (encodeBits x).length ≤ x.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hle, hlen, Nat.sub_self]
  rfl

private theorem encodePair_at_succ (x w : List Bool) :
    tapeOfList (encodePair x w) (x.length + 1) =
    match w with
    | [] => Sym.blank
    | b :: _ => if b then Sym.one else Sym.zero := by
  unfold tapeOfList encodePair
  rw [List.append_assoc]
  have hlen : (encodeBits x).length = x.length := List.length_map ..
  have hle : (encodeBits x).length ≤ x.length + 1 := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hle, hlen, Nat.add_sub_cancel_left]
  cases w with
  | nil => rfl
  | cons b bs => rfl

private def prefixOnes (k : Nat) : Nat → Sym :=
  fun i => if i < k then Sym.one else Sym.blank

private theorem wrap_scan_x (O : Oracle) (M : OTM) (x w : List Bool) :
    ∀ k ≤ x.length,
    run O (wrapDecisionAsVerifier M) k (initConfig (encodePair x w)) =
    { (initConfig (encodePair x w)) with
      state := 0
      inHead := k
      w1Tape := prefixOnes k
      w1Head := k } := by
  intro k hk
  induction k with
  | zero =>
    rw [run_zero]
    have hblank : blankTape = prefixOnes 0 := by
      funext i; simp [blankTape, prefixOnes]
    unfold initConfig
    simp [hblank]
  | succ k ih =>
    have hk' : k < x.length := by omega
    rw [run_add O _ k 1, ih (by omega), run_succ, run_zero]
    have hsym : tapeOfList (encodePair x w) k = if x[k] then Sym.one else Sym.zero :=
      encodePair_at_lt x w k hk'
    have hwt : writeOpt (prefixOnes k) k (some Sym.one) = prefixOnes (k + 1) := by
      funext i
      unfold writeOpt prefixOnes
      by_cases hi : i = k
      · subst hi; simp
      · have hbeq : (i == k) = false := beq_false_of_ne hi
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        have : (i < k) ↔ (i < k + 1) := by omega
        by_cases hlt : i < k <;> simp [hlt, show (i < k + 1) ↔ (i < k) from this.symm]
    have hact : findAction (wrapDecisionAsVerifier M).rules 0
        (tapeOfList (encodePair x w) k) (prefixOnes k k) (blankTape 0) (blankTape 0) =
        Action.step 0 Dir.right (some Sym.one) Dir.right none Dir.stay none Dir.stay := by
      rw [wrap_findAction_lt3 M 0 _ _ _ _ (by decide), hsym]
      simp only [blankTape]
      cases x[k] <;> cases (prefixOnes k k) <;> rfl
    rw [stepLog_eq_step O (wrapDecisionAsVerifier M) _ rfl hact]
    rw [hwt]
    simp only [moveHead, writeOpt]

private theorem wrap_rewind_x (O : Oracle) (M : OTM) (x : List Bool) :
    ∀ k : Nat,
    run O (wrapDecisionAsVerifier M) k
      { (initConfig (encodePair x [])) with
        state := 2
        inHead := k
        w1Tape := prefixOnes k
        w1Head := k - 1 } =
    { (initConfig (encodePair x [])) with
      state := 2
      inHead := 0
      w1Tape := blankTape
      w1Head := 0 } := by
  intro k
  induction k with
  | zero =>
    rw [run_zero]
    have hblank : prefixOnes 0 = blankTape := by funext i; simp [prefixOnes, blankTape]
    simp [hblank]
  | succ k ih =>
    rw [run_succ]
    have hsub : k + 1 - 1 = k := Nat.add_sub_cancel k 1
    rw [hsub]
    have h1 : prefixOnes (k + 1) k = Sym.one := by simp [prefixOnes]
    have hwt : writeOpt (prefixOnes (k + 1)) k (some Sym.blank) = prefixOnes k := by
      funext i
      unfold writeOpt prefixOnes
      by_cases hi : i = k
      · subst hi; simp
      · have hbeq : (i == k) = false := beq_false_of_ne hi
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        have : (i < k + 1) ↔ (i < k) := by omega
        by_cases hlt : i < k <;> simp [hlt, show (i < k + 1) ↔ (i < k) from this]
    have hact : findAction (wrapDecisionAsVerifier M).rules 2
        (tapeOfList (encodePair x []) (k + 1)) (prefixOnes (k + 1) k) (blankTape 0) (blankTape 0) =
        Action.step 2 Dir.left (some Sym.blank) Dir.left none Dir.stay none Dir.stay := by
      rw [wrap_findAction_lt3 M 2 _ _ _ _ (by decide), h1]
      simp only [blankTape]
      cases (tapeOfList (encodePair x []) (k + 1)) <;> rfl
    rw [stepLog_eq_step O (wrapDecisionAsVerifier M) _ rfl hact]
    rw [hwt]
    simp only [moveHead, writeOpt, Nat.add_sub_cancel]
    exact ih

private theorem wrap_reject_nonempty_witness (O : Oracle) (M : OTM) (x : List Bool)
    (b : Bool) (bs : List Bool) :
    (run O (wrapDecisionAsVerifier M) (x.length + 2) (initConfig (encodePair x (b :: bs)))).halted =
    some false := by
  rw [run_add O _ x.length 2, wrap_scan_x O M x (b :: bs) x.length (Nat.le_refl _)]
  rw [run_succ, run_succ, run_zero]
  have hsep : tapeOfList (encodePair x (b :: bs)) x.length = Sym.sep :=
    encodePair_at_eq x (b :: bs)
  have hact1 : findAction (wrapDecisionAsVerifier M).rules 0
      (tapeOfList (encodePair x (b :: bs)) x.length) (prefixOnes x.length x.length)
      (blankTape 0) (blankTape 0) =
      Action.step 1 Dir.right none Dir.stay none Dir.stay none Dir.stay := by
    rw [wrap_findAction_lt3 M 0 _ _ _ _ (by decide), hsep]
    simp only [blankTape]
    cases (prefixOnes x.length x.length) <;> rfl
  have hs1 :
      (stepLog O (wrapDecisionAsVerifier M)
        { (initConfig (encodePair x (b :: bs))) with
          state := 0
          inHead := x.length
          w1Tape := prefixOnes x.length
          w1Head := x.length }).1 =
      { (initConfig (encodePair x (b :: bs))) with
        state := 1
        inHead := x.length + 1
        w1Tape := prefixOnes x.length
        w1Head := x.length } := by
    rw [stepLog_eq_step O (wrapDecisionAsVerifier M) _ rfl hact1]
    rfl
  rw [hs1]
  have hnext : tapeOfList (encodePair x (b :: bs)) (x.length + 1) = if b then Sym.one else Sym.zero :=
    encodePair_at_succ x (b :: bs)
  have hact2 : findAction (wrapDecisionAsVerifier M).rules 1
      (tapeOfList (encodePair x (b :: bs)) (x.length + 1)) (prefixOnes x.length x.length)
      (blankTape 0) (blankTape 0) = Action.haltReject := by
    rw [wrap_findAction_lt3 M 1 _ _ _ _ (by decide), hnext]
    simp only [blankTape]
    cases b <;> cases (prefixOnes x.length x.length) <;> rfl
  rw [stepLog_eq_haltReject O (wrapDecisionAsVerifier M) _ rfl hact2]

private theorem wrap_empty_witness_phase3 (O : Oracle) (M : OTM) (x : List Bool) :
    run O (wrapDecisionAsVerifier M) (2 * x.length + 3) (initConfig (encodePair x [])) =
    { (initConfig (encodePair x [])) with state := 3 } := by
  have hsplit : 2 * x.length + 3 = x.length + 2 + x.length + 1 := by omega
  rw [hsplit, run_add, run_add, run_add]
  rw [wrap_scan_x O M x [] x.length (Nat.le_refl _)]
  have hsep : tapeOfList (encodePair x []) x.length = Sym.sep := encodePair_at_eq x []
  have hblk : tapeOfList (encodePair x []) (x.length + 1) = Sym.blank := encodePair_at_succ x []
  have h2 :
      run O (wrapDecisionAsVerifier M) 2
        { (initConfig (encodePair x [])) with
          state := 0
          inHead := x.length
          w1Tape := prefixOnes x.length
          w1Head := x.length } =
      { (initConfig (encodePair x [])) with
        state := 2
        inHead := x.length
        w1Tape := prefixOnes x.length
        w1Head := x.length - 1 } := by
    rw [run_succ, run_succ, run_zero]
    have hact1 : findAction (wrapDecisionAsVerifier M).rules 0
        (tapeOfList (encodePair x []) x.length) (prefixOnes x.length x.length)
        (blankTape 0) (blankTape 0) =
        Action.step 1 Dir.right none Dir.stay none Dir.stay none Dir.stay := by
      rw [wrap_findAction_lt3 M 0 _ _ _ _ (by decide), hsep]
      simp only [blankTape]
      cases (prefixOnes x.length x.length) <;> rfl
    have hs1 :
        (stepLog O (wrapDecisionAsVerifier M)
          { (initConfig (encodePair x [])) with
            state := 0
            inHead := x.length
            w1Tape := prefixOnes x.length
            w1Head := x.length }).1 =
        { (initConfig (encodePair x [])) with
          state := 1
          inHead := x.length + 1
          w1Tape := prefixOnes x.length
          w1Head := x.length } := by
      rw [stepLog_eq_step O (wrapDecisionAsVerifier M) _ rfl hact1]
      rfl
    rw [hs1]
    have hact2 : findAction (wrapDecisionAsVerifier M).rules 1
        (tapeOfList (encodePair x []) (x.length + 1)) (prefixOnes x.length x.length)
        (blankTape 0) (blankTape 0) =
        Action.step 2 Dir.left none Dir.left none Dir.stay none Dir.stay := by
      rw [wrap_findAction_lt3 M 1 _ _ _ _ (by decide), hblk]
      simp only [blankTape]
      cases (prefixOnes x.length x.length) <;> rfl
    rw [stepLog_eq_step O (wrapDecisionAsVerifier M) _ rfl hact2]
    simp only [moveHead, writeOpt, Nat.add_sub_cancel]
  rw [h2, wrap_rewind_x O M x x.length]
  rw [run_succ, run_zero]
  have hact3 : findAction (wrapDecisionAsVerifier M).rules 2
      (tapeOfList (encodePair x []) 0) (blankTape 0) (blankTape 0) (blankTape 0) =
      Action.step 3 Dir.stay none Dir.stay none Dir.stay none Dir.stay := by
    rw [wrap_findAction_lt3 M 2 _ _ _ _ (by decide)]
    simp only [blankTape]
    cases (tapeOfList (encodePair x []) 0) <;> rfl
  rw [stepLog_eq_step O (wrapDecisionAsVerifier M) _ rfl hact3]
  rfl

private theorem mapSepToBlank_encodePair_nil (x : List Bool) (i : Nat) :
    mapSepToBlank (tapeOfList (encodePair x []) i) = tapeOfList (encodeBits x) i := by
  by_cases hlt : i < x.length
  · have h1 := encodePair_at_lt x [] i hlt
    rw [h1]
    unfold tapeOfList encodeBits
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
               List.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some]
    cases x[i] <;> rfl
  · by_cases heq : i = x.length
    · subst heq
      rw [encodePair_at_eq x []]
      unfold tapeOfList encodeBits
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp : (x.map _).length ≤ x.length)]
      rfl
    · unfold tapeOfList encodePair encodeBits
      simp only [List.map_nil, List.append_nil, List.getD_eq_getElem?_getD]
      have h1 : (x.map (fun b => if b then Sym.one else Sym.zero) ++ [Sym.sep]).length ≤ i := by
        simp; omega
      have h2 : (x.map (fun b => if b then Sym.one else Sym.zero)).length ≤ i := by
        simp; omega
      rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]
      rfl

private theorem poly_slack_p_subset_np_exact (c n : Nat) :
    2 * n + 3 + polyBound c n ≤ polyBound (c + 3) n := by
  unfold polyBound
  cases n with
  | zero =>
    simp [Nat.one_pow]
    omega
  | succ k =>
    have hbase : 2 ≤ k + 2 := by omega
    have hpow_ge1 : 1 ≤ (k + 2) ^ c := Nat.one_le_pow c (k + 2) (by omega)
    have hcube : (k + 2) ^ (c + 3) = (k + 2) ^ c * ((k + 2) * ((k + 2) * (k + 2))) := by
      rw [Nat.pow_add, Nat.pow_succ, Nat.pow_two, Nat.mul_comm ((k + 2) * (k + 2)) (k + 2)]
    have h2sq : 2 * (k + 2) ≤ (k + 2) * (k + 2) := Nat.mul_le_mul_right (k + 2) hbase
    have h4 : 4 * (k + 2) ≤ (k + 2) * ((k + 2) * (k + 2)) := by
      have : 2 * (2 * (k + 2)) ≤ (k + 2) * ((k + 2) * (k + 2)) :=
        Nat.mul_le_mul hbase h2sq
      omega
    have hbig : (k + 2) ^ c * (4 * (k + 2)) ≤ (k + 2) ^ (c + 3) := by
      rw [hcube]
      exact Nat.mul_le_mul_left ((k + 2) ^ c) h4
    have hmul : (k + 2) ^ c * (4 * (k + 2)) =
        (k + 2) ^ c * (k + 2) + 3 * ((k + 2) ^ c * (k + 2)) := by
      have h4x : 4 * (k + 2) = (k + 2) + 3 * (k + 2) := by omega
      rw [h4x, Nat.mul_add, Nat.mul_left_comm]
    have hle1 : (k + 2) ^ c ≤ (k + 2) ^ c * (k + 2) := by
      have := Nat.mul_le_mul_left ((k + 2) ^ c) (by omega : 1 ≤ k + 2)
      omega
    have hlin : 3 * (k + 2) ≤ 3 * ((k + 2) ^ c * (k + 2)) := by
      have : 1 * (k + 2) ≤ (k + 2) ^ c * (k + 2) := Nat.mul_le_mul_right (k + 2) hpow_ge1
      have : 3 * (1 * (k + 2)) ≤ 3 * ((k + 2) ^ c * (k + 2)) := Nat.mul_le_mul_left 3 this
      omega
    have heq1 : k + 1 + 1 = k + 2 := by omega
    rw [heq1]
    omega

/-- Non-vacuity theorem: `P^O ⊆ NP^O` for EVERY oracle `O` and EVERY language `L`. -/
public theorem p_subset_np (O : Oracle) (L : Language) (h : InP O L) : InNP O L := by
  rcases h with ⟨M, c, hdec⟩
  refine ⟨wrapDecisionAsVerifier M, c + 3, 0, ?_⟩
  intro x
  have hslack := poly_slack_p_subset_np_exact c x.length
  constructor
  · intro hLx
    refine ⟨[], by simp [polyBound], ?_⟩
    have hrun :
        (run O (wrapDecisionAsVerifier M) (2 * x.length + 3 + polyBound c x.length)
          (initConfig (encodePair x []))).halted = some true := by
      rw [run_add, wrap_empty_witness_phase3]
      rw [wrap_phase3_sim O M (polyBound c x.length)
            { (initConfig (encodePair x [])) with state := 3 }
            (initConfig (encodeBits x))
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            (mapSepToBlank_encodePair_nil x)]
      rw [hdec x, hLx]
    exact run_halted_mono O (wrapDecisionAsVerifier M) hslack _ true hrun
  · intro ⟨w, _, hw⟩
    cases w with
    | nil =>
      have hrun :
          (run O (wrapDecisionAsVerifier M) (2 * x.length + 3 + polyBound c x.length)
            (initConfig (encodePair x []))).halted = some (L x) := by
        rw [run_add, wrap_empty_witness_phase3]
        rw [wrap_phase3_sim O M (polyBound c x.length)
              { (initConfig (encodePair x [])) with state := 3 }
              (initConfig (encodeBits x))
              ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
              (mapSepToBlank_encodePair_nil x)]
        exact hdec x
      have hmono := run_halted_mono O (wrapDecisionAsVerifier M) hslack _ (L x) hrun
      rw [hmono] at hw
      exact Option.some.inj hw
    | cons b bs =>
      have hrej := wrap_reject_nonempty_witness O M x b bs
      have hle : x.length + 2 ≤ polyBound (c + 3) x.length := by omega
      have hmono := run_halted_mono O (wrapDecisionAsVerifier M) hle _ false hrej
      rw [hmono] at hw
      cases hw

-- ============================================================================
-- Bijective Constructive Encoding `OTM ↔ Nat` (Zero Choice, Total Left Inverse)
-- ============================================================================

public def encodeSym : Sym → Nat
  | .blank => 0 | .zero => 1 | .one => 2 | .sep => 3

public def decodeSym : Nat → Option Sym
  | 0 => some .blank | 1 => some .zero | 2 => some .one | 3 => some .sep | _ => none

public theorem decode_encodeSym (s : Sym) : decodeSym (encodeSym s) = some s := by
  cases s <;> rfl

public def encodeSymPat : SymPat → Nat
  | .any => 0
  | .exact s => encodeSym s + 1

public def decodeSymPat : Nat → Option SymPat
  | 0 => some .any
  | k + 1 => (decodeSym k).map SymPat.exact

public theorem decode_encodeSymPat (p : SymPat) : decodeSymPat (encodeSymPat p) = some p := by
  cases p with
  | any => rfl
  | exact s => simp [encodeSymPat, decodeSymPat, decode_encodeSym]

public def encodeOptSym : Option Sym → Nat
  | none => 0
  | some s => encodeSym s + 1

public def decodeOptSym : Nat → Option (Option Sym)
  | 0 => some none
  | k + 1 => (decodeSym k).map some

public theorem decode_encodeOptSym (os : Option Sym) : decodeOptSym (encodeOptSym os) = some os := by
  cases os with
  | none => rfl
  | some s => simp [encodeOptSym, decodeOptSym, decode_encodeSym]

public def encodeDir : Dir → Nat
  | .left => 0 | .stay => 1 | .right => 2

public def decodeDir : Nat → Option Dir
  | 0 => some .left | 1 => some .stay | 2 => some .right | _ => none

public theorem decode_encodeDir (d : Dir) : decodeDir (encodeDir d) = some d := by
  cases d <;> rfl

public def encodeAction : Action → Nat
  | .haltAccept => 0
  | .haltReject => 1
  | .query yS nS => pairNat 0 (pairNat yS nS) + 2
  | .step ns inD w1W w1D w2W w2D qW qD =>
    let payload :=
      pairNat ns (pairNat (encodeDir inD)
        (pairNat (encodeOptSym w1W) (pairNat (encodeDir w1D)
          (pairNat (encodeOptSym w2W) (pairNat (encodeDir w2D)
            (pairNat (encodeOptSym qW) (encodeDir qD)))))))
    pairNat 1 payload + 2

public def decodeAction : Nat → Option Action
  | 0 => some .haltAccept
  | 1 => some .haltReject
  | k + 2 =>
    let (tag, payload) := unpairNat k
    if tag == 0 then
      let (yS, nS) := unpairNat payload
      some (.query yS nS)
    else if tag == 1 then
      let (ns, r1) := unpairNat payload
      let (inDC, r2) := unpairNat r1
      let (w1WC, r3) := unpairNat r2
      let (w1DC, r4) := unpairNat r3
      let (w2WC, r5) := unpairNat r4
      let (w2DC, r6) := unpairNat r5
      let (qWC, qDC) := unpairNat r6
      do
        let inD ← decodeDir inDC
        let w1W ← decodeOptSym w1WC
        let w1D ← decodeDir w1DC
        let w2W ← decodeOptSym w2WC
        let w2D ← decodeDir w2DC
        let qW ← decodeOptSym qWC
        let qD ← decodeDir qDC
        pure (.step ns inD w1W w1D w2W w2D qW qD)
    else none

public theorem decode_encodeAction (a : Action) : decodeAction (encodeAction a) = some a := by
  cases a with
  | haltAccept => rfl
  | haltReject => rfl
  | query yS nS =>
    simp [encodeAction, decodeAction, unpair_pair]
  | step ns inD w1W w1D w2W w2D qW qD =>
    simp [encodeAction, decodeAction, unpair_pair, decode_encodeDir, decode_encodeOptSym]

public def encodeRule (r : Rule) : Nat :=
  pairNat r.state (pairNat (encodeSymPat r.inPat)
    (pairNat (encodeSymPat r.w1Pat) (pairNat (encodeSymPat r.w2Pat)
      (pairNat (encodeSymPat r.qPat) (encodeAction r.act)))))

public def decodeRule (k : Nat) : Option Rule :=
  let (st, r1) := unpairNat k
  let (inC, r2) := unpairNat r1
  let (w1C, r3) := unpairNat r2
  let (w2C, r4) := unpairNat r3
  let (qC, actC) := unpairNat r4
  do
    let inP ← decodeSymPat inC
    let w1P ← decodeSymPat w1C
    let w2P ← decodeSymPat w2C
    let qP  ← decodeSymPat qC
    let act ← decodeAction actC
    pure { state := st, inPat := inP, w1Pat := w1P, w2Pat := w2P, qPat := qP, act := act }

public theorem decode_encodeRule (r : Rule) : decodeRule (encodeRule r) = some r := by
  cases r
  simp [encodeRule, decodeRule, unpair_pair, decode_encodeSymPat, decode_encodeAction]

public def encodeRules : List Rule → Nat
  | [] => 0
  | r :: rs => pairNat (encodeRule r) (encodeRules rs) + 1

public def decodeRules : Nat → Option (List Rule)
  | 0 => some []
  | k + 1 =>
    have hlt : (unpairNat k).2 < k + 1 := by
      have := snd_unpair_le k; omega
    do
      let r ← decodeRule (unpairNat k).1
      let rs ← decodeRules (unpairNat k).2
      pure (r :: rs)
termination_by n => n

public theorem decode_encodeRules (rs : List Rule) : decodeRules (encodeRules rs) = some rs := by
  induction rs with
  | nil =>
    unfold encodeRules decodeRules
    rfl
  | cons r rs ih =>
    unfold encodeRules
    rw [decodeRules]
    simp [unpair_pair, decode_encodeRule, ih]

public def encodeOTM (M : OTM) : Nat := encodeRules M.rules
public def decodeOTM (k : Nat) : Option OTM := (decodeRules k).map OTM.mk

public theorem decode_encodeOTM (M : OTM) : decodeOTM (encodeOTM M) = some M := by
  cases M
  simp [encodeOTM, decodeOTM, decode_encodeRules]

end PVsNP
