module

/-!
# Catalytic Zero-Workspace Reversible Algebra (Wild Paths 7 & 10)

Formalizes reversible catalytic register programs over `Int` (Buhrman–Cleve–
Koucký–Loff–Speelman 2014; Cook–Mertz 2024; Williams 2025) where every
auxiliary register initially holds arbitrary unknown "catalyst" data `τ : Nat → Int`
that must be restored bit-for-bit at termination.

Proves:
1. `catalytic_program_reversible`: Every catalytic program is bijectively
   invertible (`execProg (invertProg p) (execProg p s) = s`), linking directly
   to Landauer reversible computing.
2. `catalytic_mul_exact`: Explicit 10-instruction reversible bilinear gadget
   computing `dst += ± x * y` while restoring both catalysts `(r1, r2)` exactly.
3. `catalytic_multilinear_exact`: For EVERY degree `d ≥ 1`, arbitrary catalyst
   state `τ : Nat → Int`, and `dst ≥ d`, `catalyticProdProg dst xs sign` computes
   `τ dst ± ∏ xs` using ONLY the `d` catalysts `0 .. d - 1`, restores EVERY
   register `r ≠ dst` bit-for-bit to `τ r`, and uses exact instruction count
   `T(d) = 3 * 4^(d - 1) - 2` (`T(d) + 2 = 3 * 4^(d - 1)`).
-/

namespace PVsNP

@[expose] public section

/-- Elementary reversible instructions on an unbounded integer register bank. -/
inductive CatInstr where
  | addVal (dst : Nat) (v : Int)
  | subVal (dst : Nat) (v : Int)
  | addMul (dst r1 r2 : Nat)
  | subMul (dst r1 r2 : Nat)
  deriving Repr, DecidableEq

/-- Register bank state mapping register index to exact unbounded integer. -/
abbrev RegState := Nat → Int

/-- Update a single register. -/
def setReg (s : RegState) (r : Nat) (v : Int) : RegState :=
  fun i => if i = r then v else s i

/-- Execute one elementary catalytic instruction. -/
def execInstr (s : RegState) : CatInstr → RegState
  | .addVal dst v => setReg s dst (s dst + v)
  | .subVal dst v => setReg s dst (s dst - v)
  | .addMul dst r1 r2 => setReg s dst (s dst + s r1 * s r2)
  | .subMul dst r1 r2 => setReg s dst (s dst - s r1 * s r2)

/-- Execute a straight-line catalytic program. -/
def execProg (prog : List CatInstr) (s : RegState) : RegState :=
  prog.foldl execInstr s

/-- An instruction is well-formed (strictly reversible without self-aliasing)
    if bilinear multiply-accumulate never reads its own destination register. -/
def CatInstr.WellFormed : CatInstr → Prop
  | .addVal _ _ => True
  | .subVal _ _ => True
  | .addMul dst r1 r2 => dst ≠ r1 ∧ dst ≠ r2
  | .subMul dst r1 r2 => dst ≠ r1 ∧ dst ≠ r2

/-- Exact inverse of a single elementary instruction. -/
def invertInstr : CatInstr → CatInstr
  | .addVal dst v => .subVal dst v
  | .subVal dst v => .addVal dst v
  | .addMul dst r1 r2 => .subMul dst r1 r2
  | .subMul dst r1 r2 => .addMul dst r1 r2

/-- Exact inverse of a catalytic program (reverse order, invert each op). -/
def invertProg (prog : List CatInstr) : List CatInstr :=
  (prog.reverse).map invertInstr

/-- Exact integer product of a list of integers. -/
def listProd : List Int → Int
  | [] => 1
  | x :: xs => x * listProd xs

/-- Explicit 10-instruction reversible catalytic bilinear gadget:
    adds `(if sign then 1 else -1) * x * y` into `dst`, restoring `r1` and `r2`. -/
def catalyticMulGadget (dst r1 r2 : Nat) (x y : Int) (sign : Bool) : List CatInstr :=
  let posOp := if sign then CatInstr.addMul dst r1 r2 else CatInstr.subMul dst r1 r2
  let negOp := if sign then CatInstr.subMul dst r1 r2 else CatInstr.addMul dst r1 r2
  [ .addVal r1 x
  , .addVal r2 y
  , posOp
  , .subVal r1 x
  , negOp
  , .subVal r2 y
  , .addVal r1 x
  , negOp
  , .subVal r1 x
  , posOp ]

/-- Recursive zero-workspace catalytic `d`-fold multilinear product (`d = xs.length ≥ 1`).
    Uses ONLY catalyst registers `0, 1, ..., d - 1` (requiring `dst ≥ d`),
    restoring every catalyst bit-for-bit regardless of initial garbage `τ`.
    Matches `experiments/exp3_markov_and_catalytic.py` instruction-for-instruction. -/
def catalyticProdProg (dst : Nat) (xs : List Int) (sign : Bool) : List CatInstr :=
  match xs with
  | [] => []
  | [x] => [if sign then .addVal dst x else .subVal dst x]
  | x :: rest =>
    -- Place `x` at the outer level and recursively compute `∏ rest` into catalyst `rest.length`
    -- using catalysts `0 .. rest.length - 1`, reusing catalyst `0` as `r_last`!
    let rp := rest.length
    let rlast := 0
    let posOp := if sign then CatInstr.addMul dst rp rlast else CatInstr.subMul dst rp rlast
    let negOp := if sign then CatInstr.subMul dst rp rlast else CatInstr.addMul dst rp rlast
    let pPlus := catalyticProdProg rp rest true
    let pMinus := catalyticProdProg rp rest false
    pPlus ++
    [.addVal rlast x, posOp] ++
    pMinus ++
    [negOp, .subVal rlast x] ++
    pPlus ++
    [negOp] ++
    pMinus ++
    [posOp]

end

-- ============================================================================
-- Helper Lemmas
-- ============================================================================

private theorem execProg_nil (s : RegState) : execProg [] s = s := rfl

private theorem execProg_cons (i : CatInstr) (ps : List CatInstr) (s : RegState) :
    execProg (i :: ps) s = execProg ps (execInstr s i) := rfl

private theorem execProg_append (p1 p2 : List CatInstr) (s : RegState) :
    execProg (p1 ++ p2) s = execProg p2 (execProg p1 s) := by
  unfold execProg
  exact List.foldl_append

private theorem setReg_self (s : RegState) (r : Nat) (v : Int) :
    setReg s r v r = v := by
  simp [setReg]

private theorem setReg_ne (s : RegState) (r i : Nat) (v : Int) (h : i ≠ r) :
    setReg s r v i = s i := by
  simp [setReg, h]

private theorem setReg_overwrite (s : RegState) (r : Nat) (v1 v2 : Int) :
    setReg (setReg s r v1) r v2 = setReg s r v2 := by
  funext i
  by_cases h : i = r <;> simp [setReg, h]

private theorem setReg_same (s : RegState) (r : Nat) :
    setReg s r (s r) = s := by
  funext i
  by_cases h : i = r <;> simp [setReg, h]

-- ============================================================================
-- Headline Theorem 1: Exact Bijective Reversibility (Landauer Link)
-- ============================================================================

private theorem execInstr_invert (s : RegState) (i : CatInstr) (hwf : i.WellFormed) :
    execInstr (execInstr s i) (invertInstr i) = s := by
  cases i with
  | addVal dst v =>
    simp only [execInstr, invertInstr]
    rw [setReg_self, setReg_overwrite]
    have : s dst + v - v = s dst := by omega
    rw [this, setReg_same]
  | subVal dst v =>
    simp only [execInstr, invertInstr]
    rw [setReg_self, setReg_overwrite]
    have : s dst - v + v = s dst := by omega
    rw [this, setReg_same]
  | addMul dst r1 r2 =>
    rcases hwf with ⟨h1, h2⟩
    simp only [execInstr, invertInstr]
    rw [setReg_self, setReg_ne s dst r1 _ (Ne.symm h1), setReg_ne s dst r2 _ (Ne.symm h2),
        setReg_overwrite]
    have : s dst + s r1 * s r2 - s r1 * s r2 = s dst := by omega
    rw [this, setReg_same]
  | subMul dst r1 r2 =>
    rcases hwf with ⟨h1, h2⟩
    simp only [execInstr, invertInstr]
    rw [setReg_self, setReg_ne s dst r1 _ (Ne.symm h1), setReg_ne s dst r2 _ (Ne.symm h2),
        setReg_overwrite]
    have : s dst - s r1 * s r2 + s r1 * s r2 = s dst := by omega
    rw [this, setReg_same]

/-- Headline Theorem (Exact Bijective Reversibility):
    Every well-formed catalytic program is strictly reversible without energy
    dissipation or information erasure: `execProg (invertProg p) (execProg p s) = s`. -/
public theorem catalytic_program_reversible (prog : List CatInstr)
    (hwf : ∀ i ∈ prog, i.WellFormed) (s : RegState) :
    execProg (invertProg prog) (execProg prog s) = s := by
  induction prog generalizing s with
  | nil => rfl
  | cons i ps ih =>
    have hi : i.WellFormed := hwf i (by simp)
    have hps : ∀ j ∈ ps, j.WellFormed := fun j hj => hwf j (by simp [hj])
    unfold invertProg
    rw [List.reverse_cons, List.map_append, List.map_singleton, execProg_cons, execProg_append]
    change execProg [invertInstr i] (execProg (invertProg ps) (execProg ps (execInstr s i))) = s
    rw [ih hps (execInstr s i)]
    exact execInstr_invert s i hi

-- ============================================================================
-- Headline Theorem 2: 10-Instruction Exact Catalytic Multiplication Gadget
-- ============================================================================

private theorem bilin_cancel_pos (t3 t1 t2 x y : Int) :
    t3 + (t1 + x) * (t2 + y) - t1 * (t2 + y) - (t1 + x) * t2 + t1 * t2 = t3 + x * y := by
  have h1 : (t1 + x) * (t2 + y) = t1 * t2 + t1 * y + x * t2 + x * y := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
  have h2 : t1 * (t2 + y) = t1 * t2 + t1 * y := Int.mul_add t1 t2 y
  have h3 : (t1 + x) * t2 = t1 * t2 + x * t2 := Int.add_mul t1 x t2
  omega

private theorem bilin_cancel_neg (t3 t1 t2 x y : Int) :
    t3 - (t1 + x) * (t2 + y) + t1 * (t2 + y) + (t1 + x) * t2 - t1 * t2 = t3 - x * y := by
  have h := bilin_cancel_pos 0 t1 t2 x y
  omega

/-- Headline Theorem (10-Instruction Exact Catalytic Multiplication):
    For any pairwise distinct registers `(dst, r1, r2)`, arbitrary unknown initial
    register contents `s : RegState`, and integers `x, y`, `catalyticMulGadget`
    adds `± x * y` into `dst` and restores EVERY other register (including `r1`
    and `r2`) bit-for-bit to its original value `s`. -/
public theorem catalytic_mul_exact (dst r1 r2 : Nat) (x y : Int) (sign : Bool)
    (h1 : dst ≠ r1) (h2 : dst ≠ r2) (h12 : r1 ≠ r2) (s : RegState) :
    execProg (catalyticMulGadget dst r1 r2 x y sign) s =
    setReg s dst (s dst + (if sign then 1 else -1) * (x * y)) := by
  cases sign
  · -- sign = false
    funext i
    unfold catalyticMulGadget execProg
    simp only [Bool.false_eq_true, ↓reduceIte, List.foldl_cons, List.foldl_nil, execInstr,
               setReg, h1, h2, h12, h1.symm, h2.symm, h12.symm]
    by_cases hid : i = dst
    · subst hid
      simp only [↓reduceIte]
      have hcalc := bilin_cancel_neg (s i) (s r1) (s r2) x y
      have hr1 : s r1 + x - x = s r1 := by omega
      have hr2 : s r2 + y - y = s r2 := by omega
      simp only [hr1, hr2]
      omega
    · by_cases hir1 : i = r1
      · subst hir1; simp [h1.symm]
      · by_cases hir2 : i = r2
        · subst hir2; simp [h2.symm, h12.symm]
        · simp [hid, hir1, hir2]
  · -- sign = true
    funext i
    unfold catalyticMulGadget execProg
    simp only [↓reduceIte, List.foldl_cons, List.foldl_nil, execInstr,
               setReg, h1, h2, h12, h1.symm, h2.symm, h12.symm]
    by_cases hid : i = dst
    · subst hid
      simp only [↓reduceIte]
      have hcalc := bilin_cancel_pos (s i) (s r1) (s r2) x y
      have hr1 : s r1 + x - x = s r1 := by omega
      have hr2 : s r2 + y - y = s r2 := by omega
      simp only [hr1, hr2]
      omega
    · by_cases hir1 : i = r1
      · subst hir1; simp [h1.symm]
      · by_cases hir2 : i = r2
        · subst hir2; simp [h2.symm, h12.symm]
        · simp [hid, hir1, hir2]

-- ============================================================================
-- Headline Theorem 3: Arbitrary-Degree Zero-Workspace Catalytic Multilinear Product
-- ============================================================================

/-- Headline Theorem (Zero-Workspace `d`-Fold Catalytic Product & Exact Op Count):
    For EVERY nonempty integer list `xs` of length `d ≥ 1`, EVERY destination
    `dst ≥ d`, EVERY sign, and EVERY arbitrary catalyst bank `s : RegState`:
    1. All instructions in `catalyticProdProg dst xs sign` are strictly well-formed
       (hence bijectively reversible via `catalytic_program_reversible`);
    2. Execution updates `dst` to `s dst + (±1) * ∏ xs` while restoring EVERY
       other register (including all `d` catalysts `0 .. d - 1`) bit-for-bit to `s`;
    3. The exact primitive operation count satisfies `T(d) + 2 = 3 * 4^(d - 1)`. -/
public theorem catalytic_multilinear_exact (xs : List Int) (hne : xs ≠ []) :
    ∀ (dst : Nat) (_hdst : xs.length ≤ dst) (sign : Bool) (s : RegState),
      (∀ i ∈ catalyticProdProg dst xs sign, i.WellFormed) ∧
      execProg (catalyticProdProg dst xs sign) s =
        setReg s dst (s dst + (if sign then 1 else -1) * listProd xs) ∧
      (catalyticProdProg dst xs sign).length + 2 = 3 * 4 ^ (xs.length - 1) := by
  induction xs with
  | nil => exact absurd rfl hne
  | cons x rest ih =>
    cases rest with
    | nil =>
      intro dst _ sign s
      cases sign <;>
      · refine ⟨?_, ?_, ?_⟩
        · intro i hi; simp [catalyticProdProg] at hi; subst hi; trivial
        · funext j
          unfold catalyticProdProg execProg
          simp only [listProd, Int.mul_one, execInstr, setReg, List.foldl_cons, List.foldl_nil,
                     Bool.false_eq_true, ↓reduceIte]
          by_cases hj : j = dst <;> simp [hj] <;> omega
        · rfl
    | cons y ys =>
      intro dst hdst sign s
      let rest' := y :: ys
      have hrest_ne : rest' ≠ [] := by simp [rest']
      have hlen_cons : (x :: rest').length = rest'.length + 1 := rfl
      have hrp_ge : rest'.length ≤ rest'.length := Nat.le_refl _
      have hrp_pos : 0 < rest'.length := by simp [rest']
      have hdst_gt_rp : rest'.length < dst := by
        dsimp only [rest']; simp only [List.length_cons] at hdst ⊢; omega
      have hdst_ne_rp : dst ≠ rest'.length := by omega
      have hdst_ne_0 : dst ≠ 0 := by omega
      have hrp_ne_0 : rest'.length ≠ 0 := by omega
      -- Apply IH to `pPlus` and `pMinus` at any state `st`
      have hIH := ih hrest_ne rest'.length hrp_ge
      have hwfP : ∀ i ∈ catalyticProdProg rest'.length rest' true, i.WellFormed :=
        (hIH true s).1
      have hwfM : ∀ i ∈ catalyticProdProg rest'.length rest' false, i.WellFormed :=
        (hIH false s).1
      have hlenP : (catalyticProdProg rest'.length rest' true).length + 2 = 3 * 4 ^ (rest'.length - 1) :=
        (hIH true s).2.2
      have hlenM : (catalyticProdProg rest'.length rest' false).length + 2 = 3 * 4 ^ (rest'.length - 1) :=
        (hIH false s).2.2
      refine ⟨?_, ?_, ?_⟩
      · -- 1. Well-formedness of every instruction
        intro i hi
        unfold catalyticProdProg at hi
        change i ∈ catalyticProdProg rest'.length rest' true ++
            [.addVal 0 x, if sign then .addMul dst rest'.length 0 else .subMul dst rest'.length 0] ++
            catalyticProdProg rest'.length rest' false ++
            [if sign then .subMul dst rest'.length 0 else .addMul dst rest'.length 0, .subVal 0 x] ++
            catalyticProdProg rest'.length rest' true ++
            [if sign then .subMul dst rest'.length 0 else .addMul dst rest'.length 0] ++
            catalyticProdProg rest'.length rest' false ++
            [if sign then .addMul dst rest'.length 0 else .subMul dst rest'.length 0] at hi
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with ((((((h | (h | h)) | h) | (h | h)) | h) | h) | h) | h
        · exact hwfP i h
        · subst h; trivial
        · subst h; cases sign <;> exact ⟨hdst_ne_rp, hdst_ne_0⟩
        · exact hwfM i h
        · subst h; cases sign <;> exact ⟨hdst_ne_rp, hdst_ne_0⟩
        · subst h; trivial
        · exact hwfP i h
        · subst h; cases sign <;> exact ⟨hdst_ne_rp, hdst_ne_0⟩
        · exact hwfM i h
        · subst h; cases sign <;> exact ⟨hdst_ne_rp, hdst_ne_0⟩
      · -- 2. Exact state transformation + bit-for-bit catalyst restoration
        unfold catalyticProdProg
        change execProg
          (catalyticProdProg rest'.length rest' true ++
           [.addVal 0 x, if sign then .addMul dst rest'.length 0 else .subMul dst rest'.length 0] ++
           catalyticProdProg rest'.length rest' false ++
           [if sign then .subMul dst rest'.length 0 else .addMul dst rest'.length 0, .subVal 0 x] ++
           catalyticProdProg rest'.length rest' true ++
           [if sign then .subMul dst rest'.length 0 else .addMul dst rest'.length 0] ++
           catalyticProdProg rest'.length rest' false ++
           [if sign then .addMul dst rest'.length 0 else .subMul dst rest'.length 0]) s = _
        simp only [execProg_append]
        have hstepP : ∀ st : RegState,
            execProg (catalyticProdProg rest'.length rest' true) st =
            setReg st rest'.length (st rest'.length + listProd rest') := by
          intro st
          have h := (hIH true st).2.1
          simpa using h
        have hstepM : ∀ st : RegState,
            execProg (catalyticProdProg rest'.length rest' false) st =
            setReg st rest'.length (st rest'.length - listProd rest') := by
          intro st
          have h := (hIH false st).2.1
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          have hsub : st rest'.length + -1 * listProd rest' = st rest'.length - listProd rest' := by omega
          rw [hsub] at h
          exact h
        rw [hstepP, hstepM, hstepP, hstepM]
        -- Simplify pointwise for every register `j`
        funext j
        cases sign
        · simp only [Bool.false_eq_true, ↓reduceIte, execProg, List.foldl_cons, List.foldl_nil,
                     execInstr, setReg, hdst_ne_rp, hdst_ne_0, hrp_ne_0,
                     hdst_ne_rp.symm, hdst_ne_0.symm, hrp_ne_0.symm]
          by_cases hjd : j = dst
          · subst hjd
            simp only [↓reduceIte]
            have hcalc := bilin_cancel_neg (s j) (s rest'.length) (s 0) (listProd rest') x
            have hmul_comm : x * listProd rest' = listProd rest' * x := Int.mul_comm x (listProd rest')
            have hrp1 : s rest'.length + listProd rest' - listProd rest' = s rest'.length := by omega
            have h01 : s 0 + x - x = s 0 := by omega
            simp only [hrp1, h01]
            have hlp : listProd (x :: y :: ys) = x * listProd rest' := rfl
            rw [hlp]
            omega
          · by_cases hjrp : j = rest'.length
            · subst hjrp; simp [hdst_ne_rp.symm]
            · by_cases hj0 : j = 0
              · subst hj0; simp [hdst_ne_0.symm, hrp_ne_0.symm]
              · simp [hjd, hjrp, hj0]
        · simp only [↓reduceIte, execProg, List.foldl_cons, List.foldl_nil,
                     execInstr, setReg, hdst_ne_rp, hdst_ne_0, hrp_ne_0,
                     hdst_ne_rp.symm, hdst_ne_0.symm, hrp_ne_0.symm]
          by_cases hjd : j = dst
          · subst hjd
            simp only [↓reduceIte]
            have hcalc := bilin_cancel_pos (s j) (s rest'.length) (s 0) (listProd rest') x
            have hmul_comm : x * listProd rest' = listProd rest' * x := Int.mul_comm x (listProd rest')
            have hrp1 : s rest'.length + listProd rest' - listProd rest' = s rest'.length := by omega
            have h01 : s 0 + x - x = s 0 := by omega
            simp only [hrp1, h01]
            have hlp : listProd (x :: y :: ys) = x * listProd rest' := rfl
            rw [hlp]
            omega
          · by_cases hjrp : j = rest'.length
            · subst hjrp; simp [hdst_ne_rp.symm]
            · by_cases hj0 : j = 0
              · subst hj0; simp [hdst_ne_0.symm, hrp_ne_0.symm]
              · simp [hjd, hjrp, hj0]
      · -- 3. Exact closed-form operation count: `T(d) + 2 = 3 * 4^(d - 1)`
        unfold catalyticProdProg
        simp only [List.length_append, List.length_cons, List.length_nil]
        have hpow : 4 ^ rest'.length = 4 * 4 ^ (rest'.length - 1) := by
          have heq : rest'.length = (rest'.length - 1) + 1 := by omega
          conv => lhs; rw [heq]
          rw [Nat.pow_succ, Nat.mul_comm]
        have hsub1 : (x :: rest').length - 1 = rest'.length := by simp [rest']
        change (catalyticProdProg rest'.length rest' true).length + 2 +
            (catalyticProdProg rest'.length rest' false).length + 2 +
            (catalyticProdProg rest'.length rest' true).length + 1 +
            (catalyticProdProg rest'.length rest' false).length + 1 + 2 =
            3 * 4 ^ rest'.length
        omega

end PVsNP
