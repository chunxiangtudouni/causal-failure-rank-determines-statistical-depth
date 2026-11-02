module

public import PaperProofs.Structure.RawCandidateWorkspaceInit
public import PaperProofs.Structure.RawCandidateStableOrder
public import PaperProofs.Structure.RawCandidateRankScan

/-! A fixed dynamic count-ranking program.  The caller supplies only the
workspace produced by the preceding phases, not ranks or a sorted answer.
Scratch 0 stores t, 1/2 the two cards, 3 a keep bit, and 4/5 comparison bits.
The two loop counters and the rank counter occupy B+1/B+2/B+3. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateOrderingRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM

def loadWorkspace (target : Register) (offset : Nat) : List PackingOp :=
  loadCell .address 8 ++ [.base (.base (.constant .index offset)),
    .base (.base (.add .address .address .index)), .base (.base (.loadHeap target .address))]

def storeWorkspace (offset : Nat) : List PackingOp :=
  loadCell .address 8 ++ [.base (.base (.constant .index offset)),
    .base (.base (.add .address .address .index)), .base (.base (.storeHeap .address .total))]

def setWorkspace (offset value : Nat) : List PackingOp :=
  [.base (.base (.constant .total value))] ++ storeWorkspace offset

def incrementWorkspace (offset : Nat) : List PackingOp :=
  loadWorkspace .total offset ++ [.base (.base (.constant .old 1)),
    .base (.base (.add .total .total .old))] ++ storeWorkspace offset

def testWorkspace (counter exit : Nat) : List PackingOp :=
  loadWorkspace .total 0 ++ loadWorkspace .old counter ++
    [.base (.subtract .flag .total .old), .base (.base (.constant .index (5 * exit))),
      .jumpIfZero .flag .index]

def arraySlot (base count factor index : Nat) : Nat := base + count * factor + 4 + index

def arrayBase (factor : Nat) : List PackingOp :=
  loadWorkspace .fresh 0 ++ loadCell .address 8 ++
    [.base (.base (.constant .index factor)), .arithmetic .multiply .index .fresh .index,
     .base (.base (.add .address .address .index)), .base (.base (.constant .index 4)),
     .base (.base (.add .address .address .index))]

def arrayAddress (factor counter : Nat) : List PackingOp :=
  loadWorkspace .old counter ++ arrayBase factor ++ [.base (.base (.add .address .address .old))]

def loadArray (target : Register) (factor counter : Nat) : List PackingOp :=
  arrayAddress factor counter ++ [.base (.base (.loadHeap target .address))]

def storeArray (factor counter : Nat) : List PackingOp :=
  arrayAddress factor counter ++ [.base (.base (.storeHeap .address .total))]

def fetchComparison : List PackingOp :=
  loadArray .total 0 1 ++ storeCell .total 1 ++ loadArray .total 0 2 ++ storeCell .total 2 ++
    loadArray .total 1 2 ++ storeCell .total 3

def compareCards : List PackingOp :=
  loadCell .old 1 ++ loadCell .fresh 2 ++
    [.base (.subtract .total .old .fresh), .base (.subtract .flag .fresh .old),
     .base (.base (.add .flag .flag .total)), .base (.base (.constant .value 1)),
     .base (.base (.minimum .flag .flag .value)), .base (.subtract .flag .value .flag)] ++
    storeCell .flag 4 ++ [.base (.base (.minimum .total .total .value))] ++ storeCell .total 5

def compareIDs : List PackingOp :=
  loadWorkspace .old 1 ++ loadWorkspace .fresh 2 ++
    [.base (.subtract .total .old .fresh), .base (.base (.minimum .total .total .value))] ++
    loadCell .old 4 ++ [.arithmetic .multiply .total .total .old] ++ loadCell .old 5 ++
    [.base (.base (.add .total .total .old))] ++ loadCell .old 3 ++
    [.arithmetic .multiply .total .total .old] ++ loadWorkspace .old 3 ++
    [.base (.base (.add .total .total .old))] ++ storeWorkspace 3

def comparison : List PackingOp := fetchComparison ++ compareCards ++ compareIDs

def initCode : List PackingOp := setCell 0 0 ++ setWorkspace 1 0

def rowInit : List PackingOp := setWorkspace 2 0 ++ setWorkspace 3 0

def innerTail (start : Nat) : List PackingOp := incrementWorkspace 2 ++ jumpTo (start + 34)

def storeOrd : List PackingOp :=
  loadArray .flag 1 1 ++ storeCell .flag 3 ++ loadWorkspace .total 1 ++ loadArray .old 2 3 ++
    [.base (.base (.select .total .flag .total .old))] ++ storeArray 2 3

def storeInverse : List PackingOp :=
  loadWorkspace .total 3 ++ [.base (.base (.constant .old 1)),
      .base (.base (.add .total .total .old))] ++ loadCell .old 3 ++
    [.arithmetic .multiply .total .total .old] ++ storeArray 3 1

def addCount : List PackingOp :=
    loadCell .total 0 ++ loadCell .old 3 ++ [.base (.base (.add .total .total .old))] ++ storeCell .total 0

def finishRow : List PackingOp := storeOrd ++ storeInverse ++ addCount

def outerTail (start : Nat) : List PackingOp := incrementWorkspace 1 ++ jumpTo (start + 9)

def finishCode : List PackingOp := loadCell .total 0 ++ arrayBase 4 ++ [.base (.base (.storeHeap .address .total))]

def programAt (start : Nat) : List PackingOp :=
  initCode ++ testWorkspace 1 (start + 288) ++ rowInit ++ testWorkspace 2 (start + 172) ++
    comparison ++ innerTail start ++ finishRow ++ outerTail start ++ finishCode

theorem loadWorkspace_length (target : Register) (offset : Nat) :
    (loadWorkspace target offset).length = 5 := rfl

theorem storeWorkspace_length (offset : Nat) : (storeWorkspace offset).length = 5 := rfl

theorem incrementWorkspace_length (offset : Nat) : (incrementWorkspace offset).length = 12 := rfl

theorem testWorkspace_length (counter exit : Nat) : (testWorkspace counter exit).length = 13 := rfl

theorem arrayBase_length (factor : Nat) : (arrayBase factor).length = 12 := rfl

theorem arrayAddress_length (factor counter : Nat) : (arrayAddress factor counter).length = 18 := by
  simp only [arrayAddress, List.length_append, loadWorkspace_length, arrayBase_length,
    List.length_cons, List.length_nil]

theorem loadArray_length (target : Register) (factor counter : Nat) :
    (loadArray target factor counter).length = 19 := by
  simp only [loadArray, List.length_append, arrayAddress_length, List.length_cons, List.length_nil]

theorem storeArray_length (factor counter : Nat) : (storeArray factor counter).length = 19 := by
  simp only [storeArray, List.length_append, arrayAddress_length, List.length_cons, List.length_nil]

theorem fetchComparison_length : fetchComparison.length = 63 := by
  simp only [fetchComparison, List.length_append, loadArray_length, storeCell,
    List.length_cons, List.length_nil]

theorem compareCards_length : compareCards.length = 15 := by
  simp only [compareCards, loadCell, storeCell, List.length_append, List.length_cons, List.length_nil]

theorem compareIDs_length : compareIDs.length = 32 := by
  simp only [compareIDs, loadWorkspace_length, storeWorkspace_length, loadCell,
    List.length_append, List.length_cons, List.length_nil]

theorem comparison_length : comparison.length = 110 := by
  simp only [comparison, List.length_append, fetchComparison_length, compareCards_length, compareIDs_length]

theorem initCode_length : initCode.length = 9 := rfl
theorem rowInit_length : rowInit.length = 12 := rfl
theorem innerTail_length (start : Nat) : (innerTail start).length = 15 := rfl

theorem finishRow_length : finishRow.length = 101 := by
  simp only [finishRow, storeOrd, storeInverse, addCount,
    loadArray_length, storeArray_length, loadWorkspace_length, loadCell, storeCell,
    List.length_append, List.length_cons, List.length_nil]

theorem outerTail_length (start : Nat) : (outerTail start).length = 15 := rfl
theorem finishCode_length : finishCode.length = 15 := by
  simp only [finishCode, arrayBase_length, loadCell, List.length_append, List.length_cons, List.length_nil]

theorem programAt_length (start : Nat) : (programAt start).length = 303 := by
  simp only [programAt, List.length_append, initCode_length, testWorkspace_length, rowInit_length,
    comparison_length, innerTail_length, finishRow_length, outerTail_length, finishCode_length]

def totalSteps (count : Nat) : Nat := count * (138 * count + 154) + 37

private theorem state_ext {left right : NatState}
    (hr : left.register = right.register) (hh : left.heap = right.heap)
    (hp : left.pc = right.pc) (ha : left.halted = right.halted) : left = right := by
  cases left
  cases right
  cases hr
  cases hh
  cases hp
  cases ha
  rfl

def loaded (target : Register) (offset : Nat) (state : NatState) : NatState :=
  { state with
    register := Function.update
      (Function.update (Function.update state.register .address (state.heap 8 + offset)) .index offset)
      target (state.heap (state.heap 8 + offset))
    pc := state.pc + 25 }

theorem loadWorkspace_runOps (rom : PhysicalROM) (target : Register) (offset : Nat) (state : NatState) :
    runOps rom (loadWorkspace target offset) state = loaded target offset state := by
  apply state_ext
  · funext reg
    cases reg <;> cases target <;>
      simp [loadWorkspace, loaded, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [loadWorkspace, loaded, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [loadWorkspace, loaded, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [loadWorkspace, loaded, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]

def stored (offset : Nat) (state : NatState) : NatState :=
  { state with
    register := Function.update (Function.update state.register .address (state.heap 8 + offset)) .index offset
    heap := Function.update state.heap (state.heap 8 + offset) (state.register .total)
    pc := state.pc + 25 }

theorem storeWorkspace_runOps (rom : PhysicalROM) (offset : Nat) (state : NatState) :
    runOps rom (storeWorkspace offset) state = stored offset state := by
  apply state_ext
  · funext reg
    cases reg <;> simp [storeWorkspace, stored, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [storeWorkspace, stored, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [storeWorkspace, stored, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [storeWorkspace, stored, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]

def addressed (factor counter : Nat) (state : NatState) : NatState :=
  { state with
    register := Function.update
      (Function.update
        (Function.update (Function.update state.register .old (state.heap (state.heap 8 + counter)))
          .fresh (state.heap (state.heap 8)))
        .address (arraySlot (state.heap 8) (state.heap (state.heap 8)) factor (state.heap (state.heap 8 + counter))))
      .index 4
    pc := state.pc + 90 }

theorem arrayAddress_runOps (rom : PhysicalROM) (factor counter : Nat) (state : NatState) :
    runOps rom (arrayAddress factor counter) state = addressed factor counter state := by
  apply state_ext
  · funext reg
    cases reg <;> simp [arrayAddress, arrayBase, loadWorkspace, addressed, arraySlot, loadCell,
      runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute, Nat.add_assoc]
  · simp [arrayAddress, arrayBase, loadWorkspace, addressed, loadCell,
      runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [arrayAddress, arrayBase, loadWorkspace, addressed, loadCell,
      runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [arrayAddress, arrayBase, loadWorkspace, addressed, loadCell,
      runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem loadArray_runOps (rom : PhysicalROM) (target : Register) (factor counter : Nat) (state : NatState) :
    runOps rom (loadArray target factor counter) state =
      natExecuteOp rom (.base (.base (.loadHeap target .address))) (addressed factor counter state) := by
  rw [loadArray, runOps_append, arrayAddress_runOps]
  rfl

theorem storeArray_runOps (rom : PhysicalROM) (factor counter : Nat) (state : NatState) :
    runOps rom (storeArray factor counter) state =
      natExecuteOp rom (.base (.base (.storeHeap .address .total))) (addressed factor counter state) := by
  rw [storeArray, runOps_append, arrayAddress_runOps]
  rfl

theorem loadArray_heap (rom : PhysicalROM) (target : Register) (factor counter : Nat) (state : NatState) :
    (runOps rom (loadArray target factor counter) state).heap = state.heap := by
  rw [loadArray_runOps]
  rfl

theorem loadArray_value (rom : PhysicalROM) (target : Register) (factor counter : Nat) (state : NatState) :
    (runOps rom (loadArray target factor counter) state).register target =
      state.heap (arraySlot (state.heap 8) (state.heap (state.heap 8)) factor
        (state.heap (state.heap 8 + counter))) := by
  rw [loadArray_runOps]
  simp [natExecuteOp, Instruction.execute, Op.execute, addressed]

theorem storeArray_heap (rom : PhysicalROM) (factor counter : Nat) (state : NatState) :
    (runOps rom (storeArray factor counter) state).heap =
      Function.update state.heap
        (arraySlot (state.heap 8) (state.heap (state.heap 8)) factor
          (state.heap (state.heap 8 + counter))) (state.register .total) := by
  rw [storeArray_runOps]
  simp [natExecuteOp, Instruction.execute, Op.execute, addressed]

private theorem loadArray_total_preserved (rom : PhysicalROM) (target : Register)
    (factor counter : Nat) (state : NatState) (ht : target ≠ .total) :
    (runOps rom (loadArray target factor counter) state).register .total = state.register .total := by
  rw [loadArray_runOps]
  simp [natExecuteOp, Instruction.execute, Op.execute, addressed, Ne.symm ht]

private theorem storeCell_heap (rom : PhysicalROM) (source : Register) (cell : Nat) (state : NatState)
    (hsource : source ≠ .address) :
    (runOps rom (storeCell source cell) state).heap =
      Function.update state.heap cell (state.register source) := by
  simp [storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hsource]

theorem fetchComparison_heap (rom : PhysicalROM) (state : NatState)
    (hbase : 16 ≤ state.heap 8) :
    let base := state.heap 8
    let count := state.heap base
    let left := state.heap (base + 1)
    let right := state.heap (base + 2)
    (runOps rom fetchComparison state).heap =
      Function.update
        (Function.update
          (Function.update state.heap 1 (state.heap (arraySlot base count 0 left)))
          2 (state.heap (arraySlot base count 0 right)))
        3 (state.heap (arraySlot base count 1 right)) := by
  let one := runOps rom (loadArray .total 0 1) state
  let two := runOps rom (storeCell .total 1) one
  let three := runOps rom (loadArray .total 0 2) two
  let four := runOps rom (storeCell .total 2) three
  let five := runOps rom (loadArray .total 1 2) four
  have h1 : one.heap = state.heap := loadArray_heap rom .total 0 1 state
  have hv1 := loadArray_value rom .total 0 1 state
  have h2 : two.heap = Function.update state.heap 1
      (state.heap (arraySlot (state.heap 8) (state.heap (state.heap 8)) 0 (state.heap (state.heap 8 + 1)))) := by
    rw [show two = runOps rom (storeCell .total 1) one from rfl,
      storeCell_heap rom .total 1 one (by decide), h1]
    exact congrArg (Function.update state.heap 1) hv1
  have h3 : three.heap = two.heap := loadArray_heap rom .total 0 2 two
  have hv3 := loadArray_value rom .total 0 2 two
  have h4 : four.heap = Function.update two.heap 2
      (two.heap (arraySlot (two.heap 8) (two.heap (two.heap 8)) 0 (two.heap (two.heap 8 + 2)))) := by
    rw [show four = runOps rom (storeCell .total 2) three from rfl,
      storeCell_heap rom .total 2 three (by decide), h3]
    exact congrArg (Function.update two.heap 2) hv3
  have h5 : five.heap = four.heap := loadArray_heap rom .total 1 2 four
  have hv5 := loadArray_value rom .total 1 2 four
  have hrun : runOps rom fetchComparison state = runOps rom (storeCell .total 3) five := by
    simp only [fetchComparison, runOps_append]
    rfl
  dsimp only
  rw [hrun, storeCell_heap rom .total 3 five (by decide), h5, hv5, h4, h2]
  simp (disch := omega) [arraySlot]

theorem compareCards_effect (rom : PhysicalROM) (state : NatState) :
    let result := runOps rom compareCards state
    result.heap = Function.update
      (Function.update state.heap 4
        (1 - min 1 ((state.heap 1 - state.heap 2) + (state.heap 2 - state.heap 1))))
      5 (min 1 (state.heap 1 - state.heap 2)) ∧ result.register .value = 1 := by
  simp [compareCards, loadCell, storeCell, runOps, natExecuteOp, Op.execute,
    Instruction.execute, Nat.min_comm, Nat.add_comm]

theorem compareIDs_heap (rom : PhysicalROM) (state : NatState)
    (hvalue : state.register .value = 1) :
    (runOps rom compareIDs state).heap = Function.update state.heap (state.heap 8 + 3)
      (state.heap (state.heap 8 + 3) +
        (min 1 (state.heap (state.heap 8 + 1) - state.heap (state.heap 8 + 2)) * state.heap 4 +
          state.heap 5) * state.heap 3) := by
  simp [compareIDs, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp,
    natArithmetic, Op.execute, Instruction.execute, hvalue, Nat.min_comm, Nat.add_comm]

def precedesBit (leftCard rightCard leftID rightID : Nat) : Nat :=
  min 1 (rightCard - leftCard) +
    (1 - min 1 ((rightCard - leftCard) + (leftCard - rightCard))) * min 1 (rightID - leftID)

theorem precedesBit_eq (leftCard rightCard leftID rightID : Nat) :
    precedesBit leftCard rightCard leftID rightID =
      if leftCard < rightCard ∨ leftCard = rightCard ∧ leftID < rightID then 1 else 0 := by
  unfold precedesBit
  by_cases hlt : leftCard < rightCard
  · have hdiff : 1 ≤ rightCard - leftCard := by omega
    have habs : 1 ≤ (rightCard - leftCard) + (leftCard - rightCard) := by omega
    simp [hlt, Nat.min_eq_left hdiff, Nat.min_eq_left habs]
  · by_cases heq : leftCard = rightCard
    · subst rightCard
      by_cases hIDs : leftID < rightID
      · have hdiff : 1 ≤ rightID - leftID := by omega
        simp [hIDs, Nat.min_eq_left hdiff]
      · have hdiff : rightID - leftID = 0 := by omega
        simp [hIDs, hdiff]
    · have hdiff : rightCard - leftCard = 0 := by omega
      have hback : 1 ≤ leftCard - rightCard := by omega
      simp [hlt, heq, hdiff, Nat.min_eq_left hback]

def comparisonHeap (state : NatState) : Nat → Nat :=
  let base := state.heap 8
  let count := state.heap base
  let left := state.heap (base + 1)
  let right := state.heap (base + 2)
  let leftCard := state.heap (arraySlot base count 0 left)
  let rightCard := state.heap (arraySlot base count 0 right)
  let rightKeep := state.heap (arraySlot base count 1 right)
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update state.heap 1 leftCard) 2 rightCard) 3 rightKeep)
        4 (1 - min 1 ((leftCard - rightCard) + (rightCard - leftCard))))
      5 (min 1 (leftCard - rightCard)))
    (base + 3) (state.heap (base + 3) + precedesBit rightCard leftCard right left * rightKeep)

theorem comparison_heap (rom : PhysicalROM) (state : NatState) (hbase : 16 ≤ state.heap 8) :
    (runOps rom comparison state).heap = comparisonHeap state := by
  let fetched := runOps rom fetchComparison state
  let compared := runOps rom compareCards fetched
  have hf := fetchComparison_heap rom state hbase
  have hc := compareCards_effect rom fetched
  dsimp only at hf hc
  have hrun : runOps rom comparison state = runOps rom compareIDs compared := by
    simp only [comparison, runOps_append]
    rfl
  rw [hrun, compareIDs_heap rom compared hc.2, show compared.heap = _ from hc.1,
    show fetched.heap = _ from hf]
  simp (disch := omega) [comparisonHeap, precedesBit, arraySlot, Nat.add_comm, Nat.mul_comm]

theorem comparison_rank (rom : PhysicalROM) (state : NatState) (hbase : 16 ≤ state.heap 8) :
    (runOps rom comparison state).heap (state.heap 8 + 3) =
      state.heap (state.heap 8 + 3) +
        precedesBit
          (state.heap (arraySlot (state.heap 8) (state.heap (state.heap 8)) 0 (state.heap (state.heap 8 + 2))))
          (state.heap (arraySlot (state.heap 8) (state.heap (state.heap 8)) 0 (state.heap (state.heap 8 + 1))))
          (state.heap (state.heap 8 + 2)) (state.heap (state.heap 8 + 1)) *
            state.heap (arraySlot (state.heap 8) (state.heap (state.heap 8)) 1 (state.heap (state.heap 8 + 2))) := by
  rw [comparison_heap rom state hbase]
  simp [comparisonHeap]

theorem comparison_frame (rom : PhysicalROM) (state : NatState) (hbase : 16 ≤ state.heap 8)
    (address : Nat) (h1 : address ≠ 1) (h2 : address ≠ 2) (h3 : address ≠ 3)
    (h4 : address ≠ 4) (h5 : address ≠ 5) (hrank : address ≠ state.heap 8 + 3) :
    (runOps rom comparison state).heap address = state.heap address := by
  rw [comparison_heap rom state hbase]
  simp [comparisonHeap, h1, h2, h3, h4, h5, hrank]

def Precedes (card : Nat → Nat) (left right : Nat) : Prop :=
  card left < card right ∨ card left = card right ∧ left < right

instance (card : Nat → Nat) (left right : Nat) : Decidable (Precedes card left right) := by
  unfold Precedes
  infer_instance

def rankCount (card : Nat → Nat) (keep : Nat → Bool) (candidate upto : Nat) : Nat :=
  ((List.range upto).filter (fun other => keep other && decide (Precedes card other candidate))).length

theorem rankCount_zero (card : Nat → Nat) (keep : Nat → Bool) (candidate : Nat) :
    rankCount card keep candidate 0 = 0 := rfl

theorem rankCount_succ (card : Nat → Nat) (keep : Nat → Bool) (candidate upto : Nat) :
    rankCount card keep candidate (upto + 1) = rankCount card keep candidate upto +
      if keep upto && decide (Precedes card upto candidate) then 1 else 0 := by
  simp only [rankCount, List.range_succ, List.filter_append, List.length_append,
    List.filter_cons, List.filter_nil]
  split <;> rfl

theorem rankCount_lt (card : Nat → Nat) (keep : Nat → Bool) (candidate count : Nat)
    (hcandidate : candidate < count) : rankCount card keep candidate count < count := by
  have hfalse : ¬ Precedes card candidate candidate := by unfold Precedes; omega
  have hlen : rankCount card keep candidate count < (List.range count).length := by
    apply List.length_filter_lt_length_iff_exists.mpr
    refine ⟨candidate, List.mem_range.mpr hcandidate, ?_⟩
    simp [hfalse]
  simpa only [List.length_range] using hlen

def paddingOp : PackingOp := .base (.base (.constant .value 0))

private theorem getD_middle (left middle right : List PackingOp) (position : Nat)
    (hp : position < middle.length) :
    (left ++ middle ++ right).getD (left.length + position) paddingOp =
      middle.getD position paddingOp := by
  rw [List.getD_append (left ++ middle) right paddingOp _ (by simp; omega),
    List.getD_append_right left middle paddingOp _ (by omega), Nat.add_sub_cancel_left]

theorem comparison_noJump : ∀ op ∈ comparison, NoJump op := by
  simp [comparison, fetchComparison, compareCards, compareIDs, loadArray, arrayAddress, arrayBase,
    loadWorkspace, storeWorkspace, loadCell, storeCell, NoJump]

theorem incrementWorkspace_heap (rom : PhysicalROM) (offset : Nat) (state : NatState) :
    (runOps rom (incrementWorkspace offset) state).heap =
      Function.update state.heap (state.heap 8 + offset) (state.heap (state.heap 8 + offset) + 1) := by
  simp [incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, runOps,
    natExecuteOp, Op.execute, Instruction.execute]

theorem testWorkspace_effect (rom : PhysicalROM) (counter exit : Nat) (state : NatState) :
    let result := runOps rom (testWorkspace counter exit) state
    result.heap = state.heap ∧ result.pc =
      (if state.heap (state.heap 8) - state.heap (state.heap 8 + counter) = 0 then 5 * exit else state.pc + 65) ∧
      result.halted = state.halted := by
  simp [testWorkspace, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute,
    Instruction.execute, Nat.add_assoc]

theorem innerTail_effect (rom : PhysicalROM) (start : Nat) (state : NatState) :
    let result := runOps rom (innerTail start) state
    result.heap = Function.update state.heap (state.heap 8 + 2) (state.heap (state.heap 8 + 2) + 1) ∧
      result.pc = 5 * (start + 34) ∧ result.halted = state.halted := by
  simp [innerTail, incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, jumpTo,
    runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem storeOrd_heap (rom : PhysicalROM) (state : NatState) (hbase : 16 ≤ state.heap 8) :
    let base := state.heap 8
    let count := state.heap base
    let left := state.heap (base + 1)
    let rank := state.heap (base + 3)
    let kept := state.heap (arraySlot base count 1 left)
    let slot := arraySlot base count 2 rank
    (runOps rom storeOrd state).heap =
      Function.update (Function.update state.heap 3 kept) slot
        (if kept = 0 then state.heap slot else left) := by
  simp only [storeOrd, runOps_append, loadArray_runOps, storeArray_runOps, loadWorkspace_runOps]
  simp (disch := first | omega | decide) [storeCell, runOps, natExecuteOp, addressed, loaded,
    Op.execute, Instruction.execute, arraySlot]

theorem storeInverse_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom storeInverse state).heap =
      Function.update state.heap
        (arraySlot (state.heap 8) (state.heap (state.heap 8)) 3 (state.heap (state.heap 8 + 1)))
        ((state.heap (state.heap 8 + 3) + 1) * state.heap 3) := by
  simp only [storeInverse, runOps_append, storeArray_runOps, loadWorkspace_runOps]
  simp [loadCell, runOps, natExecuteOp, natArithmetic, addressed, loaded, Op.execute, Instruction.execute]

theorem addCount_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom addCount state).heap = Function.update state.heap 0 (state.heap 0 + state.heap 3) := by
  simp [addCount, loadCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute]

def finishedHeap (state : NatState) : Nat → Nat :=
  let base := state.heap 8
  let count := state.heap base
  let left := state.heap (base + 1)
  let rank := state.heap (base + 3)
  let kept := state.heap (arraySlot base count 1 left)
  let ordSlot := arraySlot base count 2 rank
  Function.update
    (Function.update
      (Function.update
        (Function.update state.heap 3 kept) ordSlot
          (if kept = 0 then state.heap ordSlot else left))
      (arraySlot base count 3 left) ((rank + 1) * kept))
    0 (state.heap 0 + kept)

theorem finishRow_heap (rom : PhysicalROM) (state : NatState) (hbase : 16 ≤ state.heap 8) :
    (runOps rom finishRow state).heap = finishedHeap state := by
  let one := runOps rom storeOrd state
  let two := runOps rom storeInverse one
  have h1 := storeOrd_heap rom state hbase
  dsimp only at h1
  have h2 := storeInverse_heap rom one
  have hrun : runOps rom finishRow state = runOps rom addCount two := by
    simp only [finishRow, runOps_append]
    rfl
  rw [hrun, addCount_heap, show two.heap = _ from h2, show one.heap = _ from h1]
  simp (disch := omega) [finishedHeap, arraySlot]

theorem finishCode_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom finishCode state).heap =
      Function.update state.heap (arraySlot (state.heap 8) (state.heap (state.heap 8)) 4 0) (state.heap 0) := by
  simp [finishCode, arrayBase, loadWorkspace, loadCell, arraySlot, runOps, natExecuteOp,
    natArithmetic, Op.execute, Instruction.execute]

theorem initCode_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom initCode state).heap =
      Function.update (Function.update state.heap 0 0) (state.heap 8 + 1) 0 := by
  simp [initCode, setCell, storeCell, setWorkspace, storeWorkspace, loadCell,
    runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem rowInit_heap (rom : PhysicalROM) (state : NatState) (hbase : 16 ≤ state.heap 8) :
    (runOps rom rowInit state).heap = Function.update
      (Function.update state.heap (state.heap 8 + 2) 0) (state.heap 8 + 3) 0 := by
  simp (disch := first | omega | decide) [rowInit, setWorkspace, storeWorkspace, loadCell,
    runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem outerTail_effect (rom : PhysicalROM) (start : Nat) (state : NatState) :
    let result := runOps rom (outerTail start) state
    result.heap = Function.update state.heap (state.heap 8 + 1) (state.heap (state.heap 8 + 1) + 1) ∧
      result.pc = 5 * (start + 9) ∧ result.halted = state.halted := by
  simp [outerTail, incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, jumpTo,
    runOps, natExecuteOp, Op.execute, Instruction.execute]

structure RankReady (base count left right rank pointer : Nat) (state : NatState) : Prop where
  base_cell : state.heap 8 = base
  count_cell : state.heap base = count
  left_cell : state.heap (base + 1) = left
  right_cell : state.heap (base + 2) = right
  rank_cell : state.heap (base + 3) = rank
  pc : state.pc = pointer
  active : state.halted = false

structure OuterReady (base count left pointer : Nat) (state : NatState) : Prop where
  base_cell : state.heap 8 = base
  count_cell : state.heap base = count
  left_cell : state.heap (base + 1) = left
  pc : state.pc = pointer
  active : state.halted = false

def RowFrame (base count left rank : Nat) (kept : Bool) (before after : NatState) : Prop :=
  ∀ address, address ≠ 0 → address ≠ 1 → address ≠ 2 → address ≠ 3 → address ≠ 4 → address ≠ 5 →
    address ≠ base + 1 → address ≠ base + 2 → address ≠ base + 3 →
    address ≠ arraySlot base count 3 left → (kept = true → address ≠ arraySlot base count 2 rank) →
    after.heap address = before.heap address

def InputTables (base count : Nat) (card : Nat → Nat) (keep : Nat → Bool) (state : NatState) : Prop :=
  (∀ index < count, state.heap (arraySlot base count 0 index) = card index) ∧
    ∀ index < count, state.heap (arraySlot base count 1 index) = bit (keep index)

def rowHeap (base count left rank : Nat) (kept : Bool) (heap : Nat → Nat) : Nat → Nat :=
  Function.update
    (Function.update
      (Function.update (Function.update heap 3 (bit kept))
        (arraySlot base count 2 rank) (if kept then left else heap (arraySlot base count 2 rank)))
      (arraySlot base count 3 left) (if kept then rank + 1 else 0))
    0 (heap 0 + bit kept)

theorem finishRow_noJump : ∀ op ∈ finishRow, NoJump op := by
  simp [finishRow, storeOrd, storeInverse, addCount, loadArray, storeArray, arrayAddress, arrayBase,
    loadWorkspace, loadCell, storeCell, NoJump]

theorem finishRow_ready (rom : PhysicalROM) (start base count left right rank : Nat)
    (card : Nat → Nat) (keep : Nat → Bool) (state : NatState) (hbase : 16 ≤ base)
    (ready : RankReady base count left right rank (5 * (start + 172)) state)
    (htables : InputTables base count card keep state) (hl : left < count) (hrank : rank < count) :
    let result := runOps rom finishRow state
    RankReady base count left right rank (5 * (start + 273)) result ∧
      InputTables base count card keep result ∧
        result.heap = rowHeap base count left rank (keep left) state.heap := by
  have hb : 16 ≤ state.heap 8 := by rw [ready.base_cell]; exact hbase
  have hh : (runOps rom finishRow state).heap = rowHeap base count left rank (keep left) state.heap := by
    have h := finishRow_heap rom state hb
    rw [show finishedHeap state = rowHeap base count left rank (keep left) state.heap by
      dsimp only [finishedHeap]
      rw [ready.base_cell, ready.count_cell, ready.left_cell, ready.rank_cell, htables.2 left hl]
      cases keep left <;> simp [rowHeap, bit]] at h
    exact h
  have htables' : InputTables base count card keep (runOps rom finishRow state) := by
    constructor
    · intro index hi
      rw [hh]
      simpa (disch := omega) [rowHeap, arraySlot] using htables.1 index hi
    · intro index hi
      rw [hh]
      simpa (disch := omega) [rowHeap, arraySlot] using htables.2 index hi
  refine ⟨?_, htables', hh⟩
  constructor
  · rw [hh]
    simpa (disch := omega) [rowHeap, arraySlot] using ready.base_cell
  · rw [hh]
    simpa (disch := omega) [rowHeap, arraySlot] using ready.count_cell
  · rw [hh]
    simpa (disch := omega) [rowHeap, arraySlot] using ready.left_cell
  · rw [hh]
    simpa (disch := omega) [rowHeap, arraySlot] using ready.right_cell
  · rw [hh]
    simpa (disch := omega) [rowHeap, arraySlot] using ready.rank_cell
  · rw [runOps_pc rom finishRow state finishRow_noJump, finishRow_length, ready.pc]
    omega
  · rw [runOps_halted, ready.active]

def InnerFrame (base : Nat) (before after : NatState) : Prop :=
  ∀ address, address ≠ base + 2 → address ≠ base + 3 →
    address ≠ 1 → address ≠ 2 → address ≠ 3 → address ≠ 4 → address ≠ 5 →
    after.heap address = before.heap address

theorem InnerFrame.refl (base : Nat) (state : NatState) : InnerFrame base state state :=
  fun _ _ _ _ _ _ _ _ => rfl

theorem InnerFrame.trans (base : Nat) {one two three : NatState}
    (h12 : InnerFrame base one two) (h23 : InnerFrame base two three) : InnerFrame base one three := by
  intro address hcounter hrank h1 h2 h3 h4 h5
  exact (h23 address hcounter hrank h1 h2 h3 h4 h5).trans (h12 address hcounter hrank h1 h2 h3 h4 h5)

theorem InputTables.of_innerFrame (base count : Nat) (card : Nat → Nat) (keep : Nat → Bool)
    {before after : NatState} (hbase : 16 ≤ base) (htables : InputTables base count card keep before)
    (hframe : InnerFrame base before after) : InputTables base count card keep after := by
  constructor
  · intro index hi
    rw [hframe (arraySlot base count 0 index) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
      (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
      (by unfold arraySlot; omega) (by unfold arraySlot; omega)]
    exact htables.1 index hi
  · intro index hi
    rw [hframe (arraySlot base count 1 index) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
      (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
      (by unfold arraySlot; omega) (by unfold arraySlot; omega)]
    exact htables.2 index hi

private theorem contribution_eq (card : Nat → Nat) (keep : Nat → Bool) (left right : Nat) :
    precedesBit (card right) (card left) right left * bit (keep right) =
      if keep right && decide (Precedes card right left) then 1 else 0 := by
  rw [precedesBit_eq]
  cases keep right <;> simp [bit, Precedes]

theorem comparison_ready (rom : PhysicalROM) (start base count left right rank : Nat)
    (card : Nat → Nat) (keep : Nat → Bool) (state : NatState) (hbase : 16 ≤ base)
    (ready : RankReady base count left right rank (5 * (start + 47)) state)
    (htables : InputTables base count card keep state) (hl : left < count) (hr : right < count) :
    RankReady base count left right
      (rank + if keep right && decide (Precedes card right left) then 1 else 0)
      (5 * (start + 157)) (runOps rom comparison state) ∧
        InnerFrame base state (runOps rom comparison state) := by
  have hb : 16 ≤ state.heap 8 := by rw [ready.base_cell]; exact hbase
  have hframe : InnerFrame base state (runOps rom comparison state) := by
    intro address _hcounter hrank h1 h2 h3 h4 h5
    exact comparison_frame rom state hb address h1 h2 h3 h4 h5 (by simpa only [ready.base_cell] using hrank)
  refine ⟨?_, hframe⟩
  constructor
  · rw [hframe 8 (by omega) (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ready.base_cell
  · rw [hframe base (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact ready.count_cell
  · rw [hframe (base + 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact ready.left_cell
  · rw [comparison_frame rom state hb (base + 2) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by rw [ready.base_cell]; omega)]
    exact ready.right_cell
  · have h := comparison_rank rom state hb
    rw [ready.base_cell, ready.count_cell, ready.left_cell, ready.right_cell, ready.rank_cell,
      htables.1 left hl, htables.1 right hr, htables.2 right hr, contribution_eq] at h
    exact h
  · rw [runOps_pc rom comparison state comparison_noJump, comparison_length, ready.pc]
    omega
  · rw [runOps_halted, ready.active]

def processedCount (keep : Nat → Bool) (upto : Nat) : Nat := ((List.range upto).filter keep).length

theorem processedCount_zero (keep : Nat → Bool) : processedCount keep 0 = 0 := rfl

theorem processedCount_succ (keep : Nat → Bool) (upto : Nat) :
    processedCount keep (upto + 1) = processedCount keep upto + bit (keep upto) := by
  cases hk : keep upto <;> simp [processedCount, List.range_succ, List.filter_append, bit, hk]

theorem paperRank_eq (q : Nat) (full : List (Finset (Fin q))) (candidate : Nat) :
    rankCount (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full)
      candidate (full.length + q + 1) = RawCandidateRankPositions.lessCount q full candidate := by
  have heq : rankCount (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full)
      candidate (full.length + q + 1) = RawCandidateRankScan.rankBefore q full candidate (full.length + q + 1) := rfl
  exact heq.trans (RawCandidateRankScan.rankBefore_full q full candidate)

theorem paperRank_injective (q : Nat) (full : List (Finset (Fin q))) (left right : Nat)
    (hl : left < full.length + q + 1) (hr : right < full.length + q + 1)
    (hkl : RawCandidateOrder.keepCandidate q full left = true)
    (hkr : RawCandidateOrder.keepCandidate q full right = true)
    (heq : rankCount (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full)
      left (full.length + q + 1) =
      rankCount (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full)
        right (full.length + q + 1)) : left = right := by
  rw [paperRank_eq, paperRank_eq] at heq
  exact RawCandidateRankPositions.lessCount_injective q full left right
    ((RawCandidateOrder.retainedCandidateIndices_mem_iff q full left).mpr ⟨hl, hkl⟩)
    ((RawCandidateOrder.retainedCandidateIndices_mem_iff q full right).mpr ⟨hr, hkr⟩) heq

theorem processedCount_full (q : Nat) (full : List (Finset (Fin q))) :
    processedCount (RawCandidateOrder.keepCandidate q full) (full.length + q + 1) =
      (RawCandidateOrder.retainedCandidateIndices q full).length := by
  simp only [processedCount, RawCandidateOrder.retainedCandidateIndices, RawCandidateOrder.retainedIndices,
    RawCandidateOrder.candidateSupports_length]
  rfl

def ProtectedAddress (base count address : Nat) : Prop :=
  5 < address ∧ address ≠ base + 1 ∧ address ≠ base + 2 ∧ address ≠ base + 3 ∧
    (∀ index < count, address ≠ arraySlot base count 2 index) ∧
    (∀ index < count, address ≠ arraySlot base count 3 index) ∧ address ≠ arraySlot base count 4 0

def OrderingFrame (base count : Nat) (before after : NatState) : Prop :=
  ∀ address, ProtectedAddress base count address → after.heap address = before.heap address

theorem OrderingFrame.refl (base count : Nat) (state : NatState) : OrderingFrame base count state state :=
  fun _ _ => rfl

theorem OrderingFrame.trans (base count : Nat) {one two three : NatState}
    (h12 : OrderingFrame base count one two) (h23 : OrderingFrame base count two three) :
    OrderingFrame base count one three := fun address h => (h23 address h).trans (h12 address h)

structure OutputPrefix (q : Nat) (full : List (Finset (Fin q))) (base upto : Nat) (state : NatState) : Prop where
  counter : state.heap 0 = processedCount (RawCandidateOrder.keepCandidate q full) upto
  inverse : ∀ candidate < upto,
    state.heap (arraySlot base (full.length + q + 1) 3 candidate) =
      if RawCandidateOrder.keepCandidate q full candidate then RawCandidateRankPositions.lessCount q full candidate + 1 else 0
  order : ∀ candidate < upto, RawCandidateOrder.keepCandidate q full candidate = true →
    state.heap (arraySlot base (full.length + q + 1) 2 (RawCandidateRankPositions.lessCount q full candidate)) = candidate

structure Sorted (q : Nat) (full : List (Finset (Fin q))) (base start : Nat)
    (before after : NatState) : Prop where
  returned : OuterReady base (full.length + q + 1) (full.length + q + 1) (5 * (start + 303)) after
  tables : InputTables base (full.length + q + 1) (RawCandidateStableOrder.candidateCard q full)
    (RawCandidateOrder.keepCandidate q full) after
  output : OutputPrefix q full base (full.length + q + 1) after
  node_count : after.heap (arraySlot base (full.length + q + 1) 4 0) =
    (RawCandidateOrder.retainedCandidateIndices q full).length
  frame : OrderingFrame base (full.length + q + 1) before after

section Containing

variable (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
  (hbound : start + 303 ≤ containing.length)
  (hcode : ∀ position < 303, containing.getD (start + position) paddingOp =
    (programAt start).getD position paddingOp)

include hbound hcode

private theorem containing_slice (leading block suffix : List PackingOp) (offset : Nat)
    (hlayout : programAt start = leading ++ block ++ suffix) (hprefix : leading.length = offset) :
    start + offset + block.length ≤ containing.length ∧
      ∀ position < block.length, containing.getD ((start + offset) + position) paddingOp =
        block.getD position paddingOp := by
  have hspan : offset + block.length ≤ 303 := by
    have hl := congrArg List.length hlayout
    simp only [programAt_length, List.length_append, hprefix] at hl
    omega
  refine ⟨by omega, ?_⟩
  intro position hp
  have hh := hcode (offset + position) (by omega)
  have hm := getD_middle leading block suffix position hp
  rw [← hlayout, hprefix] at hm
  simpa only [Nat.add_assoc] using hh.trans hm

private theorem run_straight_layout (leading block suffix : List PackingOp) (offset : Nat)
    (hlayout : programAt start = leading ++ block ++ suffix) (hprefix : leading.length = offset)
    (hstraight : ∀ op ∈ block, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing block.length state = runOps rom block state := by
  have hs := containing_slice containing start hbound hcode leading block suffix offset hlayout hprefix
  apply natRun_of_straight_segment rom containing block (start + offset)
    (by omega) ?_ hstraight state hpc hactive
  intro position hp
  have hh := hs.2 position hp
  rw [List.getD_eq_getElem containing paddingOp (by omega), List.getD_eq_getElem block paddingOp hp] at hh
  exact hh

private theorem run_branch_layout (leading lead suffix : List PackingOp) (last : PackingOp) (offset : Nat)
    (hlayout : programAt start = leading ++ (lead ++ [last]) ++ suffix) (hprefix : leading.length = offset)
    (hstraight : ∀ op ∈ lead, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing (lead.length + 1) state = runOps rom (lead ++ [last]) state := by
  have hs := containing_slice containing start hbound hcode leading (lead ++ [last]) suffix offset hlayout hprefix
  have hsize : start + offset + (lead.length + 1) ≤ containing.length := by
    simpa only [List.length_append, List.length_cons, List.length_nil] using hs.1
  rw [runOps_append, runOps]
  apply natRun_of_segment_last rom containing lead last (start + offset)
    (by omega)
    ?_ ?_ hstraight state hpc hactive
  · intro position hp
    have hh := hs.2 position (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    rw [List.getD_append lead [last] paddingOp position hp,
      List.getD_eq_getElem containing paddingOp (by omega), List.getD_eq_getElem lead paddingOp hp] at hh
    exact hh
  · have hh := hs.2 lead.length (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    rw [List.getD_append_right lead [last] paddingOp lead.length le_rfl, Nat.sub_self,
      List.getD_cons_zero, List.getD_eq_getElem containing paddingOp (by omega)] at hh
    exact hh

theorem run_comparison (state : NatState)
    (hpc : state.pc = 5 * (start + 47)) (hactive : state.halted = false) :
    natRun rom containing 110 state = runOps rom comparison state := by
  let leading := initCode ++ testWorkspace 1 (start + 288) ++ rowInit ++ testWorkspace 2 (start + 172)
  let suffix := innerTail start ++ finishRow ++ outerTail start ++ finishCode
  have hlayout : programAt start = leading ++ comparison ++ suffix := by
    simp only [programAt, leading, suffix, List.append_assoc]
  have hp : leading.length = 47 := by
    simp only [leading, List.length_append, initCode_length, testWorkspace_length, rowInit_length]
  exact run_straight_layout rom containing start hbound hcode leading comparison suffix 47
    hlayout hp comparison_noJump state hpc hactive

theorem run_innerTest (state : NatState)
    (hpc : state.pc = 5 * (start + 34)) (hactive : state.halted = false) :
    natRun rom containing 13 state = runOps rom (testWorkspace 2 (start + 172)) state := by
  let leading := initCode ++ testWorkspace 1 (start + 288) ++ rowInit
  let suffix := comparison ++ innerTail start ++ finishRow ++ outerTail start ++ finishCode
  let lead := (testWorkspace 2 (start + 172)).take 12
  have hlength : lead.length = 12 := rfl
  have hlead : lead ++ [.jumpIfZero .flag .index] = testWorkspace 2 (start + 172) := rfl
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ suffix := by
    rw [hlead]
    simp only [programAt, leading, suffix, List.append_assoc]
  have hp : leading.length = 34 := by
    simp only [leading, List.length_append, initCode_length, testWorkspace_length, rowInit_length]
  have hstraight : ∀ op ∈ lead, NoJump op := by
    simp [lead, testWorkspace, loadWorkspace, loadCell, NoJump]
  have hh := run_branch_layout rom containing start hbound hcode leading lead suffix
    (.jumpIfZero .flag .index) 34 hlayout hp hstraight state hpc hactive
  simpa only [hlead, hlength] using hh

theorem run_innerTail (state : NatState)
    (hpc : state.pc = 5 * (start + 157)) (hactive : state.halted = false) :
    natRun rom containing 15 state = runOps rom (innerTail start) state := by
  let leading := initCode ++ testWorkspace 1 (start + 288) ++ rowInit ++
    testWorkspace 2 (start + 172) ++ comparison
  let suffix := finishRow ++ outerTail start ++ finishCode
  let lead := (innerTail start).take 14
  have hlength : lead.length = 14 := rfl
  have hlead : lead ++ [.jumpIfZero .flag .index] = innerTail start := rfl
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ suffix := by
    rw [hlead]
    simp only [programAt, leading, suffix, List.append_assoc]
  have hp : leading.length = 157 := by
    simp only [leading, List.length_append, initCode_length, testWorkspace_length,
      rowInit_length, comparison_length]
  have hstraight : ∀ op ∈ lead, NoJump op := by
    simp [lead, innerTail, incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, jumpTo, NoJump]
  have hh := run_branch_layout rom containing start hbound hcode leading lead suffix
    (.jumpIfZero .flag .index) 157 hlayout hp hstraight state hpc hactive
  simpa only [hlead, hlength] using hh

theorem run_initCode (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    natRun rom containing 9 state = runOps rom initCode state := by
  let suffix := testWorkspace 1 (start + 288) ++ rowInit ++ testWorkspace 2 (start + 172) ++
    comparison ++ innerTail start ++ finishRow ++ outerTail start ++ finishCode
  have hlayout : programAt start = [] ++ initCode ++ suffix := by
    simp only [programAt, suffix, List.nil_append, List.append_assoc]
  exact run_straight_layout rom containing start hbound hcode [] initCode suffix 0 hlayout rfl
    (by simp [initCode, setCell, storeCell, setWorkspace, storeWorkspace, loadCell, NoJump])
    state (by simpa only [Nat.add_zero] using hpc) hactive

theorem run_rowInit (state : NatState)
    (hpc : state.pc = 5 * (start + 22)) (hactive : state.halted = false) :
    natRun rom containing 12 state = runOps rom rowInit state := by
  let leading := initCode ++ testWorkspace 1 (start + 288)
  let suffix := testWorkspace 2 (start + 172) ++ comparison ++ innerTail start ++ finishRow ++ outerTail start ++ finishCode
  have hlayout : programAt start = leading ++ rowInit ++ suffix := by
    simp only [programAt, leading, suffix, List.append_assoc]
  have hp : leading.length = 22 := by simp only [leading, List.length_append, initCode_length, testWorkspace_length]
  exact run_straight_layout rom containing start hbound hcode leading rowInit suffix 22 hlayout hp
    (by simp [rowInit, setWorkspace, storeWorkspace, loadCell, NoJump]) state hpc hactive

theorem run_finishRow (state : NatState)
    (hpc : state.pc = 5 * (start + 172)) (hactive : state.halted = false) :
    natRun rom containing 101 state = runOps rom finishRow state := by
  let leading := initCode ++ testWorkspace 1 (start + 288) ++ rowInit ++
    testWorkspace 2 (start + 172) ++ comparison ++ innerTail start
  let suffix := outerTail start ++ finishCode
  have hlayout : programAt start = leading ++ finishRow ++ suffix := by
    simp only [programAt, leading, suffix, List.append_assoc]
  have hp : leading.length = 172 := by
    simp only [leading, List.length_append, initCode_length, testWorkspace_length,
      rowInit_length, comparison_length, innerTail_length]
  exact run_straight_layout rom containing start hbound hcode leading finishRow suffix 172 hlayout hp
    (by simp [finishRow, storeOrd, storeInverse, addCount, loadArray, storeArray, arrayAddress, arrayBase,
      loadWorkspace, loadCell, storeCell, NoJump]) state hpc hactive

theorem run_outerTail (state : NatState)
    (hpc : state.pc = 5 * (start + 273)) (hactive : state.halted = false) :
    natRun rom containing 15 state = runOps rom (outerTail start) state := by
  let leading := initCode ++ testWorkspace 1 (start + 288) ++ rowInit ++
    testWorkspace 2 (start + 172) ++ comparison ++ innerTail start ++ finishRow
  let lead := (outerTail start).take 14
  have hlength : lead.length = 14 := rfl
  have hlead : lead ++ [.jumpIfZero .flag .index] = outerTail start := rfl
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ finishCode := by
    rw [hlead]
    simp only [programAt, leading, List.append_assoc]
  have hp : leading.length = 273 := by
    simp only [leading, List.length_append, initCode_length, testWorkspace_length,
      rowInit_length, comparison_length, innerTail_length, finishRow_length]
  have hh := run_branch_layout rom containing start hbound hcode leading lead finishCode
    (.jumpIfZero .flag .index) 273 hlayout hp
    (by simp [lead, outerTail, incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, jumpTo, NoJump])
    state hpc hactive
  simpa only [hlead, hlength] using hh

theorem run_outerTest (state : NatState)
    (hpc : state.pc = 5 * (start + 9)) (hactive : state.halted = false) :
    natRun rom containing 13 state = runOps rom (testWorkspace 1 (start + 288)) state := by
  let suffix := rowInit ++ testWorkspace 2 (start + 172) ++ comparison ++ innerTail start ++
    finishRow ++ outerTail start ++ finishCode
  let lead := (testWorkspace 1 (start + 288)).take 12
  have hlength : lead.length = 12 := rfl
  have hlead : lead ++ [.jumpIfZero .flag .index] = testWorkspace 1 (start + 288) := rfl
  have hlayout : programAt start = initCode ++ (lead ++ [.jumpIfZero .flag .index]) ++ suffix := by
    rw [hlead]
    simp only [programAt, suffix, List.append_assoc]
  have hh := run_branch_layout rom containing start hbound hcode initCode lead suffix
    (.jumpIfZero .flag .index) 9 hlayout initCode_length
    (by simp [lead, testWorkspace, loadWorkspace, loadCell, NoJump]) state hpc hactive
  simpa only [hlead, hlength] using hh

theorem run_finishCode (state : NatState)
    (hpc : state.pc = 5 * (start + 288)) (hactive : state.halted = false) :
    natRun rom containing 15 state = runOps rom finishCode state := by
  let leading := initCode ++ testWorkspace 1 (start + 288) ++ rowInit ++ testWorkspace 2 (start + 172) ++
    comparison ++ innerTail start ++ finishRow ++ outerTail start
  have hlayout : programAt start = leading ++ finishCode ++ [] := by
    simp only [programAt, leading, List.append_assoc, List.append_nil]
  have hp : leading.length = 288 := by
    simp only [leading, List.length_append, initCode_length, testWorkspace_length,
      rowInit_length, comparison_length, innerTail_length, finishRow_length, outerTail_length]
  exact run_straight_layout rom containing start hbound hcode leading finishCode [] 288 hlayout hp
    (by simp [finishCode, arrayBase, loadWorkspace, loadCell, NoJump]) state hpc hactive

theorem inner_iteration (base count left right rank : Nat) (card : Nat → Nat) (keep : Nat → Bool)
    (state : NatState) (hbase : 16 ≤ base)
    (ready : RankReady base count left right rank (5 * (start + 34)) state)
    (htables : InputTables base count card keep state) (hl : left < count) (hr : right < count) :
    let result := natRun rom containing 138 state
    RankReady base count left (right + 1)
      (rank + if keep right && decide (Precedes card right left) then 1 else 0)
      (5 * (start + 34)) result ∧ InputTables base count card keep result ∧ InnerFrame base state result := by
  let tested := runOps rom (testWorkspace 2 (start + 172)) state
  have ht := testWorkspace_effect rom 2 (start + 172) state
  dsimp only at ht
  have htested : tested.heap = state.heap := ht.1
  have rt : RankReady base count left right rank (5 * (start + 47)) tested := by
    constructor
    · exact (congrFun htested 8).trans ready.base_cell
    · exact (congrFun htested base).trans ready.count_cell
    · exact (congrFun htested (base + 1)).trans ready.left_cell
    · exact (congrFun htested (base + 2)).trans ready.right_cell
    · exact (congrFun htested (base + 3)).trans ready.rank_cell
    · have hp := ht.2.1
      rw [ready.base_cell, ready.count_cell, ready.right_cell,
        ite_eq_right (Nat.sub_ne_zero_of_lt hr), ready.pc] at hp
      dsimp only [tested]
      omega
    · exact ht.2.2.trans ready.active
  have htestedTables : InputTables base count card keep tested := by
    constructor
    · intro index hi
      rw [htested]
      exact htables.1 index hi
    · intro index hi
      rw [htested]
      exact htables.2 index hi
  let compared := runOps rom comparison tested
  rcases comparison_ready rom start base count left right rank card keep tested hbase rt htestedTables hl hr with
    ⟨rc, hfc⟩
  have htail := innerTail_effect rom start compared
  dsimp only at htail
  have hbc : compared.heap 8 = base := rc.base_cell
  have hjc : compared.heap (base + 2) = right := rc.right_cell
  have hh : (runOps rom (innerTail start) compared).heap =
      Function.update compared.heap (base + 2) (right + 1) := by
    simpa only [hbc, hjc] using htail.1
  have hrun : natRun rom containing 138 state = runOps rom (innerTail start) compared := by
    rw [show 138 = 13 + (110 + 15) by decide, natRun_add,
      run_innerTest rom containing start hbound hcode state ready.pc ready.active]
    change natRun rom containing (110 + 15) tested = _
    rw [natRun_add, run_comparison rom containing start hbound hcode tested rt.pc rt.active]
    exact run_innerTail rom containing start hbound hcode compared rc.pc rc.active
  have hframe : InnerFrame base state (runOps rom (innerTail start) compared) := by
    intro address hcounter hrank h1 h2 h3 h4 h5
    rw [hh]
    simpa only [Function.update_of_ne hcounter] using
      (hfc address hcounter hrank h1 h2 h3 h4 h5).trans (congrFun htested address)
  dsimp only
  rw [hrun]
  refine ⟨?_, InputTables.of_innerFrame base count card keep hbase htables hframe, hframe⟩
  constructor
  · rw [hh]
    simpa (disch := omega) using rc.base_cell
  · rw [hh]
    simpa using rc.count_cell
  · rw [hh]
    simpa using rc.left_cell
  · rw [hh]
    simp
  · rw [hh]
    simpa using rc.rank_cell
  · exact htail.2.1
  · exact htail.2.2.trans rc.active

theorem rank_scan_partial (base count left : Nat) (card : Nat → Nat) (keep : Nat → Bool)
    (state : NatState) (hbase : 16 ≤ base)
    (ready : RankReady base count left 0 0 (5 * (start + 34)) state)
    (htables : InputTables base count card keep state) (hl : left < count)
    (upto : Nat) (hupto : upto ≤ count) :
    let result := natRun rom containing (138 * upto) state
    RankReady base count left upto (rankCount card keep left upto) (5 * (start + 34)) result ∧
      InputTables base count card keep result ∧ InnerFrame base state result := by
  revert hupto
  induction upto with
  | zero =>
    intro _
    exact ⟨ready, htables, InnerFrame.refl base state⟩
  | succ upto ih =>
    intro hupto
    rcases ih (by omega) with ⟨rp, htp, hfp⟩
    let previous := natRun rom containing (138 * upto) state
    have hs := inner_iteration rom containing start hbound hcode base count left upto
      (rankCount card keep left upto) card keep previous hbase rp htp hl (by omega)
    dsimp only at hs
    have hrun : natRun rom containing (138 * (upto + 1)) state = natRun rom containing 138 previous := by
      rw [show 138 * (upto + 1) = 138 * upto + 138 by omega, natRun_add]
    dsimp only
    rw [hrun, rankCount_succ]
    exact ⟨hs.1, hs.2.1, InnerFrame.trans base hfp hs.2.2⟩

theorem rank_scan (base count left : Nat) (card : Nat → Nat) (keep : Nat → Bool)
    (state : NatState) (hbase : 16 ≤ base)
    (ready : RankReady base count left 0 0 (5 * (start + 34)) state)
    (htables : InputTables base count card keep state) (hl : left < count) :
    let result := natRun rom containing (138 * count + 13) state
    RankReady base count left count (rankCount card keep left count) (5 * (start + 172)) result ∧
      InputTables base count card keep result ∧ InnerFrame base state result := by
  rcases rank_scan_partial rom containing start hbound hcode base count left card keep state hbase
    ready htables hl count le_rfl with ⟨rp, htp, hfp⟩
  let previous := natRun rom containing (138 * count) state
  have ht := testWorkspace_effect rom 2 (start + 172) previous
  dsimp only at ht
  have hbp : previous.heap 8 = base := rp.base_cell
  have hmp : previous.heap base = count := rp.count_cell
  have hjp : previous.heap (base + 2) = count := rp.right_cell
  have hh : (runOps rom (testWorkspace 2 (start + 172)) previous).heap = previous.heap := ht.1
  have hrun : natRun rom containing (138 * count + 13) state =
      runOps rom (testWorkspace 2 (start + 172)) previous := by
    rw [natRun_add]
    exact run_innerTest rom containing start hbound hcode previous rp.pc rp.active
  have hframe : InnerFrame base state (runOps rom (testWorkspace 2 (start + 172)) previous) := by
    intro address hcounter hrank h1 h2 h3 h4 h5
    exact (congrFun hh address).trans (hfp address hcounter hrank h1 h2 h3 h4 h5)
  dsimp only
  rw [hrun]
  refine ⟨?_, InputTables.of_innerFrame base count card keep hbase htables hframe, hframe⟩
  constructor
  · exact (congrFun hh 8).trans rp.base_cell
  · exact (congrFun hh base).trans rp.count_cell
  · exact (congrFun hh (base + 1)).trans rp.left_cell
  · exact (congrFun hh (base + 2)).trans rp.right_cell
  · exact (congrFun hh (base + 3)).trans rp.rank_cell
  · simpa only [hbp, hmp, hjp, Nat.sub_self, ite_true] using ht.2.1
  · exact ht.2.2.trans rp.active

theorem outer_iteration (base count left : Nat) (card : Nat → Nat) (keep : Nat → Bool)
    (state : NatState) (hbase : 16 ≤ base)
    (ready : OuterReady base count left (5 * (start + 9)) state)
    (htables : InputTables base count card keep state) (hl : left < count) :
    let rank := rankCount card keep left count
    let result := natRun rom containing (138 * count + 154) state
    OuterReady base count (left + 1) (5 * (start + 9)) result ∧
      InputTables base count card keep result ∧
      result.heap 0 = state.heap 0 + bit (keep left) ∧
      result.heap (arraySlot base count 3 left) = (if keep left then rank + 1 else 0) ∧
      result.heap (arraySlot base count 2 rank) =
        (if keep left then left else state.heap (arraySlot base count 2 rank)) ∧
      RowFrame base count left rank (keep left) state result := by
  let tested := runOps rom (testWorkspace 1 (start + 288)) state
  let initialized := runOps rom rowInit tested
  let ranked := natRun rom containing (138 * count + 13) initialized
  let written := runOps rom finishRow ranked
  let finished := runOps rom (outerTail start) written
  let rank := rankCount card keep left count
  have hrank : rank < count := rankCount_lt card keep left count hl
  have ht := testWorkspace_effect rom 1 (start + 288) state
  dsimp only at ht
  have htt : tested.heap = state.heap := ht.1
  have htestpc : tested.pc = 5 * (start + 22) := by
    have hp := ht.2.1
    rw [ready.base_cell, ready.count_cell, ready.left_cell, ite_eq_right (Nat.sub_ne_zero_of_lt hl), ready.pc] at hp
    dsimp only [tested]
    omega
  have htestactive : tested.halted = false := ht.2.2.trans ready.active
  have hbtested : 16 ≤ tested.heap 8 := by rw [htt, ready.base_cell]; exact hbase
  have hiheap : initialized.heap = Function.update (Function.update state.heap (base + 2) 0) (base + 3) 0 := by
    have h := rowInit_heap rom tested hbtested
    simpa only [htt, ready.base_cell] using h
  have ri : RankReady base count left 0 0 (5 * (start + 34)) initialized := by
    constructor
    · rw [hiheap]
      simpa (disch := omega) using ready.base_cell
    · rw [hiheap]
      simpa using ready.count_cell
    · rw [hiheap]
      simpa using ready.left_cell
    · rw [hiheap]
      simp
    · rw [hiheap]
      simp
    · rw [show initialized = runOps rom rowInit tested from rfl,
        runOps_pc rom rowInit tested (by simp [rowInit, setWorkspace, storeWorkspace, loadCell, NoJump]),
        rowInit_length, htestpc]
      omega
    · rw [show initialized = runOps rom rowInit tested from rfl, runOps_halted, htestactive]
  have hfi : InnerFrame base state initialized := by
    intro address hcounter hrank' _h1 _h2 _h3 _h4 _h5
    rw [hiheap]
    simp [hcounter, hrank']
  have hti := InputTables.of_innerFrame base count card keep hbase htables hfi
  rcases rank_scan rom containing start hbound hcode base count left card keep initialized hbase ri hti hl with
    ⟨rr, htr, hfr⟩
  have hfr' : InnerFrame base state ranked := InnerFrame.trans base hfi hfr
  rcases finishRow_ready rom start base count left count rank card keep ranked hbase rr htr hl hrank with
    ⟨rw', htw, hhw⟩
  have hbw : written.heap 8 = base := rw'.base_cell
  have hiw : written.heap (base + 1) = left := rw'.left_cell
  have ho := outerTail_effect rom start written
  dsimp only at ho
  have hho : finished.heap = Function.update written.heap (base + 1) (left + 1) := by
    simpa only [hbw, hiw] using ho.1
  have hrun : natRun rom containing (138 * count + 154) state = finished := by
    rw [show 138 * count + 154 = 13 + (12 + ((138 * count + 13) + (101 + 15))) by omega,
      natRun_add, run_outerTest rom containing start hbound hcode state ready.pc ready.active]
    change natRun rom containing (12 + ((138 * count + 13) + (101 + 15))) tested = _
    rw [natRun_add, run_rowInit rom containing start hbound hcode tested htestpc htestactive]
    change natRun rom containing ((138 * count + 13) + (101 + 15)) initialized = _
    rw [natRun_add]
    change natRun rom containing (101 + 15) ranked = _
    rw [natRun_add, run_finishRow rom containing start hbound hcode ranked rr.pc rr.active]
    exact run_outerTail rom containing start hbound hcode written rw'.pc rw'.active
  have hframe : RowFrame base count left rank (keep left) state finished := by
    intro address h0 h1 h2 h3 h4 h5 hi hj hr hinv hord
    rw [hho, show written.heap = _ from hhw]
    have hf := hfr' address hj hr h1 h2 h3 h4 h5
    cases hk : keep left
    · by_cases heq : address = arraySlot base count 2 rank
      · subst address
        simpa [rowHeap, hk, bit, h0, h3, hi, hinv] using hf
      · simpa [rowHeap, hk, bit, h0, h3, hi, hinv, heq] using hf
    · have hnord := hord hk
      simpa [rowHeap, hk, bit, h0, h3, hi, hinv, hnord] using hf
  have htf : InputTables base count card keep finished := by
    constructor
    · intro index hindex
      rw [hho]
      simpa (disch := omega) [arraySlot] using htw.1 index hindex
    · intro index hindex
      rw [hho]
      simpa (disch := omega) [arraySlot] using htw.2 index hindex
  have hf0 : ranked.heap 0 = state.heap 0 :=
    hfr' 0 (by omega) (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hford : ranked.heap (arraySlot base count 2 rank) = state.heap (arraySlot base count 2 rank) :=
    hfr' _ (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
      (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
  dsimp only
  rw [hrun]
  refine ⟨?_, htf, ?_, ?_, ?_, hframe⟩
  · constructor
    · rw [hho]
      simpa (disch := omega) using hbw
    · rw [hho]
      simpa using rw'.count_cell
    · rw [hho]
      simp
    · exact ho.2.1
    · exact ho.2.2.trans rw'.active
  · rw [hho, show written.heap = _ from hhw]
    simpa (disch := omega) [rowHeap] using congrArg (fun n => n + bit (keep left)) hf0
  · rw [hho, show written.heap = _ from hhw]
    simp (disch := omega) [rowHeap, arraySlot, rank]
  · rw [hho, show written.heap = _ from hhw]
    cases keep left
    · simpa (disch := omega) [rowHeap, bit, arraySlot, rank] using hford
    · simp (disch := omega) [rowHeap, bit, arraySlot, rank]

theorem outer_scan_partial (q : Nat) (full : List (Finset (Fin q))) (base : Nat)
    (state : NatState) (hbase : 16 ≤ base)
    (ready : OuterReady base (full.length + q + 1) 0 (5 * (start + 9)) state)
    (htables : InputTables base (full.length + q + 1) (RawCandidateStableOrder.candidateCard q full)
      (RawCandidateOrder.keepCandidate q full) state)
    (hzero : state.heap 0 = 0) (upto : Nat) (hupto : upto ≤ full.length + q + 1) :
    let result := natRun rom containing ((138 * (full.length + q + 1) + 154) * upto) state
    OuterReady base (full.length + q + 1) upto (5 * (start + 9)) result ∧
      InputTables base (full.length + q + 1) (RawCandidateStableOrder.candidateCard q full)
        (RawCandidateOrder.keepCandidate q full) result ∧
      OutputPrefix q full base upto result ∧ OrderingFrame base (full.length + q + 1) state result := by
  revert hupto
  induction upto with
  | zero =>
    intro _
    refine ⟨ready, htables, ?_, OrderingFrame.refl _ _ state⟩
    constructor
    · exact hzero
    · intro candidate hc
      omega
    · intro candidate hc
      omega
  | succ upto ih =>
    intro hupto
    rcases ih (by omega) with ⟨rp, htp, hop, hfp⟩
    let previous := natRun rom containing ((138 * (full.length + q + 1) + 154) * upto) state
    let next := natRun rom containing (138 * (full.length + q + 1) + 154) previous
    let rank := rankCount (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full)
      upto (full.length + q + 1)
    have hcurrent : upto < full.length + q + 1 := by omega
    have hrank : rank < full.length + q + 1 := rankCount_lt _ _ _ _ hcurrent
    rcases outer_iteration rom containing start hbound hcode base (full.length + q + 1) upto
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full)
      previous hbase rp htp hcurrent with ⟨rn, htn, hcount, hinverse, horder, hrow⟩
    have hrun : natRun rom containing ((138 * (full.length + q + 1) + 154) * (upto + 1)) state = next := by
      rw [Nat.mul_succ, natRun_add]
    have hon : OutputPrefix q full base (upto + 1) next := by
      constructor
      · rw [hcount, hop.counter, processedCount_succ]
      · intro candidate hc
        by_cases heq : candidate = upto
        · subst candidate
          simpa only [paperRank_eq] using hinverse
        · have hprior : candidate < upto := by omega
          have hf := hrow (arraySlot base (full.length + q + 1) 3 candidate)
            (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
            (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
            (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
            (by unfold arraySlot; omega) (by intro _; unfold arraySlot; omega)
          exact hf.trans (hop.inverse candidate hprior)
      · intro candidate hc hk
        by_cases heq : candidate = upto
        · subst candidate
          simpa only [paperRank_eq, hk, ite_true] using horder
        · have hprior : candidate < upto := by omega
          have hraw : candidate < full.length + q + 1 := by omega
          have hcandidateRank := RawCandidateRankScan.lessCount_lt_candidateCount q full candidate hraw
          have hne : RawCandidateOrder.keepCandidate q full upto = true →
              RawCandidateRankPositions.lessCount q full candidate ≠ rank := by
            intro hku hsame
            apply heq
            apply paperRank_injective q full candidate upto hraw hcurrent hk hku
            rw [paperRank_eq]
            exact hsame
          have hf := hrow
            (arraySlot base (full.length + q + 1) 2 (RawCandidateRankPositions.lessCount q full candidate))
            (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
            (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
            (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
            (by unfold arraySlot; omega) (by
              intro hku hequal
              apply hne hku
              unfold arraySlot at hequal
              omega)
          exact hf.trans (hop.order candidate hprior hk)
    have hfn : OrderingFrame base (full.length + q + 1) previous next := by
      intro address hprotected
      rcases hprotected with ⟨hsmall, hi, hj, hr, hord, hinv, _hnode⟩
      exact hrow address (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        hi hj hr (hinv upto hcurrent) (fun _ => hord rank hrank)
    dsimp only
    rw [hrun]
    exact ⟨rn, htn, hon, OrderingFrame.trans _ _ hfp hfn⟩

/-- Complete actual dynamic sorting, with the caller arrays as its only
semantic handoff.  Both loop clocks are proved from fetched instructions. -/
theorem sort (q : Nat) (full : List (Finset (Fin q))) (base : Nat) (state : NatState)
    (hbase : 16 ≤ base) (hptr : state.heap 8 = base) (hcount : state.heap base = full.length + q + 1)
    (htables : InputTables base (full.length + q + 1) (RawCandidateStableOrder.candidateCard q full)
      (RawCandidateOrder.keepCandidate q full) state)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    Sorted q full base start state (natRun rom containing (totalSteps (full.length + q + 1)) state) := by
  let initialized := runOps rom initCode state
  let scanned := natRun rom containing
    ((138 * (full.length + q + 1) + 154) * (full.length + q + 1)) initialized
  let tested := runOps rom (testWorkspace 1 (start + 288)) scanned
  let finished := runOps rom finishCode tested
  have hih : initialized.heap = Function.update (Function.update state.heap 0 0) (base + 1) 0 := by
    simpa only [hptr] using initCode_heap rom state
  have ri : OuterReady base (full.length + q + 1) 0 (5 * (start + 9)) initialized := by
    constructor
    · rw [hih]
      simpa (disch := omega) using hptr
    · rw [hih]
      simpa (disch := omega) using hcount
    · rw [hih]
      simp
    · rw [show initialized = runOps rom initCode state from rfl,
        runOps_pc rom initCode state
          (by simp [initCode, setCell, storeCell, setWorkspace, storeWorkspace, loadCell, NoJump]),
        initCode_length, hpc]
      omega
    · rw [show initialized = runOps rom initCode state from rfl, runOps_halted, hactive]
  have hti : InputTables base (full.length + q + 1) (RawCandidateStableOrder.candidateCard q full)
      (RawCandidateOrder.keepCandidate q full) initialized := by
    constructor
    · intro index hi
      rw [hih]
      simpa (disch := omega) [arraySlot] using htables.1 index hi
    · intro index hi
      rw [hih]
      simpa (disch := omega) [arraySlot] using htables.2 index hi
  have hzero : initialized.heap 0 = 0 := by rw [hih]; simp (disch := omega)
  have hfi : OrderingFrame base (full.length + q + 1) state initialized := by
    intro address hp
    rw [hih]
    simp [show address ≠ 0 by have h := hp.1; omega, hp.2.1]
  rcases outer_scan_partial rom containing start hbound hcode q full base initialized hbase ri hti hzero
    (full.length + q + 1) le_rfl with ⟨rs, hts, hos, hfs⟩
  have ht := testWorkspace_effect rom 1 (start + 288) scanned
  dsimp only at ht
  have hbs : scanned.heap 8 = base := rs.base_cell
  have hms : scanned.heap base = full.length + q + 1 := rs.count_cell
  have his : scanned.heap (base + 1) = full.length + q + 1 := rs.left_cell
  have htt : tested.heap = scanned.heap := ht.1
  have htestpc : tested.pc = 5 * (start + 288) := by
    simpa only [hbs, hms, his, Nat.sub_self, ite_true] using ht.2.1
  have htestactive : tested.halted = false := ht.2.2.trans rs.active
  have hfh : finished.heap = Function.update scanned.heap
      (arraySlot base (full.length + q + 1) 4 0) (scanned.heap 0) := by
    simpa only [htt, hbs, hms] using finishCode_heap rom tested
  have hclock : totalSteps (full.length + q + 1) =
      9 + (((138 * (full.length + q + 1) + 154) * (full.length + q + 1)) + (13 + 15)) := by
    unfold totalSteps
    nlinarith
  have hrun : natRun rom containing (totalSteps (full.length + q + 1)) state = finished := by
    rw [hclock, natRun_add, run_initCode rom containing start hbound hcode state hpc hactive]
    change natRun rom containing
      (((138 * (full.length + q + 1) + 154) * (full.length + q + 1)) + (13 + 15)) initialized = _
    rw [natRun_add]
    change natRun rom containing (13 + 15) scanned = _
    rw [natRun_add, run_outerTest rom containing start hbound hcode scanned rs.pc rs.active]
    exact run_finishCode rom containing start hbound hcode tested htestpc htestactive
  rw [hrun]
  constructor
  · constructor
    · rw [hfh]
      simpa (disch := omega) [arraySlot] using hbs
    · rw [hfh]
      simpa (disch := omega) [arraySlot] using hms
    · rw [hfh]
      simpa (disch := omega) [arraySlot] using his
    · rw [show finished = runOps rom finishCode tested from rfl,
        runOps_pc rom finishCode tested (by simp [finishCode, arrayBase, loadWorkspace, loadCell, NoJump]),
        finishCode_length, htestpc]
      omega
    · rw [show finished = runOps rom finishCode tested from rfl, runOps_halted, htestactive]
  · constructor
    · intro index hi
      rw [hfh]
      simpa (disch := omega) [arraySlot] using hts.1 index hi
    · intro index hi
      rw [hfh]
      simpa (disch := omega) [arraySlot] using hts.2 index hi
  · constructor
    · rw [hfh]
      simpa (disch := omega) [arraySlot] using hos.counter
    · intro candidate hc
      rw [hfh]
      simpa (disch := omega) [arraySlot] using hos.inverse candidate hc
    · intro candidate hc hk
      have hrc := RawCandidateRankScan.lessCount_lt_candidateCount q full candidate hc
      rw [hfh]
      simpa (disch := omega) [arraySlot] using hos.order candidate hc hk
  · rw [hfh]
    rw [Function.update_self]
    exact (show scanned.heap 0 = processedCount (RawCandidateOrder.keepCandidate q full)
      (full.length + q + 1) from hos.counter).trans (processedCount_full q full)
  · apply OrderingFrame.trans _ _ (OrderingFrame.trans _ _ hfi hfs)
    intro address hp
    change finished.heap address = scanned.heap address
    rw [hfh]
    simp [hp.2.2.2.2.2.2]

end Containing

theorem append_slice (left right : List PackingOp) :
    left.length + 303 ≤ (left ++ programAt left.length ++ right).length ∧
      ∀ position < 303,
        (left ++ programAt left.length ++ right).getD (left.length + position) paddingOp =
          (programAt left.length).getD position paddingOp := by
  constructor
  · simp only [List.length_append, programAt_length]
    omega
  · intro position hp
    rw [List.getD_append (left ++ programAt left.length) right paddingOp _ (by
      simp only [List.length_append, programAt_length]; omega),
      List.getD_append_right left (programAt left.length) paddingOp _ (by omega), Nat.add_sub_cancel_left]

/-- The actual append layout discharges the public code-slice premises. -/
theorem sort_append (q : Nat) (full : List (Finset (Fin q))) (left right : List PackingOp)
    (base : Nat) (state : NatState) (hbase : 16 ≤ base)
    (hptr : state.heap 8 = base) (hcount : state.heap base = full.length + q + 1)
    (htables : InputTables base (full.length + q + 1) (RawCandidateStableOrder.candidateCard q full)
      (RawCandidateOrder.keepCandidate q full) state)
    (hpc : state.pc = 5 * left.length) (hactive : state.halted = false) :
    Sorted q full base left.length state
      (natRun (rawIncidenceROM q full) (left ++ programAt left.length ++ right)
        (totalSteps (full.length + q + 1)) state) := by
  exact sort (rawIncidenceROM q full) _ left.length (append_slice left right).1 (append_slice left right).2
    q full base state hbase hptr hcount htables hpc hactive

/-- The IDs actually stored by the count-ranking machine name exactly the
support at each position of the original prepared node order. -/
theorem Sorted.support_at_position (q : Nat) (full : List (Finset (Fin q)))
    (base start : Nat) (before after : NatState) (sorted : Sorted q full base start before after)
    (hq : 0 < q) (position : Nat)
    (hp : position < (RawCandidateOrder.retainedCandidateIndices q full).length) :
    ∃ candidate, candidate ∈ RawCandidateOrder.retainedCandidateIndices q full ∧
      after.heap (arraySlot base (full.length + q + 1) 2 position) = candidate ∧
      after.heap (arraySlot base (full.length + q + 1) 3 candidate) = position + 1 ∧
      (prepareNormalization q full).order.getD position ∅ =
        (RawCandidateOrder.candidateSupports q full).getD candidate ∅ := by
  have hsize : (prepareNormalization q full).indexed.nodes.size =
      (RawCandidateOrder.retainedCandidateIndices q full).length :=
    (RawCandidateRankPositions.sortedCandidateIndices_length q full hq).symm.trans
      (RawCandidateStableOrder.sortedCandidateIndices_perm q full).length_eq
  have hp' : position < (prepareNormalization q full).indexed.nodes.size := by rw [hsize]; exact hp
  obtain ⟨candidate, ⟨hmem, hrank, hsupport⟩, _⟩ :=
    RawCandidateRankPositions.existsUnique_candidate_and_support_at_position q full hq position hp'
  obtain ⟨hcandidate, hkeep⟩ := (RawCandidateOrder.retainedCandidateIndices_mem_iff q full candidate).mp hmem
  refine ⟨candidate, hmem, ?_, ?_, hsupport⟩
  · have h := sorted.output.order candidate hcandidate hkeep
    simpa only [hrank] using h
  · have h := sorted.output.inverse candidate hcandidate
    simpa only [hkeep, ite_true, hrank] using h

theorem totalSteps_quadratic (count : Nat) : totalSteps count ≤ 330 * (count + 1) ^ 2 := by
  unfold totalSteps
  nlinarith

end PaperProofs.Structure.LaminarTree.RawCandidateOrderingRAM
