module

public import PaperProofs.Structure.RawCandidateIncidenceWord
public import PaperProofs.Structure.PA17_WordBounds_023
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private candidate of the fixed32 raw query preserving hardware.address.
Only the old readonly query's short paths are adapted: the two eager q-read
instructions move into the stage-read branch. No heap write or free restore. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareBankNodeBit022Raw
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine
  RawIncidenceLaminarRAM RawIncidenceScanSafety

def headerLead (start : Nat) : List PackingOp :=
  [.base (.base (.constant .index 0)), .base (.base (.loadROM .input .total .index)),
   .base (.base (.constant .index (5 * (start + 31))))]
def header (start : Nat) : List PackingOp := headerLead start ++ [.jumpIfZero .old .index]
def classifyLead (start : Nat) : List PackingOp :=
  [.base (.subtract .flag .old .total), .base (.base (.constant .index (5 * (start + 19))))]
def classify (start : Nat) : List PackingOp := classifyLead start ++ [.jumpIfZero .flag .index]
def singletonLead (start : Nat) : List PackingOp :=
  RawCandidateIncidenceBlock.singletonLead start
def singletonTest (start : Nat) : List PackingOp := singletonLead start ++ [.jumpIfZero .flag .index]
def stageRead : List PackingOp :=
  [.base (.base (.constant .index 1)), .base (.base (.loadROM .input .value .index)),
   .base (.base (.constant .flag 1)), .base (.subtract .flag .old .flag),
   .arithmetic .multiply .flag .flag .value, .base (.base (.add .flag .flag .fresh)),
   .base (.base (.constant .index 2)), .base (.base (.add .index .flag .index)),
   .base (.base (.loadROM .input .value .index))]
def programAt (start : Nat) : List PackingOp :=
  header start ++ classify start ++ singletonTest start ++ jumpTo (start + 32) ++
    stageRead ++ jumpTo (start + 32) ++ [.base (.base (.constant .value 1))]
theorem programAt_length (start : Nat) : (programAt start).length = 32 := rfl

def paddingOp : PackingOp := .base (.base (.constant .value 0))

def pathIndices (N candidate tool : Nat) : List Nat :=
  if candidate = 0 then List.range 4 ++ [31]
  else if candidate ≤ N then List.range 7 ++ (List.range 12).map (19 + ·)
  else if candidate - N - 1 = tool then List.range 16 ++ [31]
  else List.range 19

def pathOps (start N candidate tool : Nat) : List PackingOp :=
  if candidate = 0 then header start ++ [.base (.base (.constant .value 1))]
  else if candidate ≤ N then header start ++ classify start ++ stageRead ++ jumpTo (start + 32)
  else if candidate - N - 1 = tool then
    header start ++ classify start ++ singletonTest start ++ [.base (.base (.constant .value 1))]
  else header start ++ classify start ++ singletonTest start ++ jumpTo (start + 32)

def steps (N candidate tool : Nat) : Nat :=
  if candidate = 0 then 5 else if candidate ≤ N then 19
  else if candidate - N - 1 = tool then 17 else 19

theorem pathIndices_length (N candidate tool : Nat) : (pathIndices N candidate tool).length = steps N candidate tool := by
  by_cases hr : candidate = 0
  · simp [pathIndices, steps, hr]
  · by_cases hs : candidate ≤ N
    · simp [pathIndices, steps, hr, hs]
    · by_cases heq : candidate - N - 1 = tool <;>
        simp [pathIndices, steps, hr, hs, heq]

theorem pathOps_length (start N candidate tool : Nat) : (pathOps start N candidate tool).length = steps N candidate tool := by
  by_cases hr : candidate = 0
  · simp [pathOps, steps, hr, header, headerLead]
  · by_cases hs : candidate ≤ N
    · simp [pathOps, steps, hr, hs, header, headerLead,
        classify, classifyLead, stageRead, jumpTo]
    · by_cases heq : candidate - N - 1 = tool <;>
        simp [pathOps, steps, hr, hs, heq,
          header, headerLead, classify, classifyLead, singletonTest, singletonLead, RawCandidateIncidenceBlock.singletonLead, jumpTo]

theorem path_index_lt (N candidate tool count : Nat) (hc : count < steps N candidate tool) :
    (pathIndices N candidate tool).getD count 32 < 32 := by
  by_cases hr : candidate = 0
  · simp only [steps, hr, ite_true] at hc
    interval_cases count <;> simp [pathIndices, hr]
  · by_cases hs : candidate ≤ N
    · simp only [steps, hr, ite_false, hs, ite_true] at hc
      interval_cases count <;> simp [pathIndices, hr, hs]
    · by_cases heq : candidate - N - 1 = tool
      · simp only [steps, hr, ite_false, hs, heq, ite_true] at hc
        interval_cases count <;> simp [pathIndices, hr, hs, heq]
      · simp only [steps, hr, ite_false, hs, heq] at hc
        interval_cases count <;> simp [pathIndices, hr, hs, heq]

theorem path_index_le (N candidate tool count : Nat) (hc : count ≤ steps N candidate tool) :
    (pathIndices N candidate tool).getD count 32 ≤ 32 := by
  by_cases heq : count = steps N candidate tool
  · subst count
    rw [← pathIndices_length, List.getD_eq_default]
    omega
  · exact (path_index_lt N candidate tool count (by omega)).le

theorem path_op_matches (start N candidate tool count : Nat) (hc : count < steps N candidate tool) :
    (programAt start).getD ((pathIndices N candidate tool).getD count 32) paddingOp =
      (pathOps start N candidate tool).getD count paddingOp := by
  by_cases hr : candidate = 0
  · simp only [steps, hr, ite_true] at hc
    interval_cases count <;> simp [pathIndices, pathOps, hr] <;> rfl
  · by_cases hs : candidate ≤ N
    · simp only [steps, hr, ite_false, hs, ite_true] at hc
      interval_cases count <;> simp [pathIndices, pathOps, hr, hs] <;> rfl
    · by_cases heq : candidate - N - 1 = tool
      · simp only [steps, hr, ite_false, hs, heq, ite_true] at hc
        interval_cases count <;> simp [pathIndices, pathOps, hr, hs, heq] <;> rfl
      · simp only [steps, hr, ite_false, hs, heq] at hc
        interval_cases count <;> simp [pathIndices, pathOps, hr, hs, heq] <;> rfl

theorem stage_pointer_bound {N q candidate tool : Nat} (hr : candidate ≠ 0)
    (hs : candidate ≤ N) (ht : tool < q) : 2 + (candidate - 1) * q + tool < N * q + 2 := by
  have hm := Nat.mul_le_mul_right q (show candidate - 1 + 1 ≤ N by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem path_prefix_pc (q : Nat) (full : List (Finset (Fin q))) (start : Nat)
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 5 * start) (hcandidate : state.register .old = candidate.val)
    (htool : state.register .fresh = tool.val) (count : Nat) (hc : count ≤ steps full.length candidate.val tool.val) :
    (runOps (rawIncidenceROM q full) ((pathOps start full.length candidate.val tool.val).take count) state).pc =
      5 * (start + (pathIndices full.length candidate.val tool.val).getD count 32) := by
  by_cases hr : candidate.val = 0
  · simp only [steps, hr, ite_true] at hc
    interval_cases count <;>
      simp [pathOps, pathIndices, hr, header, headerLead, runOps, natExecuteOp, Op.execute,
        Instruction.execute, hcandidate, hpc]
    all_goals omega
  · by_cases hs : candidate.val ≤ full.length
    · simp only [steps, hr, ite_false, hs, ite_true] at hc
      interval_cases count <;>
        simp [pathOps, pathIndices, hr, hs, header, headerLead, classify, classifyLead,
          stageRead, jumpTo, runOps, natExecuteOp, Op.execute,
          Instruction.execute, raw_header_N, hcandidate, hpc, Nat.sub_eq_zero_of_le hs]
      all_goals omega
    · have hsub : candidate.val - full.length ≠ 0 := by omega
      by_cases heq : candidate.val - full.length - 1 = tool.val
      · simp only [steps, hr, ite_false, hs, heq, ite_true] at hc
        interval_cases count <;>
          simp [pathOps, pathIndices, hr, hs, heq, header, headerLead, classify, classifyLead,
            singletonTest, singletonLead, RawCandidateIncidenceBlock.singletonLead, runOps, natExecuteOp, Op.execute, Instruction.execute,
            raw_header_N, hcandidate, htool, hpc, hsub]
        all_goals omega
      · simp only [steps, hr, ite_false, hs, heq] at hc
        interval_cases count <;>
          simp [pathOps, pathIndices, hr, hs, heq, header, headerLead, classify, classifyLead,
            singletonTest, singletonLead, RawCandidateIncidenceBlock.singletonLead, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute,
            raw_header_N, hcandidate, htool, hpc, hsub]
        all_goals first | omega | (split_ifs <;> omega)

theorem path_prefix_accessFits (q : Nat) (full : List (Finset (Fin q))) (start heapWords : Nat)
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hcandidate : state.register .old = candidate.val) (htool : state.register .fresh = tool.val)
    (count : Nat) (hc : count < steps full.length candidate.val tool.val) :
    NatAccessFits (rawIncidenceROM q full) heapWords
      (runOps (rawIncidenceROM q full) ((pathOps start full.length candidate.val tool.val).take count) state)
      ((pathOps start full.length candidate.val tool.val).getD count paddingOp) := by
  by_cases hr : candidate.val = 0
  · simp only [steps, hr, ite_true] at hc
    interval_cases count <;>
      simp [pathOps, hr, header, headerLead, runOps, natExecuteOp, Op.execute,
        Instruction.execute, NatAccessFits, AccessFits, rawIncidenceROM, PhysicalROM.words]
  · by_cases hs : candidate.val ≤ full.length
    · have hptr := stage_pointer_bound hr hs tool.isLt
      simp only [steps, hr, ite_false, hs, ite_true] at hc
      interval_cases count <;>
        simp [pathOps, hr, hs, header, headerLead, classify, classifyLead, stageRead,
          jumpTo, runOps, natExecuteOp, natArithmetic,
          Op.execute, Instruction.execute, NatAccessFits, AccessFits, hcandidate, htool,
          rawIncidenceROM, PhysicalROM.words, PhysicalROM.semantic, incidence_length]
      omega
    · by_cases heq : candidate.val - full.length - 1 = tool.val
      · simp only [steps, hr, ite_false, hs, heq, ite_true] at hc
        interval_cases count <;>
          simp [pathOps, hr, hs, heq, header, headerLead, classify, classifyLead,
            singletonTest, singletonLead, RawCandidateIncidenceBlock.singletonLead, runOps, natExecuteOp, Op.execute, Instruction.execute,
            NatAccessFits, AccessFits, rawIncidenceROM, PhysicalROM.words]
      · simp only [steps, hr, ite_false, hs, heq] at hc
        interval_cases count <;>
          simp [pathOps, hr, hs, heq, header, headerLead, classify, classifyLead,
            singletonTest, singletonLead, RawCandidateIncidenceBlock.singletonLead, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute,
            NatAccessFits, AccessFits, rawIncidenceROM, PhysicalROM.words]

theorem path_prefix_frame (q : Nat) (full : List (Finset (Fin q))) (start candidate tool : Nat)
    (state : NatState) (count : Nat) (hc : count ≤ steps full.length candidate tool) :
    let after := runOps (rawIncidenceROM q full) ((pathOps start full.length candidate tool).take count) state
    after.heap = state.heap ∧ after.register .old = state.register .old ∧ after.register .fresh = state.register .fresh ∧ after.register .address = state.register .address := by
  by_cases hr : candidate = 0
  · simp only [steps, hr, ite_true] at hc
    interval_cases count <;> simp [pathOps, hr, header, headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · by_cases hs : candidate ≤ full.length
    · simp only [steps, hr, ite_false, hs, ite_true] at hc
      interval_cases count <;> simp [pathOps, hr, hs, header, headerLead, classify, classifyLead,
        stageRead, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
    · by_cases heq : candidate - full.length - 1 = tool
      · simp only [steps, hr, ite_false, hs, heq, ite_true] at hc
        interval_cases count <;> simp [pathOps, hr, hs, heq, header, headerLead, classify, classifyLead,
          singletonTest, singletonLead, RawCandidateIncidenceBlock.singletonLead, runOps, natExecuteOp, Op.execute, Instruction.execute]
      · simp only [steps, hr, ite_false, hs, heq] at hc
        interval_cases count <;> simp [pathOps, hr, hs, heq, header, headerLead, classify, classifyLead,
          singletonTest, singletonLead, RawCandidateIncidenceBlock.singletonLead, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]

private theorem widen_fits (factor N q : Nat) (hf : 16 ≤ factor) {value : Nat}
    (h : Fits (indexWidth 16 N q) value) : Fits (indexWidth factor N q) value :=
  PA17WordBounds023.fits_mono_bits (PA17WordBounds023.indexWidth_mono_factor 16 factor N q hf) h

/-- Root's fixed ord-cache offset fits the common32 width (and every
already supported factor≥16). It is not a per-instance code eligibility. -/
theorem literal532_fits (factor N q : Nat) (hf : 16 ≤ factor) : Fits (indexWidth factor N q) 532 :=
  (show 532 ≤ N * q + N + q + 640 by omega).trans_lt
    (widen_fits factor N q hf (fits_checker_register_bound N q))

private theorem raw_read_bit_fits_wide (factor q : Nat) (full : List (Finset (Fin q)))
    (hf : 16 ≤ factor) (candidate : Fin (full.length + q + 1)) (tool : Fin q)
    (hr : candidate.val ≠ 0) (hs : candidate.val ≤ full.length) :
    Fits (indexWidth factor full.length q) ((rawIncidenceROM q full).semantic.read .input
      (2 + (candidate.val - 1) * q + tool.val)) := by
  have hbit := raw_bit_le_one q full ⟨candidate.val - 1, by omega⟩ tool
  have hone : Fits (indexWidth factor full.length q) 1 :=
    (show 1 ≤ full.length * q + full.length + q + 640 by omega).trans_lt
      (widen_fits factor full.length q hf (fits_checker_register_bound full.length q))
  exact hbit.trans_lt hone

theorem path_prefix_registersFit_wide (factor q : Nat) (full : List (Finset (Fin q)))
    (hf : 16 ≤ factor) (start : Nat)
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hfit : RegistersFit (indexWidth factor full.length q) state)
    (hend : Fits (indexWidth factor full.length q) (5 * (start + 32)))
    (hcandidate : state.register .old = candidate.val) (htool : state.register .fresh = tool.val)
    (count : Nat) (hc : count ≤ steps full.length candidate.val tool.val) :
    RegistersFit (indexWidth factor full.length q)
      (runOps (rawIncidenceROM q full) ((pathOps start full.length candidate.val tool.val).take count) state) := by
  have hK := widen_fits factor full.length q hf (fits_checker_register_bound full.length q)
  have hsmall (value : Nat) (hv : value ≤ full.length * q + full.length + q + 640) :
      Fits (indexWidth factor full.length q) value := hv.trans_lt hK
  have h31 : Fits (indexWidth factor full.length q) (5 * (start + 31)) := lt_of_le_of_lt (by omega) hend
  have h19 : Fits (indexWidth factor full.length q) (5 * (start + 19)) := lt_of_le_of_lt (by omega) hend
  have hcandidateLt := candidate.isLt
  have htoolLt := tool.isLt
  by_cases hr : candidate.val = 0
  · simp only [steps, hr, ite_true] at hc
    interval_cases count <;> intro reg <;> cases reg <;>
      simp [pathOps, hr, header, headerLead, runOps, natExecuteOp, Op.execute,
        Instruction.execute, raw_header_N, hcandidate, htool]
    all_goals first | exact hfit _ | exact h31 | apply hsmall; omega
  · by_cases hs : candidate.val ≤ full.length
    · have hptr := stage_pointer_bound hr hs tool.isLt
      have hread := raw_read_bit_fits_wide factor q full hf candidate tool hr hs
      have hread' : Fits (indexWidth factor full.length q) ((rawIncidenceROM q full).semantic.read .input
          ((candidate.val - 1) * q + tool.val + 2)) := by
        simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hread
      simp only [steps, hr, ite_false, hs, ite_true] at hc
      interval_cases count <;> intro reg <;> cases reg <;>
        simp [pathOps, hr, hs, header, headerLead, classify, classifyLead,
          stageRead, jumpTo, runOps, natExecuteOp, natArithmetic,
          Op.execute, Instruction.execute, raw_header_N, raw_header_q, hcandidate, htool]
      all_goals first | exact hfit _ | exact h31 | exact h19 | exact hend | exact hread' | apply hsmall; omega
    · by_cases heq : candidate.val - full.length - 1 = tool.val
      · simp only [steps, hr, ite_false, hs, heq, ite_true] at hc
        interval_cases count <;> intro reg <;> cases reg <;>
          simp [pathOps, hr, hs, heq, header, headerLead, classify, classifyLead,
            singletonTest, singletonLead, RawCandidateIncidenceBlock.singletonLead, runOps, natExecuteOp, Op.execute, Instruction.execute,
            raw_header_N, hcandidate, htool]
        all_goals first | exact hfit _ | exact h31 | exact h19 | apply hsmall; omega
      · simp only [steps, hr, ite_false, hs, heq] at hc
        interval_cases count <;> intro reg <;> cases reg <;>
          simp [pathOps, hr, hs, heq, header, headerLead, classify, classifyLead,
            singletonTest, singletonLead, RawCandidateIncidenceBlock.singletonLead, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute,
            raw_header_N, hcandidate, htool]
        all_goals first | exact hfit _ | exact h31 | exact h19 | exact hend | apply hsmall; omega


section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 32 ≤ containing.length)
  (hcode : ∀ position < 32, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)
  (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
  (hpc : state.pc = 5 * start) (hactive : state.halted = false)
  (hcandidate : state.register .old = candidate.val) (htool : state.register .fresh = tool.val)

include hbound hcode hpc hactive hcandidate htool

theorem natRun_prefix_eq (count : Nat) (hc : count ≤ steps full.length candidate.val tool.val) :
    natRun (rawIncidenceROM q full) containing count state =
      runOps (rawIncidenceROM q full) ((pathOps start full.length candidate.val tool.val).take count) state := by
  revert hc
  induction count with
  | zero =>
    intro _
    rfl
  | succ count ih =>
    intro hc
    have hk : count < steps full.length candidate.val tool.val := by omega
    have hlen : count < (pathOps start full.length candidate.val tool.val).length := by rw [pathOps_length]; exact hk
    let previous := runOps (rawIncidenceROM q full) ((pathOps start full.length candidate.val tool.val).take count) state
    let index := (pathIndices full.length candidate.val tool.val).getD count 32
    have hi : index < 32 := path_index_lt _ _ _ _ hk
    have hp : previous.pc = 5 * (start + index) := path_prefix_pc q full start candidate tool state hpc hcandidate htool count hk.le
    have ha : previous.halted = false := (runOps_halted _ _ _).trans hactive
    have hh := (hcode index hi).trans (path_op_matches start full.length candidate.val tool.val count hk)
    rw [List.getD_eq_getElem containing paddingOp (by omega),
      List.getD_eq_getElem _ paddingOp hlen] at hh
    rw [natRun_succ, ih hk.le,
      natStep_of_index _ containing previous (start + index) (by omega) hp ha,
      List.take_succ_eq_append_getElem hlen, runOps_append]
    exact congrArg (fun op => natExecuteOp (rawIncidenceROM q full) op previous) hh

theorem natRun_prefix_pc (count : Nat) (hc : count ≤ steps full.length candidate.val tool.val) :
    (natRun (rawIncidenceROM q full) containing count state).pc =
      5 * (start + (pathIndices full.length candidate.val tool.val).getD count 32) := by
  rw [natRun_prefix_eq q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool count hc]
  exact path_prefix_pc q full start candidate tool state hpc hcandidate htool count hc

end Linked

theorem steps_le (N candidate tool : Nat) : steps N candidate tool ≤ 19 := by
  unfold steps
  split_ifs <;> omega

/-- Actual selected path implements the old semantic candidate support;
this reuses the established support-to-candidate-list correspondence. -/
theorem path_value (q : Nat) (full : List (Finset (Fin q))) (start : Nat)
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hcandidate : state.register .old = candidate.val) (htool : state.register .fresh = tool.val) :
    (runOps (rawIncidenceROM q full) (pathOps start full.length candidate.val tool.val) state).register .value =
      bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅)) := by
  rw [← RawCandidateIncidenceRAM.support_eq_candidateSupports_getD]
  by_cases hr : candidate.val = 0
  · simp [pathOps, RawCandidateIncidenceRAM.support, hr, header, headerLead,
      runOps, natExecuteOp, Op.execute, Instruction.execute, hcandidate, bit]
  · by_cases hs : candidate.val ≤ full.length
    · have hread : (rawIncidenceROM q full).semantic.read .input
          (tool.val + (candidate.val - 1) * q + 2) = bit (decide (tool ∈ full[candidate.val - 1]'(by omega))) := by
        simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (raw_bit q full ⟨candidate.val - 1, by omega⟩ tool)
      simp [pathOps, RawCandidateIncidenceRAM.support, hr, hs, header, headerLead, classify,
        classifyLead, stageRead, jumpTo, runOps, natExecuteOp, natArithmetic,
        Op.execute, Instruction.execute, raw_header_N, raw_header_q, hcandidate, htool,
        Nat.add_comm, Nat.add_left_comm]
      exact hread
    · by_cases heq : candidate.val - full.length - 1 = tool.val
      · simp [pathOps, RawCandidateIncidenceRAM.support, hr, hs, heq, header, headerLead, classify,
          classifyLead, singletonTest, singletonLead, RawCandidateIncidenceBlock.singletonLead,
          runOps, natExecuteOp, Op.execute, Instruction.execute, raw_header_N,
          hcandidate, htool, bit, eq_comm]
      · simp [pathOps, RawCandidateIncidenceRAM.support, hr, hs, heq, Ne.symm heq, header, headerLead,
          classify, classifyLead, singletonTest, singletonLead, RawCandidateIncidenceBlock.singletonLead,
          jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute, raw_header_N,
          hcandidate, htool, bit, Fin.ext_iff, eq_comm]

def ReturnedActive (start : Nat) (before after : NatState) (answer : Nat) : Prop :=
  after.register .value = answer ∧ after.register .old = before.register .old ∧
    after.register .fresh = before.register .fresh ∧ after.register .address = before.register .address ∧
    after.heap = before.heap ∧ after.pc = 5 * (start + 32) ∧ after.halted = false

theorem query (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
    (hbound : start + 32 ≤ containing.length)
    (hcode : ∀ position < 32, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false)
    (hcandidate : state.register .old = candidate.val) (htool : state.register .fresh = tool.val) :
    ReturnedActive start state
      (natRun (rawIncidenceROM q full) containing (steps full.length candidate.val tool.val) state)
      (bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))) := by
  let n := steps full.length candidate.val tool.val
  have hrun := natRun_prefix_eq q full containing start hbound hcode candidate tool state
    hpc hactive hcandidate htool n le_rfl
  have hlen : (pathOps start full.length candidate.val tool.val).take n =
      pathOps start full.length candidate.val tool.val := by
    apply List.take_of_length_le
    rw [pathOps_length]
  have hframe := path_prefix_frame q full start candidate.val tool.val state n le_rfl
  have hp := path_prefix_pc q full start candidate tool state hpc hcandidate htool n le_rfl
  have hend : (pathIndices full.length candidate.val tool.val).getD n 32 = 32 := by
    rw [List.getD_eq_default]
    rw [pathIndices_length]
  rw [hend] at hp
  unfold ReturnedActive
  rw [hrun]
  refine ⟨?_, hframe.2.1, hframe.2.2.1, hframe.2.2.2, hframe.1, hp, ?_⟩
  · rw [hlen]
    exact path_value q full start candidate tool state hcandidate htool
  · exact (runOps_halted _ _ _).trans hactive

end PaperProofs.Structure.LaminarTree.PA06A19PrepareBankNodeBit022Raw
