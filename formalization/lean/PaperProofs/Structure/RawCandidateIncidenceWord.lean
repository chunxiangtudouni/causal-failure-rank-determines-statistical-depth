module

public import PaperProofs.Structure.RawCandidateIncidenceBlock
public import PaperProofs.Structure.PackingWordRefinement
public import PaperProofs.Structure.RawIncidenceOuterSafety
import Mathlib.Tactic.IntervalCases

/-! Word safety of each actual branch of the fixed candidate-bit query.
The lists below describe its proved executed path; they neither generate
code nor replace fetched execution with a host query. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateIncidenceWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine
  RawIncidenceLaminarRAM RawIncidenceScanSafety
open RawCandidateIncidenceBlock (programAt header headerLead classify classifyLead singletonTest singletonLead stageRead)

def paddingOp : PackingOp := .base (.base (.constant .value 0))

def pathIndices (N candidate tool : Nat) : List Nat :=
  if candidate = 0 then List.range 6 ++ [31]
  else if candidate ≤ N then List.range 9 ++ (List.range 10).map (21 + ·)
  else if candidate - N - 1 = tool then List.range 18 ++ [31]
  else List.range 21

def pathOps (start N candidate tool : Nat) : List PackingOp :=
  if candidate = 0 then header start ++ [.base (.base (.constant .value 1))]
  else if candidate ≤ N then header start ++ classify start ++ stageRead ++ jumpTo (start + 32)
  else if candidate - N - 1 = tool then
    header start ++ classify start ++ singletonTest start ++ [.base (.base (.constant .value 1))]
  else header start ++ classify start ++ singletonTest start ++ jumpTo (start + 32)

def steps (N candidate tool : Nat) : Nat := RawCandidateIncidenceRAM.querySteps N candidate tool - 1

theorem pathIndices_length (N candidate tool : Nat) : (pathIndices N candidate tool).length = steps N candidate tool := by
  by_cases hr : candidate = 0
  · simp [pathIndices, steps, RawCandidateIncidenceRAM.querySteps, hr]
  · by_cases hs : candidate ≤ N
    · simp [pathIndices, steps, RawCandidateIncidenceRAM.querySteps, hr, hs]
    · by_cases heq : candidate - N - 1 = tool <;>
        simp [pathIndices, steps, RawCandidateIncidenceRAM.querySteps, hr, hs, heq]

theorem pathOps_length (start N candidate tool : Nat) : (pathOps start N candidate tool).length = steps N candidate tool := by
  by_cases hr : candidate = 0
  · simp [pathOps, steps, RawCandidateIncidenceRAM.querySteps, hr, header, headerLead]
  · by_cases hs : candidate ≤ N
    · simp [pathOps, steps, RawCandidateIncidenceRAM.querySteps, hr, hs, header, headerLead,
        classify, classifyLead, stageRead, RawCandidateIncidenceRAM.stageRead, jumpTo]
    · by_cases heq : candidate - N - 1 = tool <;>
        simp [pathOps, steps, RawCandidateIncidenceRAM.querySteps, hr, hs, heq,
          header, headerLead, classify, classifyLead, singletonTest, singletonLead, jumpTo]

theorem path_index_lt (N candidate tool count : Nat) (hc : count < steps N candidate tool) :
    (pathIndices N candidate tool).getD count 32 < 32 := by
  by_cases hr : candidate = 0
  · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_true] at hc
    interval_cases count <;> simp [pathIndices, hr]
  · by_cases hs : candidate ≤ N
    · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, ite_true] at hc
      interval_cases count <;> simp [pathIndices, hr, hs]
    · by_cases heq : candidate - N - 1 = tool
      · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, heq, ite_true] at hc
        interval_cases count <;> simp [pathIndices, hr, hs, heq]
      · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, heq] at hc
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
  · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_true] at hc
    interval_cases count <;> simp [pathIndices, pathOps, hr] <;> rfl
  · by_cases hs : candidate ≤ N
    · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, ite_true] at hc
      interval_cases count <;> simp [pathIndices, pathOps, hr, hs] <;> rfl
    · by_cases heq : candidate - N - 1 = tool
      · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, heq, ite_true] at hc
        interval_cases count <;> simp [pathIndices, pathOps, hr, hs, heq] <;> rfl
      · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, heq] at hc
        interval_cases count <;> simp [pathIndices, pathOps, hr, hs, heq] <;> rfl

theorem stage_pointer_bound {N q candidate tool : Nat} (hr : candidate ≠ 0)
    (hs : candidate ≤ N) (ht : tool < q) : 2 + (candidate - 1) * q + tool < N * q + 2 := by
  have hm := Nat.mul_le_mul_right q (show candidate - 1 + 1 ≤ N by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  omega

private theorem raw_read_bit_fits (q : Nat) (full : List (Finset (Fin q)))
    (candidate : Fin (full.length + q + 1)) (tool : Fin q)
    (hr : candidate.val ≠ 0) (hs : candidate.val ≤ full.length) :
    Fits (indexWidth 16 full.length q) ((rawIncidenceROM q full).semantic.read .input
      (2 + (candidate.val - 1) * q + tool.val)) := by
  rw [raw_bit q full ⟨candidate.val - 1, by omega⟩ tool]
  have hf : Fits (indexWidth 16 full.length q) 1 :=
    (show 1 ≤ full.length * q + full.length + q + 640 by omega).trans_lt (fits_checker_register_bound full.length q)
  cases decide (tool ∈ full[candidate.val - 1]'(by omega)) <;> simp only [bit]
  · exact (show 0 ≤ 1 by omega).trans_lt hf
  · exact hf

theorem path_prefix_pc (q : Nat) (full : List (Finset (Fin q))) (start : Nat)
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 5 * start) (hcandidate : state.register .old = candidate.val)
    (htool : state.register .fresh = tool.val) (count : Nat) (hc : count ≤ steps full.length candidate.val tool.val) :
    (runOps (rawIncidenceROM q full) ((pathOps start full.length candidate.val tool.val).take count) state).pc =
      5 * (start + (pathIndices full.length candidate.val tool.val).getD count 32) := by
  by_cases hr : candidate.val = 0
  · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_true] at hc
    interval_cases count <;>
      simp [pathOps, pathIndices, hr, header, headerLead, runOps, natExecuteOp, Op.execute,
        Instruction.execute, hcandidate, hpc]
    all_goals omega
  · by_cases hs : candidate.val ≤ full.length
    · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, ite_true] at hc
      interval_cases count <;>
        simp [pathOps, pathIndices, hr, hs, header, headerLead, classify, classifyLead,
          stageRead, RawCandidateIncidenceRAM.stageRead, jumpTo, runOps, natExecuteOp, Op.execute,
          Instruction.execute, raw_header_N, hcandidate, hpc, Nat.sub_eq_zero_of_le hs]
      all_goals omega
    · have hsub : candidate.val - full.length ≠ 0 := by omega
      by_cases heq : candidate.val - full.length - 1 = tool.val
      · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, heq, ite_true] at hc
        interval_cases count <;>
          simp [pathOps, pathIndices, hr, hs, heq, header, headerLead, classify, classifyLead,
            singletonTest, singletonLead, runOps, natExecuteOp, Op.execute, Instruction.execute,
            raw_header_N, hcandidate, htool, hpc, hsub]
        all_goals omega
      · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, heq] at hc
        interval_cases count <;>
          simp [pathOps, pathIndices, hr, hs, heq, header, headerLead, classify, classifyLead,
            singletonTest, singletonLead, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute,
            raw_header_N, hcandidate, htool, hpc, hsub]
        all_goals first | omega | (split_ifs <;> omega)

theorem path_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (start : Nat)
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 32)))
    (hcandidate : state.register .old = candidate.val) (htool : state.register .fresh = tool.val)
    (count : Nat) (hc : count ≤ steps full.length candidate.val tool.val) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((pathOps start full.length candidate.val tool.val).take count) state) := by
  have hK := fits_checker_register_bound full.length q
  have hsmall (value : Nat) (hv : value ≤ full.length * q + full.length + q + 640) :
      Fits (indexWidth 16 full.length q) value := hv.trans_lt hK
  have h31 : Fits (indexWidth 16 full.length q) (5 * (start + 31)) := lt_of_le_of_lt (by omega) hend
  have h21 : Fits (indexWidth 16 full.length q) (5 * (start + 21)) := lt_of_le_of_lt (by omega) hend
  have hcandidateLt := candidate.isLt
  have htoolLt := tool.isLt
  by_cases hr : candidate.val = 0
  · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_true] at hc
    interval_cases count <;> intro reg <;> cases reg <;>
      simp [pathOps, hr, header, headerLead, runOps, natExecuteOp, Op.execute,
        Instruction.execute, raw_header_N, raw_header_q, hcandidate, htool]
    all_goals first | exact hfit _ | exact h31 | apply hsmall; omega
  · by_cases hs : candidate.val ≤ full.length
    · have hptr := stage_pointer_bound hr hs tool.isLt
      have hread := raw_read_bit_fits q full candidate tool hr hs
      have hread' : Fits (indexWidth 16 full.length q) ((rawIncidenceROM q full).semantic.read .input
          ((candidate.val - 1) * q + tool.val + 2)) := by
        simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hread
      simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, ite_true] at hc
      interval_cases count <;> intro reg <;> cases reg <;>
        simp [pathOps, hr, hs, header, headerLead, classify, classifyLead,
          stageRead, RawCandidateIncidenceRAM.stageRead, jumpTo, runOps, natExecuteOp, natArithmetic,
          Op.execute, Instruction.execute, raw_header_N, raw_header_q, hcandidate, htool]
      all_goals first | exact hfit _ | exact h31 | exact h21 | exact hend | exact hread' | apply hsmall; omega
    · by_cases heq : candidate.val - full.length - 1 = tool.val
      · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, heq, ite_true] at hc
        interval_cases count <;> intro reg <;> cases reg <;>
          simp [pathOps, hr, hs, heq, header, headerLead, classify, classifyLead,
            singletonTest, singletonLead, runOps, natExecuteOp, Op.execute, Instruction.execute,
            raw_header_N, raw_header_q, hcandidate, htool]
        all_goals first | exact hfit _ | exact h31 | exact h21 | apply hsmall; omega
      · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, heq] at hc
        interval_cases count <;> intro reg <;> cases reg <;>
          simp [pathOps, hr, hs, heq, header, headerLead, classify, classifyLead,
            singletonTest, singletonLead, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute,
            raw_header_N, raw_header_q, hcandidate, htool]
        all_goals first | exact hfit _ | exact h31 | exact h21 | exact hend | apply hsmall; omega

theorem path_prefix_accessFits (q : Nat) (full : List (Finset (Fin q))) (start heapWords : Nat)
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hcandidate : state.register .old = candidate.val) (htool : state.register .fresh = tool.val)
    (count : Nat) (hc : count < steps full.length candidate.val tool.val) :
    NatAccessFits (rawIncidenceROM q full) heapWords
      (runOps (rawIncidenceROM q full) ((pathOps start full.length candidate.val tool.val).take count) state)
      ((pathOps start full.length candidate.val tool.val).getD count paddingOp) := by
  by_cases hr : candidate.val = 0
  · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_true] at hc
    interval_cases count <;>
      simp [pathOps, hr, header, headerLead, runOps, natExecuteOp, Op.execute,
        Instruction.execute, NatAccessFits, AccessFits, rawIncidenceROM, PhysicalROM.words]
  · by_cases hs : candidate.val ≤ full.length
    · have hptr := stage_pointer_bound hr hs tool.isLt
      simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, ite_true] at hc
      interval_cases count <;>
        simp [pathOps, hr, hs, header, headerLead, classify, classifyLead, stageRead,
          RawCandidateIncidenceRAM.stageRead, jumpTo, runOps, natExecuteOp, natArithmetic,
          Op.execute, Instruction.execute, NatAccessFits, AccessFits, hcandidate, htool,
          rawIncidenceROM, PhysicalROM.words, PhysicalROM.semantic, incidence_length]
      omega
    · by_cases heq : candidate.val - full.length - 1 = tool.val
      · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, heq, ite_true] at hc
        interval_cases count <;>
          simp [pathOps, hr, hs, heq, header, headerLead, classify, classifyLead,
            singletonTest, singletonLead, runOps, natExecuteOp, Op.execute, Instruction.execute,
            NatAccessFits, AccessFits, rawIncidenceROM, PhysicalROM.words]
      · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, heq] at hc
        interval_cases count <;>
          simp [pathOps, hr, hs, heq, header, headerLead, classify, classifyLead,
            singletonTest, singletonLead, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute,
            NatAccessFits, AccessFits, rawIncidenceROM, PhysicalROM.words]

theorem path_prefix_frame (q : Nat) (full : List (Finset (Fin q))) (start candidate tool : Nat)
    (state : NatState) (count : Nat) (hc : count ≤ steps full.length candidate tool) :
    let after := runOps (rawIncidenceROM q full) ((pathOps start full.length candidate tool).take count) state
    after.heap = state.heap ∧ after.register .old = state.register .old ∧ after.register .fresh = state.register .fresh := by
  by_cases hr : candidate = 0
  · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_true] at hc
    interval_cases count <;> simp [pathOps, hr, header, headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · by_cases hs : candidate ≤ full.length
    · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, ite_true] at hc
      interval_cases count <;> simp [pathOps, hr, hs, header, headerLead, classify, classifyLead,
        stageRead, RawCandidateIncidenceRAM.stageRead, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
    · by_cases heq : candidate - full.length - 1 = tool
      · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, heq, ite_true] at hc
        interval_cases count <;> simp [pathOps, hr, hs, heq, header, headerLead, classify, classifyLead,
          singletonTest, singletonLead, runOps, natExecuteOp, Op.execute, Instruction.execute]
      · simp only [steps, RawCandidateIncidenceRAM.querySteps, hr, ite_false, hs, heq] at hc
        interval_cases count <;> simp [pathOps, hr, hs, heq, header, headerLead, classify, classifyLead,
          singletonTest, singletonLead, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]

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

theorem natRun_prefix_safe
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 32)))
    (count : Nat) (hc : count ≤ steps full.length candidate.val tool.val) :
    RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing count state) ∧
      Fits (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing count state).pc ∧
      (natRun (rawIncidenceROM q full) containing count state).halted = false := by
  refine ⟨?_, ?_, ?_⟩
  · rw [natRun_prefix_eq q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool count hc]
    exact path_prefix_registersFit q full start candidate tool state hfit hend hcandidate htool count hc
  · rw [natRun_prefix_pc q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool count hc]
    have hi := path_index_le full.length candidate.val tool.val count hc
    exact lt_of_le_of_lt (by omega) hend
  · rw [natRun_prefix_eq q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool count hc,
      runOps_halted, hactive]

theorem word_run_eq_nat
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 32)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ steps full.length candidate.val tool.val) :
    packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q)) =
      (natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 16 full.length q) := by
  apply natRun_toWord _ _ _ count hwords
  intro k hk
  have hs := natRun_prefix_safe q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool
    hfit hend k (by omega)
  exact ⟨hs.1, hs.2.1⟩

theorem word_prefix_safe
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 32)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (heapWords count : Nat) (hc : count < steps full.length candidate.val tool.val) :
    let after := packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q))
    after.halted = false ∧
      after.pc.toNat = 5 * (start + (pathIndices full.length candidate.val tool.val).getD count 32) ∧
      after.pc.toNat + 4 < (packingCode containing).length ∧
      PackingOp.decode (fetch containing after) =
        some ((pathOps start full.length candidate.val tool.val).getD count paddingOp) ∧
      packingAccessFits (rawIncidenceROM q full) heapWords after
        ((pathOps start full.length candidate.val tool.val).getD count paddingOp) := by
  have hs := natRun_prefix_safe q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool hfit hend count hc.le
  have hpcNat := natRun_prefix_pc q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool count hc.le
  have hword := word_run_eq_nat q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool hfit hend hwords count hc.le
  let index := (pathIndices full.length candidate.val tool.val).getD count 32
  have hi : index < 32 := path_index_lt _ _ _ _ hc
  dsimp only
  rw [hword]
  have hpcWord : ((natRun (rawIncidenceROM q full) containing count state).toWord
      (indexWidth 16 full.length q)).pc.toNat = 5 * (start + index) := by
    change (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs.2.1, hpcNat]
  refine ⟨hs.2.2, hpcWord, ?_, ?_, ?_⟩
  · rw [hpcWord, packingCode_length]
    omega
  · change PackingOp.decode (physicalFetch _ (packingCode containing)
      (BitVec.ofNat _ (natRun (rawIncidenceROM q full) containing count state).pc).toNat) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs.2.1, physicalFetch_eq _ _ _ hwords, hpcNat]
    change PackingOp.decode (natFetch containing (5 * (start + index))) = _
    rw [natFetch_body containing (start + index) (by omega), decode_encode]
    have hh := (hcode index hi).trans (path_op_matches start full.length candidate.val tool.val count hc)
    rw [List.getD_eq_getElem containing paddingOp (by omega)] at hh
    exact congrArg some hh
  · apply physical_access_of_nat _ heapWords _ _ hs.1
    rw [natRun_prefix_eq q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool count hc.le]
    exact path_prefix_accessFits q full start heapWords candidate tool state hcandidate htool count hc

theorem word_prefix_values
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 32)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ steps full.length candidate.val tool.val) :
    let after := packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q))
    (∀ register, (after.register register).toNat =
      (natRun (rawIncidenceROM q full) containing count state).register register) ∧
      after.pc.toNat = 5 * (start + (pathIndices full.length candidate.val tool.val).getD count 32) ∧ after.halted = false := by
  have hs := natRun_prefix_safe q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool hfit hend count hc
  dsimp only
  rw [word_run_eq_nat q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool hfit hend hwords count hc]
  refine ⟨fun register => toWord_register_toNat _ _ hs.1 register, ?_, hs.2.2⟩
  change (BitVec.ofNat _ _).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs.2.1, natRun_prefix_pc q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool count hc]

theorem word_prefix_frame
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 32)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ steps full.length candidate.val tool.val) :
    let before := state.toWord (indexWidth 16 full.length q)
    let after := packingRun (rawIncidenceROM q full) containing count before
    after.heap = before.heap ∧ after.register .old = before.register .old ∧ after.register .fresh = before.register .fresh := by
  have hf := path_prefix_frame q full start candidate.val tool.val state count hc
  dsimp only at hf ⊢
  rw [word_run_eq_nat q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool hfit hend hwords count hc,
    natRun_prefix_eq q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool count hc]
  exact ⟨congrArg (fun heap : Nat → Nat => fun address : BitVec (indexWidth 16 full.length q) =>
      BitVec.ofNat _ (heap address.toNat)) hf.1,
    congrArg (BitVec.ofNat _) hf.2.1, congrArg (BitVec.ofNat _) hf.2.2⟩

def WordReturnedActive (N q start : Nat) (before after : WordState (indexWidth 16 N q)) (answer : Nat) : Prop :=
  (after.register .value).toNat = answer ∧ after.register .old = before.register .old ∧
    after.register .fresh = before.register .fresh ∧ after.heap = before.heap ∧
    after.pc.toNat = 5 * (start + 32) ∧ after.halted = false

theorem query_word
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 32)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing)) :
    WordReturnedActive full.length q start (state.toWord (indexWidth 16 full.length q))
      (packingRun (rawIncidenceROM q full) containing (steps full.length candidate.val tool.val)
        (state.toWord (indexWidth 16 full.length q)))
      (bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))) := by
  have hn := RawCandidateIncidenceBlock.query q full containing start hbound (by
    intro position hp
    have hh := hcode position hp
    rw [List.getD_eq_getElem containing paddingOp (by omega),
      List.getD_eq_getElem _ paddingOp (by rw [RawCandidateIncidenceBlock.programAt_length]; exact hp)] at hh
    exact hh) candidate tool state hpc hactive hcandidate htool
  change RawCandidateIncidenceBlock.ReturnedActive start state
    (natRun (rawIncidenceROM q full) containing (steps full.length candidate.val tool.val) state) _ at hn
  have hbit : Fits (indexWidth 16 full.length q)
      (bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))) := by
    have hone : Fits (indexWidth 16 full.length q) 1 :=
      (show 1 ≤ full.length * q + full.length + q + 640 by omega).trans_lt (fits_checker_register_bound full.length q)
    cases decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅) <;> simp only [bit]
    · exact (show 0 ≤ 1 by omega).trans_lt hone
    · exact hone
  rw [word_run_eq_nat q full containing start hbound hcode candidate tool state hpc hactive hcandidate htool
    hfit hend hwords (steps full.length candidate.val tool.val) le_rfl]
  refine ⟨?_, congrArg (BitVec.ofNat _) hn.2.1, congrArg (BitVec.ofNat _) hn.2.2.1, ?_, ?_, hn.2.2.2.2.2⟩
  · change (BitVec.ofNat _ _).toNat = _
    rw [hn.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbit]
  · exact congrArg (fun heap : Nat → Nat => fun address : BitVec (indexWidth 16 full.length q) =>
      BitVec.ofNat _ (heap address.toNat)) hn.2.2.2.1
  · change (BitVec.ofNat _ _).toNat = _
    rw [hn.2.2.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hend]

end Linked

theorem append_slice (left right : List PackingOp) :
    left.length + 32 ≤ (left ++ programAt left.length ++ right).length ∧
      ∀ position < 32, (left ++ programAt left.length ++ right).getD (left.length + position) paddingOp =
        (programAt left.length).getD position paddingOp := by
  constructor
  · simp only [List.length_append, RawCandidateIncidenceBlock.programAt_length]
    omega
  · intro position hp
    rw [List.getD_append (left ++ programAt left.length) right paddingOp _ (by
        simp only [List.length_append, RawCandidateIncidenceBlock.programAt_length]
        omega),
      List.getD_append_right left (programAt left.length) paddingOp _ (by omega),
      Nat.add_sub_cancel_left]

theorem query_word_append (q : Nat) (full : List (Finset (Fin q))) (left right : List PackingOp)
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 5 * left.length) (hactive : state.halted = false)
    (hcandidate : state.register .old = candidate.val) (htool : state.register .fresh = tool.val)
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (left.length + 32)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode (left ++ programAt left.length ++ right))) :
    WordReturnedActive full.length q left.length (state.toWord (indexWidth 16 full.length q))
      (packingRun (rawIncidenceROM q full) (left ++ programAt left.length ++ right)
        (steps full.length candidate.val tool.val) (state.toWord (indexWidth 16 full.length q)))
      (bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))) :=
  query_word q full _ left.length (append_slice left right).1 (append_slice left right).2
    candidate tool state hpc hactive hcandidate htool hfit hend hwords

end PaperProofs.Structure.LaminarTree.RawCandidateIncidenceWord
