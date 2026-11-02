module

public import Structure.PSTR_UniformQueryCode_113
public import Structure.PSTR_ReplySpill_022

/-! Actual18-op live dispatcher after the shared query exit. q0 skips all
positive updates; the command is genuinely reloaded from the original ROM.
Only address/total/flag are written, preserving the four OLD reply words. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace PaperProofs.Structure.LaminarTree.PSTRLiveDispatch

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRWordSegments PSTRCountKernel PSTRReplySpill

def zeroLead (done : Nat) : List PackingOp :=
  [.base (.base (.constant .total 1)),
   .base (.base (.loadROM .input .flag .total)),
   .base (.base (.constant .total (5 * done)))]

def zeroBlock (done : Nat) : List PackingOp := zeroLead done ++ [.jumpIfZero .flag .total]

def commandLead (done : Nat) : List PackingOp :=
  [.base (.base (.constant .total 0)),
   .base (.base (.loadROM .input .address .total)),
   .arithmetic .multiply .address .address .flag,
   .base (.base (.constant .total 2)),
   .base (.base (.add .address .address .total)),
   .base (.base (.loadROM .input .flag .address)),
   .base (.base (.constant .total (5 * done)))]

def commandBlock (done : Nat) : List PackingOp := commandLead done ++ [.jumpIfZero .flag .total]

def correctLead (correct : Nat) : List PackingOp :=
  [.base (.base (.constant .total 1)),
   .base (.subtract .flag .flag .total),
   .base (.base (.constant .total (5 * correct)))]

def correctBlock (correct : Nat) : List PackingOp := correctLead correct ++ [.jumpIfZero .flag .total]

def errorLead (failed : Nat) : List PackingOp := [.base (.base (.constant .total (5 * failed)))]

def errorBlock (failed : Nat) : List PackingOp := errorLead failed ++ [.jumpIfZero .index .total]

def program (correct failed done : Nat) : List PackingOp :=
  ((zeroBlock done ++ commandBlock done) ++ correctBlock correct) ++ errorBlock failed

theorem zeroLead_length (done : Nat) : (zeroLead done).length = 3 := rfl
theorem zeroBlock_length (done : Nat) : (zeroBlock done).length = 4 := rfl
theorem commandLead_length (done : Nat) : (commandLead done).length = 7 := rfl
theorem commandBlock_length (done : Nat) : (commandBlock done).length = 8 := rfl
theorem correctLead_length (correct : Nat) : (correctLead correct).length = 3 := rfl
theorem correctBlock_length (correct : Nat) : (correctBlock correct).length = 4 := rfl
theorem errorLead_length (failed : Nat) : (errorLead failed).length = 1 := rfl
theorem errorBlock_length (failed : Nat) : (errorBlock failed).length = 2 := rfl
theorem program_length (correct failed done : Nat) : (program correct failed done).length = 18 := rfl

theorem block_trans (whole container block : List PackingOp) (origin offset : Nat)
    (outer : PSTROuterCountCode.BlockAt whole origin container)
    (inner : PSTROuterCountCode.BlockAt container offset block) :
    PSTROuterCountCode.BlockAt whole (origin + offset) block := by
  refine ⟨by have ho := outer.bound; have hi := inner.bound; omega, ?_⟩
  intro index hi
  have hn : offset + index < container.length := by have h := inner.bound; omega
  simpa only [Nat.add_assoc] using (outer.code (offset + index) hn).trans (inner.code index hi)

private theorem own_block (correct failed done : Nat) (before block after : List PackingOp) (origin : Nat)
    (heq : program correct failed done = before ++ block ++ after) (hlen : before.length = origin) :
    PSTROuterCountCode.BlockAt (program correct failed done) origin block := by
  have bound : origin + block.length ≤ (program correct failed done).length := by
    rw [heq, List.length_append, List.length_append, hlen]
    omega
  refine ⟨bound, ?_⟩
  intro index hi
  have hg := congrArg (fun ops : List PackingOp => ops.getD (origin + index) (.base (.base (.constant .value 0)))) heq
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by simp only [List.length_append, hlen]; omega)] at hg
  exact hg.trans (by simpa only [hlen] using PSTROuterCountCode.middle_get before block after index hi)

theorem zero_slice (correct failed done : Nat) :
    PSTROuterCountCode.BlockAt (program correct failed done) 0 (zeroBlock done) := by
  apply own_block correct failed done [] (zeroBlock done) (commandBlock done ++ correctBlock correct ++ errorBlock failed) 0
  · simp only [program, List.nil_append, List.append_assoc]
  · rfl

theorem command_slice (correct failed done : Nat) :
    PSTROuterCountCode.BlockAt (program correct failed done) 4 (commandBlock done) := by
  apply own_block correct failed done (zeroBlock done) (commandBlock done) (correctBlock correct ++ errorBlock failed) 4
  · simp only [program, List.append_assoc]
  · exact zeroBlock_length done

theorem correct_slice (correct failed done : Nat) :
    PSTROuterCountCode.BlockAt (program correct failed done) 12 (correctBlock correct) := by
  apply own_block correct failed done (zeroBlock done ++ commandBlock done) (correctBlock correct) (errorBlock failed) 12
  · rfl
  · rw [List.length_append, zeroBlock_length, commandBlock_length]

theorem error_slice (correct failed done : Nat) :
    PSTROuterCountCode.BlockAt (program correct failed done) 16 (errorBlock failed) := by
  apply own_block correct failed done ((zeroBlock done ++ commandBlock done) ++ correctBlock correct) (errorBlock failed) [] 16
  · simp only [program, List.append_nil]
  · rw [List.length_append, List.length_append, zeroBlock_length, commandBlock_length, correctBlock_length]

theorem zeroLead_straight (done : Nat) : StraightProgram (zeroLead done) := by
  simp [zeroLead, StraightProgram, StraightOp]
theorem commandLead_straight (done : Nat) : StraightProgram (commandLead done) := by
  simp [commandLead, StraightProgram, StraightOp]
theorem correctLead_straight (correct : Nat) : StraightProgram (correctLead correct) := by
  simp [correctLead, StraightProgram, StraightOp]
theorem errorLead_straight (failed : Nat) : StraightProgram (errorLead failed) := by
  simp [errorLead, StraightProgram, StraightOp]

theorem program_readOnly (correct failed done : Nat) : ∀ op ∈ program correct failed done, ReadOnly op := by
  simp [program, zeroBlock, zeroLead, commandBlock, commandLead, correctBlock, correctLead, errorBlock, errorLead, ReadOnly]

theorem prefix_heap {bits : Nat} (rom : PhysicalROM) (correct failed done count : Nat) (state : WordState bits) :
    (executeOps rom ((program correct failed done).take count) state).heap = state.heap :=
  readOnly_prefix_heap rom _ state (program_readOnly correct failed done) count

theorem prefix_reply {bits : Nat} (rom : PhysicalROM) (correct failed done count : Nat)
    (state : WordState bits) (hc : count ≤ 18) :
    ReplyRegisters state (executeOps rom ((program correct failed done).take count) state) := by
  interval_cases count <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem code_fit {bits : Nat} (correct failed done : Nat) (hb : 8 ≤ bits)
    (hc : Fits bits (5 * correct)) (hf : Fits bits (5 * failed)) (hd : Fits bits (5 * done)) :
    WordsFit bits (packingCode (program correct failed done)) := by
  have hp : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  intro value hv
  simp [packingCode, program, zeroBlock, zeroLead, commandBlock, commandLead,
    correctBlock, correctLead, errorBlock, errorLead, PackingOp.encode, Op.encodeWords,
    Instruction.encodeWords, PackingPrimitive.word, Register.word, Region.word, haltWords] at hv
  unfold Fits at hc hf hd ⊢
  omega

theorem branch_run {bits : Nat} (rom : PhysicalROM) (whole lead : List PackingOp)
    (start : Nat) (test target : Register)
    (block : PSTROuterCountCode.BlockAt whole start (lead ++ [.jumpIfZero test target]))
    (straight : StraightProgram lead) (hw : WordsFit bits (packingCode whole))
    (hpc : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole (lead.length + 1) state = executeOps rom (lead ++ [.jumpIfZero test target]) state := by
  rw [segment_last rom whole lead (.jumpIfZero test target) start ?_ ?_ ?_ straight hw hpc state hp ha]
  · rw [executeOps_append]
    rfl
  · have h := block.bound
    simpa only [List.length_append, List.length_singleton, Nat.add_assoc] using h
  · intro index hi
    exact (block.code index (by simp only [List.length_append, List.length_singleton]; omega)).trans
      (List.getElem_append_left hi)
  · have h := block.code lead.length (by simp only [List.length_append, List.length_singleton]; omega)
    exact h.trans (by
      simp)

end PaperProofs.Structure.LaminarTree.PSTRLiveDispatch
