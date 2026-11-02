module

public import Structure.PSTR_BuildLower_DispatchRun_019
public import Structure.PA06_A19Prepare_BankPacked021_Prefix

/-! Concrete actual double-cutoff heap ports. The packed branch is the frozen
A06 read21/write72 backend, not a code parameter or supplied scalar answer.
Old logical C0 and new physical packed capacity C remain distinct. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteHeap
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM
open CompactControllerClaims (dataHeap)
variable {bits : Nat}

def read (start : Nat) (pointer : Register) : List PackingOp :=
  readDispatcher PA06A19PrepareBankPacked021.read start pointer

def write (start : Nat) (pointer : Register) : List PackingOp :=
  writeDispatcher (PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)) start pointer

theorem read_length (start : Nat) (pointer : Register) : (read start pointer).length = 45 := by
  rw [read, readDispatcher_length, PA06A19PrepareBankPacked021.read_length]

theorem write_length (start : Nat) (pointer : Register) : (write start pointer).length = 96 := by
  rw [write, writeDispatcher_length, PA06A19PrepareBankPacked021.safeWrite_length]

/-- The actual two-cutoff view: logical C0 is bank3, while C is the NEW
physical packing capacity. Ordinary targets use the actual bank6 indexBase. -/
def readView (q C : Nat) (state : WordState bits) (pointer : Register) : Nat :=
  if (Ordinary.pointerValue state pointer).toNat <
      (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat then
    unpackHeap q C bits (dataHeap state.heap) (Ordinary.pointerValue state pointer).toNat
  else (state.heap (Ordinary.targetAddress state pointer)).toNat

private theorem classifier_heap (rom : PhysicalROM) (pointer : Register) (pc : Nat) (state : WordState bits) :
    (executeOps rom (memoryClassify pointer pc) state).heap = state.heap := by
  have hh := (memoryClassify_prefix_frame rom pointer pc state (memoryClassify pointer pc).length).1
  simpa only [List.take_length] using hh

private theorem classifier_base (rom : PhysicalROM) (pointer : Register) (pc : Nat) (state : WordState bits) :
    (executeOps rom (memoryClassify pointer pc) state).register .address = state.register .address := by
  have hh := (memoryClassify_prefix_frame rom pointer pc state (memoryClassify pointer pc).length).2
  simpa only [List.take_length] using hh

private theorem classifier_pointer (rom : PhysicalROM) (pointer : Register) (pc : Nat) (state : WordState bits) :
    Ordinary.pointerValue (executeOps rom (memoryClassify pointer pc) state) pointer = Ordinary.pointerValue state pointer := by
  simp only [Ordinary.pointerValue, classifier_heap, classifier_base]

private theorem classifier_target (rom : PhysicalROM) (pointer : Register) (pc : Nat) (state : WordState bits) :
    Ordinary.targetAddress (executeOps rom (memoryClassify pointer pc) state) pointer = Ordinary.targetAddress state pointer := by
  simp only [Ordinary.targetAddress, classifier_heap, classifier_base, classifier_pointer]

theorem read_result_value (q C : Nat) (rom : PhysicalROM) (left : List PackingOp)
    (pointer : Register) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits)
    (hcapacity : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤ C)
    (hscale : (Ordinary.pointerValue state pointer).toNat <
        (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat →
      Fits bits ((Ordinary.pointerValue state pointer).toNat * CapacityBits.width q)) :
    ((DispatchRun.result rom left PA06A19PrepareBankPacked021.read (Ordinary.read pointer) pointer state).register .value).toNat =
      readView q C state pointer := by
  let tested := executeOps rom (memoryClassify pointer
    (5 * (left.length + 9 + PA06A19PrepareBankPacked021.read.length + 3))) state
  have htHeap : tested.heap = state.heap := classifier_heap rom pointer _ state
  have htOld : tested.register .old = Ordinary.pointerValue state pointer := memoryClassify_old rom pointer _ state
  by_cases hg : DispatchRun.ordinaryCase pointer state
  · have hng : ¬(Ordinary.pointerValue state pointer).toNat <
        (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat := Nat.not_lt.mpr hg
    simp only [DispatchRun.result, hg, ite_true, readView, hng, ite_false]
    rw [Ordinary.read_value, classifier_heap, classifier_target]
  · have hlt : (Ordinary.pointerValue state pointer).toNat <
        (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat := Nat.lt_of_not_ge hg
    have hd := PA06A19PrepareBankPacked021.read_decodes q C rom tested (by rwa [htHeap]) hb hw
      (by rw [htOld]; exact hscale hlt) (by rw [htOld]; exact hlt.trans_le hcapacity)
    rw [htHeap, htOld] at hd
    simp only [DispatchRun.result, hg, ite_false, readView, hlt, ite_true]
    change ((executeOps rom PA06A19PrepareBankPacked021.read tested).register .value).toNat = _
    exact hd

theorem read_call_value (q C : Nat) (rom : PhysicalROM) (left right : List PackingOp)
    (pointer : Register) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits)
    (hcapacity : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤ C)
    (hscale : (Ordinary.pointerValue state pointer).toNat <
        (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat →
      Fits bits ((Ordinary.pointerValue state pointer).toNat * CapacityBits.width q))
    (hcode : WordsFit bits (packingCode (left ++ read left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ read left.length pointer ++ right).length))
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false) :
    let count := DispatchRun.steps PA06A19PrepareBankPacked021.read (Ordinary.read pointer) pointer state
    count ≤ 45 ∧ ((packingRun rom (left ++ read left.length pointer ++ right) count state).register .value).toNat =
      readView q C state pointer := by
  have hc : DispatchRun.code PA06A19PrepareBankPacked021.read (Ordinary.read pointer) left.length pointer =
      read left.length pointer := DispatchRun.code_read _ _ _
  have hrun := DispatchRun.run rom left PA06A19PrepareBankPacked021.read (Ordinary.read pointer) right pointer
    PA06A19PrepareBankPacked021.read_straight (Ordinary.read_straight pointer)
    (by rwa [hc]) (by rwa [hc]) state hpc ha
  dsimp only
  constructor
  · have ht := DispatchRun.steps_le_code PA06A19PrepareBankPacked021.read (Ordinary.read pointer) left.length pointer state
    rwa [hc, read_length] at ht
  · rw [hc] at hrun
    rw [hrun]
    exact read_result_value q C rom left pointer state hh hb hw hcapacity hscale

theorem write_call (rom : PhysicalROM) (left right : List PackingOp) (pointer : Register) (state : WordState bits)
    (hcode : WordsFit bits (packingCode (left ++ write left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ write left.length pointer ++ right).length))
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false) :
    let packed := PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)
    let count := DispatchRun.steps packed (Ordinary.write pointer) pointer state
    count ≤ 96 ∧ packingRun rom (left ++ write left.length pointer ++ right) count state =
      DispatchRun.result rom left packed (Ordinary.write pointer) pointer state := by
  have hc : DispatchRun.code (PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer))
      (Ordinary.write pointer) left.length pointer = write left.length pointer := DispatchRun.code_write _ _ _
  dsimp only
  constructor
  · have ht := DispatchRun.steps_le_code (PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer))
      (Ordinary.write pointer) left.length pointer state
    rwa [hc, write_length] at ht
  · rw [← hc]
    exact DispatchRun.run rom left _ _ right pointer (PA06A19PrepareBankPacked021.safeWrite_straight _)
      (Ordinary.write_straight pointer) (by rwa [hc]) (by rwa [hc]) state hpc ha

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteHeap
