module

public import Structure.PSTR_BuildLower_ViewFrame_047
public import Structure.PSTR_BuildLower_SourceFacts_046

/-! A data-only simulation relation for the finite original source heap and
its seven actual VM words. Literal ALU lowering preserves this relation along
the fetched execution, and its every clock preserves the source heap view. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
variable {bits : Nat}

structure Represents (q C0 C indexBase I base : Nat) (logical : State) (physical : WordState bits) : Prop where
  address : physical.register .address = BitVec.ofNat bits base
  registers : portRegisters (BitVec.ofNat bits base) physical.heap = fun reg => BitVec.ofNat bits (logical.register reg)
  heap : ∀ a < C0 + I, PA06A19PreparePackedView013.view q C0 C indexBase physical.heap a = logical.heap a

theorem straight_prefix (rom : PhysicalROM) (left block right : List PackingOp)
    (state : WordState bits) (hs : StraightProgram block)
    (hcode : WordsFit bits (packingCode (left ++ block ++ right)))
    (hpcfit : Fits bits (5 * (left ++ block ++ right).length))
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ block.length) :
    packingRun rom (left ++ block ++ right) count state = executeOps rom (block.take count) state := by
  have hl : (block.take count).length = count := List.length_take_of_le hc
  conv_lhs => rw [← hl]
  apply PSTRWordSegments.straight_segment rom _ _ left.length
    (by simp only [List.length_append, hl]; omega) ?_ ?_ hcode hpcfit state hpc ha
  · intro i hi
    have hh := PA17UniformGenerator035a.segment_index left block right i (by rw [hl] at hi; omega)
    simpa only [List.getElem_take] using hh
  · intro op hm
    exact hs op (List.mem_of_mem_take hm)

theorem value_range (op : ValueOp) (rom : PhysicalROM) :
    BankRangeFrame (bits := bits) rom op.relativeLower 32 39 := by
  refine ⟨relativeValue_base_prefix op rom, ?_⟩
  intro state point outside count
  exact relativeValue_prefix_frame op rom state point
    (outside (registerOffset op.target) (registerSlot_bounds op.target).1 (registerSlot_bounds op.target).2) count

theorem value_word_exact (op : ValueOp) (rom : PhysicalROM) (logical : State)
    (hf : ∀ reg, Fits bits (logical.register reg)) :
    Function.update (fun reg => BitVec.ofNat bits (logical.register reg)) op.target
      (op.value (fun reg => BitVec.ofNat bits (logical.register reg))) =
        fun reg => BitVec.ofNat bits ((op.original.execute rom.semantic logical).register reg) := by
  have hh := congrArg WordState.register (PA17WordExecution021.op_toWord bits rom op.original logical hf)
  simpa only [valueOp_original_registers, wordState] using hh

theorem literal_alu (q C0 C indexBase I base : Nat) (source physical : PhysicalROM)
    (op : ValueOp) (logical : State) (state : WordState bits)
    (hrep : Represents q C0 C indexBase I base logical state)
    (hf : ∀ reg, Fits bits (logical.register reg))
    (hbits : 6 ≤ bits) (hend : Fits bits (base + 39))
    (hC : C0 ≤ C) (hpacked : 4 + packedCapacityWords q C bits ≤ indexBase)
    (hdisjoint : indexBase + I ≤ base + 32)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ op.relativeLower ++ right)))
    (hpcfit : Fits bits (5 * (left ++ op.relativeLower ++ right).length)) :
    let after := packingRun physical (left ++ op.relativeLower ++ right) op.relativeLower.length state
    op.relativeLower.length ≤ 13 ∧
      Represents q C0 C indexBase I base (op.original.execute source.semantic logical) after ∧
      after.pc = BitVec.ofNat bits (5 * (left.length + op.relativeLower.length)) ∧ after.halted = false := by
  dsimp only
  rcases ValueStep.call op physical left right state hbits hpc ha hcode hpcfit with
    ⟨hlen, hvm, hpcAfter, hactive, hbaseAfter, _⟩
  refine ⟨hlen, ⟨hbaseAfter.trans hrep.address, ?_, ?_⟩, hpcAfter, hactive⟩
  · have he : portRegisters (BitVec.ofNat bits base)
        (packingRun physical (left ++ op.relativeLower ++ right) op.relativeLower.length state).heap =
        Function.update (portRegisters (BitVec.ofNat bits base) state.heap) op.target
          (op.value (portRegisters (BitVec.ofNat bits base) state.heap)) := by
      simpa only [valueOp_original_registers, hrep.address] using hvm
    rw [he, hrep.registers]
    exact value_word_exact op source logical hf
  · intro a had
    have hs : (op.original.execute source.semantic logical).heap = logical.heap := by cases op <;> rfl
    rw [hs, ValueStep.run op physical left right state hpc ha hcode hpcfit]
    have hh := ViewFrame.bankRange_view physical op.relativeLower 32 39 (value_range op physical) (by decide)
      q C0 C indexBase I base state hrep.address hend (by omega) hC hpacked hdisjoint op.relativeLower.length a had
    rw [List.take_length] at hh
    exact hh.trans (hrep.heap a had)

theorem literal_alu_prefix_heap (q C0 C indexBase I base : Nat) (physical : PhysicalROM)
    (op : ValueOp) (state : WordState bits) (hbase : state.register .address = BitVec.ofNat bits base)
    (hbits : 0 < bits) (hend : Fits bits (base + 39))
    (hC : C0 ≤ C) (hpacked : 4 + packedCapacityWords q C bits ≤ indexBase)
    (hdisjoint : indexBase + I ≤ base + 32)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ op.relativeLower ++ right)))
    (hpcfit : Fits bits (5 * (left ++ op.relativeLower ++ right).length))
    (count : Nat) (hc : count ≤ op.relativeLower.length) (a : Nat) (had : a < C0 + I) :
    PA06A19PreparePackedView013.view q C0 C indexBase
      (packingRun physical (left ++ op.relativeLower ++ right) count state).heap a =
      PA06A19PreparePackedView013.view q C0 C indexBase state.heap a := by
  rw [straight_prefix physical left op.relativeLower right state (relativeValue_straight op) hcode hpcfit hpc ha count hc]
  exact ViewFrame.bankRange_view physical op.relativeLower 32 39 (value_range op physical) (by decide)
    q C0 C indexBase I base state hbase hend hbits hC hpacked hdisjoint count a had

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
