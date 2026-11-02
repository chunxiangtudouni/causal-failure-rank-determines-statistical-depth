module

public import Structure.PSTR_BuildLower_SourceRep_048

/-! The real common suffix of source ROM/heap loads: the obtained hardware
value is actually stored in the target VM word. It preserves the finite source
heap view at every fetched clock; no free virtual-register update is used. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
variable {bits : Nat}

def loaded (logical : State) (target : Register) (value : Nat) : State :=
  {logical with register := Function.update logical.register target value, pc := logical.pc + 5}

theorem finish_load (q C0 C indexBase I base : Nat) (physical : PhysicalROM)
    (target : Register) (value : Nat) (logical : State) (state : WordState bits)
    (hrep : Represents q C0 C indexBase I base logical state)
    (hvalue : state.register .value = BitVec.ofNat bits value)
    (hbits : 6 ≤ bits) (hend : Fits bits (base + 39))
    (hC : C0 ≤ C) (hpacked : 4 + packedCapacityWords q C bits ≤ indexBase)
    (hdisjoint : indexBase + I ≤ base + 32)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ relativeWrite (registerOffset target) ++ right)))
    (hpcfit : Fits bits (5 * (left ++ relativeWrite (registerOffset target) ++ right).length)) :
    let after := packingRun physical (left ++ relativeWrite (registerOffset target) ++ right) 3 state
    Represents q C0 C indexBase I base (loaded logical target value) after ∧
      after.pc = BitVec.ofNat bits (5 * (left.length + 3)) ∧ after.halted = false := by
  dsimp only
  have hr : packingRun physical (left ++ relativeWrite (registerOffset target) ++ right) 3 state =
      executeOps physical (relativeWrite (registerOffset target)) state := by
    have hh := straight_prefix physical left (relativeWrite (registerOffset target)) right state
      (relativeWrite_straight _) hcode hpcfit hpc ha 3 (by rw [relativeWrite_length])
    rw [List.take_of_length_le (by rw [relativeWrite_length])] at hh
    exact hh
  have hf := ViewFrame.relativeWrite_range (bits := bits) physical (registerOffset target) 32 39
    (registerSlot_bounds target).1 (registerSlot_bounds target).2
  have haddr : (executeOps physical (relativeWrite (registerOffset target)) state).register .address =
      state.register .address := by
    simpa only [List.take_length] using hf.1 state (relativeWrite (registerOffset target)).length
  rw [hr]
  refine ⟨⟨haddr.trans hrep.address, ?_, ?_⟩, ?_, ?_⟩
  · rw [relativeWrite_heap, hrep.address, portRegisters_update _ (ValueStep.bank_injective _ hbits), hrep.registers, hvalue]
    funext reg
    by_cases he : reg = target
    · subst reg
      simp only [loaded, Function.update_self]
    · simp only [loaded, Function.update_of_ne he]
  · intro a had
    have hh := ViewFrame.bankRange_view physical (relativeWrite (registerOffset target)) 32 39 hf (by decide)
      q C0 C indexBase I base state hrep.address hend (by omega) hC hpacked hdisjoint
      (relativeWrite (registerOffset target)).length a had
    rw [List.take_length] at hh
    exact hh.trans (hrep.heap a had)
  · rw [executeOps_pc physical _ state (relativeWrite_straight _), hpc, relativeWrite_length, BitVec.ofNat_add_ofNat]
    congr 1
  · rw [executeOps_halted, ha]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
