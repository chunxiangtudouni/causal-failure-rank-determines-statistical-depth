module

public import Structure.PSTR_BuildLower_StageInput_029
public import Structure.PSTR_BuildLower_LoadResources_101
public import Structure.PSTR_BuildLower_InlineAccess_120

/-! The true stage-input getter executes the source3/raw2 header adjustment.
Its actual six prefixes are readonly and every actual access is allocated;
the raw-input prefix length is derived from the genuine supplied incidence. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.StageResources
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open RawTreePreprocessingClaims PA17PackedTranslator034

section Generic
variable {bits : Nat}

theorem local_safe (physical : PhysicalROM) (pointer : Register) (heapWords : Nat) (state : WordState bits)
    (oneFit : Fits bits 1)
    (pointerRoom : (state.register .address + BitVec.ofNat bits (registerOffset pointer)).toNat < heapWords)
    (inputRoom : (Ordinary.pointerValue state pointer).toNat - 1 < (physical.words .input).length) :
    PackedAccessSafe heapWords physical (StageInput.code pointer) state := by
  have differenceFit : (Ordinary.pointerValue state pointer).toNat - 1 < 2 ^ bits :=
    (Nat.sub_le _ _).trans_lt (Ordinary.pointerValue state pointer).isLt
  simp [BitVec.toNat_add] at pointerRoom
  unfold Ordinary.pointerValue at differenceFit inputRoom
  intro clock hc
  change clock < 6 at hc
  interval_cases clock <;>
    simp [StageInput.code, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt oneFit,
      Nat.mod_eq_of_lt differenceFit]
  all_goals first | exact pointerRoom | exact inputRoom

end Generic

theorem actual_resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (used : Finset (Fin q))
    (row : Fin full.length) (tool : Fin q) (pointer : Register) (state : WordState (bits q full))
    (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hp : (Ordinary.pointerValue state pointer).toNat = 3 + row.val * q + tool.val)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ StageInput.code pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ StageInput.code pointer ++ right).length)) :
    ResourceTrace.Keeps q full (CompactControllerClaims.controllerInput q full used)
        (left ++ StageInput.code pointer ++ right) state 6 ∧
      TraceAccess.Safe (allocated q full) (CompactControllerClaims.controllerInput q full used)
        (left ++ StageInput.code pointer ++ right) state 6 := by
  let physical := CompactControllerClaims.controllerInput q full used
  have prefixROM : PA06A19PrepareROM001.ROMPrefix (rawIncidenceROM q full) physical :=
    PA06A19PrepareROM001.inputTail_prefix _ ((List.finRange q).map (fun tool => bit (decide (tool ∈ used))))
  have rawRoom : 2 + row.val * q + tool.val < ((rawIncidenceROM q full).words .input).length := by
    rw [RawIncidenceLaminarRAM.raw_input_length]
    have hm : (row.val + 1) * q ≤ full.length * q := Nat.mul_le_mul_right q row.isLt
    rw [Nat.add_mul, Nat.one_mul] at hm
    have ht := tool.isLt
    omega
  have inputRoom : (Ordinary.pointerValue state pointer).toNat - 1 < (physical.words .input).length := by
    rw [hp]
    have hh := rawRoom.trans_le (prefixROM.length_le .input)
    omega
  have oneFit : Fits (bits q full) 1 :=
    lt_of_lt_of_le (by decide : 1 < 2 ^ 32) (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (bits_room q full))
  have primitive := local_safe physical pointer (allocated q full) state oneFit
    (BankAccess.point_room q full hq state base (registerOffset pointer)
      (by have hh := registerSlot_bounds pointer; change 32 ≤ registerOffset pointer ∧ registerOffset pointer < 39 at hh; omega)) inputRoom
  constructor
  · apply ResourceTrace.of_readonly q full physical _ state 6 bounded
    intro clock hc
    rw [SourceRep.straight_prefix physical left _ right state (StageInput.code_straight pointer) hcode hpcfit hpc ha clock
      (by simpa only [StageInput.code_length] using hc)]
    exact (StageInput.prefix_frame physical pointer state clock).1
  · have result := TraceAccess.straight physical left (StageInput.code pointer) right (allocated q full) state
      (StageInput.code_straight pointer) primitive hpc ha hcode hpcfit
    simpa only [StageInput.code_length] using result

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.StageResources
