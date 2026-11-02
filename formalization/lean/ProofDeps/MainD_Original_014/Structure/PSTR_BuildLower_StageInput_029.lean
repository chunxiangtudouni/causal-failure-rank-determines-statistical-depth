module

public import Structure.PSTR_BuildLower_NodePrep_021
public import Structure.PA06_A19Prepare_ROM_001

/-! Source given-input stage pointers have header size3; real raw input has
header size2. The fixed executed subtract-by-one is essential. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.StageInput
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM RawTreePreprocessingClaims
variable {bits : Nat}

def code (pointer : Register) : List PackingOp :=
  relativeRead (registerOffset pointer) .old ++
    [.base (.base (.constant .fresh 1)), .base (.subtract .index .old .fresh),
     .base (.base (.loadROM .input .value .index))]

theorem code_length (pointer : Register) : (code pointer).length = 6 := rfl

theorem code_straight (pointer : Register) : StraightProgram (code pointer) := by
  simp [code, relativeRead, StraightProgram, StraightOp]

theorem prefix_frame (rom : PhysicalROM) (pointer : Register) (state : WordState bits) (count : Nat) :
    (executeOps rom ((code pointer).take count) state).heap = state.heap ∧
      (executeOps rom ((code pointer).take count) state).register .address = state.register .address := by
  by_cases hc : count ≤ 6
  · interval_cases count <;>
      simp [code, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]
  · rw [List.take_of_length_le (by rw [code_length]; omega)]
    exact ⟨rfl, rfl⟩

theorem value (rom : PhysicalROM) (pointer : Register) (state : WordState bits) (payload : Nat)
    (hp : (Ordinary.pointerValue state pointer).toNat = 3 + payload) :
    (executeOps rom (code pointer) state).register .value =
      BitVec.ofNat bits ((rom.words .input).getD (2 + payload) 0) := by
  have hw := (Ordinary.pointerValue state pointer).isLt
  rw [hp] at hw
  have h1 : 1 < 2 ^ bits := by omega
  have hs : 2 + payload < 2 ^ bits := by omega
  have he : 3 + payload - 1 = 2 + payload := by omega
  unfold Ordinary.pointerValue at hp
  simp [code, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hs, he]

theorem original_stage_value (q : Nat) (full : List (Finset (Fin q))) (initialUsed : Finset (Fin q))
    (row : Fin full.length) (tool : Fin q) (pointer : Register) (state : WordState bits)
    (hp : (Ordinary.pointerValue state pointer).toNat = 3 + row.val * q + tool.val) :
    (executeOps (CompactControllerClaims.controllerInput q full initialUsed) (code pointer) state).register .value =
      BitVec.ofNat bits (bit (decide (tool ∈ full[row.val]))) := by
  rw [value _ pointer state (row.val * q + tool.val) (by simpa only [Nat.add_assoc] using hp)]
  have prefixROM : PA06A19PrepareROM001.ROMPrefix (rawIncidenceROM q full)
      (CompactControllerClaims.controllerInput q full initialUsed) :=
    PA06A19PrepareROM001.inputTail_prefix _ ((List.finRange q).map (fun tool => bit (decide (tool ∈ initialUsed))))
  have haddress : 2 + row.val * q + tool.val < ((rawIncidenceROM q full).words .input).length := by
    rw [raw_input_length]
    have hmul : (row.val + 1) * q ≤ full.length * q := Nat.mul_le_mul_right q row.isLt
    have htool := tool.isLt
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega
  have hr := prefixROM.read_eq .input (2 + row.val * q + tool.val) haddress
  change (CompactControllerClaims.controllerInput q full initialUsed).semantic.read .input _ = _ at hr
  rw [raw_bit q full row tool] at hr
  change BitVec.ofNat bits ((CompactControllerClaims.controllerInput q full initialUsed).semantic.read .input (2 + (row.val * q + tool.val))) = _
  rw [← Nat.add_assoc, hr]

theorem run (rom : PhysicalROM) (pointer : Register) (left right : List PackingOp)
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ code pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ code pointer ++ right).length)) :
    packingRun rom (left ++ code pointer ++ right) 6 state = executeOps rom (code pointer) state := by
  apply PSTRWordSegments.straight_segment rom _ _ left.length
    (by simp only [List.length_append, code_length]; omega)
    (PA17UniformGenerator035a.segment_index left (code pointer) right) (code_straight pointer)
    hcode hpcfit state hpc ha

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.StageInput

