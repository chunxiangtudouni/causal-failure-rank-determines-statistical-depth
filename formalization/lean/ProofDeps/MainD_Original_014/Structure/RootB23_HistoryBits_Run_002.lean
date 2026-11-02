module

public import Structure.RootB23_HistoryBits_Codec_001

/-! The history below is the very same state history produced by the original
native transitions.  No bound on symbols, serials or arbitrary histories is an
additional assumption.  Seeds, accounting and reporting modes remain arbitrary. -/

@[expose] public section

namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23HistoryBits

open PSTRTMNativeEventBits220

variable {I : Instance}

theorem cubic_dominates (value : Nat) (positive : 1 ≤ value) :
    value ≤ value ^ 3 ∧ value ^ 2 ≤ value ^ 3 ∧ 1 ≤ value ^ 3 := by
  have square : value ≤ value * value := by nlinarith
  have cube : value * value ≤ value * value * value := by nlinarith
  constructor
  · simpa only [pow_succ, pow_zero, one_mul] using square.trans cube
  constructor
  · simpa only [pow_succ, pow_zero, one_mul] using cube
  · exact positive.trans (by simpa only [pow_succ, pow_zero, one_mul] using square.trans cube)

/-- Every original protocol prefix, including failed paths and all late reports. -/
theorem prefix_controllerInput_length_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : Nat} {state : State I}
    (actual : Prefix input C mode accounting policy seed truth tapes n state)
    (available : Finset I.Tool) (budget : Rat) :
    (controllerInput input C available budget state.history).length ≤
      128 * (inputSize input C budget + state.clock + 1) ^ 3 := by
  let room := inputSize input C budget + state.clock + 1
  have positive : 1 ≤ room := by unfold room; omega
  have raw := controllerInput_length_le_payload input C available budget state.history
  have count := PSTRTMNativeHistory204.prefix_history_length_le
    input C mode accounting policy seed truth tapes actual
  have fields := prefix_history_eventBits_le
    input C mode accounting policy seed truth tapes actual budget
  have stageBits := natBits_le_value_add_one I.stageCount
  have toolBits := natBits_le_value_add_one I.toolCount
  have clockBits := natBits_le_value_add_one state.clock
  have dimensions : (preparationInput input C budget).length + I.stageCount +
      I.toolCount + 1 = inputSize input C budget := rfl
  have stageRoom : I.stageCount + 1 ≤ room := by unfold room; omega
  have clockRoom : state.clock ≤ room := by unfold room; omega
  have eventsRoom : state.history.length ≤ room ^ 2 := by
    have product := Nat.mul_le_mul stageRoom clockRoom
    rw [pow_two]
    exact count.trans product
  have fieldRoom : 8 * ((preparationInput input C budget).length +
      natBits I.stageCount + natBits I.toolCount + natBits state.clock + 4) ≤ 48 * room := by
    unfold room
    omega
  have allFields : payloadBits (state.history.flatMap encodeEvent) ≤ 48 * room ^ 3 := by
    have multiplied := Nat.mul_le_mul eventsRoom fieldRoom
    have normalized : room ^ 2 * (48 * room) = 48 * room ^ 3 := by ring
    exact fields.trans (normalized ▸ multiplied)
  have staticRoom : 3 * (preparationInput input C budget).length +
      6 * I.toolCount ≤ 6 * room := by unfold room; omega
  obtain ⟨linear, square, one⟩ := cubic_dominates room positive
  change _ ≤ 128 * room ^ 3
  nlinarith

/-- The total interpreter freezes after halt.  Its current state is still an
original Prefix at an earlier clock, so the same bound covers halted clocks. -/
theorem run_controllerInput_length_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (legal : LegalRule input C mode accounting policy)
    (sample : Seed × input.World) (clock : Nat)
    (available : Finset I.Tool) (budget : Rat) :
    (controllerInput input C available budget
      (run input C mode accounting policy sample clock).history).length ≤
        128 * (inputSize input C budget + clock + 1) ^ 3 := by
  obtain ⟨steps, beforeClock, actual⟩ :=
    run_has_prefix input C mode accounting policy legal sample clock
  have bound := prefix_controllerInput_length_le input C mode accounting policy sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) actual available budget
  have realClock := prefix_clock input C mode accounting policy sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) actual
  rw [realClock] at bound
  exact bound.trans (Nat.mul_le_mul_left 128
    (Nat.pow_le_pow_left (by omega) 3))

end PaperProofs.Common.Native.RationalControllerComputation.RootB23HistoryBits
