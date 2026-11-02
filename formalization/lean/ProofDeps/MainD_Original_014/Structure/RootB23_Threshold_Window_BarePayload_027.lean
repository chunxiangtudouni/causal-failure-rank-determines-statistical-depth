module

public import Structure.RootB23_Threshold_Window_PayloadActual_026

/-! One fixed bare-input machine preserves the real Bookmark memory port
through allocation and all four remote copies. Its result is exactly the
owned-zero/four-original-field interface of the final serializer. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.BarePayload
open Turing PSTRTMSeq005 PA17TMDivisionCompose006 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticBookmark014
open PA17TMRatArithmeticWidth018 (BoundedRun)

def baseCap (k : Nat) : Nat := totalStates 32 (BareReserve.rowCap k)
attribute [local implicit_reducible] baseCap
def rowCap (k : Nat) : Nat := baseCap k + 5160
theorem base_le (k : Nat) : baseCap k ≤ rowCap k := by unfold rowCap; omega
theorem payload_le (k : Nat) : 5160 ≤ rowCap k := by unfold rowCap; omega

def rows (k : Nat) (phase : Fin 33) : Machine (rowCap k) :=
  if phase.val = 0 then padMachine (base_le k) (BareReserve.machine k)
  else padMachine (payload_le k) (PayloadFour.machine (phase.val - 1))

def ports (k : Nat) (phase : Fin 33) (localLabel : Fin (rowCap k + 1)) :
    Option (Fin 33 × Fin (rowCap k + 1)) :=
  if phase.val = 0 then
    if bounded : localLabel.val < baseCap k + 1 then
      let prior := phaseOf (p := 32) (s := BareReserve.rowCap k) ⟨localLabel.val, bounded⟩
      if prior.val = 0 then none else some (prior, 0)
    else none
  else none

def machine (k : Nat) : Machine (totalStates 32 (rowCap k)) := blockMachine (rows k) (ports k)

theorem rows_start (k : Nat) : rows k 0 = padMachine (base_le k) (BareReserve.machine k) := by
  simp only [rows, Fin.val_zero, ite_true]

theorem rows_memory (k : Nat) (memory : Fin 32) :
    rows k (BareReserve.memoryPhase memory) = padMachine (payload_le k) (PayloadFour.machine memory.val) := by
  have positive : (BareReserve.memoryPhase memory).val ≠ 0 := by change memory.val + 1 ≠ 0; omega
  have which : (BareReserve.memoryPhase memory).val - 1 = memory.val := by change memory.val + 1 - 1 = memory.val; omega
  simp only [rows, positive, ite_false, which]

theorem ports_memory (k : Nat) (memory : Fin 32) (localLabel : Fin (rowCap k + 1)) :
    ports k (BareReserve.memoryPhase memory) localLabel = none := by
  have positive : (BareReserve.memoryPhase memory).val ≠ 0 := by change memory.val + 1 ≠ 0; omega
  simp only [ports, positive, ite_false]

theorem ports_observed (k : Nat) (memory : Fin 32) (q : Fin (baseCap k + 1))
    (observed : phaseOf (p := 32) (s := BareReserve.rowCap k) q = BareReserve.memoryPhase memory) :
    ports k 0 (padLabel (base_le k) q) = some (BareReserve.memoryPhase memory, 0) := by
  have positive : (BareReserve.memoryPhase memory).val ≠ 0 := by change memory.val + 1 ≠ 0; omega
  dsimp only [ports, padLabel]
  simp only [Fin.val_zero, ite_true, dite_eq_left q.isLt]
  change (if (phaseOf (p := 32) (s := BareReserve.rowCap k) q).val = 0 then none
    else some (phaseOf (p := 32) (s := BareReserve.rowCap k) q, 0)) = _
  rw [observed]
  simp only [positive, ite_false]

def final (k : Nat) (base : List Bool) (x y : Rat) : MachineState (totalStates 32 (rowCap k)) :=
  blockCfg (BareReserve.memoryPhase (mNx x y))
    (padCfg (payload_le k)
      ⟨5160, Tape.mk₂ (List.replicate (k * fieldWidth x y ^ 4 + 4) false ++ PayloadActual.archive base x y)
        (PayloadActual.fields x y)⟩)

def coefficient (k : Nat) : Nat := 16 * k + 2048 + 8192 * (k + 3) ^ 2

/-- Actual canonical bare pair, arbitrary original WEST archive, no room,
bit tuple, width, source-state or inner-run hypothesis. Original bits are
read by one fixed table and restored by its actual selected memory row. -/
theorem bare_payload_actual (k : Nat) (base : List Bool) (x y : Rat) :
    ∃ trace, RunsFrom (machine k)
      ⟨0, Tape.mk₂ base (encodeDatum (.rational x) ++ encodeDatum (.rational y))⟩ trace (final k base x y) ∧
      trace.length ≤ coefficient k * (fieldWidth x y + 1) ^ 8 ∧
      ∀ inputLength clock, visitedSpace (machine k) inputLength (trace.take clock) ≤
        inputLength + 2 * (coefficient k * (fieldWidth x y + 1) ^ 8) + 1 := by
  obtain ⟨before, beforeRun, beforeTime, _⟩ := BareReserve.bare_reserve_actual k base x y
  obtain ⟨after, afterRun, afterTime⟩ := PayloadActual.actual_bounded k base x y
  let initialTape := Tape.mk₂ base (encodeDatum (.rational x) ++ encodeDatum (.rational y))
  let middleTape := (BareReserve.final k base x y).Tape
  let endTape := Tape.mk₂ (List.replicate (k * fieldWidth x y ^ 4 + 4) false ++ PayloadActual.archive base x y)
    (PayloadActual.fields x y)
  have afterRun' : RunsFrom (PayloadFour.machine (mNx x y).val)
      ⟨0, middleTape⟩ after ⟨5160, endTape⟩ := by
    simpa only [middleTape, BareReserve.final_tape, endTape] using afterRun
  have paddedBefore := pad_runsFrom (base_le k) (BareReserve.machine k) _ _ _ beforeRun
  have atStart : RunsFrom (rows k 0)
      (padCfg (base_le k) ⟨0, initialTape⟩) (before.map (padCfg (base_le k)))
      (padCfg (base_le k) (BareReserve.final k base x y)) := by
    rw [rows_start]
    exact paddedBefore
  have startSegment := block_segment (rows k) (ports k) 0 _ _ _ atStart
  have transfer := block_transfer (rows k) (ports k) 0 _
    (BareReserve.memoryPhase (mNx x y), 0) atStart.2.2.2
      (ports_observed k (mNx x y) _ (BareReserve.final_memory k base x y))
  have paddedAfter := pad_runsFrom (payload_le k) (PayloadFour.machine (mNx x y).val) _ _ _ afterRun'
  have atMemory : RunsFrom (rows k (BareReserve.memoryPhase (mNx x y)))
      (padCfg (payload_le k) ⟨0, middleTape⟩) (after.map (padCfg (payload_le k)))
      (padCfg (payload_le k) ⟨5160, endTape⟩) := by
    rw [rows_memory]
    exact paddedAfter
  have finishRun := block_runsFrom (rows k) (ports k) (BareReserve.memoryPhase (mNx x y)) _ _ _
    atMemory (ports_memory k (mNx x y) _)
  have fullSegment := segment_append (machine k) _ _ _ _ _ _ startSegment
    ⟨finishRun.1, finishRun.2.1, finishRun.2.2.1⟩ transfer
  let trace := (before.map (padCfg (base_le k))).map (blockCfg (p := 32) 0) ++
    (after.map (padCfg (payload_le k))).map (blockCfg (BareReserve.memoryPhase (mNx x y)))
  have run : RunsFrom (machine k) ⟨0, initialTape⟩ trace (final k base x y) := by
    have joined := segment_runsFrom (machine k) _ _ _ fullSegment finishRun.2.2.2
    simpa only [trace, blockCfg_zero, padCfg, padLabel, Fin.val_zero, Fin.mk_zero, final, endTape]
      using joined
  have time : trace.length ≤ coefficient k * (fieldWidth x y + 1) ^ 8 := by
    have length : trace.length = before.length + after.length := by
      dsimp only [trace]
      rw [List.length_append, List.length_map, List.length_map, List.length_map, List.length_map]
    rw [length]
    calc
      _ ≤ (16 * k + 2048) * (fieldWidth x y + 1) ^ 8 +
          (8192 * (k + 3) ^ 2) * (fieldWidth x y + 1) ^ 8 := Nat.add_le_add beforeTime afterTime
      _ = _ := by unfold coefficient; ring
  refine ⟨trace, run, time, ?_⟩
  intro inputLength clock
  have space := PSTRTMTrace002.visitedSpace_le (machine k) inputLength (trace.take clock)
  have taken : (trace.take clock).length ≤ trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  omega

theorem final_tape (k : Nat) (base : List Bool) (x y : Rat) :
    (final k base x y).Tape =
      Tape.mk₂ (List.replicate (k * fieldWidth x y ^ 4 + 4) false ++ PayloadActual.archive base x y)
        (PayloadActual.fields x y) := rfl

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.BarePayload
