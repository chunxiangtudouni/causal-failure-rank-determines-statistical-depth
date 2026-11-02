module

public import Structure.RootB23_Threshold_Window_BareBookmark_011
public import Structure.RootB23_Threshold_Window_PhysicalReserve_014

/-! Actual bare2Rat -> total SUM -> four equal physical counters -> quartic
gap. The observed first bits remain in actual finite control across the
whole allocator, ready for the subsequent payload copy/serialization. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.BareReserve
open Turing PSTRTMSeq005 PA17TMDivisionCompose006 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticBookmark014
open PA17TMRatArithmeticWidth018 (BoundedRun)

def sourceRight (x y : Rat) : List Bool :=
  PA17TMRatArithmeticFarLoad031.fieldWord
    (PA17TMRatArithmeticFarLoad031.nxContext (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail)
    (false :: (numeratorDigits x).tail) (PA17TMRatArithmeticFarLoad031.workSuffix 0 [])

theorem sourceRight_eq (x y : Rat) : sourceRight x y = nxRight x y ++ [false,false,false] := by
  simp only [sourceRight, PA17TMRatArithmeticFarLoad031.fieldWord,
    PA17TMRatArithmeticFarLoad031.nxContext, PA17TMRatArithmeticFarLoad031.dxContext,
    PA17TMRatArithmeticWidth018.nxStream, PA17TMRatArithmeticFarLoad031.workSuffix,
    PA17TMRatArithmeticCopy006.workspace, nxRight, dxRight, syRight, nyRight, dyRight,
    clampFirst, List.replicate_zero, List.nil_append, List.append_assoc, List.cons_append]
  rfl

theorem sourceTape_eq (base : List Bool) (x y : Rat) :
    Tape.mk₂ (false :: sign x :: base) (nxRight x y) =
      Tape.mk₂ (false :: sign x :: base) (sourceRight x y) := by
  rw [sourceRight_eq]
  symm
  have first := PA17TMRatArithmeticBankCopy024.tape_append_false
    (false :: sign x :: base) (nxRight x y)
  have second := PA17TMRatArithmeticBankCopy024.tape_append_false
    (false :: sign x :: base) (nxRight x y ++ [false])
  have third := PA17TMRatArithmeticBankCopy024.tape_append_false
    (false :: sign x :: base) ((nxRight x y ++ [false]) ++ [false])
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using (third.trans second).trans first

theorem width_eq (x y : Rat) :
    TotalWidth.width (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail = fieldWidth x y := by
  change (clampFirst (numeratorDigits x)).length + (clampFirst (denominatorDigits x)).length +
    (clampFirst (numeratorDigits y)).length + (clampFirst (denominatorDigits y)).length = fieldWidth x y
  rw [clampFirst_length _ (numerator_ne_nil x), clampFirst_length _ (denominator_ne_nil x),
    clampFirst_length _ (numerator_ne_nil y), clampFirst_length _ (denominator_ne_nil y)]
  rfl

def retainedArchive (base : List Bool) (x y : Rat) : List Bool :=
  PhysicalReserve.preservedArchive (sign x :: base) (numeratorDigits x).tail
    (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail

theorem actual_reserve_bounded (k : Nat) (base : List Bool) (x y : Rat) :
    BoundedRun (PhysicalReserve.reserveMachine k)
      (Tape.mk₂ (false :: sign x :: base) (nxRight x y)) (PhysicalReserve.reserveExit k)
      (Tape.mk₂ (false :: retainedArchive base x y)
        (powerWord (fieldWidth x y) 4 (k * fieldWidth x y ^ 4)))
      ((16 * k + 1024) * (fieldWidth x y + 1) ^ 8) := by
  have actual := (PhysicalReserve.reserve_bounded k (sign x :: base)
    (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail).mono
      (PhysicalReserve.reserveFee_le k _)
  rw [width_eq] at actual
  rw [sourceTape_eq base x y]
  exact actual

def rowCap (k : Nat) : Nat := 2397 + PhysicalReserve.reserveCap k
theorem bookmark_le (k : Nat) : 2397 ≤ rowCap k := by unfold rowCap; omega
theorem reserve_le (k : Nat) : PhysicalReserve.reserveCap k ≤ rowCap k := by unfold rowCap; omega

def memoryPhase (memory : Fin 32) : Fin 33 := ⟨memory.val + 1, by have h := memory.isLt; omega⟩

def rows (k : Nat) (phase : Fin 33) : Machine (rowCap k) :=
  if phase.val = 0 then padMachine (bookmark_le k) BareBookmark.bareBookmarkMachine
  else padMachine (reserve_le k) (PhysicalReserve.reserveMachine k)

def ports (k : Nat) (phase : Fin 33) (localLabel : Fin (rowCap k + 1)) :
    Option (Fin 33 × Fin (rowCap k + 1)) :=
  if phase.val = 0 then
    if bounded : 2206 ≤ localLabel.val ∧ localLabel.val < 2398 then
      if (localLabel.val - 2206) % 6 = 0 then
        some (⟨(localLabel.val - 2206) / 6 + 1, by omega⟩, 0)
      else none
    else none
  else none

def machine (k : Nat) : Machine (totalStates 32 (rowCap k)) := blockMachine (rows k) (ports k)

theorem rows_start (k : Nat) :
    rows k 0 = padMachine (bookmark_le k) BareBookmark.bareBookmarkMachine := by
  simp only [rows, Fin.val_zero, ite_true]

theorem rows_memory (k : Nat) (memory : Fin 32) :
    rows k (memoryPhase memory) = padMachine (reserve_le k) (PhysicalReserve.reserveMachine k) := by
  have positive : (memoryPhase memory).val ≠ 0 := by change memory.val + 1 ≠ 0; omega
  simp only [rows, positive, ite_false]

theorem ports_memory (k : Nat) (memory : Fin 32) (localLabel : Fin (rowCap k + 1)) :
    ports k (memoryPhase memory) localLabel = none := by
  have positive : (memoryPhase memory).val ≠ 0 := by change memory.val + 1 ≠ 0; omega
  simp only [ports, positive, ite_false]

theorem ports_observed (k : Nat) (memory : Fin 32) (localLabel : Fin (rowCap k + 1))
    (observed : localLabel.val = 2206 + 6 * memory.val) :
    ports k 0 localLabel = some (memoryPhase memory, 0) := by
  have hm := memory.isLt
  have bounded : 2206 ≤ localLabel.val ∧ localLabel.val < 2398 := by omega
  have remainder : (localLabel.val - 2206) % 6 = 0 := by omega
  have quotient : (localLabel.val - 2206) / 6 = memory.val := by omega
  simp only [ports, Fin.val_zero, ite_true, dite_eq_left bounded, ite_eq_left remainder]
  apply congrArg some
  apply Prod.ext
  · apply Fin.ext
    change (localLabel.val - 2206) / 6 + 1 = memory.val + 1
    omega
  · rfl

def bookmarkLast (base : List Bool) (x y : Rat) : MachineState 2397 :=
  ⟨rightLabel (a := 93) (BareBookmark.bookmarkFinal base x y).q,
    Tape.mk₂ (false :: sign x :: base) (nxRight x y)⟩

theorem bookmarkLast_label (base : List Bool) (x y : Rat) :
    (bookmarkLast base x y).q.val = 2206 + 6 * (mNx x y).val := by
  simp only [bookmarkLast, rightLabel, BareBookmark.bookmarkFinal,
    PA17TMRatArithmeticBookmark014.memoryCfg, blockCfg, label,
    PA17TMRatArithmeticBookmark014.memoryPhase, Fin.val_zero]
  norm_num
  ring

def final (k : Nat) (base : List Bool) (x y : Rat) : MachineState (totalStates 32 (rowCap k)) :=
  blockCfg (memoryPhase (mNx x y))
    (padCfg (reserve_le k)
      ⟨PhysicalReserve.reserveExit k, Tape.mk₂ (false :: retainedArchive base x y)
        (powerWord (fieldWidth x y) 4 (k * fieldWidth x y ^ 4))⟩)

/-- A fixed program, bare canonical input and arbitrary original WEST
archive. All total-W production, all four copies, and exact quartic growth
are actual transitions. The finite memory is retained, not discarded by an
unconditional sequence reset. Payload marshalling remains the next step. -/
theorem bare_reserve_actual (k : Nat) (base : List Bool) (x y : Rat) :
    ∃ trace, RunsFrom (machine k)
      ⟨0, Tape.mk₂ base (encodeDatum (.rational x) ++ encodeDatum (.rational y))⟩ trace
      (final k base x y) ∧
      trace.length ≤ (16 * k + 2048) * (fieldWidth x y + 1) ^ 8 ∧
      ∀ inputLength clock, visitedSpace (machine k) inputLength (trace.take clock) ≤
        inputLength + 2 * ((16 * k + 2048) * (fieldWidth x y + 1) ^ 8) + 1 := by
  obtain ⟨before, bookmarkRun, bookmarkTime⟩ := BareBookmark.bareBookmark_bounded base x y
  obtain ⟨after, reserveRun, reserveTime⟩ := actual_reserve_bounded k base x y
  let initialTape := Tape.mk₂ base (encodeDatum (.rational x) ++ encodeDatum (.rational y))
  let middleTape := Tape.mk₂ (false :: sign x :: base) (nxRight x y)
  let first := (⟨0, initialTape⟩ : MachineState 2397)
  let last := bookmarkLast base x y
  have originalRun : RunsFrom BareBookmark.bareBookmarkMachine first before last := bookmarkRun
  have paddedBefore := pad_runsFrom (bookmark_le k) BareBookmark.bareBookmarkMachine _ _ _ originalRun
  have atStart : RunsFrom (rows k 0) (padCfg (bookmark_le k) first)
      (before.map (padCfg (bookmark_le k))) (padCfg (bookmark_le k) last) := by
    rw [rows_start]
    exact paddedBefore
  have startSegment := block_segment (rows k) (ports k) 0 _ _ _ atStart
  have transfer := block_transfer (rows k) (ports k) 0 _ (memoryPhase (mNx x y), 0)
    atStart.2.2.2 (ports_observed k (mNx x y) _ (bookmarkLast_label base x y))
  have paddedAfter := pad_runsFrom (reserve_le k) (PhysicalReserve.reserveMachine k) _ _ _ reserveRun
  have atMemory : RunsFrom (rows k (memoryPhase (mNx x y)))
      (padCfg (reserve_le k) ⟨0, middleTape⟩)
      (after.map (padCfg (reserve_le k)))
      (padCfg (reserve_le k)
        ⟨PhysicalReserve.reserveExit k, Tape.mk₂ (false :: retainedArchive base x y)
          (powerWord (fieldWidth x y) 4 (k * fieldWidth x y ^ 4))⟩) := by
    rw [rows_memory]
    exact paddedAfter
  have finishRun := block_runsFrom (rows k) (ports k) (memoryPhase (mNx x y)) _ _ _
    atMemory (ports_memory k (mNx x y) _)
  have fullSegment := segment_append (machine k) _ _ _ _ _ _ startSegment
    ⟨finishRun.1, finishRun.2.1, finishRun.2.2.1⟩ transfer
  let trace := (before.map (padCfg (bookmark_le k))).map (blockCfg (p := 32) 0) ++
    (after.map (padCfg (reserve_le k))).map (blockCfg (memoryPhase (mNx x y)))
  have run : RunsFrom (machine k)
      ⟨0, initialTape⟩ trace (final k base x y) := by
    have joined := segment_runsFrom (machine k) _ _ _ fullSegment finishRun.2.2.2
    simpa only [trace, first, blockCfg_zero, padCfg, padLabel, Fin.val_zero, Fin.mk_zero, final]
      using joined
  have time : trace.length ≤ (16 * k + 2048) * (fieldWidth x y + 1) ^ 8 := by
    have positive : 1 ≤ fieldWidth x y + 1 := by omega
    have square : (fieldWidth x y + 1) ^ 2 ≤ (fieldWidth x y + 1) ^ 8 :=
      Nat.pow_le_pow_right positive (by decide)
    have linear : fieldWidth x y ≤ (fieldWidth x y + 1) ^ 8 := by
      have h : fieldWidth x y + 1 ≤ (fieldWidth x y + 1) ^ 8 := by
        simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1 ≤ 8)
      exact (Nat.le_succ (fieldWidth x y)).trans h
    have one : 1 ≤ (fieldWidth x y + 1) ^ 8 := by
      simpa only [pow_zero] using Nat.pow_le_pow_right positive (by decide : 0 ≤ 8)
    simp only [trace, List.length_append, List.length_map]
    nlinarith
  refine ⟨trace, run, time, ?_⟩
  intro inputLength clock
  have space := PSTRTMTrace002.visitedSpace_le (machine k) inputLength (trace.take clock)
  have taken : (trace.take clock).length ≤ trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  omega

theorem final_tape (k : Nat) (base : List Bool) (x y : Rat) :
    (final k base x y).Tape = Tape.mk₂ (false :: retainedArchive base x y)
      (powerWord (fieldWidth x y) 4 (k * fieldWidth x y ^ 4)) := rfl

theorem final_memory (k : Nat) (base : List Bool) (x y : Rat) :
    phaseOf (p := 32) (s := rowCap k) (final k base x y).q = memoryPhase (mNx x y) :=
  phaseOf_label _ _

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.BareReserve
