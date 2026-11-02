module

public import Common.PSTR_SYM_RawEOFPolynomial_064
public import Common.PSTR_WordVM_VirtualBool_025

/-! A genuine fixed two-stack caller component for the ORIGINAL raw input.
The old trace is produced here by064, not supplied by a new caller field.
Its terminal head-bit push and charged gotoReturn1 execute in full.
This is TM2 source code; the original Bool->encodedInput bootstrap of040
is a separate still-open obligation. Tape equality does not clear stacks. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawStack

open Turing PSTRSymbolicRawLoop PSTRSymbolicCursorArchive PSTRSymbolicLaneScan
open PSTRTMRawNat010 PSTRTMIncrement009
open PaperProofs.Common.Native.PSTRWordVM

abbrev Store := VirtualBool.OldStore (states := loopSupport.card)
abbrev State (C : Type*) := VirtualReturn.State C Store
abbrev Statement (C : Type*) := VirtualReturn.Statement C Store

noncomputable def source : Unit → VirtualReturn.SmallStatement Store :=
  VirtualBool.source rawLoopMachine

noncomputable def program {C : Type*} (caller : Statement C) : Fin 2 → Statement C :=
  VirtualReturn.program source caller

def archiveLeft (data : List Datum) (digits : List Bool) : List Bool :=
  (navigationCells (PSTRSymbolicLaneArchive.allDatumPairs data)).reverse ++
    false :: (leftBlocks digits.reverse ++ [false])

theorem represented_left {C : Type*} (state : State C) :
    (VirtualBool.representedState state).Tape.left = ListBlank.mk (state.stk 1) :=
  Tape.mk'_left _ _

theorem represented_right {C : Type*} (state : State C) :
    (VirtualBool.representedState state).Tape.right₀ = ListBlank.mk (state.stk 0) :=
  Tape.mk'_right₀ _ _

/-- The original positive input, actual fixed code, SAME old run and real
return. Neither a supplied trace nor pre-parsed archive is an input. The
ListBlank statements intentionally do NOT assert finite stacks []/[true]. -/
theorem actual_raw_stack {C : Type*} {I : Instance}
    (caller : Statement C) (context : C) (background : Fin 16 → List Bool)
    (input : StatisticalInput I) (available : Finset I.Tool) (positive : 0 < I.stageCount) :
    ∃ (digits : List Bool) (path : List (State C)) (final : State C),
      path.head? = some (VirtualReturn.configuration context background
        (TM2.init (Γ := PSTRWordBool.PushPop.Alphabet) (Λ := Unit) (σ := Store) 0
          (CompactPrice.symbolicInput input available))) ∧
      path.IsChain (fun before after => TM2.step (program caller) before = some after) ∧
      path.getLast? = some final ∧ final.l = some 1 ∧
      (VirtualBool.representedState final).Tape =
        archiveTape (rawInstance input ++ rawSet available) [] digits [] true ∧
      ListBlank.mk (final.stk 1) = ListBlank.mk (archiveLeft (rawInstance input ++ rawSet available) digits) ∧
      ListBlank.mk (final.stk 0) = ListBlank.mk [true] ∧
      valueDigits digits = 0 ∧ 3 ≤ digits.length ∧
      path.length ≤ 4097 * ((CompactPrice.symbolicInput input available).length + 1)^3 ∧
      (∀ current ∈ path, current.var.1 = context ∧
        ∀ slot, slot ≠ 0 → slot ≠ 1 → current.stk slot = background slot) ∧
      ∀ current ∈ path, VirtualReturn.occupiedSlots current.stk ≤ VirtualReturn.outside background +
        16384 * ((CompactPrice.symbolicInput input available).length + 1)^3 := by
  obtain ⟨digits, oldTrace, oldFinal, actual, oldTape, _head, _right, value, width, time, space⟩ :=
    original_raw_eof_polynomial input available positive
  obtain ⟨path, final, first, chain, last, returned, represented, _order, length, _context, frames, mass⟩ :=
    VirtualBool.same_old_run rawLoopMachine caller context background
      (CompactPrice.symbolicInput input available) oldTrace oldFinal
      actual.1 actual.2.1 actual.2.2.1 actual.2.2.2.1
  have tape : (VirtualBool.representedState final).Tape =
      archiveTape (rawInstance input ++ rawSet available) [] digits [] true := by
    rw [represented]
    exact oldTape
  have left := congrArg Tape.left tape
  have right := congrArg Tape.right₀ tape
  rw [represented_left] at left
  rw [represented_right] at right
  have wholeSpace := space oldTrace.length
  simp only [List.take_length] at wholeSpace
  refine ⟨digits, path, final, first, chain, last, returned, tape, ?_, ?_, value, width, ?_, frames, ?_⟩
  · simpa only [archiveTape, archiveLeft, Tape.mk₂, Tape.mk'_left] using left
  · simpa only [archiveTape, Tape.mk₂, Tape.mk'_right₀] using right
  · rw [length]
    have positiveCube : 1 ≤ ((CompactPrice.symbolicInput input available).length + 1)^3 := by
      nlinarith [Nat.zero_le ((CompactPrice.symbolicInput input available).length^2),
        Nat.zero_le ((CompactPrice.symbolicInput input available).length^3)]
    omega
  · intro current present
    exact (mass current present).trans (Nat.add_le_add_left wholeSpace _)

theorem body_at_entry {C : Type*} (caller : Statement C) :
    program caller 0 = VirtualReturn.statement (source ()) := rfl

theorem source_actions : PSTRWordBool.ScannerClock.actions
    (VirtualReturn.statement (C := Unit) (source ())) = 4 :=
  VirtualBool.actions rawLoopMachine

theorem source_pushes : PSTRWordBool.AuxWorkspace.pushes
    (VirtualReturn.statement (C := Unit) (source ())) = 2 :=
  VirtualBool.pushes rawLoopMachine

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawStack
