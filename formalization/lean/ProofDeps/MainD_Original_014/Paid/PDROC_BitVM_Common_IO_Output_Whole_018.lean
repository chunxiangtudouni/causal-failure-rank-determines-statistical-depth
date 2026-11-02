module

public import Paid.PDROC_BitVM_Common_IO_Output_Rows_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing PaperProofs.Paid.Computation
open PaperProofs.Common.Native.PSTRWordBool

attribute [local implicit_reducible] Turing.TM2to1.Γ'

/-- Starting at the WHOLE actual encoded32-stack tape, physically
extract stack0 beyond all old data, run the genuine inverse codec,
scan its real unary header, and HALT with naked stack0 at right0.
The output's positive length is the sole format property; in the main
VM it follows from encodeArtifact's real TRUE footer. Other31 stacks
are arbitrary and are retained as old physical archive. -/
theorem whole_output_path (cells : Fin 32 → List Bool)
    (positive : 0 < (cells (0 : Fin 32)).length) (saved : Store)
    (changed : ListBlank StackRows)
    (represented : ∀ slot, changed.map (proj slot) = ListBlank.mk ((cells slot).map some).reverse) :
    ∃ final : TM1.Cfg Bool Label Store, ∃ path : ActualPath (TM1.step program)
      (cfg 0 saved (TM1to1.trTape (FiniteTrackCodec.encode_default 32) (ScannerPaths.baseTape changed))) final,
      final.l = none ∧ final.Tape.right₀ = ListBlank.mk (cells (0 : Fin 32)) ∧
      path.posts.length ≤ 1024 * (stackHeight cells + 1)^2 := by
  have height : 0 < stackHeight cells := positive.trans_le (length_le_height cells (0 : Fin 32))
  have nonempty : (sourceDataBottom cells).reverse ≠ [] := by
    apply List.length_pos_iff_ne_nil.mp
    simpa only [List.length_reverse, sourceDataBottom_length] using positive
  obtain ⟨current, rest, shape⟩ := List.exists_cons_of_ne_nil nonempty
  have word : (current :: rest).map Prod.fst = cells (0 : Fin 32) := by
    rw [← shape]
    exact sourceDataBottom_bits cells
  have count : rest.length + 1 = (cells (0 : Fin 32)).length := by
    have lengths := congrArg List.length shape
    simpa [sourceDataBottom_length] using lengths.symm
  obtain ⟨final, ⟨posts, chain, last⟩, halt, right, bound⟩ :=
    framed_output_path saved current rest (canonicalAbove cells positive)
  have tape : TM1to1.trTape (FiniteTrackCodec.encode_default 32) (ScannerPaths.baseTape changed) =
      Tape.mk₁ ((unreadLeft (current :: rest)).reverse ++ flatRows (absentTails (canonicalAbove cells positive))) := by
    rw [actual_encoded_tape_canonical cells height changed represented, canonical_frame cells positive, shape]
  refine ⟨final, ⟨posts, ?_, ?_⟩, halt, ?_, ?_⟩
  · simpa only [tape] using chain
  · simpa only [tape] using last
  · simpa only [word] using right
  · have postBound : posts.length ≤ rest.length + (stackHeight cells - (cells (0 : Fin 32)).length) + 4 +
        128 * ((stackHeight cells - (cells (0 : Fin 32)).length) + 2 * rest.length + 2)^2 := by
      simpa only [canonicalAbove_length] using bound
    have width := length_le_height cells (0 : Fin 32)
    have linear : (stackHeight cells - (cells (0 : Fin 32)).length) + 2 * rest.length + 2 ≤
        2 * stackHeight cells := by omega
    have squared := Nat.pow_le_pow_left linear 2
    nlinarith

noncomputable def outputMachine :
    BitMachine (PDROC.BitVM.Common.tm1NativeSupport program Finset.univ).card :=
  PDROC.BitVM.Common.tm1BitMachine program Finset.univ

noncomputable def outputBudget : Nat := 1025 * SupportClock.clock program Finset.univ + 1

/-- A fixed finite Bool machine, independent of cells/word widths,
compiled from the above actual physical controller. The selected real
TM0 trace starts on the entire old encoded tape; every65/67-cell shuttle,
all32 presence probes, the inverse codec and header skip are paid by the
same fixed SupportClock. This is the final I/O phase, not the whole VM. -/
theorem whole_output_bit_run (cells : Fin 32 → List Bool)
    (positive : 0 < (cells (0 : Fin 32)).length) (changed : ListBlank StackRows)
    (represented : ∀ slot, changed.map (proj slot) = ListBlank.mk ((cells slot).map some).reverse) :
    ∃ trace final,
      BitRuns outputMachine
        ((canonicalTracks cells).flatMap (fun row => (FiniteTrackCodec.encode row).toList)) trace final ∧
      final.Tape.right₀ = ListBlank.mk (cells (0 : Fin 32)) ∧
      trace.length ≤ outputBudget * (stackHeight cells + 1)^2 ∧
      visitedBitSpace outputMachine
        ((canonicalTracks cells).flatMap (fun row => (FiniteTrackCodec.encode row).toList)).length trace ≤
        65 * stackHeight cells + 2 * (outputBudget * (stackHeight cells + 1)^2) + 1 := by
  let input := (canonicalTracks cells).flatMap (fun row => (FiniteTrackCodec.encode row).toList)
  obtain ⟨sourceFinal, path, halt, right, bound⟩ := whole_output_path cells positive default changed represented
  have height : 0 < stackHeight cells := positive.trans_le (length_le_height cells (0 : Fin 32))
  have tape : TM1to1.trTape (FiniteTrackCodec.encode_default 32) (ScannerPaths.baseTape changed) = Tape.mk₁ input :=
    actual_encoded_tape_canonical cells height changed represented
  let sourceTrace := TM1.init (Γ := Bool) (Λ := Label) (σ := Store) input :: path.posts
  have first : sourceTrace.head? = some (TM1.init input) := rfl
  have initial : cfg 0 default
      (TM1to1.trTape (FiniteTrackCodec.encode_default 32) (ScannerPaths.baseTape changed)) = TM1.init input := by
    rw [tape]
    rfl
  have chain : sourceTrace.IsChain (fun before after => TM1.step program before = some after) := by
    simpa only [initial] using path.chain
  have last : sourceTrace.getLast? = some sourceFinal := by simpa only [initial] using path.last
  have stopped : TM1.step program sourceFinal = none := by
    rcases sourceFinal with ⟨label, saved, tape⟩
    change label = none at halt
    subst label
    rfl
  have squarePositive : 1 ≤ (stackHeight cells + 1)^2 := Nat.one_le_pow' 2 (stackHeight cells)
  have sourceBound : sourceTrace.length ≤ 1025 * (stackHeight cells + 1)^2 := by
    have postBound : path.posts.length ≤ 1024 * (stackHeight cells + 1)^2 := bound
    simp only [sourceTrace, List.length_cons]
    nlinarith
  obtain ⟨trace, final, actual, finalTape, nativeBound, _⟩ :=
    PDROC.BitVM.Common.tm1_actual_bit_trace program Finset.univ supports input sourceTrace sourceFinal
      first chain last stopped
  have time : trace.length ≤ outputBudget * (stackHeight cells + 1)^2 := by
    calc
      trace.length ≤ SupportClock.clock program Finset.univ * sourceTrace.length + 1 := nativeBound
      _ ≤ SupportClock.clock program Finset.univ * (1025 * (stackHeight cells + 1)^2) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ sourceBound) 1
      _ ≤ outputBudget * (stackHeight cells + 1)^2 := by unfold outputBudget; nlinarith
  have inputLength : input.length = 65 * stackHeight cells := by
    unfold input canonicalTracks
    simp only [List.length_flatMap, List.map_ofFn, List.Vector.toList_length]
    change (List.ofFn (fun _ : Fin (stackHeight cells) => 65)).sum = 65 * stackHeight cells
    rw [List.ofFn_const, List.sum_replicate_nat]
    exact Nat.mul_comm _ _
  refine ⟨trace, final, actual, ?_, time, ?_⟩
  · simpa only [finalTape] using right
  · change visitedBitSpace outputMachine input.length trace ≤ _
    calc
      visitedBitSpace outputMachine input.length trace ≤
          input.length + 2 * (outputBudget * (stackHeight cells + 1)^2) + 1 :=
        PDROC.BitVM.Common.visitedBitSpace_of_clock outputMachine input.length trace _ time
      _ = 65 * stackHeight cells + 2 * (outputBudget * (stackHeight cells + 1)^2) + 1 := by rw [inputLength]

/-- The decoder's states/code/constant are fixed BEFORE every source
stack word and actual compiler representation. These are logical source
invariants for phase composition, not extra inputs to the Bool machine. -/
theorem uniform_whole_output_decoder :
    ∃ states : Nat, ∃ machine : BitMachine states, ∃ boundConstant : Nat, 0 < boundConstant ∧
      ∀ (cells : Fin 32 → List Bool), 0 < (cells (0 : Fin 32)).length →
      ∀ (changed : ListBlank StackRows),
      (∀ slot, changed.map (proj slot) = ListBlank.mk ((cells slot).map some).reverse) →
      ∃ trace final,
        BitRuns machine
          ((canonicalTracks cells).flatMap (fun row => (FiniteTrackCodec.encode row).toList)) trace final ∧
        final.Tape.right₀ = ListBlank.mk (cells (0 : Fin 32)) ∧
        trace.length ≤ boundConstant * (stackHeight cells + 1)^2 ∧
        visitedBitSpace machine
          ((canonicalTracks cells).flatMap (fun row => (FiniteTrackCodec.encode row).toList)).length trace ≤
          65 * stackHeight cells + 2 * (boundConstant * (stackHeight cells + 1)^2) + 1 := by
  refine ⟨_, outputMachine, outputBudget, ?_, whole_output_bit_run⟩
  unfold outputBudget
  omega

end PDROC.BitVM.Common.IO.Output
