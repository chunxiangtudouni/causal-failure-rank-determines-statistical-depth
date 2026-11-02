module

public import Paid.PDROC_BitVM_Common_IO_Wide_Cost_016

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

def naturalDigits (value : Nat) : List Bool :=
  List.ofFn (fun position : Fin (natBits value) => value.testBit position.val)

theorem encodeNatBits_rawField (value : Nat) : encodeNatBits value = rawField (naturalDigits value) := by
  simp [encodeNatBits, rawField, naturalDigits]

theorem encodeNatBits_six : encodeNatBits 6 = [true, true, true, false, false, true, true] := by decide

/-- Exactly the ten numeric fields of the original six Cells. The first
fixed block contains the original list header and first natural tag; all
other blocks contain only their actual Cell tag/sign, if any. -/
def rawBlocks (n k : Nat) (gamma risk review fee : Rat) : List FieldBlock :=
  [⟨[true, true, true, false, false, true, true, false], naturalDigits n⟩,
   ⟨[false], naturalDigits k⟩,
   ⟨[true, decide (gamma < 0)], naturalDigits gamma.num.natAbs⟩,
   ⟨[], naturalDigits gamma.den⟩,
   ⟨[true, decide (risk < 0)], naturalDigits risk.num.natAbs⟩,
   ⟨[], naturalDigits risk.den⟩,
   ⟨[true, decide (review < 0)], naturalDigits review.num.natAbs⟩,
   ⟨[], naturalDigits review.den⟩,
   ⟨[true, decide (fee < 0)], naturalDigits fee.num.natAbs⟩,
   ⟨[], naturalDigits fee.den⟩]

theorem rawBlocks_length (n k : Nat) (gamma risk review fee : Rat) :
    (rawBlocks n k gamma risk review fee).length = 10 := rfl

theorem rawBlocks_scheduled (n k : Nat) (gamma risk review fee : Rat) :
    Scheduled 0 (rawBlocks n k gamma risk review fee) := by
  norm_num [rawBlocks, Scheduled, PDROC.BitVM.Common.IO.Bootstrap.followingField,
    PDROC.BitVM.Common.IO.Bootstrap.followingSkip]

theorem rawBlocks_count (n k : Nat) (gamma risk review fee : Rat) :
    CountMatches ⟨0, 8, false, false, 0⟩ (rawBlocks n k gamma risk review fee) := rfl

theorem original_raw_blocks (n k : Nat) (gamma risk review fee : Rat) :
    encodeBits [.natural n, .natural k, .rational gamma, .rational risk, .rational review, .rational fee] =
      fieldsWord (rawBlocks n k gamma risk review fee) ++ [true] := by
  simp only [encodeBits, List.length_cons, List.length_nil]
  rw [encodeNatBits_six]
  simp [rawBlocks, fieldsWord, blockWord, encodeCellBits, encodeNatBits_rawField, List.append_assoc]

/-- ONE fixed finite Bool TM1 starts on the ORIGINAL six-Cell bitstream.
It really processes every header/tag/sign/unary/payload/footer, erases its
workspace, restores the first track head, and HALTs on the WHOLE pointed
65-bit encoding of the true Fin32-stack initial tape. -/
theorem original_six_path (n k : Nat) (gamma risk review fee : Rat) :
    ∃ finalStore : Store, ∃ path : ActualPath (TM1.step program)
      (TM1.init (Γ := Bool) (Λ := Label) (σ := Store)
        (encodeBits [.natural n, .natural k, .rational gamma, .rational risk, .rational review, .rational fee]))
      (⟨none, finalStore, Tape.mk₁ (encodedInit32
        (encodeBits [.natural n, .natural k, .rational gamma, .rational risk, .rational review, .rational fee]))⟩ :
        TM1.Cfg Bool Label Store),
      path.posts.length ≤ 65536 * ((encodeBits
        [.natural n, .natural k, .rational gamma, .rational risk, .rational review, .rational fee]).length + 1)^2 := by
  rw [original_raw_blocks]
  let blocks := rawBlocks n k gamma risk review fee
  let word := fieldsWord blocks
  let start : Store := ⟨0, 8, false, false, 0⟩
  obtain ⟨middleStore, middle, middleField, middleBound⟩ :=
    fields_path blocks start [] [true] (rawBlocks_scheduled n k gamma risk review fee)
      (rawBlocks_count n k gamma risk review fee)
  obtain ⟨finish, finishBound⟩ := cursor_finish_path middleStore middleField word
  have edge : TM1.step program
      (TM1.init (Γ := Bool) (Λ := Label) (σ := Store) (word ++ [true])) =
      some (cursorState 1 start [] (word ++ [true])) := by
    simpa [cursorState, state, start, unmarkedRows, leftRows] using initialize_step (word ++ [true])
  let first : ActualPath (TM1.step program)
      (TM1.init (Γ := Bool) (Λ := Label) (σ := Store) (word ++ [true]))
      (cursorState 1 start [] (word ++ [true])) := ActualPath.single edge
  let main : ActualPath (TM1.step program)
      (cursorState 1 start [] (word ++ [true])) (cursorState 4 middleStore word [true]) :=
    ⟨middle.posts, by simpa [word] using middle.chain, by simpa [word] using middle.last⟩
  let joined := (first.trans main).trans finish
  refine ⟨footerReadStore middleStore, joined, ?_⟩
  have mainBound : main.posts.length ≤ fieldsCost blocks 1 0 := by simpa [main] using middleBound
  have coarse := fieldsCost_coarse blocks 1 0
  have blockCount : blocks.length = 10 := rfl
  rw [blockCount] at coarse
  have length : joined.posts.length = 1 + main.posts.length + finish.posts.length := by
    simp only [joined, ActualPath.trans, first, ActualPath.single, List.length_append,
      List.length_cons, List.length_nil]
  rw [length]
  simp only [List.length_append, List.length_cons, List.length_nil]
  change fieldsCost blocks 1 0 ≤ 256 * 10 * (1 + 0 + 2 * word.length + 2)^2 at coarse
  nlinarith

end PDROC.BitVM.Common.IO.Wide
