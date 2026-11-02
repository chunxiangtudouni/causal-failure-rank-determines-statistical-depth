module

public import Paid.PDROC_BitVM_Common_IO_Wide_Raw_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing PaperProofs.Paid.Computation
open PaperProofs.Common.Native.PSTRWordBool

/-- Fixed code/support/store selected BEFORE every P and fee. All long
data remain on the original Bool tape. -/
noncomputable def bootstrapMachine :
    BitMachine (PDROC.BitVM.Common.tm1NativeSupport program Finset.univ).card :=
  PDROC.BitVM.Common.tm1BitMachine program Finset.univ

noncomputable def bootstrapBudget : Nat := 65537 * SupportClock.clock program Finset.univ + 1

/-- The actual finite BoolTM0 bootstrap, including charges for every
65-cell move/write and cleanup. This is the input adapter only; it does
not assert a VM interpreter or any artifact output. -/
theorem original_raw_bit_run (P : PaperProofs.Paid.Parameters) (fee : Rat) :
    ∃ trace final,
      BitRuns bootstrapMachine (encodeBits (rawInput P fee)) trace final ∧
      final.Tape = Tape.mk₁ (encodedInit32 (encodeBits (rawInput P fee))) ∧
      trace.length ≤ bootstrapBudget * ((encodeBits (rawInput P fee)).length + 1)^2 ∧
      visitedBitSpace bootstrapMachine (encodeBits (rawInput P fee)).length trace ≤
        (encodeBits (rawInput P fee)).length +
          2 * (bootstrapBudget * ((encodeBits (rawInput P fee)).length + 1)^2) + 1 := by
  let input := encodeBits (rawInput P fee)
  obtain ⟨saved, path, bound⟩ := original_six_path P.certificate.stages P.tools
    P.certificate.gamma P.certificate.risk P.reviewFee fee
  let sourceFinal : TM1.Cfg Bool Label Store := ⟨none, saved, Tape.mk₁ (encodedInit32 input)⟩
  let sourceTrace := TM1.init (Γ := Bool) (Λ := Label) (σ := Store) input :: path.posts
  have first : sourceTrace.head? = some (TM1.init input) := rfl
  have chain : sourceTrace.IsChain (fun before after => TM1.step program before = some after) :=
    path.chain
  have last : sourceTrace.getLast? = some sourceFinal := path.last
  have halt : TM1.step program sourceFinal = none := rfl
  have squarePositive : 1 ≤ (input.length + 1)^2 := Nat.one_le_pow' 2 input.length
  have sourceBound : sourceTrace.length ≤ 65537 * (input.length + 1)^2 := by
    have postBound : path.posts.length ≤ 65536 * (input.length + 1)^2 := bound
    simp only [sourceTrace, List.length_cons]
    nlinarith
  obtain ⟨trace, final, actual, tape, nativeBound, _⟩ :=
    PDROC.BitVM.Common.tm1_actual_bit_trace program Finset.univ supports input sourceTrace sourceFinal
      first chain last halt
  have time : trace.length ≤ bootstrapBudget * (input.length + 1)^2 := by
    calc
      trace.length ≤ SupportClock.clock program Finset.univ * sourceTrace.length + 1 := nativeBound
      _ ≤ SupportClock.clock program Finset.univ * (65537 * (input.length + 1)^2) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ sourceBound) 1
      _ ≤ bootstrapBudget * (input.length + 1)^2 := by unfold bootstrapBudget; nlinarith
  refine ⟨trace, final, actual, tape, time, ?_⟩
  exact PDROC.BitVM.Common.visitedBitSpace_of_clock bootstrapMachine input.length trace _ time

/-- Uniformity is explicit: states, machine and positive constant all
precede P/fee, with no prepared data, width, fuel or workspace input. -/
theorem uniform_original_raw_bootstrap :
    ∃ states : Nat, ∃ machine : BitMachine states, ∃ boundConstant : Nat, 0 < boundConstant ∧
      ∀ (P : PaperProofs.Paid.Parameters) (fee : Rat), ∃ trace final,
        BitRuns machine (encodeBits (rawInput P fee)) trace final ∧
        final.Tape = Tape.mk₁ (encodedInit32 (encodeBits (rawInput P fee))) ∧
        trace.length ≤ boundConstant * ((encodeBits (rawInput P fee)).length + 1)^2 ∧
        visitedBitSpace machine (encodeBits (rawInput P fee)).length trace ≤
          (encodeBits (rawInput P fee)).length +
            2 * (boundConstant * ((encodeBits (rawInput P fee)).length + 1)^2) + 1 := by
  refine ⟨_, bootstrapMachine, bootstrapBudget, ?_, original_raw_bit_run⟩
  unfold bootstrapBudget
  omega

end PDROC.BitVM.Common.IO.Wide
