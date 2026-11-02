module

public import Common.PSTR_WordBool_IsolatedRatRun_072
public import Structure.PA17_TM_RatArithmetic_AddSubFull_079a

/-! The concrete next original word callee: actual RAW 1-p on physical
13/14. The fixed RawSub program and constants precede ALL priors/archives.
No arithmetic oracle, Word truncation or resident allocator is introduced. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.IsolatedRat

open Turing RationalControllerComputation
open PA17TMRatArithmeticAddSubController075 PA17TMRatArithmeticAddSubFull079

variable {C : Type*}

def rawBudget (p : Rat) : Nat := addSubResourceCoefficient * ((encode [.rational 1, .rational p]).length + 1)^4

/-- This is the actual internal entry for the getter/encoder consumer.
Packet13 and empty14 must be produced physically. Archive1 and unread0
are arbitrary real background; the final caller2 has not executed. -/
theorem actual_prior_complement (caller : Statement C controllerCap) (context : C)
    (memory : BoolOnStacks.Store controllerCap) (background : Stack → List Bool) (p : Rat) :
    ∃ (trace : List (State C controllerCap)) (final : State C controllerCap),
      trace.head? = some (entry context memory background (encode [.rational 1, .rational p])) ∧
      trace.IsChain (fun a b => TM2.step (program subMachine caller) a = some b) ∧
      trace.getLast? = some final ∧ final.l = some 2 ∧
      (represented final).Tape = Tape.mk₁ (encode [.rational (1-p)]) ∧
      trace.length ≤ rawBudget p + 2 ∧
      (∀ current ∈ trace, current.var.1 = context ∧
        (∀ slot, slot ≠ 13 → slot ≠ 14 → current.stk slot = background slot) ∧
        occupied current.stk ≤ outside background + rawBudget p) ∧
      (∀ current ∈ trace.dropLast, current.l ≠ some 2) ∧
      ∀ current ∈ trace, ∀ point : Label, point ≠ 2 →
        (∀ node ∈ AuxWorkspace.nodes (program subMachine caller point) current.var current.stk,
          (∀ slot, (node.2 slot).length ≤ outside background + rawBudget p + 2) ∧
          ∀ slot, slot ≠ 13 → slot ≠ 14 → node.2 slot = background slot) ∧
        ScannerStatement.clock (program subMachine caller point) current.var current.stk ≤
          8 * (outside background + rawBudget p + 3) := by
  obtain ⟨old, oldFinal, actual, tape, time, space⟩ := original_add_sub_contract true 1 p
  have oldSpace : visitedSpace subMachine (encode [.rational 1, .rational p]).length old ≤ rawBudget p := by
    simpa only [List.take_length, subMachine, rawBudget, originalPower] using space old.length
  obtain ⟨trace, final, head, chain, last, active, result, count, bounds, proper, internal⟩ :=
    actual_old_call subMachine caller context memory background (encode [.rational 1, .rational p]) old oldFinal
      actual.1 actual.2.1 actual.2.2.1 actual.2.2.2.1
  have timeBound : old.length ≤ rawBudget p := time
  refine ⟨trace, final, head, chain, last, active, ?_, ?_, ?_, proper, ?_⟩
  · rw [result]
    exact tape
  · omega
  · intro current member
    have actualBound := bounds current member
    exact ⟨actualBound.1, actualBound.2.1, actualBound.2.2.trans (Nat.add_le_add_left oldSpace _)⟩
  · intro current member point properPoint
    obtain ⟨nodes, clock⟩ := internal current member point properPoint
    refine ⟨?_, clock.trans (Nat.mul_le_mul_left 8 (by omega))⟩
    intro node present
    exact ⟨fun slot => ((nodes node present).1 slot).trans (by omega), (nodes node present).2⟩

theorem raw_constant_positive : 0 < addSubResourceCoefficient := addSubResourceCoefficient_pos

end PaperProofs.Common.Native.PSTRWordBool.IsolatedRat
