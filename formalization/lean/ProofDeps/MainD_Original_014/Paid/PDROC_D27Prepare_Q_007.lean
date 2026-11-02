module

public import Paid.PDROC_D27Prepare_Q_006
public import Paid.PDROC_D27Prepare_Search_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Q

/-- The complete original optional-increment ceiling routine, including
every actual physical prefix. It is shared by both Q ceilings and by J.
The hypothetical successor is bounded even when the branch skips it. -/
theorem ceiling_pages_bounded (R : Finset ℕ) (input : List Cell) (start increment join : ℕ)
    (startInside : start < pageCount) (incrementInside : increment < pageCount)
    (source target : ℕ) (sourceInside : source < 64) (targetInside : target < 64)
    (inside : target ∈ R) (notOne : target ≠ 14) (value : ℚ) (nonnegative : 0 ≤ value)
    (coreLayout : pageCode start = ceilCore source target ++ branch join increment)
    (incrementLayout : pageCode increment = natBinarySlots .add target 14 target ++ go join)
    (before : State) (location : before.pc = pc start)
    (fresh : before.register .fresh = .natural 0)
    (sourceValue : Search.SlotHas before source (.rational value))
    (one : Search.SlotHas before 14 (.natural 1)) (B : ℕ)
    (bounded : StateBounds 64 B before) (addressBits : 1 + natBits 64 ≤ B)
    (encoding : ratEncodingBits value + 1 ≤ B) :
    ∃ (after : State) (trace : List State), after.pc = pc join ∧
      Search.SlotHas after target (.natural (Nat.ceil value)) ∧
      after.output = before.output ∧ after.register .fresh = before.register .fresh ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧ trace.length ≤ 23 ∧
      trace.IsChain (fun a b => step Program.program input a = some b) ∧
      (∀ state ∈ trace, StateBounds 64 B state) ∧
      (∀ state ∈ trace, MemoryProgress R before state) ∧
      after.heap = Function.update before.heap target (.natural (Nat.ceil value)) ∧
      after.live = insert target before.live := by
  let terminal := ceilCoreResult before 0 source target value
  let destination := if value.num.natAbs % value.den = 0 then pc join else pc increment
  let middle : State := {terminal with pc := destination}
  have executed : linearExecute input (ceilCore source target) before = some terminal :=
    ceilCore_execute input before 0 source target value fresh
      (by simpa only [Nat.zero_add] using sourceValue.1)
      (by simpa only [Nat.zero_add] using sourceValue.2)
  have fields := ceilCoreResult_fields before 0 source target value
  have coreBounds := ceilCore_prefix_bounds input before source target 64 B value bounded fresh
    sourceValue.1 sourceValue.2 sourceInside targetInside addressBits encoding
  have coreFrame := ceilCore_prefix_memory R input before source target value inside fresh sourceValue
  have middleBound : StateBounds 64 B middle := (coreBounds.final executed).with_pc destination
  have middleFrame : MemoryProgress R before middle := (coreFrame.final executed).with_pc destination
  have middleHeap : middle.heap = Function.update before.heap target
      (.natural (value.num.natAbs / value.den)) := by
    simpa only [middle, terminal, Nat.zero_add] using fields.1
  have middleLive : middle.live = insert target before.live := by
    simpa only [middle, terminal, Nat.zero_add] using fields.2.1
  have middleFresh : middle.register .fresh = .natural 0 := fields.2.2.1.trans fresh
  have quotient : Search.SlotHas middle target (.natural (value.num.natAbs / value.den)) := by
    constructor
    · rw [middleLive]; exact Finset.mem_insert_self _ _
    · rw [middleHeap, Function.update_self]
  have oneMiddle : Search.SlotHas middle 14 (.natural 1) := by
    constructor
    · rw [middleLive]; exact Finset.mem_insert_of_mem one.1
    · rw [middleHeap, Function.update_of_ne (Ne.symm notOne)]; exact one.2
  have incrementBounds := natBinarySlots_prefix_bounds input middle target 14 target 64 B .add
    (value.num.natAbs / value.den) 1 (value.num.natAbs / value.den + 1)
    middleBound middleFresh quotient.1 oneMiddle.1 quotient.2 oneMiddle.2 targetInside
    (by decide) targetInside addressBits (quotient_succ_bits value B encoding) rfl
  let memory : SlotMemory := ⟨middle.heap, middle.live⟩
  let next := memory.write target (.natural (value.num.natAbs / value.den + 1))
  have matched : MemoryMatch middle memory := ⟨rfl, rfl, middleFresh⟩
  have evaluated : (SlotCommand.natural .add target 14 target).eval memory = some next :=
    natural_eval memory .add target 14 target _ _ _ quotient oneMiddle rfl
  have incrementFrame : LinearPrefixMemory R input (natBinarySlots .add target 14 target) middle :=
    command_prefix_memory R (.natural .add target 14 target) input middle memory next matched evaluated inside
  obtain ⟨after, trace, head, last, length, chain, afterPc, heap, live, afterFresh,
    output, members, afterShape⟩ := Search.ceiling_pages_trace input start increment join startInside
      incrementInside source target notOne value nonnegative coreLayout incrementLayout
      before location fresh sourceValue one
  have afterBound : StateBounds 64 B after := by
    rcases afterShape with same | ⟨lastTerminal, lastExecuted, lastShape⟩
    · simpa only [same] using middleBound
    · rw [lastShape]; exact (incrementBounds.final lastExecuted).with_pc (pc join)
  have afterFrame : MemoryProgress R before after := progress_of_write R before after target
    (.natural (Nat.ceil value)) inside heap live
  refine ⟨after, trace, afterPc, ⟨?_, ?_⟩, output, afterFresh,
    head, last, length, chain, ?_, ?_, heap, live⟩
  · rw [live]; exact Finset.mem_insert_self _ _
  · rw [heap, Function.update_self]
  · intro state member
    rcases members state member with (same | ⟨count, _, actual⟩) | (same | ⟨count, _, actual⟩)
    · simpa only [same] using middleBound
    · exact coreBounds count state actual
    · simpa only [same] using afterBound
    · exact incrementBounds count state actual
  · intro state member
    rcases members state member with (same | ⟨count, _, actual⟩) | (same | ⟨count, _, actual⟩)
    · simpa only [same] using middleFrame
    · exact coreFrame count state actual
    · simpa only [same] using afterFrame
    · exact middleFrame.trans (incrementFrame count state actual)

end PDROC.D27Prepare.Q
