module

public import Paid.PDROC_D27Prepare_Search_005
public import Paid.PDROC_D27Prepare_Memory_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame

namespace PDROC.D27Prepare.Search

open Program Memory

def ceilingIncrementCommands (target : ℕ) : List SlotCommand :=
  [.natural .add target 14 target]

theorem ceilingIncrement_compiled (target : ℕ) :
    slotSequenceCode (ceilingIncrementCommands target) = natBinarySlots .add target 14 target := rfl

/-- The complete two-page ceiling routine, shared by Q and J. It includes
the actual optional increment and its jump. The intermediate state and
the increment's full-body terminal witness retain all register information. -/
theorem ceiling_pages_trace (input : List Cell) (start increment join : ℕ)
    (startInside : start < pageCount) (incrementInside : increment < pageCount)
    (source target : ℕ) (notOne : target ≠ 14) (value : ℚ) (nonnegative : 0 ≤ value)
    (coreLayout : pageCode start = ceilCore source target ++ branch join increment)
    (incrementLayout : pageCode increment = natBinarySlots .add target 14 target ++ go join)
    (before : State) (location : before.pc = pc start)
    (fresh : before.register .fresh = .natural 0)
    (sourceValue : SlotHas before source (.rational value))
    (one : SlotHas before 14 (.natural 1)) :
    let middle := {ceilCoreResult before 0 source target value with
      pc := if value.num.natAbs % value.den = 0 then pc join else pc increment}
    ∃ (final : State) (trace : List State), trace.head? = some before ∧
      trace.getLast? = some final ∧ trace.length ≤ 23 ∧
      trace.IsChain (fun a b => step Program.program input a = some b) ∧
      final.pc = pc join ∧
      final.heap = Function.update before.heap target (.natural (Nat.ceil value)) ∧
      final.live = insert target before.live ∧
      final.register .fresh = before.register .fresh ∧ final.output = before.output ∧
      (∀ state ∈ trace,
        (state = middle ∨ ∃ count ≤ 10,
          linearExecute input ((ceilCore source target).take count) before = some state) ∨
        (state = final ∨ ∃ count ≤ 10,
          linearExecute input ((natBinarySlots .add target 14 target).take count) middle = some state)) ∧
      (final = middle ∨ ∃ terminal : State,
        linearExecute input (natBinarySlots .add target 14 target) middle = some terminal ∧
          final = {terminal with pc := pc join}) := by
  dsimp only
  let middle := {ceilCoreResult before 0 source target value with
    pc := if value.num.natAbs % value.den = 0 then pc join else pc increment}
  obtain ⟨first, firstHead, firstLast, firstLength, firstChain,
    middleHeap, middleLive, middleFresh, middleOutput, firstPrefixes⟩ :=
    ceil_core_page_trace input start startInside before location source target join increment
      value coreLayout fresh sourceValue
  have ceiling : value.num.natAbs / value.den +
      (if value.num.natAbs % value.den = 0 then 0 else 1) = Nat.ceil value :=
    ceilingValue_eq value nonnegative
  by_cases remainder : value.num.natAbs % value.den = 0
  · have valueCeiling : value.num.natAbs / value.den = Nat.ceil value := by
      simpa only [ite_eq_left remainder, Nat.add_zero] using ceiling
    refine ⟨middle, first, firstHead, firstLast, ?_, firstChain, ?_, ?_, middleLive,
      middleFresh, middleOutput, ?_, Or.inl rfl⟩
    · omega
    · simp only [middle, ite_eq_left remainder]
    · simpa only [valueCeiling] using middleHeap
    · intro state member
      exact Or.inl (firstPrefixes state member)
  · have valueCeiling : value.num.natAbs / value.den + 1 = Nat.ceil value := by
      simpa only [ite_eq_right remainder] using ceiling
    have middleLocation : middle.pc = pc increment := by simp only [middle, ite_eq_right remainder]
    have middleBase : middle.register .fresh = .natural 0 := middleFresh.trans fresh
    let memory : SlotMemory := ⟨middle.heap, middle.live⟩
    let next := memory.write target (.natural (value.num.natAbs / value.den + 1))
    have matched : MemoryMatch middle memory := ⟨rfl, rfl, middleBase⟩
    have quotient : Has memory target (.natural (value.num.natAbs / value.den)) := by
      constructor
      · change target ∈ middle.live
        rw [middleLive]
        exact Finset.mem_insert_self _ _
      · change middle.heap target = _
        rw [middleHeap, Function.update_self]
    have oneValue : Has memory 14 (.natural 1) := by
      constructor
      · change 14 ∈ middle.live
        rw [middleLive]
        exact Finset.mem_insert_of_mem one.1
      · change middle.heap 14 = _
        rw [middleHeap, Function.update_of_ne (Ne.symm notOne)]
        exact one.2
    have command := natural_eval memory .add target 14 target
      (value.num.natAbs / value.den) 1 (value.num.natAbs / value.den + 1)
      quotient oneValue rfl
    have evaluated : slotSequenceEval (ceilingIncrementCommands target) memory = some next := by
      simp only [ceilingIncrementCommands, slotSequenceEval, command, Option.bind_some, next]
    obtain ⟨final, later, finalMatch, finalPc, finalOutput, laterHead, laterLast,
      laterLength, laterChain, laterPrefixes, terminalWitness⟩ :=
      sequence_page_trace input increment join incrementInside (ceilingIncrementCommands target)
        incrementLayout middle middleLocation memory next matched evaluated
    have finalHeap : final.heap = Function.update before.heap target (.natural (Nat.ceil value)) := by
      rw [finalMatch.heap]
      change Function.update middle.heap target (.natural (value.num.natAbs / value.den + 1)) = _
      rw [middleHeap, Function.update_idem, valueCeiling]
    have finalLive : final.live = insert target before.live := by
      rw [finalMatch.live]
      change insert target middle.live = _
      rw [middleLive, Finset.insert_idem]
    refine ⟨final, joinTrace first later,
      joinTrace_head first later before middle firstHead firstLast laterHead,
      joinTrace_last first later final laterLast, ?_,
      joinTrace_chain Program.program input first later middle firstChain laterChain firstLast laterHead,
      finalPc, finalHeap, finalLive, finalMatch.base.trans fresh.symm,
      finalOutput.trans middleOutput, ?_, Or.inr ?_⟩
    · have laterSize : later.length = 12 := by
        simpa [ceilingIncrement_compiled, natBinarySlots,
          PDLower.CalibrationCompute.loadSlot, PDLower.CalibrationCompute.storeSlot] using laterLength
      simp only [joinTrace, List.length_append, List.length_dropLast, firstLength, laterSize]
      decide
    · intro state member
      rcases List.mem_append.mp member with early | late
      · exact Or.inl (firstPrefixes state (List.mem_of_mem_dropLast early))
      · apply Or.inr
        have bodyLength : (natBinarySlots .add target 14 target).length = 10 := by
          simp [natBinarySlots, PDLower.CalibrationCompute.loadSlot, PDLower.CalibrationCompute.storeSlot]
        simpa only [ceilingIncrement_compiled, bodyLength] using laterPrefixes state late
    · simpa only [ceilingIncrement_compiled] using terminalWitness

end PDROC.D27Prepare.Search
