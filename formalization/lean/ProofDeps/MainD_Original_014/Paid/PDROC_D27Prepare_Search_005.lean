module

public import Paid.PDROC_D27Prepare_Search_004
public import Paid.PDROC_D27Prepare_Program_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

namespace PDROC.D27Prepare.Search

/-- Raw and literal constants survive any actual fragment that preserves
these heap addresses, keeps them live, and preserves fresh. -/
theorem RawConstants.transport (P : PaperProofs.Paid.Parameters) (fee : ℚ)
    (before after : State) (raw : RawConstants P fee before)
    (heap : ∀ address, address < 6 ∨ (13 ≤ address ∧ address ≤ 21) →
      after.heap address = before.heap address)
    (live : before.live ⊆ after.live)
    (fresh : after.register .fresh = before.register .fresh) : RawConstants P fee after := by
  have transfer (address : ℕ) (value : Cell)
      (read : address < 6 ∨ (13 ≤ address ∧ address ≤ 21))
      (old : SlotHas before address value) : SlotHas after address value :=
    SlotHas_of_heap_live before after address value old (heap address read) (fun h => live h)
  exact ⟨fresh.trans raw.fresh,
    transfer 0 _ (by decide) raw.stages, transfer 1 _ (by decide) raw.tools,
    transfer 2 _ (by decide) raw.gamma, transfer 3 _ (by decide) raw.risk,
    transfer 4 _ (by decide) raw.reviewFee, transfer 5 _ (by decide) raw.feeValue,
    transfer 13 _ (by decide) raw.natZero, transfer 14 _ (by decide) raw.natOne,
    transfer 15 _ (by decide) raw.natTwo, transfer 16 _ (by decide) raw.ratZero,
    transfer 17 _ (by decide) raw.ratOne, transfer 18 _ (by decide) raw.ratTwo,
    transfer 19 _ (by decide) raw.ratThree, transfer 20 _ (by decide) raw.ratFour,
    transfer 21 _ (by decide) raw.ratHalf⟩

/-- Append one actual fetched control step to a straight fragment. Every
state is a successful literal prefixStates or the actual control successor. -/
theorem fragment_control_trace (input : List Cell) (code : List Instruction)
    (straight : StraightCode code) (before middle after : State)
    (fetch : FetchesCode Program.program before.pc code)
    (execute : linearExecute input code before = some middle)
    (control : step Program.program input middle = some after) :
    ∃ trace : List State, trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.length = code.length + 2 ∧
      trace.IsChain (fun a b => step Program.program input a = some b) ∧
      ∀ state ∈ trace, state = after ∨ ∃ count ≤ code.length,
        linearExecute input (code.take count) before = some state := by
  obtain ⟨first, whole, _wholeEq, _firstHead, firstLast, _firstLength, _firstChain,
    firstPrefix, wholeHead, wholeLast, wholeLength, wholeChain, _wholeTime, wholeMembers⟩ :=
    Program.literal_control_trace input code straight before middle after fetch execute control
  have decomposition : first.dropLast ++ [middle] = first :=
    List.dropLast_append_getLast? middle (by rw [firstLast]; simp)
  refine ⟨whole, wholeHead, wholeLast, wholeLength, wholeChain, ?_⟩
  intro state member
  rcases wholeMembers state member with early | late
  · rw [← decomposition] at early
    rcases List.mem_append.mp early with prefixStates | terminal
    · obtain ⟨count, inside, executed⟩ := firstPrefix state prefixStates
      exact Or.inr ⟨count, inside.le, executed⟩
    · have equal : state = middle := by simpa only [List.mem_singleton] using terminal
      subst state
      exact Or.inr ⟨code.length, le_rfl, by simpa using execute⟩
  · exact Or.inl late

/-- A rational comparison page follows its actual Boolean result. The
entire page must be fetched from the one fixed preparation program. -/
theorem rat_compare_page_trace (input : List Cell) (page : ℕ)
    (inside : page < Program.pageCount) (before : State) (location : before.pc = Program.pc page)
    (comparison : Comparison) (left right whenZero whenNonzero : ℕ) (x y : ℚ)
    (layout : Program.pageCode page =
      Program.ratCompareSlots comparison left right ++ Program.branch whenZero whenNonzero)
    (fresh : before.register .fresh = .natural 0)
    (leftValue : SlotHas before left (.rational x))
    (rightValue : SlotHas before right (.rational y)) :
    let middle := Program.comparisonResult before 0 left right (comparison.rat x y)
    let after := {middle with pc :=
      if (comparison.rat x y) then (Program.pc whenNonzero) else (Program.pc whenZero)}
    ∃ trace : List State, trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.length = 9 ∧ trace.IsChain (fun a b => step Program.program input a = some b) ∧
      after.heap = before.heap ∧ after.live = before.live ∧
      after.register .fresh = before.register .fresh ∧ after.output = before.output ∧
      ∀ state ∈ trace, state = after ∨ ∃ count ≤ 7,
        linearExecute input ((Program.ratCompareSlots comparison left right).take count) before = some state := by
  dsimp only
  let middle := Program.comparisonResult before 0 left right (comparison.rat x y)
  let after := {middle with pc :=
    if (comparison.rat x y) then (Program.pc whenNonzero) else (Program.pc whenZero)}
  have allFetch := Program.fetches_page page inside
  have compareFetch : FetchesCode Program.program before.pc
      (Program.ratCompareSlots comparison left right) := by
    intro offset inCode
    rw [location]
    have fetched := allFetch offset (by rw [layout, List.length_append]; omega)
    rw [layout, List.getElem?_append_left inCode] at fetched
    exact fetched
  have execute : linearExecute input (Program.ratCompareSlots comparison left right) before = some middle :=
    Program.ratCompareSlots_execute input before 0 left right x y comparison fresh
      (by simpa using leftValue.1) (by simpa using rightValue.1)
      (by simpa using leftValue.2) (by simpa using rightValue.2)
  have fields := Program.comparisonResult_fields before 0 left right (comparison.rat x y)
  have controlFetch : Program.program[middle.pc]? =
      some (.branchZero .flag (Program.pc whenZero) (Program.pc whenNonzero)) := by
    have fetched := allFetch 7 (by rw [layout]; change 7 < 8; decide)
    have middlePc : middle.pc = Program.pc page + 7 := by
      dsimp only [middle]
      rw [fields.2.2.2.2.1, location]
    rw [middlePc]
    simpa [layout, Program.ratCompareSlots, PDLower.CalibrationCompute.loadSlot,
      Program.branch] using fetched
  have control : step Program.program input middle = some after := by
    have branched := Program.branch_step input middle (Program.pc whenZero) (Program.pc whenNonzero)
      (if (comparison.rat x y) then 1 else 0) controlFetch fields.2.2.2.1
    cases value : comparison.rat x y <;> simpa [after, value] using branched
  obtain ⟨trace, head, last, length, chain, prefixStates⟩ :=
    fragment_control_trace input (Program.ratCompareSlots comparison left right)
      (Program.ratCompareSlots_straight comparison left right) before middle after compareFetch execute control
  refine ⟨trace, head, last, ?_, chain, fields.1, fields.2.1, fields.2.2.1,
    fields.2.2.2.2.2, ?_⟩
  · simpa [Program.ratCompareSlots, PDLower.CalibrationCompute.loadSlot] using length
  · simpa [Program.ratCompareSlots, PDLower.CalibrationCompute.loadSlot] using prefixStates

/-- A natural comparison page follows its actual Boolean result. The
entire page must be fetched from the one fixed preparation program. -/
theorem nat_compare_page_trace (input : List Cell) (page : ℕ)
    (inside : page < Program.pageCount) (before : State) (location : before.pc = Program.pc page)
    (comparison : Comparison) (left right whenZero whenNonzero : ℕ) (x y : ℕ)
    (layout : Program.pageCode page =
      Program.natCompareSlots comparison left right ++ Program.branch whenZero whenNonzero)
    (fresh : before.register .fresh = .natural 0)
    (leftValue : SlotHas before left (.natural x))
    (rightValue : SlotHas before right (.natural y)) :
    let middle := Program.comparisonResult before 0 left right (comparison.nat x y)
    let after := {middle with pc :=
      if (comparison.nat x y) then (Program.pc whenNonzero) else (Program.pc whenZero)}
    ∃ trace : List State, trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.length = 9 ∧ trace.IsChain (fun a b => step Program.program input a = some b) ∧
      after.heap = before.heap ∧ after.live = before.live ∧
      after.register .fresh = before.register .fresh ∧ after.output = before.output ∧
      ∀ state ∈ trace, state = after ∨ ∃ count ≤ 7,
        linearExecute input ((Program.natCompareSlots comparison left right).take count) before = some state := by
  dsimp only
  let middle := Program.comparisonResult before 0 left right (comparison.nat x y)
  let after := {middle with pc :=
    if (comparison.nat x y) then (Program.pc whenNonzero) else (Program.pc whenZero)}
  have allFetch := Program.fetches_page page inside
  have compareFetch : FetchesCode Program.program before.pc
      (Program.natCompareSlots comparison left right) := by
    intro offset inCode
    rw [location]
    have fetched := allFetch offset (by rw [layout, List.length_append]; omega)
    rw [layout, List.getElem?_append_left inCode] at fetched
    exact fetched
  have execute : linearExecute input (Program.natCompareSlots comparison left right) before = some middle :=
    Program.natCompareSlots_execute input before 0 left right x y comparison fresh
      (by simpa using leftValue.1) (by simpa using rightValue.1)
      (by simpa using leftValue.2) (by simpa using rightValue.2)
  have fields := Program.comparisonResult_fields before 0 left right (comparison.nat x y)
  have controlFetch : Program.program[middle.pc]? =
      some (.branchZero .flag (Program.pc whenZero) (Program.pc whenNonzero)) := by
    have fetched := allFetch 7 (by rw [layout]; change 7 < 8; decide)
    have middlePc : middle.pc = Program.pc page + 7 := by
      dsimp only [middle]
      rw [fields.2.2.2.2.1, location]
    rw [middlePc]
    simpa [layout, Program.natCompareSlots, PDLower.CalibrationCompute.loadSlot,
      Program.branch] using fetched
  have control : step Program.program input middle = some after := by
    have branched := Program.branch_step input middle (Program.pc whenZero) (Program.pc whenNonzero)
      (if (comparison.nat x y) then 1 else 0) controlFetch fields.2.2.2.1
    cases value : comparison.nat x y <;> simpa [after, value] using branched
  obtain ⟨trace, head, last, length, chain, prefixStates⟩ :=
    fragment_control_trace input (Program.natCompareSlots comparison left right)
      (Program.natCompareSlots_straight comparison left right) before middle after compareFetch execute control
  refine ⟨trace, head, last, ?_, chain, fields.1, fields.2.1, fields.2.2.1,
    fields.2.2.2.2.2, ?_⟩
  · simpa [Program.natCompareSlots, PDLower.CalibrationCompute.loadSlot] using length
  · simpa [Program.natCompareSlots, PDLower.CalibrationCompute.loadSlot] using prefixStates

/-- A finite command specification followed by the literal jump of one
fixed page. This instantiates the verified command compiler and the
actual control trace; no search result is an input to the machine. -/
theorem sequence_page_trace (input : List Cell) (page target : ℕ)
    (inside : page < Program.pageCount) (commands : List Program.SlotCommand)
    (layout : Program.pageCode page = Program.slotSequenceCode commands ++ Program.go target)
    (before : State) (location : before.pc = Program.pc page)
    (memory next : Program.SlotMemory) (matched : Program.MemoryMatch before memory)
    (evaluated : Program.slotSequenceEval commands memory = some next) :
    ∃ (after : State) (trace : List State), Program.MemoryMatch after next ∧
      after.pc = Program.pc target ∧ after.output = before.output ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.length = (Program.slotSequenceCode commands).length + 2 ∧
      trace.IsChain (fun a b => step Program.program input a = some b) ∧
      (∀ state ∈ trace, state = after ∨ ∃ count ≤ (Program.slotSequenceCode commands).length,
        linearExecute input ((Program.slotSequenceCode commands).take count) before = some state) ∧
      ∃ terminal : State, linearExecute input (Program.slotSequenceCode commands) before = some terminal ∧
        after = {terminal with pc := Program.pc target} := by
  obtain ⟨middle, execute, middleMatch, middleOutput, middlePc⟩ :=
    Program.slotSequence_realize commands input before memory next matched evaluated
  let after := {middle with pc := Program.pc target}
  have allFetch := Program.fetches_page page inside
  have bodyFetch : FetchesCode Program.program before.pc (Program.slotSequenceCode commands) := by
    intro offset inCode
    rw [location]
    have fetched := allFetch offset (by rw [layout, List.length_append]; omega)
    rw [layout, List.getElem?_append_left inCode] at fetched
    exact fetched
  have controlFetch : Program.program[middle.pc]? = some (.jump (Program.pc target)) := by
    rw [middlePc, location]
    have fetched := allFetch (Program.slotSequenceCode commands).length
      (by rw [layout, List.length_append]; simp only [Program.go, List.length_singleton]; omega)
    simpa only [layout, List.getElem?_append_right (le_refl _), Nat.sub_self,
      Program.go, List.getElem?_cons_zero] using fetched
  have control : step Program.program input middle = some after :=
    Program.jump_step input middle (Program.pc target) controlFetch
  obtain ⟨trace, head, last, length, chain, prefixes⟩ :=
    fragment_control_trace input (Program.slotSequenceCode commands)
      (Program.slotSequence_straight commands) before middle after bodyFetch execute control
  refine ⟨after, trace, ?_, rfl, middleOutput, head, last, length, chain, prefixes, middle, execute, rfl⟩
  exact ⟨middleMatch.heap, middleMatch.live, middleMatch.base⟩

/-- The quotient/remainder ceiling page uses the actual positive rational
denominator. The branch sees the true integer remainder, including zero. -/
theorem ceil_core_page_trace (input : List Cell) (page : ℕ)
    (inside : page < Program.pageCount) (before : State) (location : before.pc = Program.pc page)
    (source target whenZero whenNonzero : ℕ) (value : ℚ)
    (layout : Program.pageCode page =
      Program.ceilCore source target ++ Program.branch whenZero whenNonzero)
    (fresh : before.register .fresh = .natural 0)
    (sourceValue : SlotHas before source (.rational value)) :
    let middle := Program.ceilCoreResult before 0 source target value
    let after := {middle with pc := if value.num.natAbs % value.den = 0
      then (Program.pc whenZero) else (Program.pc whenNonzero)}
    ∃ trace : List State, trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.length = 12 ∧ trace.IsChain (fun a b => step Program.program input a = some b) ∧
      after.heap = Function.update before.heap target (.natural (value.num.natAbs / value.den)) ∧
      after.live = insert target before.live ∧
      after.register .fresh = before.register .fresh ∧ after.output = before.output ∧
      ∀ state ∈ trace, state = after ∨ ∃ count ≤ 10,
        linearExecute input ((Program.ceilCore source target).take count) before = some state := by
  dsimp only
  let middle := Program.ceilCoreResult before 0 source target value
  let after := {middle with pc := if value.num.natAbs % value.den = 0
    then (Program.pc whenZero) else (Program.pc whenNonzero)}
  have allFetch := Program.fetches_page page inside
  have bodyFetch : FetchesCode Program.program before.pc (Program.ceilCore source target) := by
    intro offset inCode
    rw [location]
    have fetched := allFetch offset (by rw [layout, List.length_append]; omega)
    rw [layout, List.getElem?_append_left inCode] at fetched
    exact fetched
  have execute : linearExecute input (Program.ceilCore source target) before = some middle :=
    Program.ceilCore_execute input before 0 source target value fresh
      (by simpa using sourceValue.1) (by simpa using sourceValue.2)
  have fields := Program.ceilCoreResult_fields before 0 source target value
  have controlFetch : Program.program[middle.pc]? =
      some (.branchZero .flag (Program.pc whenZero) (Program.pc whenNonzero)) := by
    have fetched := allFetch 10 (by rw [layout]; change 10 < 11; decide)
    have middlePc : middle.pc = Program.pc page + 10 := by
      dsimp only [middle]
      rw [fields.2.2.2.2.1, location]
    rw [middlePc]
    simpa [layout, Program.ceilCore, PDLower.CalibrationCompute.loadSlot,
      PDLower.CalibrationCompute.storeSlot, Program.branch] using fetched
  have control : step Program.program input middle = some after :=
    Program.branch_step input middle (Program.pc whenZero) (Program.pc whenNonzero)
      (value.num.natAbs % value.den) controlFetch fields.2.2.2.1
  obtain ⟨trace, head, last, length, chain, prefixes⟩ :=
    fragment_control_trace input (Program.ceilCore source target)
      (Program.ceilCore_straight source target) before middle after bodyFetch execute control
  refine ⟨trace, head, last, ?_, chain, ?_, ?_, fields.2.2.1, fields.2.2.2.2.2, ?_⟩
  · simpa [Program.ceilCore, PDLower.CalibrationCompute.loadSlot,
      PDLower.CalibrationCompute.storeSlot] using length
  · simpa only [Nat.zero_add] using fields.1
  · simpa only [Nat.zero_add] using fields.2.1
  · simpa [Program.ceilCore, PDLower.CalibrationCompute.loadSlot,
      PDLower.CalibrationCompute.storeSlot] using prefixes

end PDROC.D27Prepare.Search
