module

public import Paid.PDROC_D27Prepare_Tail_001
public import Paid.PDROC_D27Prepare_Search_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.D27Prepare.FloorRun

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute linearExecute_append)
open PDMenu.ComputeFrame
open Program Memory Tail

/-- The actual page37 first computes the original signed floor and then
branches on its real strict-positivity comparison. In particular, a zero
floor takes page38 before any rational division can be executed. -/
theorem signed_floor_page_trace (input : List Cell) (P : Parameters) (fee : ℚ)
    (before : State) (memory : SlotMemory) (matched : MemoryMatch before memory)
    (location : before.pc = pc 37)
    (hz : Has memory 12 (.rational (P.zeroChargeRisk fee)))
    (hr : Has memory 3 (.rational P.certificate.risk))
    (hf : Has memory 43 (.rational (P.firstChargeFloor fee)))
    (hzero : Has memory 16 (.rational 0)) :
    ∃ (arithmetic terminal after : State) (trace : List State),
      MemoryMatch arithmetic (positiveFloorNext memory P fee) ∧
      linearExecute input (slotSequenceCode positiveFloorCommands) before = some arithmetic ∧
      linearExecute input (ratCompareSlots .less 16 44) arithmetic = some terminal ∧
      MemoryMatch after (positiveFloorNext memory P fee) ∧
      after.pc = (if (Comparison.less.rat 0 (P.positiveValueFloor fee)) then (pc 39) else (pc 38)) ∧
      after = {terminal with pc := after.pc} ∧ after.output = before.output ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧ trace.length = 29 ∧
      trace.IsChain (fun a b => step program input a = some b) ∧
      ∀ state ∈ trace, state = after ∨ ∃ count ≤ 27,
        linearExecute input (positiveFloorSetup.take count) before = some state := by
  obtain ⟨arithmetic, arithmeticExecute, arithmeticMatch, arithmeticOutput, arithmeticPc⟩ :=
    slotSequence_realize positiveFloorCommands input before memory (positiveFloorNext memory P fee)
      matched (positiveFloor_body_eval memory P fee hz hr hf)
  have floorHas : Has (positiveFloorNext memory P fee) 44 (.rational (P.positiveValueFloor fee)) :=
    Has.write_same _ _ _
  have zeroHas : Has (positiveFloorNext memory P fee) 16 (.rational 0) := by
    apply Has.write_other
    · exact Has.write_other memory 16 32 (.rational 0)
        (.rational (P.zeroChargeRisk fee - P.certificate.risk)) hzero (by decide)
    · decide
  have zeroSlot := match_has arithmetic (positiveFloorNext memory P fee) 16 (.rational 0) arithmeticMatch zeroHas
  have floorSlot := match_has arithmetic (positiveFloorNext memory P fee) 44
    (.rational (P.positiveValueFloor fee)) arithmeticMatch floorHas
  let value := Comparison.less.rat 0 (P.positiveValueFloor fee)
  let terminal := comparisonResult arithmetic 0 16 44 value
  have comparisonExecute : linearExecute input (ratCompareSlots .less 16 44) arithmetic = some terminal :=
    ratCompareSlots_execute input arithmetic 0 16 44 0 (P.positiveValueFloor fee) .less arithmeticMatch.base
      (by simpa using zeroSlot.1) (by simpa using floorSlot.1)
      (by simpa using zeroSlot.2) (by simpa using floorSlot.2)
  have fields := comparisonResult_fields arithmetic 0 16 44 value
  have executed : linearExecute input positiveFloorSetup before = some terminal := by
    rw [← positiveFloor_compiled, linearExecute_append, arithmeticExecute, Option.bind_some]
    exact comparisonExecute
  have straight : StraightCode positiveFloorSetup := by
    rw [← positiveFloor_compiled]
    intro instruction member
    rcases List.mem_append.mp member with arithmeticMember | comparisonMember
    · exact slotSequence_straight positiveFloorCommands instruction arithmeticMember
    · exact ratCompareSlots_straight .less 16 44 instruction comparisonMember
  have fetch : FetchesCode program before.pc positiveFloorSetup := by
    rw [location]
    exact fetches_page_part 37 (by decide) [] positiveFloorSetup (branch 38 39) rfl
  have terminalPc : terminal.pc = pc 37 + 27 := by
    have bodyLength : (slotSequenceCode positiveFloorCommands).length = 20 := rfl
    have comparisonPc := fields.2.2.2.2.1
    change terminal.pc = arithmetic.pc + 7 at comparisonPc
    omega
  have controlFetch : program[terminal.pc]? = some (.branchZero .flag (pc 38) (pc 39)) := by
    rw [terminalPc]
    exact fetches_page 37 (by decide) 27 (by decide)
  let after : State := {terminal with pc := if value then (pc 39) else (pc 38)}
  have control : step program input terminal = some after := by
    have actual := branch_step input terminal (pc 38) (pc 39) (if value then 1 else 0)
      controlFetch fields.2.2.2.1
    cases hvalue : value <;> simpa [after, hvalue] using actual
  obtain ⟨trace, head, last, length, chain, members⟩ :=
    Search.fragment_control_trace input positiveFloorSetup straight before terminal after fetch executed control
  have afterMatch : MemoryMatch after (positiveFloorNext memory P fee) :=
    ⟨fields.1.trans arithmeticMatch.heap, fields.2.1.trans arithmeticMatch.live,
      fields.2.2.1.trans arithmeticMatch.base⟩
  refine ⟨arithmetic, terminal, after, trace, arithmeticMatch, arithmeticExecute, comparisonExecute,
    afterMatch, rfl, rfl, fields.2.2.2.2.2.trans arithmeticOutput, head, last, ?_, chain, ?_⟩
  · simpa only [show positiveFloorSetup.length = 27 from rfl] using length
  · simpa only [show positiveFloorSetup.length = 27 from rfl] using members

end PDROC.D27Prepare.FloorRun
