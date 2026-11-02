module

public import Paid.PDROC_D27Prepare_Tail_001
public import Paid.PDROC_D27Prepare_Search_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.D27Prepare.Tail

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame
open Program Memory

theorem dyadic_update_trace (input : List Cell) (before : State) (memory : SlotMemory) (i : ℕ)
    (matched : MemoryMatch before memory) (location : before.pc = pc 23)
    (hindex : Has memory 35 (.natural i)) (hone : Has memory 14 (.natural 1))
    (hpower : Has memory 39 (.rational ((1 / 2 : ℚ) ^ i)))
    (hhalf : Has memory 21 (.rational (1 / 2))) :
    ∃ (after : State) (trace : List State), MemoryMatch after (dyadicNext memory i) ∧
      after.pc = pc 22 ∧ after.output = before.output ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.length = 22 ∧ trace.IsChain (fun a b => step program input a = some b) ∧
      (∀ state ∈ trace, state = after ∨ ∃ count ≤ 20,
        linearExecute input (dyadicStep.take count) before = some state) ∧
      ∃ terminal : State, linearExecute input dyadicStep before = some terminal ∧
        after = {terminal with pc := pc 22} := by
  simpa only [dyadicStep_compiled, show dyadicStep.length = 20 from rfl] using
    Search.sequence_page_trace input 23 22 (by decide) dyadicStepCommands rfl before location memory
      (dyadicNext memory i) matched (dyadic_body_eval memory i hindex hone hpower hhalf)

theorem halve_update_trace (input : List Cell) (before : State) (memory : SlotMemory) (x j : ℕ)
    (matched : MemoryMatch before memory) (location : before.pc = pc 44)
    (hx : Has memory 47 (.natural x)) (hj : Has memory 10 (.natural j))
    (htwo : Has memory 15 (.natural 2)) (hone : Has memory 14 (.natural 1)) :
    ∃ (after : State) (trace : List State), MemoryMatch after (halveNext memory x j) ∧
      after.pc = pc 43 ∧ after.output = before.output ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.length = 22 ∧ trace.IsChain (fun a b => step program input a = some b) ∧
      (∀ state ∈ trace, state = after ∨ ∃ count ≤ 20,
        linearExecute input (budgetHalveStep.take count) before = some state) ∧
      ∃ terminal : State, linearExecute input budgetHalveStep before = some terminal ∧
        after = {terminal with pc := pc 43} := by
  simpa only [budgetHalveStep_compiled, show budgetHalveStep.length = 20 from rfl] using
    Search.sequence_page_trace input 44 43 (by decide) budgetHalveStepCommands rfl before location memory
      (halveNext memory x j) matched (halve_body_eval memory x j hx hj htwo hone)

end PDROC.D27Prepare.Tail
