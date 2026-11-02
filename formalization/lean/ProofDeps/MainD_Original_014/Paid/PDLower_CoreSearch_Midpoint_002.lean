module

public import Paid.PDLower_CoreSearch_TargetMemory_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute linearExecute_append storeSlotResult)

namespace PDLower.CoreSearch

def midpointCommands : List HeaderCommand :=
  [.constant 39 (.rational (1/2)),.rational .add 14 15 24,.rational .multiply 24 39 24]

def midpointValues (values : ℕ→Cell) (lower upper : ℚ) : ℕ→Cell :=
  let one := Function.update values 39 (.rational (1/2))
  let two := Function.update one 24 (.rational (lower+upper))
  Function.update two 24 (.rational ((lower+upper)/2))

def midpointResult (before : State) (lower upper : ℚ) : State :=
  let one := constantSlotResult before 0 39 (.rational (1/2))
  let two := ratBinarySlotsResult one 0 14 15 24 (lower+upper)
  ratBinarySlotsResult two 0 24 39 24 ((lower+upper)/2)

theorem midpointCommands_valid : ∀ command∈midpointCommands,command.Valid := by
  intro command member
  simp only [midpointCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same|same|same <;> subst command <;> dsimp only [HeaderCommand.Valid,headerWords] <;> decide

theorem midpointCommands_targets : ∀ command∈midpointCommands,commandTarget command∈scalarRegion := by
  intro command member
  simp only [midpointCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same|same|same <;> subst command <;> decide

theorem midpointCode_length : (headerCode midpointCommands).length=24 := rfl

theorem midpointCommands_eval (values : ℕ→Cell) (lower upper : ℚ)
    (lowerValue : values 14=.rational lower) (upperValue : values 15=.rational upper) :
    headerEval midpointCommands values=some (midpointValues values lower upper) := by
  simp [midpointCommands,headerEval,HeaderCommand.eval,Cell.rat?,RatOp.eval,lowerValue,upperValue,midpointValues,div_eq_mul_inv]

theorem midpointValues_value (values : ℕ→Cell) (lower upper : ℚ) :
    midpointValues values lower upper 24=.rational ((lower+upper)/2) := by simp [midpointValues]

theorem midpointResult_total (before : State) (lower upper : ℚ) :
    (midpointResult before lower upper).register .total=.rational ((lower+upper)/2) := by
  simp [midpointResult,ratBinarySlotsResult,storeSlotResult,State.set]

theorem midpoint_execute (input : List Cell) (before : State) (values : ℕ→Cell) (lower upper : ℚ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (lowerValue : values 14=.rational lower) (upperValue : values 15=.rational upper) :
    linearExecute input (headerCode midpointCommands) before=some (midpointResult before lower upper) := by
  let one := constantSlotResult before 0 39 (.rational (1/2))
  let firstValues := Function.update values 39 (.rational (1/2))
  have firstRun := constantSlot_execute input before 0 39 (.rational (1/2)) fresh
  have firstHeader : Header one 0 firstValues := header.constantSlot 39 (.rational (1/2))
  have firstFresh : one.register .fresh=.natural 0 := (constantSlotResult_fields before 0 39 (.rational (1/2))).2.2.1.trans fresh
  have second := firstHeader.ratBinarySlots input 14 15 24 .add lower upper (lower+upper)
    (by decide) (by decide) (by simp [firstValues,lowerValue]) (by simp [firstValues,upperValue]) firstFresh rfl
  let two := ratBinarySlotsResult one 0 14 15 24 (lower+upper)
  let secondValues := Function.update firstValues 24 (.rational (lower+upper))
  have secondHeader : Header two 0 secondValues := second.2
  have secondFresh : two.register .fresh=.natural 0 := (ratBinarySlotsResult_base one 0 14 15 24 (lower+upper)).trans firstFresh
  have third := secondHeader.ratBinarySlots input 24 39 24 .multiply (lower+upper) (1/2) ((lower+upper)/2)
    (by decide) (by decide) (by simp [secondValues]) (by simp [secondValues,firstValues]) secondFresh
    (by simp [RatOp.eval,div_eq_mul_inv])
  simp only [midpointCommands,headerCode,List.flatMap_cons,List.flatMap_nil,List.append_nil,HeaderCommand.code]
  rw [linearExecute_append,firstRun,Option.bind_some]
  change linearExecute input (ratBinarySlots .add 14 15 24++ratBinarySlots .multiply 24 39 24) one=
    some (midpointResult before lower upper)
  rw [linearExecute_append,second.1,Option.bind_some]
  exact third.1

/-- Original source midpoint, from the real live cells14/15. One fetched
24-op trace writes24 and39 only, preserves all original prepared/copy
cells at every prefix, and leaves the true middle penalty in .total for
Root039's actual dynamic solver call. No source penalty enters the code. -/
theorem midpoint_trace (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (lower upper : ℚ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (lowerValue : values 14=.rational lower) (upperValue : values 15=.rational upper)
    (fetched : FetchesCode program before.pc (headerCode midpointCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤375 ∧
      Header after 0 (midpointValues values lower upper) ∧ after.register .fresh=.natural 0 ∧
      after.pc=before.pc+24 ∧ after.register .total=.rational ((lower+upper)/2) ∧
      after.heap 24=.rational ((lower+upper)/2) ∧ after.output=before.output ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  obtain ⟨trace,after,head,last,chain,cost,run,afterHeader,afterFresh,pc,output,memory⟩ :=
    commands_trace_scalar midpointCommands program input before values (midpointValues values lower upper)
      midpointCommands_valid midpointCommands_targets header fresh (midpointCommands_eval values lower upper lowerValue upperValue) fetched
  have direct := midpoint_execute input before values lower upper header fresh lowerValue upperValue
  have equal : after=midpointResult before lower upper := Option.some.inj (run.symm.trans direct)
  have total : after.register .total=.rational ((lower+upper)/2) := equal.symm ▸ midpointResult_total before lower upper
  have value := (afterHeader.value 24 (by decide)).trans (midpointValues_value values lower upper)
  exact ⟨trace,after,head,last,chain,by simpa only [midpointCode_length] using cost,afterHeader,afterFresh,
    by simpa only [midpointCode_length] using pc,total,value,output,memory⟩

end PDLower.CoreSearch
