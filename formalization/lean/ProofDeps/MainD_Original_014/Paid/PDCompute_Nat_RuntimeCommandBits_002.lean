module
public import Paid.PDCompute_Nat_SlotBits_001
public import Paid.PDCompute_SolverSequenceBits_155
public import Paid.PDCompute_SolverRuntimeCommands_085

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)
open PDROC.CalibrationRow.Operand

/-- Actual finite mixed-command realization, exposing its successful
literal execution rather than postulating a machine or resource run. -/
theorem runtimeCommand_realize (command : RuntimeCommand) (input : List Cell) (before : State)
    (base n k : ℕ) (values next : ℕ → Cell) (valid : command.Valid) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (evaluated : command.eval values=some next) :
    ∃ after : State,linearExecute input command.code before=some after ∧ Header after base next ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+command.code.length ∧
      Frame before after base n k ∧ after.output=before.output := by
  cases command with
  | scalar command => exact command.realize input before base n k values next valid header fresh evaluated
  | natural operation left right target =>
    cases hx : values left with
    | rational x => simp [RuntimeCommand.eval,hx,Cell.nat?] at evaluated
    | natural x =>
      cases hy : values right with
      | rational y => simp [RuntimeCommand.eval,hx,hy,Cell.nat?] at evaluated
      | natural y =>
        have bound : ((operation.eval x y).bind fun result=>some (Function.update values target (.natural result)))=some next:=by
          simpa [RuntimeCommand.eval,hx,hy,Cell.nat?] using evaluated
        obtain ⟨result,computed,same⟩:=Option.bind_eq_some_iff.mp bound
        have equal : Function.update values target (.natural result)=next:=Option.some.inj same
        subst next
        have fields:=PDROC.D27Prepare.Program.natBinarySlotsResult_fields before base left right target result
        exact ⟨natBinarySlotsResult before base left right target x y result,
          natBinarySlots_execute input before base left right target x y result operation values header valid.1 valid.2.1 hx hy fresh computed,
          natBinarySlots_header before base left right target x y result values header,fields.2.2.1.trans fresh,fields.2.2.2.1,
          slotWrite_frame before _ base target n k (.natural result) valid.2.2 fields.1 fields.2.1,fields.2.2.2.2⟩

/-- The scalar branch reuses frozen155. Only the real natural result is
newly bounded; arbitrary prior scratch/header cells retain the same B. -/
theorem runtimeCommand_prefix_safe (command : RuntimeCommand) (input : List Cell) (before : State)
    (base budget : ℕ) (values next : ℕ → Cell) (valid : command.Valid)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (evaluated : command.eval values=some next) (safe : RootD27.Bits.SafeBits before budget)
    (nextBits : HeaderValueBits next budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (pcBits : natBits (before.pc+command.code.length)≤budget) : PrefixSafe input command.code before budget := by
  cases command with
  | scalar command => exact command.prefix_safe input before base budget values next valid header fresh evaluated safe nextBits addressBits pcBits
  | natural operation left right target =>
    cases hx : values left with
    | rational x => simp [RuntimeCommand.eval,hx,Cell.nat?] at evaluated
    | natural x =>
      cases hy : values right with
      | rational y => simp [RuntimeCommand.eval,hx,hy,Cell.nat?] at evaluated
      | natural y =>
        have bound : ((operation.eval x y).bind fun result=>some (Function.update values target (.natural result)))=some next:=by
          simpa [RuntimeCommand.eval,hx,hy,Cell.nat?] using evaluated
        obtain ⟨result,computed,same⟩:=Option.bind_eq_some_iff.mp bound
        have equal : Function.update values target (.natural result)=next:=Option.some.inj same
        subst next
        have resultBits : (.natural result : Cell).bits≤budget:=by simpa only [Function.update_self] using nextBits target valid.2.2
        exact natBinarySlots_prefix_safe input before base budget left right target operation x y result values header fresh
          valid.1 valid.2.1 valid.2.2 hx hy computed safe resultBits addressBits pcBits

theorem runtimeCommand_prefix_memory (command : RuntimeCommand) (input : List Cell) (before after : State)
    (base : ℕ) (values next : ℕ → Cell) (valid : command.Valid) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (evaluated : command.eval values=some next)
    (count : ℕ) (bound : count≤command.code.length)
    (execute : linearExecute input (command.code.take count) before=some after) : HeaderMemory before after base := by
  cases command with
  | scalar command => exact command.prefix_memory input before after base values next valid header fresh evaluated count bound execute
  | natural operation left right target =>
    cases hx : values left with
    | rational x => simp [RuntimeCommand.eval,hx,Cell.nat?] at evaluated
    | natural x =>
      cases hy : values right with
      | rational y => simp [RuntimeCommand.eval,hx,hy,Cell.nat?] at evaluated
      | natural y =>
        have evaluatedBound : ((operation.eval x y).bind fun result=>some (Function.update values target (.natural result)))=some next:=by
          simpa [RuntimeCommand.eval,hx,hy,Cell.nat?] using evaluated
        obtain ⟨result,computed,same⟩:=Option.bind_eq_some_iff.mp evaluatedBound
        have equal : Function.update values target (.natural result)=next:=Option.some.inj same
        subst next
        exact natBinarySlots_prefix_memory input before after base left right target x y result operation values header
          valid.1 valid.2.1 valid.2.2 hx hy fresh computed count bound execute

end PDCompute.NatControl
