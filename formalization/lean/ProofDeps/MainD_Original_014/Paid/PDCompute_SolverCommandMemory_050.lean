module

public import Paid.PDCompute_SolverHeaderMemory_049

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)

theorem HeaderCommand.prefix_memory (command : HeaderCommand) (input : List Cell) (before after : State)
    (base : ℕ) (values next : ℕ → Cell) (valid : command.Valid)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (heval : command.eval values=some next) (count : ℕ) (hcount : count ≤ command.code.length)
    (hexec : linearExecute input (command.code.take count) before=some after) :
    HeaderMemory before after base := by
  cases command with
  | constant target value =>
    by_cases short : count < 4
    · have memory := constantSlot_prefix_memory input before after base target value hbase count short hexec
      exact HeaderMemory.of_unchanged base memory.1 memory.2.1 memory.2.2
    · have exactCount : count=4 := by change count ≤ 4 at hcount; omega
      subst count
      have full : linearExecute input (constantSlot target value) before=some after := hexec
      rw [constantSlot_execute input before base target value hbase] at full
      have eq := Option.some.inj full
      subst after
      have fields := constantSlotResult_fields before base target value
      exact HeaderMemory.write header target valid value fields.1 fields.2.1 fields.2.2.2.2
  | copy source target =>
    by_cases short : count < 6
    · have memory := copySlot_prefix_memory input before after base source target hbase
        (header.live source valid.1) count short hexec
      exact HeaderMemory.of_unchanged base memory.1 memory.2.1 memory.2.2
    · have exactCount : count=6 := by change count ≤ 6 at hcount; omega
      subst count
      have full : linearExecute input (copySlot source target) before=some after := hexec
      rw [copySlot_execute input before base source target hbase (header.live source valid.1)] at full
      have eq := Option.some.inj full
      subst after
      have fields := copySlotResult_fields before base source target
      exact HeaderMemory.write header target valid.2 _ fields.1 fields.2.1 fields.2.2.2.2
  | rational operation left right target =>
    cases hx : values left with
    | natural x => simp [HeaderCommand.eval,hx,Cell.rat?] at heval
    | rational x =>
      cases hy : values right with
      | natural y => simp [HeaderCommand.eval,hx,hy,Cell.rat?] at heval
      | rational y =>
        have hh : ((operation.eval x y).bind fun value =>
            some (Function.update values target (.rational value)))=some next := by
          simpa [HeaderCommand.eval,hx,hy,Cell.rat?] using heval
        obtain ⟨value,hoperation,_⟩ := Option.bind_eq_some_iff.mp hh
        have leftValue := (header.value left valid.1).trans hx
        have rightValue := (header.value right valid.2.1).trans hy
        by_cases short : count < 10
        · have memory := ratBinarySlots_prefix_memory input before after base left right target operation x y value
            hbase (header.live left valid.1) (header.live right valid.2.1) leftValue rightValue hoperation
            count short hexec
          exact HeaderMemory.of_unchanged base memory.1 memory.2.1 memory.2.2
        · have exactCount : count=10 := by change count ≤ 10 at hcount; omega
          subst count
          have full : linearExecute input (ratBinarySlots operation left right target) before=some after := hexec
          rw [ratBinarySlots_execute input before base left right target operation x y value hbase
            (header.live left valid.1) (header.live right valid.2.1) leftValue rightValue hoperation] at full
          have eq := Option.some.inj full
          subst after
          exact HeaderMemory.write header target valid.2.2 (.rational value)
            (ratBinarySlotsResult_heap ..) (ratBinarySlotsResult_live ..) (ratBinarySlotsResult_output ..)

end PDCompute.Solver
