module

public import Paid.PDCompute_SolverSlotMoves_025

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame

/-- A finite code-generation notation. Each constructor expands to four,
six or ten of the ORIGINAL ISA instructions; it is not a new machine
primitive. The theorem below proves the expansion on actual live cells. -/
inductive HeaderCommand where
  | constant (target : ℕ) (value : Cell)
  | copy (source target : ℕ)
  | rational (operation : RatOp) (left right target : ℕ)

def HeaderCommand.code : HeaderCommand → List Instruction
  | .constant target value => constantSlot target value
  | .copy source target => copySlot source target
  | .rational operation left right target => ratBinarySlots operation left right target

def HeaderCommand.Valid : HeaderCommand → Prop
  | .constant target _ => target < headerWords
  | .copy source target => source < headerWords ∧ target < headerWords
  | .rational _ left right target => left < headerWords ∧ right < headerWords ∧ target < headerWords

def HeaderCommand.eval (command : HeaderCommand) (values : ℕ → Cell) : Option (ℕ → Cell) := do
  match command with
  | .constant target value => pure (Function.update values target value)
  | .copy source target => pure (Function.update values target (values source))
  | .rational operation left right target =>
    let x ← (values left).rat?
    let y ← (values right).rat?
    let value ← operation.eval x y
    pure (Function.update values target (.rational value))

theorem HeaderCommand.code_straight (command : HeaderCommand) : StraightCode command.code := by
  cases command with
  | constant target value => exact constantSlot_straight target value
  | copy source target => exact copySlot_straight source target
  | rational operation left right target => exact ratBinarySlots_straight operation left right target

theorem HeaderCommand.code_length_le (command : HeaderCommand) : command.code.length ≤ 10 := by
  cases command with
  | constant target value => change 4 ≤ 10; decide
  | copy source target => change 6 ≤ 10; decide
  | rational operation left right target => change 10 ≤ 10; decide

theorem HeaderCommand.realize (command : HeaderCommand) (input : List Cell) (before : State)
    (base n k : ℕ) (values next : ℕ → Cell) (valid : command.Valid)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (heval : command.eval values=some next) :
    ∃ after : State, linearExecute input command.code before=some after ∧ Header after base next ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+command.code.length ∧
      Frame before after base n k ∧ after.output=before.output := by
  cases command with
  | constant target value =>
    have hn : Function.update values target value=next := Option.some.inj heval
    subst next
    have fields := constantSlotResult_fields before base target value
    refine ⟨constantSlotResult before base target value,constantSlot_execute input before base target value hbase,
      Header.constantSlot header target value,fields.2.2.1.trans hbase,fields.2.2.2.1,?_,fields.2.2.2.2⟩
    exact slotWrite_frame before _ base target n k value valid fields.1 fields.2.1
  | copy source target =>
    have hn : Function.update values target (values source)=next := Option.some.inj heval
    subst next
    have fields := copySlotResult_fields before base source target
    refine ⟨copySlotResult before base source target,
      copySlot_execute input before base source target hbase (Header.live header source valid.1),
      Header.copySlot header source target valid.1,fields.2.2.1.trans hbase,fields.2.2.2.1,?_,fields.2.2.2.2⟩
    exact slotWrite_frame before _ base target n k _ valid.2 fields.1 fields.2.1
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
        obtain ⟨value,hoperation,hn⟩ := Option.bind_eq_some_iff.mp hh
        have hn' : Function.update values target (.rational value)=next := Option.some.inj hn
        subst next
        have hr := Header.ratBinarySlots header input left right target operation x y value
          valid.1 valid.2.1 hx hy hbase hoperation
        refine ⟨ratBinarySlotsResult before base left right target value,hr.1,hr.2,
          (ratBinarySlotsResult_base ..).trans hbase,ratBinarySlotsResult_pc ..,
          ratBinarySlotsResult_frame before base left right target value n k valid.2.2,
          ratBinarySlotsResult_output ..⟩

end PDCompute.Solver
