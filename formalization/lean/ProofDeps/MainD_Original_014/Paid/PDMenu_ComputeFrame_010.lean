module

public import Paid.PDMenu_ComputeFrame_009

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu.ComputeFrame

open PaperProofs.Paid.Computation

/-- Typed one-step interfaces use only the original state and the exact
original operation's success. Aliases between registers are allowed. -/
theorem execute_natOp (operation : NatOp) (target left right : Register) (input : List Cell)
    (before : State) (a b value : ℕ)
    (hleft : before.register left=.natural a) (hright : before.register right=.natural b)
    (hvalue : operation.eval a b=some value) :
    (Instruction.natOp operation target left right).execute input before=
      some (({before with pc:=before.pc+1}).set target (.natural value)) := by
  simp [Instruction.execute,hleft,hright,Cell.nat?,hvalue]

theorem execute_ratOp (operation : RatOp) (target left right : Register) (input : List Cell)
    (before : State) (a b value : ℚ)
    (hleft : before.register left=.rational a) (hright : before.register right=.rational b)
    (hvalue : operation.eval a b=some value) :
    (Instruction.ratOp operation target left right).execute input before=
      some (({before with pc:=before.pc+1}).set target (.rational value)) := by
  simp [Instruction.execute,hleft,hright,Cell.rat?,hvalue]

theorem execute_loadInput (target pointer : Register) (input : List Cell) (before : State)
    (address : ℕ) (value : Cell) (haddress : before.register pointer=.natural address)
    (hfetched : input[address]?=some value) :
    (Instruction.loadInput target pointer).execute input before=
      some (({before with pc:=before.pc+1}).set target value) := by
  simp [Instruction.execute,haddress,Cell.nat?,hfetched]

theorem execute_load (target pointer : Register) (input : List Cell) (before : State)
    (address : ℕ) (haddress : before.register pointer=.natural address) (hlive : address ∈ before.live) :
    (Instruction.load target pointer).execute input before=
      some (({before with pc:=before.pc+1}).set target (before.heap address)) := by
  simp [Instruction.execute,haddress,Cell.nat?,hlive]

theorem execute_store (pointer source : Register) (input : List Cell) (before : State)
    (address : ℕ) (haddress : before.register pointer=.natural address) :
    (Instruction.store pointer source).execute input before=
      some {before with
        heap:=Function.update before.heap address (before.register source)
        live:=insert address before.live
        pc:=before.pc+1} := by
  simp [Instruction.execute,haddress,Cell.nat?]

theorem execute_release (pointer : Register) (input : List Cell) (before : State)
    (address : ℕ) (haddress : before.register pointer=.natural address) :
    (Instruction.release pointer).execute input before=
      some {before with
        heap:=Function.update before.heap address (.natural 0)
        live:=before.live.erase address
        pc:=before.pc+1} := by
  simp [Instruction.execute,haddress,Cell.nat?]

theorem execute_natCompare (comparison : Comparison) (target left right : Register) (input : List Cell)
    (before : State) (a b : ℕ)
    (hleft : before.register left=.natural a) (hright : before.register right=.natural b) :
    (Instruction.natCompare comparison target left right).execute input before=
      some (({before with pc:=before.pc+1}).set target (.natural (if comparison.nat a b then 1 else 0))) := by
  simp [Instruction.execute,hleft,hright,Cell.nat?]

theorem execute_ratCompare (comparison : Comparison) (target left right : Register) (input : List Cell)
    (before : State) (a b : ℚ)
    (hleft : before.register left=.rational a) (hright : before.register right=.rational b) :
    (Instruction.ratCompare comparison target left right).execute input before=
      some (({before with pc:=before.pc+1}).set target (.natural (if comparison.rat a b then 1 else 0))) := by
  simp [Instruction.execute,hleft,hright,Cell.rat?]

theorem execute_natToRat (target source : Register) (input : List Cell) (before : State)
    (value : ℕ) (hsource : before.register source=.natural value) :
    (Instruction.natToRat target source).execute input before=
      some (({before with pc:=before.pc+1}).set target (.rational value)) := by
  simp [Instruction.execute,hsource,Cell.nat?]

theorem execute_branchZero (condition : Register) (zeroPC nonzeroPC : ℕ) (input : List Cell) (before : State)
    (value : ℕ) (hvalue : before.register condition=.natural value) :
    (Instruction.branchZero condition zeroPC nonzeroPC).execute input before=
      some {before with pc:=if value=0 then zeroPC else nonzeroPC} := by
  simp [Instruction.execute,hvalue,Cell.nat?]

theorem execute_jumpIndirect (source : Register) (input : List Cell) (before : State)
    (target : ℕ) (hsource : before.register source=.natural target) :
    (Instruction.jumpIndirect source).execute input before=some {before with pc:=target} := by
  simp [Instruction.execute,hsource,Cell.nat?]

end PDMenu.ComputeFrame
