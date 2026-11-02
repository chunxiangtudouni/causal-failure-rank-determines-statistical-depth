module

public import Paid.PDROC_BitVM_VM_CFG_Program_003
public import Paid.PDROC_BitVM_VM_ISA_AllData_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Refinement

open Turing PaperProofs.Paid.Computation

/-! SOURCE ONLY. These relations describe genuine old local paths.
Logical states, source arrays and the proof-only trace are not new
runtime flags or transition evaluators. The machine remains Program002. -/

def instructionOf : Program.Choice → Instruction
  | .inl data => data.val
  | .inr control => control.val

theorem instructionOf_classify (instruction : Instruction) :
    instructionOf (ISA.classify instruction) = instruction := by
  unfold ISA.classify
  split <;> rfl

theorem instructionOf_localChoice (code : Program) (pc : Program.PC code) :
    instructionOf (Program.localChoice code pc) = (code[pc.val]'pc.isLt) :=
  instructionOf_classify _

abbrev LocalState (backend : ISA.RatBackend) (code : Program) (choice : Program.Choice) :=
  TM2.Cfg ISA.Alphabet (Program.ChoiceLabel backend code choice) (Program.ChoiceStore backend code choice)

def localBefore (backend : ISA.RatBackend) (code : Program) (choice : Program.Choice)
    (contents : ISA.Stack → List Bool) : LocalState backend code choice :=
  ⟨some (Program.choiceStart backend code choice), Program.choiceInitial backend code choice, contents⟩

def LocalActualRun (backend : ISA.RatBackend) (core : Bool) (code : Program) (choice : Program.Choice)
    (contents : ISA.Stack → List Bool) (run : List (LocalState backend code choice))
    (final : LocalState backend code choice) : Prop :=
  run.head? = some (localBefore backend code choice contents) ∧
  run.IsChain (fun a b => TM2.step (Program.choiceProgram backend core code choice) a = some b) ∧
  run.getLast? = some final ∧ TM2.step (Program.choiceProgram backend core code choice) final = none

/-- Success of any of the ORIGINAL fifteen data constructors advances
the original PC by exactly one. No control constructor is admitted. -/
theorem data_pc_succ (input : List Cell) (data : ISA.DataInstruction)
    (logical next : PaperProofs.Paid.Computation.State)
    (success : Instruction.execute input data.val logical = some next) : next.pc = logical.pc + 1 := by
  rcases data with ⟨instruction, eligible⟩
  cases instruction with
  | branchZero _ _ _ | jump _ | jumpIndirect _ | halt => cases eligible
  | constant target value | move target source | loadInput target pointer
  | load target pointer | store pointer source | release pointer
  | natOp operation target left right | ratOp operation target left right
  | natCompare comparison target left right | ratCompare comparison target left right
  | natToRat target source | numeratorAbs target source | denominator target source
  | negative target source | output source =>
    simp only [Instruction.execute, PaperProofs.Paid.Computation.State.set,
      Option.bind_eq_bind, Option.bind_eq_some_iff] at success
    grind

/-- AllData.complete identifies semantic/resource witnesses as ONE old
halting path. Its positive source constants precede every caller datum.
The next-PC witness here only verifies the STATIC data successor. -/
theorem data_local (backend : ISA.RatBackend) (core : Bool) (code : Program)
    (pc : Program.PC code) (data : ISA.DataInstruction) :
    ∃ C D : Nat, 0 < C ∧ 0 < D ∧
      ∀ (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
        (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool),
        input.length = Log.BankMount.fieldCount core → Source.Ready input logical events contents →
        logical.pc = pc.val → Instruction.execute input data.val logical = some next →
        ∀ valid : next.pc < code.size,
        ∃ (run : List (LocalState backend code (.inl data))) (final : LocalState backend code (.inl data)),
          LocalActualRun backend core code (.inl data) contents run final ∧
          Source.Observables input next (events ++ (Log.eventOf data.val logical).toList) final.stk ∧
          Program.choiceNext backend code pc (.inl data) final.var = some ⟨next.pc, valid⟩ ∧
          run.length ≤ C * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^D := by
  obtain ⟨C, D, positiveC, positiveD, chosen⟩ := ISA.AllData.complete backend core data
  refine ⟨C, D, positiveC, positiveD, ?_⟩
  intro input logical next events contents size ready position success valid
  obtain ⟨run, final, actual, observed, time⟩ := chosen input logical next events contents size ready success
  have successor : pc.val + 1 = next.pc := by
    rw [data_pc_succ input data logical next success, position]
  refine ⟨run, final, actual, observed, ?_, time⟩
  change Control.literalPC code (pc.val + 1) = some ⟨next.pc, valid⟩
  rw [successor]
  exact Control.literalPC_of_lt code next.pc valid

end PDROC.BitVM.VM.CFG.Refinement
