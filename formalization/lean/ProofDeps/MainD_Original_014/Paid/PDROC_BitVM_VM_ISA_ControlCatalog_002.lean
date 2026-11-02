module

public import Paid.PDROC_BitVM_VM_ISA_ControlCatalog_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.ControlCatalog

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-! SOURCE-ONLY proof handoff. These are semantic/resource relations;
none is called by program/observedNext, and no logical RAM state/value is
introduced into the machine's finite labels or runtime store. -/

def NextMatches (code : Program) (choice : Option (Control.PC code)) (target : Nat) : Prop :=
  match choice with
  | some actual => actual.val = target
  | none => code.size ≤ target

theorem literal_matches (code : Program) (target : Nat) :
    NextMatches code (Control.literalPC code target) target := by
  by_cases bound : target < code.size
  · rw [Control.literalPC_of_lt code target bound]
    rfl
  · rw [Control.literalPC_outside code target (by omega)]
    exact Nat.not_lt.mp bound

theorem searched_matches (code : Program) (query : Nat) (choice : Option (Control.PC code))
    (meaning : Control.Indirect.SearchMeaning code query 0 choice) : NextMatches code choice query := by
  cases choice with
  | some actual => exact meaning.1
  | none =>
    change code.size ≤ query
    by_contra outside
    have bound : query < code.size := by omega
    exact meaning ⟨query, bound⟩ (Nat.zero_le _) rfl

theorem execute_branch_matches (code : Program) (input : List Cell)
    (logical next : PaperProofs.Paid.Computation.State) (condition : Register) (whenZero whenNonzero : Nat)
    (success : Instruction.execute input (.branchZero condition whenZero whenNonzero) logical = some next) :
    NextMatches code (rawObservedNext code (.branchZero condition whenZero whenNonzero)
      (Kernel.Branch.captured (encodeCellBits (logical.register condition)))) next.pc := by
  cases value : logical.register condition with
  | natural query =>
    have actual : Instruction.execute input (.branchZero condition whenZero whenNonzero) logical =
        some {logical with pc := if query = 0 then whenZero else whenNonzero} :=
      Kernel.Control.original_branch_execute input logical condition whenZero whenNonzero query value
    have same : next = {logical with pc := if query = 0 then whenZero else whenNonzero} :=
      Option.some.inj (success.symm.trans actual)
    subst next
    simpa only [observed_branch_natural] using
      literal_matches code (if query = 0 then whenZero else whenNonzero)
  | rational query => simp [Instruction.execute, value, Cell.nat?] at success

theorem execute_jump_matches (code : Program) (input : List Cell)
    (logical next : PaperProofs.Paid.Computation.State) (target : Nat)
    (success : Instruction.execute input (.jump target) logical = some next) :
    NextMatches code (rawObservedNext code (.jump target) ()) next.pc := by
  have same : next = {logical with pc := target} := Option.some.inj success.symm
  subst next
  exact literal_matches code target

/-- This uses the flag's WHOLE actual scanner meaning. A successful
original step is used only as a proof specification, never as a runtime
evaluator or an answer/target fed to the indirect machine. -/
theorem execute_indirect_matches (code : Program) (input : List Cell)
    (logical next : PaperProofs.Paid.Computation.State) (source : Register)
    (flags : Control.Indirect.Store code)
    (meaning : Control.Indirect.JumpMeaning code (logical.register source) (Control.Indirect.selected code flags))
    (success : Instruction.execute input (.jumpIndirect source) logical = some next) :
    NextMatches code (rawObservedNext code (.jumpIndirect source) flags) next.pc := by
  cases value : logical.register source with
  | natural query =>
    have actual : Instruction.execute input (.jumpIndirect source) logical = some {logical with pc := query} := by
      simp [Instruction.execute, value, Cell.nat?]
    have same : next = {logical with pc := query} := Option.some.inj (success.symm.trans actual)
    subst next
    apply searched_matches
    simpa only [Control.Indirect.JumpMeaning, value, rawObservedNext] using meaning
  | rational query => simp [Instruction.execute, value, Cell.nat?] at success

/-- Exact catalogue-indexed whole indirect path. initial is a fixed
finite default; reset is STILL executed by the real callee, not omitted
because a proof happened to know that default. -/
theorem indirect_runs (code : Program) (source : Register) (value : Cell)
    (contents : Stack → List Bool)
    (register : contents (Kernel.RegisterGlobal.registerSlot source) = encodeCellBits value) :
    ∃ (run : List (TM2.Cfg Alphabet (LocalLabel code (.jumpIndirect source)) (LocalStore code (.jumpIndirect source))))
      (final : TM2.Cfg Alphabet (LocalLabel code (.jumpIndirect source)) (LocalStore code (.jumpIndirect source))),
      run.head? = some ⟨some (rawStart code (.jumpIndirect source)), rawInitial code (.jumpIndirect source), contents⟩ ∧
      run.IsChain (fun before after => TM2.step (rawProgram code (.jumpIndirect source)) before = some after) ∧
      run.getLast? = some final ∧ TM2.step (rawProgram code (.jumpIndirect source)) final = none ∧ final.l = none ∧
      final.stk = Control.Indirect.cleared contents ∧
      Control.Indirect.JumpMeaning code value (rawObservedNext code (.jumpIndirect source) final.var) ∧
      run.length ≤ Control.Indirect.scratchCost contents + 3 * (encodeCellBits value).length +
        code.size * Control.Indirect.candidateBudget code + 34 :=
  Control.Indirect.cell_runs code source value (rawInitial code (.jumpIndirect source)) contents register

theorem indirect_frame (code : Program) (source : Register) (value : Cell)
    (contents : Stack → List Bool)
    (register : contents (Kernel.RegisterGlobal.registerSlot source) = encodeCellBits value) :
    ∃ (run : List (Control.Indirect.State code)) (final : Control.Indirect.State code),
      run.head? = some ⟨some (rawStart code (.jumpIndirect source)), rawInitial code (.jumpIndirect source), contents⟩ ∧
      run.IsChain (fun before after => TM2.step (rawProgram code (.jumpIndirect source)) before = some after) ∧
      run.getLast? = some final ∧ final.l = none ∧
      (∀ reg : Register, final.stk (Kernel.RegisterGlobal.registerSlot reg) = contents (Kernel.RegisterGlobal.registerSlot reg)) ∧
      (∀ role : Stack, 1 ≤ role.val ∧ role.val < 24 → final.stk role = contents role) ∧
      Control.Indirect.JumpMeaning code value (rawObservedNext code (.jumpIndirect source) final.var) := by
  obtain ⟨run, final, head, chain, last, halt, registers, frame, _, meaning, _⟩ :=
    Control.Indirect.original_registers_preserved code source value (rawInitial code (.jumpIndirect source)) contents register
  refine ⟨run, final, head, chain, last, halt, registers, ?_, meaning⟩
  intro role safeRole
  apply frame role
  intro index
  fin_cases index <;>
    (intro same; have values := congrArg Fin.val same; simp [Control.Indirect.clearSlot] at values; omega)

/-- Fixed source constants precede caller data. Every old scratch byte
and runtime register word is charged, with no provided bit width or fuel. -/
theorem indirect_resource (code : Program) (source : Register) :
    ∃ C : Nat, 0 < C ∧ ∀ (value : Cell) (contents : Stack → List Bool),
      contents (Kernel.RegisterGlobal.registerSlot source) = encodeCellBits value →
      ∃ (run : List (Control.Indirect.State code)) (final : Control.Indirect.State code),
        run.head? = some ⟨some (rawStart code (.jumpIndirect source)), rawInitial code (.jumpIndirect source), contents⟩ ∧
        run.IsChain (fun before after => TM2.step (rawProgram code (.jumpIndirect source)) before = some after) ∧
        run.getLast? = some final ∧ TM2.step (rawProgram code (.jumpIndirect source)) final = none ∧
        run.length ≤ C * (Kernel.NatInstruction.dataSize contents + 1) := by
  refine ⟨code.size * Control.Indirect.candidateBudget code + 42, by omega, ?_⟩
  intro value contents register
  obtain ⟨run, final, head, chain, last, halt, _, _, _, time⟩ := indirect_runs code source value contents register
  refine ⟨run, final, head, chain, last, halt, time.trans ?_⟩
  have a := Kernel.NatInstruction.dataSize_each contents 24
  have b := Kernel.NatInstruction.dataSize_each contents 26
  have c := Kernel.NatInstruction.dataSize_each contents 27
  have d := Kernel.NatInstruction.dataSize_each contents 28
  have word : (encodeCellBits value).length ≤ Kernel.NatInstruction.dataSize contents := by
    rw [← register]
    exact Kernel.NatInstruction.dataSize_each contents (Kernel.RegisterGlobal.registerSlot source)
  unfold Control.Indirect.scratchCost
  have productNonnegative : 0 ≤ (code.size * Control.Indirect.candidateBudget code) *
      Kernel.NatInstruction.dataSize contents := Nat.zero_le _
  nlinarith

end PDROC.BitVM.VM.ISA.ControlCatalog
