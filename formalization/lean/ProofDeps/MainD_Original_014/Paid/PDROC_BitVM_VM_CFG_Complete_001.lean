module

public import Paid.PDROC_BitVM_VM_CFG_Run_003
public import Paid.PDROC_BitVM_VM_CFG_Refinement_004
public import Paid.PDROC_BitVM_VM_CFG_Refinement_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Complete

open Turing PDROC.BitVM.Common.IO PaperProofs.Paid.Computation

/-- Original PC is only a proof relation to a genuine finite-code entry.
No RAM state, unbounded PC, prefix, event list or fuel is in sigma. -/
def Entry (backend : ISA.RatBackend) (code : Program) (logical : PaperProofs.Paid.Computation.State)
    (physical : Program.State backend code) : Prop :=
  ∃ pc : Program.PC code, logical.pc = pc.val ∧ physical.l = some (Program.entry backend code pc)

def LocalStep (backend : ISA.RatBackend) (core : Bool) (code : Program) (input : List Cell) (C d : ℕ) : Prop :=
  ∀ (logical next : PaperProofs.Paid.Computation.State) (instruction : Instruction)
    (events : List Log.HeapEvent) (physical : Program.State backend code),
    code[logical.pc]? = some instruction → step code input logical = some next → next.pc < code.size →
    Source.Ready input logical events physical.stk → Entry backend code logical physical →
    ∃ after : Program.State backend code, Entry backend code next after ∧
      Source.Ready input next (events ++ (Log.eventOf instruction logical).toList) after.stk ∧
      ∃ path : ActualPath (TM2.step (Program.program backend core code)) physical after,
        path.posts.length ≤ C * (Kernel.NatInstruction.dataSize physical.stk + (encodeBits input).length + 1)^d

def LocalHalt (backend : ISA.RatBackend) (core : Bool) (code : Program) (input : List Cell) (C d : ℕ) : Prop :=
  ∀ (logical : PaperProofs.Paid.Computation.State) (events : List Log.HeapEvent) (physical : Program.State backend code),
    code[logical.pc]? = some .halt → Source.Ready input logical events physical.stk → Entry backend code logical physical →
    ∃ after : Program.State backend code, TM2.step (Program.program backend core code) after = none ∧
      Source.Ready input logical events after.stk ∧
      ∃ path : ActualPath (TM2.step (Program.program backend core code)) physical after,
        path.posts.length ≤ C * (Kernel.NatInstruction.dataSize physical.stk + (encodeBits input).length + 1)^d

/-- C,d depend only on fixed backend/core/code, BEFORE all inputs.
Input6/13 is correctly scoped here: we do not claim the unguarded
all-input StepPolynomial contract of Run003. Both callbacks below are
discharged by the actual compiled FullCFG step and terminal theorems. -/
theorem local_callbacks (backend : ISA.RatBackend) (core : Bool) (code : Program) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ ∀ input : List Cell,
      input.length = Log.BankMount.fieldCount core →
      LocalStep backend core code input C d ∧ LocalHalt backend core code input C d := by
  obtain ⟨stepC, stepD, stepPositiveC, stepPositiveD, stepRun⟩ :=
    Refinement.source_step_polynomial backend core code
  obtain ⟨haltC, haltD, haltPositiveC, haltPositiveD, haltRun⟩ :=
    Refinement.fetched_halt_polynomial backend core code
  let C := stepC + haltC
  let d := stepD + haltD
  refine ⟨C, d, by dsimp only [C]; omega, by dsimp only [d]; omega, ?_⟩
  intro input size
  constructor
  · intro logical next instruction events physical fetched success valid ready related
    obtain ⟨pc, position, atEntry⟩ := related
    rcases physical with ⟨label, store, contents⟩
    change label = some (Program.entry backend code pc) at atEntry
    subst label
    have fetchedSyntax : (code[pc.val]'pc.isLt) = instruction := by
      apply Option.some.inj
      simpa only [position, Array.getElem?_eq_getElem pc.isLt] using fetched
    obtain ⟨run, final, nextStore, path, _localActual, nextReady, time⟩ :=
      stepRun pc store input logical next events contents size ready position success valid
    let after := Program.atEntry backend code ⟨next.pc, valid⟩ nextStore (Cleanup.cleaned final.stk)
    refine ⟨after, ⟨⟨next.pc, valid⟩, rfl, rfl⟩, ?_, path, ?_⟩
    · change Source.Ready input next (events ++ (Log.eventOf instruction logical).toList) (Cleanup.cleaned final.stk)
      simpa only [fetchedSyntax] using nextReady
    · have positive : 1 ≤ Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1 := by omega
      have coefficient : stepC ≤ C := by dsimp only [C]; omega
      have degree : stepD ≤ d := by dsimp only [d]; omega
      exact time.trans (Nat.mul_le_mul coefficient (Nat.pow_le_pow_right positive degree))
  · intro logical events physical fetched ready related
    obtain ⟨pc, position, atEntry⟩ := related
    rcases physical with ⟨label, store, contents⟩
    change label = some (Program.entry backend code pc) at atEntry
    subst label
    obtain ⟨terminal, halted, finalReady, path, time⟩ :=
      haltRun pc store input logical events contents ready position fetched
    refine ⟨terminal, halted, finalReady, path, ?_⟩
    have positive : 1 ≤ Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1 := by omega
    have coefficient : haltC ≤ C := by dsimp only [C]; omega
    have degree : haltD ≤ d := by dsimp only [d]; omega
    exact time.trans (Nat.mul_le_mul coefficient (Nat.pow_le_pow_right positive degree))

/-- Source Runs supplies code nonemptiness. The native boot is ALREADY
the literalPC0 entry; this equality changes no tape or finite store and
its next real entry/reset instruction remains part of FullCFG execution. -/
theorem before_at_zero (backend : ISA.RatBackend) (code : Program) (contents : ISA.Stack → List Bool)
    (positive : 0 < code.size) :
    Program.before backend code contents =
      Program.atEntry backend code ⟨0, positive⟩ (Program.initial backend code) contents := by
  unfold Program.before Program.start
  rw [Control.literalPC_of_lt code 0 positive]
  rfl

theorem before_related (backend : ISA.RatBackend) (code : Program) (contents : ISA.Stack → List Bool)
    (positive : 0 < code.size) : Entry backend code PaperProofs.Paid.Computation.initial (Program.before backend code contents) := by
  rw [before_at_zero backend code contents positive]
  exact ⟨⟨0, positive⟩, rfl, rfl⟩

end PDROC.BitVM.VM.CFG.Complete
