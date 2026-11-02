module

public import Paid.PDROC_BitVM_VM_CFG_Refinement_003
public import Paid.PDROC_BitVM_VM_ISA_ControlResources_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Refinement

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Common.IO
open scoped BigOperators

/-! SOURCE ONLY. All constants below depend only on fixed compiled
code/backend/core. They precede ALL input, logical states, actual bytes
and finite caller stores. Occupancy pays the actual SAME-path cleanup;
there is no assumed post-op data bound or global T/B/I oracle. -/

theorem choice_resource (backend : ISA.RatBackend) (core : Bool) (code : Program) (choice : Program.Choice) :
    ∃ C D : Nat, 0 < C ∧ 0 < D ∧
      ∀ (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
        (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool),
        input.length = Log.BankMount.fieldCount core → Source.Ready input logical events contents →
        Instruction.execute input (instructionOf choice) logical = some next →
        ∃ (run : List (LocalState backend code choice)) (final : LocalState backend code choice),
          LocalActualRun backend core code choice contents run final ∧
          run.length ≤ C * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^D := by
  cases choice with
  | inl data => exact ISA.AllData.resource backend core data
  | inr control =>
    obtain ⟨C, D, positiveC, positiveD, chosen⟩ := ISA.ControlResources.resource code control
    refine ⟨C, D, positiveC, positiveD, ?_⟩
    intro input logical next events contents _size ready success
    exact chosen input logical next events contents ready success

/-- Determinism transfers the resource result to ANY actual whole local
halting run at this exact entry. In particular it bounds the semantic
run already embedded by source_step, without selecting a second path. -/
theorem choice_time (backend : ISA.RatBackend) (core : Bool) (code : Program) (choice : Program.Choice) :
    ∃ C D : Nat, 0 < C ∧ 0 < D ∧
      ∀ (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
        (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool),
        input.length = Log.BankMount.fieldCount core → Source.Ready input logical events contents →
        Instruction.execute input (instructionOf choice) logical = some next →
        ∀ (run : List (LocalState backend code choice)) (final : LocalState backend code choice),
          LocalActualRun backend core code choice contents run final →
          run.length ≤ C * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^D := by
  obtain ⟨C, D, positiveC, positiveD, chosen⟩ := choice_resource backend core code choice
  refine ⟨C, D, positiveC, positiveD, ?_⟩
  intro input logical next events contents size ready success run final actual
  obtain ⟨known, knownFinal, knownActual, time⟩ := chosen input logical next events contents size ready success
  obtain ⟨same, _sameFinal⟩ := Kernel.Trace.final_unique
    (TM2.step (Program.choiceProgram backend core code choice)) (localBefore backend code choice contents)
    final knownFinal run known actual.1 actual.2.1 actual.2.2.1 actual.2.2.2
    knownActual.1 knownActual.2.1 knownActual.2.2.1 knownActual.2.2.2
  rw [same]
  exact time

theorem uniform_local_time (backend : ISA.RatBackend) (core : Bool) (code : Program) :
    ∃ C D : Nat, 0 < C ∧ 0 < D ∧
      ∀ (pc : Program.PC code) (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
        (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool),
        input.length = Log.BankMount.fieldCount core → Source.Ready input logical events contents →
        Instruction.execute input (code[pc.val]'pc.isLt) logical = some next →
        ∀ (run : List (OpcodeState backend code pc)) (final : OpcodeState backend code pc),
          LocalActualRun backend core code (Program.localChoice code pc) contents run final →
          run.length ≤ C * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^D := by
  classical
  choose coefficient degree _positiveCoefficient _positiveDegree chosen using
    (fun pc : Program.PC code => choice_time backend core code (Program.localChoice code pc))
  obtain ⟨C, D, positiveC, positiveD, uniform⟩ := Source.finite_local_polynomial coefficient degree
  refine ⟨C, D, positiveC, positiveD, ?_⟩
  intro pc input logical next events contents size ready success run final actual
  have chosenSuccess : Instruction.execute input (instructionOf (Program.localChoice code pc)) logical = some next := by
    rw [instructionOf_localChoice]
    exact success
  exact (chosen pc input logical next events contents size ready chosenSuccess run final actual).trans
    (uniform pc (Kernel.NatInstruction.dataSize contents + (encodeBits input).length))

def localPushCap (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : Program.PC code) : Nat :=
  PDROC.BitVM.Common.sourcePushCap (Program.opcodeProgram backend core code pc)
    (Finset.univ : Finset (Program.OpcodeLabel backend code pc))

def pushCap (backend : ISA.RatBackend) (core : Bool) (code : Program) : Nat :=
  (Finset.univ : Finset (Program.PC code)).sup (localPushCap backend core code)

theorem localPushCap_le (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : Program.PC code) :
    localPushCap backend core code pc ≤ pushCap backend core code :=
  Finset.le_sup (f := localPushCap backend core code) (Finset.mem_univ pc)

/-- ALL actual output stack lengths, including arbitrary untouched old
data, are paid by the SAME established source path. Summing32 roles pays
the physical cleaner's entry; the cleaner is not assumed free. -/
theorem final_data_bound (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : Program.PC code)
    (contents : ISA.Stack → List Bool) (run : List (OpcodeState backend code pc)) (final : OpcodeState backend code pc)
    (actual : LocalActualRun backend core code (Program.localChoice code pc) contents run final) :
    Cleanup.dataSize final.stk ≤
      32 * (Kernel.NatInstruction.dataSize contents + pushCap backend core code * run.length) := by
  cases run with
  | nil => cases actual.1
  | cons first rest =>
    have same : first = localBefore backend code (Program.localChoice code pc) contents := Option.some.inj actual.1
    subst first
    have supported : (localBefore backend code (Program.localChoice code pc) contents).l ∈
        Finset.insertNone (Finset.univ : Finset (Program.OpcodeLabel backend code pc)) :=
      Finset.some_mem_insertNone.mpr (Finset.mem_univ _)
    have occupied := PDROC.BitVM.Common.source_path_occupancy
      (Program.opcodeProgram backend core code pc) (Finset.univ : Finset (Program.OpcodeLabel backend code pc))
      (Program.opcode_supports backend core code pc)
      (localBefore backend code (Program.localChoice code pc) contents) rest
      (Kernel.NatInstruction.dataSize contents) supported (Kernel.NatInstruction.dataSize_each contents) actual.2.1
    have member : final ∈ localBefore backend code (Program.localChoice code pc) contents :: rest :=
      List.mem_of_mem_getLast? (by rw [actual.2.2.1]; rfl)
    have all : ∀ role : ISA.Stack, (final.stk role).length ≤
        Kernel.NatInstruction.dataSize contents + pushCap backend core code *
          (localBefore backend code (Program.localChoice code pc) contents :: rest).length := by
      intro role
      have entry := (occupied final member).2 role
      change (final.stk role).length ≤ Kernel.NatInstruction.dataSize contents +
        localPushCap backend core code pc * rest.length at entry
      exact entry.trans (Nat.add_le_add_left
        (Nat.mul_le_mul (localPushCap_le backend core code pc) (by simp)) _)
    change (Finset.univ : Finset ISA.Stack).sum (fun role => (final.stk role).length) ≤ _
    calc
      _ ≤ (Finset.univ : Finset ISA.Stack).sum (fun _ => Kernel.NatInstruction.dataSize contents +
          pushCap backend core code * (localBefore backend code (Program.localChoice code pc) contents :: rest).length) :=
        Finset.sum_le_sum (fun role _ => all role)
      _ = _ := by simp

def stepCoefficient (sourceCoefficient cap : Nat) : Nat :=
  sourceCoefficient + 640 * (1 + cap * sourceCoefficient) + 28

theorem stepCoefficient_positive (sourceCoefficient cap : Nat) : 0 < stepCoefficient sourceCoefficient cap := by
  dsimp only [stepCoefficient]
  omega

/-- One common positive C,D before all physical callers and inputs.
The path is exactly source_step's witness; the same localrun bound and
its own occupancy absorb the real final-data cleanup cost. -/
theorem source_step_polynomial (backend : ISA.RatBackend) (core : Bool) (code : Program) :
    ∃ C D : Nat, 0 < C ∧ 0 < D ∧
      ∀ (pc : Program.PC code) (store : Program.Store backend code) (input : List Cell)
        (logical next : PaperProofs.Paid.Computation.State) (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool),
        input.length = Log.BankMount.fieldCount core → Source.Ready input logical events contents →
        logical.pc = pc.val → PaperProofs.Paid.Computation.step code input logical = some next →
        ∀ valid : next.pc < code.size,
        ∃ (run : List (OpcodeState backend code pc)) (final : OpcodeState backend code pc)
          (nextStore : Program.Store backend code)
          (path : ActualPath (TM2.step (Program.program backend core code))
            (Program.atEntry backend code pc store contents)
            (Program.atEntry backend code ⟨next.pc, valid⟩ nextStore (Cleanup.cleaned final.stk))),
          LocalActualRun backend core code (Program.localChoice code pc) contents run final ∧
          Source.Ready input next (events ++ (Log.eventOf (code[pc.val]'pc.isLt) logical).toList) (Cleanup.cleaned final.stk) ∧
          path.posts.length ≤ C * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^D := by
  obtain ⟨C, D, _positiveC, positiveD, localTime⟩ := uniform_local_time backend core code
  refine ⟨stepCoefficient C (pushCap backend core code), D,
    stepCoefficient_positive C (pushCap backend core code), positiveD, ?_⟩
  intro pc store input logical next events contents size ready position success valid
  obtain ⟨run, final, nextStore, path, actual, done, time⟩ :=
    source_step backend core code pc store input logical next events contents size ready position success valid
  have executed : Instruction.execute input (code[pc.val]'pc.isLt) logical = some next := by
    simpa only [PaperProofs.Paid.Computation.step, position, Array.getElem?_eq_getElem pc.isLt,
      Option.bind_eq_bind, Option.bind_some] using success
  let g := Kernel.NatInstruction.dataSize contents
  let cap := pushCap backend core code
  let base := g + (encodeBits input).length + 1
  let H := base^D
  have sourceTime : run.length ≤ C * H := localTime pc input logical next events contents size ready executed run final actual
  have baseBound : base ≤ H := by
    change base ≤ base^D
    simpa only [pow_one] using Nat.pow_le_pow_right (by dsimp only [base]; omega : 1 ≤ base) (by omega : 1 ≤ D)
  have gBound : g ≤ H := by dsimp only [base] at baseBound; omega
  have oneBound : 1 ≤ H := by dsimp only [base] at baseBound; omega
  have dataBound := final_data_bound backend core code pc contents run final actual
  have inside : g + cap * run.length ≤ (1 + cap * C) * H := by
    calc
      _ ≤ H + cap * (C * H) := Nat.add_le_add gBound (Nat.mul_le_mul_left cap sourceTime)
      _ = _ := by ring
  have finalBound : Cleanup.dataSize final.stk ≤ 32 * ((1 + cap * C) * H) :=
    dataBound.trans (Nat.mul_le_mul_left 32 inside)
  refine ⟨run, final, nextStore, path, actual, done, ?_⟩
  change path.posts.length ≤ stepCoefficient C cap * H
  calc
    path.posts.length ≤ run.length + 20 * (Cleanup.dataSize final.stk + 1) + 8 := time
    _ ≤ C * H + 20 * (32 * ((1 + cap * C) * H) + 1) + 8 :=
      Nat.add_le_add_right
        (Nat.add_le_add sourceTime (Nat.mul_le_mul_left 20 (Nat.add_le_add_right finalBound 1))) 8
    _ ≤ stepCoefficient C cap * H := by
      dsimp only [stepCoefficient]
      nlinarith only [oneBound]

end PDROC.BitVM.VM.CFG.Refinement
