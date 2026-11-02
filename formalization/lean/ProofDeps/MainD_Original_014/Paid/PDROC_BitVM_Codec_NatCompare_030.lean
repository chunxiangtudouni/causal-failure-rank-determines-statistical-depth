module

public import Paid.PDROC_BitVM_Codec_NatCompare_029

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.BitVM.Codec.NatCompare

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal
open PDROC.BitVM.Codec.FieldOps (Path)

def coreCfg (direction : Bool) (extra : BranchStore × Bool) (source : CoreState) : State :=
  StoreIso.cfg coreIso (Inline.cfg (coreLabels direction) (coreFinish direction) extra source)

/-- The actual LE-to-Cell call is selected once. Its original register
reads happen before any write to the original comparison destination. -/
theorem core_call (comparison : Comparison) (target left right : Register) (direction : Bool)
    (logical : PaperProofs.Paid.Computation.State) (a b : ℕ)
    (contents : Stack → List Bool) (saved : BranchStore) (flag : Bool)
    (represented : ∀ reg, contents (registerSlot reg) = encodeCellBits (logical.register reg))
    (leftNat : logical.register (orderedLeft direction left right) = .natural a)
    (rightNat : logical.register (orderedRight direction left right) = .natural b)
    (emptyRight : contents 0 = []) (emptyLeft : contents 24 = []) :
    ∃ ready : State, ∃ path : Path (program comparison target left right)
      (⟨some (coreLabels direction (.inl 0)), (saved, (coreInitial, flag)), contents⟩ : State) ready,
      ready.l = some (coreFinish direction) ∧ ready.var.1 = saved ∧ ready.var.2.2 = flag ∧
      ready.stk 0 = [] ∧ ready.stk 24 = [] ∧
      ready.stk (tempSlot direction) = encodeCellBits (.natural (if decide (a ≤ b) then 1 else 0)) ∧
      (∀ other, other ≠ 0 → other ≠ 24 → other ≠ tempSlot direction → ready.stk other = contents other) ∧
      path.states.length ≤ coreBudget (orderedLeft direction left right) (orderedRight direction left right) contents a b := by
  obtain ⟨after, localPath, halted, work0, work24, cell, frame, time⟩ :=
    core_runs (tempSlot direction) (temp_not_right direction) (temp_not_left direction)
      logical (orderedLeft direction left right) (orderedRight direction left right) a b contents none
      represented leftNat rightNat emptyRight emptyLeft
  have edge : ∀ x y, TM2.step (coreMachine direction left right) x = some y →
      TM2.step (program comparison target left right) (coreCfg direction (saved, flag) x) =
        some (coreCfg direction (saved, flag) y) := by
    intro x y actual
    exact FieldOps.iso_inline_edge coreIso (coreLabels direction) (coreFinish direction) (saved, flag)
      (coreMachine direction left right) (program comparison target left right) (by intro label; rfl) x y actual
  let transported := localPath.transport (coreCfg direction (saved, flag)) edge
  refine ⟨coreCfg direction (saved, flag) after, transported, ?_, rfl, rfl, work0, work24, cell, frame, ?_⟩
  · change some (after.l.map (coreLabels direction) |>.getD (coreFinish direction)) = _
    rw [halted]
    rfl
  · exact (localPath.transport_length (coreCfg direction (saved, flag)) edge).trans_le time

def branchFinish (direction : Bool) : Label := if direction then control 6 else control 4
def branchCfg (direction : Bool) (extra : CoreStore × Bool)
    (source : PDROC.BitVM.Kernel.Branch.State) : State :=
  Inline.cfg (fun _ : Unit => coreFinish direction) (branchFinish direction) extra source

theorem branch_agrees (comparison : Comparison) (target left right : Register) (direction : Bool) (label : Unit) :
    program comparison target left right (coreFinish direction) =
      Inline.statement (τ := CoreStore × Bool) (fun _ : Unit => coreFinish direction)
        (branchFinish direction) (PDROC.BitVM.Kernel.Branch.program (tempSlot direction) label) := by
  cases direction <;> cases label <;> rfl

/-- NONE and FALSE are distinguished by the actual fixed five-prefix
inspector; even a malformed word is physically restored without change. -/
theorem branch_call (comparison : Comparison) (target left right : Register) (direction : Bool)
    (contents : Stack → List Bool) (saved : Store) :
    ∃ path : Path (program comparison target left right)
      (⟨some (coreFinish direction), saved, contents⟩ : State)
      (⟨some (branchFinish direction),
        (PDROC.BitVM.Kernel.Branch.captured (contents (tempSlot direction)), saved.2), contents⟩ : State),
      path.states.length = 2 := by
  obtain ⟨run, head, chain, last, _halt, length⟩ :=
    PDROC.BitVM.Kernel.Branch.runs (tempSlot direction) contents saved.1
  let localPath : Path (PDROC.BitVM.Kernel.Branch.program (tempSlot direction))
      (⟨some (), saved.1, contents⟩ : PDROC.BitVM.Kernel.Branch.State)
      (⟨none, PDROC.BitVM.Kernel.Branch.captured (contents (tempSlot direction)), contents⟩ : PDROC.BitVM.Kernel.Branch.State) :=
    ⟨run, head, chain, last⟩
  have edge : ∀ x y, TM2.step (PDROC.BitVM.Kernel.Branch.program (tempSlot direction)) x = some y →
      TM2.step (program comparison target left right) (branchCfg direction saved.2 x) =
        some (branchCfg direction saved.2 y) := by
    intro x y actual
    exact Inline.step_edge (fun _ : Unit => coreFinish direction) (branchFinish direction)
      (PDROC.BitVM.Kernel.Branch.program (tempSlot direction)) (program comparison target left right)
      (branch_agrees comparison target left right direction) x y saved.2 actual
  exact ⟨localPath.transport (branchCfg direction saved.2) edge,
    (localPath.transport_length (branchCfg direction saved.2) edge).trans length⟩

theorem bool_inspected (flag : Bool) :
    !PDROC.BitVM.Kernel.Branch.zeroFlag
      (PDROC.BitVM.Kernel.Branch.captured (encodeCellBits (.natural (if flag then 1 else 0)))) = flag := by
  cases flag <;> rfl

theorem save_step (comparison : Comparison) (target left right : Register)
    (contents : Stack → List Bool) (saved : Store) :
    TM2.step (program comparison target left right) (⟨some (control 4), saved, contents⟩ : State) =
      some (⟨some (coreLabels true (.inl 0)),
        (saved.1, (coreInitial, !PDROC.BitVM.Kernel.Branch.zeroFlag saved.1)), contents⟩ : State) := rfl

theorem push_step (comparison : Comparison) (target left right : Register)
    (contents : Stack → List Bool) (saved : Store) :
    TM2.step (program comparison target left right) (⟨some (control 6), saved, contents⟩ : State) =
      some (⟨some (writerLabels 0), saved,
        Function.update contents 0 (encodeNatBits (if resultFlag comparison saved then 1 else 0) ++ contents 0)⟩ : State) := by
  change some (TM2.stepAux
    (.push 0 (resultFlag comparison) (.push 0 (fun _ => false)
      (.push 0 (fun _ => true) (.goto (fun _ => writerLabels 0))))) saved contents) = _
  simp only [TM2.stepAux, Function.update_self, Function.update_idem]
  rw [FieldOps.bool_word]
  rfl


def writerCfg (extra : BranchStore × (ComputeStore × Bool)) (source : NatWriter.Global.State) : State :=
  StoreIso.cfg writerIso (Inline.cfg writerLabels (control 7) extra source)

theorem writer_call (comparison : Comparison) (target left right : Register) (value : ℕ)
    (contents : Stack → List Bool) (saved : Store)
    (representation : ListBlank.mk (contents 0) = ListBlank.mk
      (PaperProofs.Common.Native.RationalControllerComputation.encodeNat value)) :
    ∃ ready : State, ∃ path : Path (program comparison target left right)
      (⟨some (writerLabels 0), saved, contents⟩ : State) ready,
      ready.l = some (control 7) ∧ ready.stk 0 = [] ∧ ready.stk 24 = [] ∧
      ready.stk (registerSlot target) = encodeCellBits (.natural value) ∧
      (∀ other, other ≠ 0 → other ≠ 24 → other ≠ registerSlot target → ready.stk other = contents other) ∧
      path.states.length ≤ 32 * ((contents 0).length + (contents 24).length + (contents (registerSlot target)).length + 1) := by
  obtain ⟨run, after, head, chain, last, halt, work0, work24, cell, time, frame⟩ :=
    NatWriter.Global.runs (registerSlot target) (RatMarshal.source_not_right target)
      (RatMarshal.register_not_left target) value contents saved.2.1.2.1 representation
  let localPath : Path (writerMachine target) (NatWriter.Global.before contents saved.2.1.2.1) after := ⟨run, head, chain, last⟩
  have edge : ∀ x y, TM2.step (writerMachine target) x = some y →
      TM2.step (program comparison target left right) (writerCfg (saved.1, (saved.2.1.1, saved.2.2)) x) =
        some (writerCfg (saved.1, (saved.2.1.1, saved.2.2)) y) := by
    intro x y actual
    exact FieldOps.iso_inline_edge writerIso writerLabels (control 7) (saved.1, (saved.2.1.1, saved.2.2))
      (writerMachine target) (program comparison target left right) (by intro label; rfl) x y actual
  have halted : after.l = none := by
    rcases after with ⟨label, finiteStore, data⟩
    cases label with
    | none => rfl
    | some label => cases halt
  let transported := localPath.transport (writerCfg (saved.1, (saved.2.1.1, saved.2.2))) edge
  refine ⟨writerCfg (saved.1, (saved.2.1.1, saved.2.2)) after, transported, ?_, work0, work24, cell, frame, ?_⟩
  · change some (after.l.map writerLabels |>.getD (control 7)) = _
    rw [halted]
    rfl
  · exact (localPath.transport_length (writerCfg (saved.1, (saved.2.1.1, saved.2.2))) edge).trans_le time

end PDROC.BitVM.Codec.NatCompare
