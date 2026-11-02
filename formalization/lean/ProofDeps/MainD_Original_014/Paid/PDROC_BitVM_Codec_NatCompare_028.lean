module

public import Paid.PDROC_BitVM_Codec_NatCast_027
public import Paid.PDROC_BitVM_Kernel_InternalInstruction_019
public import Paid.PDROC_BitVM_Kernel_Branch_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.BitVM.Codec.NatCompare

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal
open PDROC.BitVM.Codec.FieldOps (Path cfg_eq)

abbrev Stack := RatMarshal.Stack
abbrev Alphabet := RatMarshal.Alphabet
abbrev ComputeStore := PDROC.BitVM.Kernel.Internal.Store .lessEqual
abbrev CoreStore := ComputeStore × NatWriter.Store
abbrev CoreLabel := PDROC.BitVM.Kernel.Internal.Label ⊕ (NatWriter.Label ⊕ Unit)
abbrev CoreState := TM2.Cfg Alphabet CoreLabel CoreStore

def coreComputeLabels : PDROC.BitVM.Kernel.Internal.Label → CoreLabel := Sum.inl
def coreWriterLabels (label : NatWriter.Label) : CoreLabel := .inr (.inl label)
def coreDone : CoreLabel := .inr (.inr ())

/-- A fixed binary LE call followed by genuine canonical Cell writeback to
one compile-time physical slot. No original register is used as scratch. -/
def coreProgram (dst : Stack) (notRight : dst ≠ 0) (notLeft : dst ≠ 24)
    (left right : Register) : CoreLabel → TM2.Stmt Alphabet CoreLabel CoreStore
  | .inl label => Inline.statement coreComputeLabels (coreWriterLabels 0)
      (PDROC.BitVM.Kernel.Internal.program .lessEqual left right label)
  | .inr (.inl label) => StoreIso.statement (Equiv.prodComm _ _)
      (Inline.statement coreWriterLabels coreDone (NatWriter.Global.machine dst notRight notLeft label))
  | .inr (.inr _) => .halt

def coreBefore (contents : Stack → List Bool) (saved : Option Bool) : CoreState :=
  Inline.cfg coreComputeLabels (coreWriterLabels 0) (none, ())
    (PDROC.BitVM.Kernel.Internal.before .lessEqual contents saved)

def coreComputeCfg (source : PDROC.BitVM.Kernel.Internal.State .lessEqual) : CoreState :=
  Inline.cfg coreComputeLabels (coreWriterLabels 0) (none, ()) source

def coreWriterCfg (saved : ComputeStore) (source : NatWriter.Global.State) : CoreState :=
  StoreIso.cfg (Equiv.prodComm _ _) (Inline.cfg coreWriterLabels coreDone saved source)

def coreCeiling (left right : Register) (contents : Stack → List Bool) (a b : ℕ) : ℕ :=
  PDROC.BitVM.Kernel.NatInstruction.dataSize contents +
    PDROC.BitVM.Kernel.InternalInstruction.computePushCap .lessEqual left right *
      PDROC.BitVM.Kernel.NatInstruction.computeBudget a b

def coreBudget (left right : Register) (contents : Stack → List Bool) (a b : ℕ) : ℕ :=
  PDROC.BitVM.Kernel.NatInstruction.computeBudget a b +
    32 * (3 * coreCeiling left right contents a b + 1) + 2

theorem core_supports (dst : Stack) (notRight : dst ≠ 0) (notLeft : dst ≠ 24)
    (left right : Register) :
    TM2.Supports (coreProgram dst notRight notLeft left right) Finset.univ := by
  have every : ∀ code : TM2.Stmt Alphabet CoreLabel CoreStore, TM2.SupportsStmt Finset.univ code := by
    intro code
    induction code with
    | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
    | branch _ _ _ yes no => exact ⟨yes, no⟩
    | goto _ => exact fun _ => Finset.mem_univ _
    | halt => trivial
  exact ⟨Finset.mem_univ _, fun label _ => every (coreProgram dst notRight notLeft left right label)⟩

/-- The single selected native trace pays for its actual FALSE padding;
the single selected writer trace really clears both work stacks and old
destination. Arbitrary untouched stacks are carried from the same caller. -/
theorem core_runs (dst : Stack) (notRight : dst ≠ 0) (notLeft : dst ≠ 24)
    (logical : PaperProofs.Paid.Computation.State) (left right : Register) (a b : ℕ)
    (contents : Stack → List Bool) (saved : Option Bool)
    (represented : ∀ reg, contents (registerSlot reg) = encodeCellBits (logical.register reg))
    (leftNat : logical.register left = .natural a) (rightNat : logical.register right = .natural b)
    (emptyRight : contents 0 = []) (emptyLeft : contents 24 = []) :
    ∃ after : CoreState, ∃ path : Path (coreProgram dst notRight notLeft left right)
      (coreBefore contents saved) after,
      after.l = none ∧ after.stk 0 = [] ∧ after.stk 24 = [] ∧
      after.stk dst = encodeCellBits (.natural (if decide (a ≤ b) then 1 else 0)) ∧
      (∀ other, other ≠ 0 → other ≠ 24 → other ≠ dst → after.stk other = contents other) ∧
      path.states.length ≤ coreBudget left right contents a b := by
  obtain ⟨compute, computed, head, chain, last, halt, regs, result, time, occupied, frame⟩ :=
    PDROC.BitVM.Kernel.InternalInstruction.compute_resources .lessEqual logical left right a b
      contents saved represented leftNat rightNat emptyRight emptyLeft
  let localCompute : Path (PDROC.BitVM.Kernel.Internal.program .lessEqual left right)
      (PDROC.BitVM.Kernel.Internal.before .lessEqual contents saved) computed := ⟨compute, head, chain, last⟩
  have edge : ∀ x y, TM2.step (PDROC.BitVM.Kernel.Internal.program .lessEqual left right) x = some y →
      TM2.step (coreProgram dst notRight notLeft left right) (coreComputeCfg x) = some (coreComputeCfg y) := by
    intro x y actual
    exact Inline.step_edge coreComputeLabels (coreWriterLabels 0)
      (PDROC.BitVM.Kernel.Internal.program .lessEqual left right) (coreProgram dst notRight notLeft left right)
      (by intro label; rfl) x y (none, ()) actual
  let first := localCompute.transport coreComputeCfg edge
  have computedHalt : computed.l = none := by
    rcases computed with ⟨label, finiteStore, data⟩
    cases label with
    | none => rfl
    | some label => cases halt
  let ready := coreComputeCfg computed
  have boundary : ready = coreWriterCfg computed.var (NatWriter.Global.before computed.stk none) := by
    rcases computed with ⟨label, finiteStore, data⟩
    change label = none at computedHalt
    subst label
    rfl
  have representation : ListBlank.mk (computed.stk 0) = ListBlank.mk
      (PaperProofs.Common.Native.RationalControllerComputation.encodeNat (if decide (a ≤ b) then 1 else 0)) := result
  obtain ⟨writer, written, wHead, wChain, wLast, wHalt, work0, work24, cell, wTime, wFrame⟩ :=
    NatWriter.Global.runs dst notRight notLeft (if decide (a ≤ b) then 1 else 0) computed.stk none representation
  let localWriter : Path (NatWriter.Global.machine dst notRight notLeft)
      (NatWriter.Global.before computed.stk none) written := ⟨writer, wHead, wChain, wLast⟩
  have wEdge : ∀ x y, TM2.step (NatWriter.Global.machine dst notRight notLeft) x = some y →
      TM2.step (coreProgram dst notRight notLeft left right) (coreWriterCfg computed.var x) =
        some (coreWriterCfg computed.var y) := by
    intro x y actual
    exact FieldOps.iso_inline_edge (Equiv.prodComm _ _) coreWriterLabels coreDone computed.var
      (NatWriter.Global.machine dst notRight notLeft) (coreProgram dst notRight notLeft left right)
      (by intro label; rfl) x y actual
  let second := localWriter.transport (coreWriterCfg computed.var) wEdge
  let first' := first.castLast boundary
  have writtenHalt : written.l = none := by
    rcases written with ⟨label, finiteStore, data⟩
    cases label with
    | none => rfl
    | some label => cases wHalt
  let returned := coreWriterCfg computed.var written
  have position : returned.l = some coreDone := by
    change some (written.l.map coreWriterLabels |>.getD coreDone) = _
    rw [writtenHalt]
    rfl
  let final : CoreState := ⟨none, returned.var, returned.stk⟩
  have finalEdge : TM2.step (coreProgram dst notRight notLeft left right) returned = some final := by
    rcases returned with ⟨label, finiteStore, data⟩
    change label = some coreDone at position
    subst label
    rfl
  let third := Path.single finalEdge
  let joined := (first'.append second).append third
  have oldFrame : ∀ other, other ≠ 0 → other ≠ 24 → computed.stk other = contents other := by
    intro other not0 not24
    by_cases selectedLeft : other = registerSlot left
    · subst other
      exact (regs left).trans (represented left).symm
    by_cases selectedRight : other = registerSlot right
    · subst other
      exact (regs right).trans (represented right).symm
    apply frame other
    · intro index
      fin_cases index
      · exact selectedLeft
      · exact not0
      · exact not24
    · intro index
      fin_cases index
      · exact selectedRight
      · exact not0
      · exact not24
    · intro index
      fin_cases index
      · exact not0
      · exact not24
  have member : computed ∈ compute := List.mem_of_mem_getLast? (by rw [last]; rfl)
  have c0 := occupied computed member 0
  have c24 := occupied computed member 24
  have cdst := occupied computed member dst
  have writerBound : writer.length ≤ 32 * (3 * coreCeiling left right contents a b + 1) := by
    change (computed.stk 0).length ≤ coreCeiling left right contents a b at c0
    change (computed.stk 24).length ≤ coreCeiling left right contents a b at c24
    change (computed.stk dst).length ≤ coreCeiling left right contents a b at cdst
    omega
  have firstLength : first'.states.length = compute.length := localCompute.transport_length coreComputeCfg edge
  have secondLength : second.states.length = writer.length := localWriter.transport_length (coreWriterCfg computed.var) wEdge
  have total := (first'.append second).append_length third
  have totalFirst := first'.append_length second
  refine ⟨final, joined, rfl, work0, work24, cell, ?_, ?_⟩
  · intro other not0 not24 notDst
    exact (wFrame other not0 not24 notDst).trans (oldFrame other not0 not24)
  · change joined.states.length ≤ coreBudget left right contents a b
    change joined.states.length ≤ (first'.append second).states.length + third.states.length at total
    have thirdLength : third.states.length = 2 := rfl
    rw [firstLength, secondLength] at totalFirst
    rw [thirdLength] at total
    unfold coreBudget
    omega

end PDROC.BitVM.Codec.NatCompare
