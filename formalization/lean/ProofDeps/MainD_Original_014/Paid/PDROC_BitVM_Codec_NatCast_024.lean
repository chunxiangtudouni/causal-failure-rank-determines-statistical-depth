module

public import Paid.PDROC_BitVM_Codec_NatCast_023

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Codec.NatCast

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Codec.FieldOps (Path iso_inline_edge lift_three)
open PaperProofs.Common.Native.RationalControllerComputation (encodeNat)

abbrev MarshalState := TM2.Cfg Alphabet PDROC.BitVM.Kernel.NatMarshal.Label WriterStore

def marshalCfg (readerSaved : RatMarshal.Store) (state : MarshalState) : State :=
  StoreIso.cfg (Equiv.prodComm _ _) (Inline.cfg marshalLabels (writerLabels 0) readerSaved state)

/-- A real selected full Nat Cell is copied to native0, after its actual
source FALSE tag read. The source is restored and the whole suffix is empty
because the real preceding entry clears produced native0/24 emptiness. -/
theorem marshal_call (target source : Register) (value : ℕ)
    (contents : Stack → List Bool) (readerSaved : RatMarshal.Store) (saved : Option Bool)
    (sourceCell : contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source) = encodeCellBits (.natural value))
    (rightEmpty : contents 0 = []) (leftEmpty : contents 24 = []) :
    ∃ path : Path (program target source)
      (⟨some (marshalLabels 0), (readerSaved, (saved, ())), contents⟩ : State)
      (⟨some (writerLabels 0), (readerSaved, (none, ())),
        Function.update contents 0 (encodeNatBits value)⟩ : State),
      path.states.length = 2 * (encodeNatBits value).length + 5 := by
  let word := encodeNatBits value
  obtain ⟨run, head, chain, last, _halt, length, _source, _target, _scratch⟩ :=
    PDROC.BitVM.Kernel.NatMarshal.marshal_runs word [] saved
  simp only [PDROC.BitVM.Kernel.NatMarshal.final, List.append_nil] at last
  have beforeData := RatMarshal.three_selected (PDROC.BitVM.Kernel.NatMarshalGlobal.embedding source) contents (false :: word) [] []
    sourceCell rightEmpty leftEmpty
  have afterData : Lift.slots (PDROC.BitVM.Kernel.NatMarshalGlobal.embedding source) (Function.update contents 0 word) =
      PDROC.BitVM.Log.TwoStack.threeStacks (false :: word) word [] := by
    change Lift.slots (PDROC.BitVM.Kernel.NatMarshalGlobal.embedding source) (Function.update contents ((PDROC.BitVM.Kernel.NatMarshalGlobal.embedding source) 1) word) = _
    rw [Lift.slots_update, beforeData, Copy.update_second]
  obtain ⟨lifted, liftedLength⟩ := lift_three (PDROC.BitVM.Kernel.NatMarshalGlobal.embedding source) PDROC.BitVM.Kernel.NatMarshal.program
    (PDROC.BitVM.Kernel.NatMarshal.before word [] saved)
    (⟨none, (none, ()), PDROC.BitVM.Log.TwoStack.threeStacks (false :: word) word []⟩ :
      PDROC.BitVM.Kernel.NatMarshal.State) run head chain last contents
    (Function.update contents 0 word) beforeData afterData
    (by intro other outside; exact Function.update_of_ne (outside 1) _ _)
  have edge : ∀ a b, TM2.step (Lift.machine (PDROC.BitVM.Kernel.NatMarshalGlobal.embedding source) PDROC.BitVM.Kernel.NatMarshal.program) a = some b →
      TM2.step (program target source) (marshalCfg readerSaved a) = some (marshalCfg readerSaved b) := by
    intro a b actual
    exact iso_inline_edge (Equiv.prodComm _ _) marshalLabels (writerLabels 0) readerSaved
      (Lift.machine (PDROC.BitVM.Kernel.NatMarshalGlobal.embedding source) PDROC.BitVM.Kernel.NatMarshal.program)
      (program target source) (marshal_agrees target source) a b actual
  let transported := lifted.transport (marshalCfg readerSaved) edge
  exact ⟨transported, (lifted.transport_length (marshalCfg readerSaved) edge).trans
    (liftedLength.trans length)⟩

def writerCfg (readerSaved : RatMarshal.Store) (state : NatWriter.Global.State) : State :=
  StoreIso.cfg (Equiv.prodComm _ _) (Inline.cfg writerLabels (control 3) readerSaved state)

/-- ONE canonical Nat writer path, including arbitrary old target bytes.
The actual fixed FALSE sign/caller store remains as finite carried data. -/
theorem writer_call (target source : Register) (value : ℕ)
    (contents : Stack → List Bool) (readerSaved : RatMarshal.Store) (saved : Option Bool)
    (representation : ListBlank.mk (contents 0) = ListBlank.mk (encodeNat value)) :
    ∃ (ready : State) (path : Path (program target source)
      (⟨some (writerLabels 0), (readerSaved, (saved, ())), contents⟩ : State) ready),
      ready.l = some (control 3) ∧ ready.var.1 = readerSaved ∧
      ready.stk 0 = [] ∧ ready.stk 24 = [] ∧
      ready.stk (25 : Stack) = encodeCellBits (.natural value) ∧
      (∀ other, other ≠ 0 → other ≠ 24 → other ≠ (25 : Stack) →
        ready.stk other = contents other) ∧
      path.states.length ≤ 32 * ((contents 0).length + (contents 24).length +
        (contents (25 : Stack)).length + 1) := by
  obtain ⟨run, after, head, chain, last, halt, right, left, targetWord, time, frame⟩ :=
    NatWriter.Global.runs (25 : Stack)
      (by decide) (by decide)
      value contents saved representation
  have halted : after.l = none := by
    rcases after with ⟨label, finiteStore, data⟩
    cases label with
    | none => rfl
    | some label => cases halt
  let localPath : Path tempWriter (NatWriter.Global.before contents saved) after :=
    ⟨run, head, chain, last⟩
  have edge : ∀ a b, TM2.step tempWriter a = some b →
      TM2.step (program target source) (writerCfg readerSaved a) = some (writerCfg readerSaved b) := by
    intro a b actual
    exact iso_inline_edge (Equiv.prodComm _ _) writerLabels (control 3) readerSaved
      tempWriter (program target source) (writer_agrees target source) a b actual
  let transported := localPath.transport (writerCfg readerSaved) edge
  refine ⟨writerCfg readerSaved after, transported, ?_, rfl, right, left, targetWord, frame, ?_⟩
  · change some (after.l.map writerLabels |>.getD (control 3)) = some (control 3)
    rw [halted]
    rfl
  · exact (localPath.transport_length (writerCfg readerSaved) edge).trans_le time

end PDROC.BitVM.Codec.NatCast
