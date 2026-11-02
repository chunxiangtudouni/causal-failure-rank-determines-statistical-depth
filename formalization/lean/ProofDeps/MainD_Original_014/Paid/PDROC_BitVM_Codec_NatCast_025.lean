module

public import Paid.PDROC_BitVM_Codec_NatCast_024

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Codec.NatCast

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Codec.FieldOps (Path iso_inline_edge lift_three)

def clearSlot (stage : Fin 4) : Stack :=
  if stage = 0 then 0 else if stage = 1 then 24 else if stage = 2 then 25 else 26

def clearStart (stage : Fin 4) : Label :=
  if stage = 0 then control 1 else if stage = 1 then control 2 else if stage = 2 then control 4 else control 5

def clearFinish (stage : Fin 4) : Label :=
  if stage = 0 then control 2 else if stage = 1 then marshalLabels 0 else if stage = 2 then control 5 else control 6

theorem clear_agrees (target source : Register) (stage : Fin 4) (label : Unit) :
    program target source (clearStart stage) = StoreIso.statement FieldOps.clearIso
      (Inline.statement (τ := Bool × WriterStore) (fun _ : Unit => clearStart stage) (clearFinish stage)
        (PDROC.BitVM.Kernel.Clear.program (clearSlot stage) label)) := by
  cases label
  fin_cases stage <;> rfl

def clearCfg (stage : Fin 4) (extra : Bool × WriterStore)
    (state : PDROC.BitVM.Kernel.Clear.State) : State :=
  StoreIso.cfg FieldOps.clearIso (Inline.cfg (fun _ : Unit => clearStart stage) (clearFinish stage) extra state)

theorem clear_call (target source : Register) (stage : Fin 4)
    (contents : Stack → List Bool) (saved : Store) :
    ∃ path : Path (program target source)
      (⟨some (clearStart stage), saved, contents⟩ : State)
      (⟨some (clearFinish stage), ((none, saved.1.2), saved.2),
        Function.update contents (clearSlot stage) []⟩ : State),
      path.states.length = (contents (clearSlot stage)).length + 2 := by
  obtain ⟨run, head, chain, last, _halt, length, _frame⟩ :=
    PDROC.BitVM.Kernel.Clear.runs (clearSlot stage) contents saved.1.1
  let localPath : Path (PDROC.BitVM.Kernel.Clear.program (clearSlot stage))
      (⟨some (), saved.1.1, contents⟩ : PDROC.BitVM.Kernel.Clear.State)
      (⟨none, none, Function.update contents (clearSlot stage) []⟩ : PDROC.BitVM.Kernel.Clear.State) :=
    ⟨run, head, chain, last⟩
  let transform := clearCfg stage (saved.1.2, saved.2)
  have edge : ∀ a b, TM2.step (PDROC.BitVM.Kernel.Clear.program (clearSlot stage)) a = some b →
      TM2.step (program target source) (transform a) = some (transform b) := by
    intro a b actual
    exact iso_inline_edge FieldOps.clearIso (fun _ : Unit => clearStart stage) (clearFinish stage)
      (saved.1.2, saved.2) (PDROC.BitVM.Kernel.Clear.program (clearSlot stage))
      (program target source) (clear_agrees target source stage) a b actual
  exact ⟨localPath.transport transform edge, (localPath.transport_length transform edge).trans length⟩

def literalCfg (extra : Bool × WriterStore)
    (state : TM2.Cfg Alphabet Unit (Option Bool)) : State :=
  StoreIso.cfg FieldOps.clearIso (Inline.cfg (fun _ : Unit => control 3) (assemblerLabels 0) extra state)

/-- The fixed complete Nat1 is REALLY written after clearing old26.
Neither a denominator answer nor any initialized work area is supplied. -/
theorem literal_call (target source : Register) (contents : Stack → List Bool) (saved : Store)
    (scratch : contents 24 = []) :
    ∃ path : Path (program target source) (⟨some (control 3), saved, contents⟩ : State)
      (⟨some (assemblerLabels 0), ((none, saved.1.2), saved.2),
        Function.update contents 26 one⟩ : State),
      path.states.length = (contents 26).length + 2 := by
  obtain ⟨run, head, chain, last, _halt, length, _source, _target, _scratch⟩ :=
    PDROC.BitVM.Kernel.RegisterMove.literal_runs one (contents 0) (contents 26) saved.1.1
  have beforeData := RatMarshal.three_selected literalEmbedding contents (contents 0) (contents 26) [] rfl rfl scratch
  have afterData : Lift.slots literalEmbedding (Function.update contents 26 one) =
      PDROC.BitVM.Log.TwoStack.threeStacks (contents 0) one [] := by
    change Lift.slots literalEmbedding (Function.update contents (literalEmbedding 1) one) = _
    rw [Lift.slots_update, beforeData, Copy.update_second]
  obtain ⟨lifted, liftedLength⟩ := lift_three literalEmbedding
    (PDROC.BitVM.Kernel.RegisterMove.literalProgram one)
    (PDROC.BitVM.Kernel.RegisterMove.clearState (some ()) saved.1.1 (contents 0) (contents 26))
    (PDROC.BitVM.Kernel.RegisterMove.clearState none none (contents 0) one)
    run head chain last contents (Function.update contents 26 one) beforeData afterData
    (by intro other outside; exact Function.update_of_ne (outside 1) _ _)
  have edge : ∀ a b, TM2.step (Lift.machine literalEmbedding (PDROC.BitVM.Kernel.RegisterMove.literalProgram one)) a = some b →
      TM2.step (program target source) (literalCfg (saved.1.2, saved.2) a) =
        some (literalCfg (saved.1.2, saved.2) b) := by
    intro a b actual
    exact iso_inline_edge FieldOps.clearIso (fun _ : Unit => control 3) (assemblerLabels 0)
      (saved.1.2, saved.2) (Lift.machine literalEmbedding (PDROC.BitVM.Kernel.RegisterMove.literalProgram one))
      (program target source) (literal_agrees target source) a b actual
  exact ⟨lifted.transport (literalCfg (saved.1.2, saved.2)) edge,
    (lifted.transport_length (literalCfg (saved.1.2, saved.2)) edge).trans (liftedLength.trans length)⟩

def assemblerCfg (writerSaved : WriterStore) (state : RatAssembler.State) : State :=
  Inline.cfg assemblerLabels (control 4) writerSaved state

/-- Natural cast identities only DESCRIBE the canonical bytes produced by
the real copy/literal producers. Actual assembly invokes one genuine path;
the mathematical Nat cast is not a primitive transition. -/
theorem assembler_call (target source : Register) (value : ℕ)
    (contents : Stack → List Bool) (saved : Option Bool) (writerSaved : WriterStore)
    (numerator : contents 25 = encodeCellBits (.natural value))
    (denominator : contents 26 = one) :
    ∃ (ready : State) (path : Path (program target source)
      (⟨some (assemblerLabels 0), ((saved, false), writerSaved), contents⟩ : State) ready),
      ready.l = some (control 4) ∧ ready.var = ((none, false), writerSaved) ∧
      ready.stk (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target) = encodeCellBits (.rational value) ∧
      ready.stk 24 = [] ∧ ready.stk 0 = contents 0 ∧
      (∀ other, other ≠ PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target → other ≠ 24 →
        ready.stk other = contents other) ∧
      path.states.length ≤ 32 * (RatAssembler.inputSize target 0 1 contents + 1) := by
  have sign : false = decide ((value : ℚ) < 0) := by
    have nonnegative : ¬(value : ℚ) < 0 := not_lt.mpr (Nat.cast_nonneg value)
    simp only [nonnegative, decide_false]
  have num : contents (RatMarshal.tempSlot 0) = encodeCellBits (.natural (value : ℚ).num.natAbs) := by
    change contents 25 = _
    simpa only [Rat.num_natCast, Int.natAbs_natCast] using numerator
  have den : contents (RatMarshal.tempSlot 1) = encodeCellBits (.natural (value : ℚ).den) := by
    change contents 26 = _
    simpa only [Rat.den_natCast, one] using denominator
  obtain ⟨run, after, head, chain, last, _halt, halted, store, targetWord, scratch, right,
    frame, _temps, _regs, time, _occupied⟩ :=
    RatAssembler.runs target 0 1 value contents saved false sign num den
  let localPath : Path (RatAssembler.program target 0 1) (RatAssembler.before contents saved false) after :=
    ⟨run, head, chain, last⟩
  have edge : ∀ a b, TM2.step (RatAssembler.program target 0 1) a = some b →
      TM2.step (program target source) (assemblerCfg writerSaved a) = some (assemblerCfg writerSaved b) := by
    intro a b actual
    exact Inline.step_edge assemblerLabels (control 4) (RatAssembler.program target 0 1)
      (program target source) (assembler_agrees target source) a b writerSaved actual
  let transported := localPath.transport (assemblerCfg writerSaved) edge
  refine ⟨assemblerCfg writerSaved after, transported, ?_, ?_, targetWord, scratch, right, frame, ?_⟩
  · change some (after.l.map assemblerLabels |>.getD (control 4)) = some (control 4)
    rw [halted]
    rfl
  · change (after.var, writerSaved) = _
    rw [store]
  · exact (localPath.transport_length (assemblerCfg writerSaved) edge).trans_le time

end PDROC.BitVM.Codec.NatCast
