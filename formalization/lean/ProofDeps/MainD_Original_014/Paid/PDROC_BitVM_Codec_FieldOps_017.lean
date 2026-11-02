module

public import Paid.PDROC_BitVM_Codec_FieldOps_016

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Codec.FieldOps

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation

def clearSlot (stage : Fin 4) : Stack :=
  if stage = 0 then 0 else if stage = 1 then 24 else if stage = 2 then 25 else 26

def clearStart (stage : Fin 4) : Label :=
  if stage = 0 then control 1 else if stage = 1 then control 2 else if stage = 2 then control 4 else control 5

def clearFinish (stage : Fin 4) : Label :=
  if stage = 0 then control 2 else if stage = 1 then readerLabels 0 else if stage = 2 then control 5 else control 6

theorem clear_agrees (kind : Kind) (target source : Register) (stage : Fin 4) (label : Unit) :
    program kind target source (clearStart stage) = StoreIso.statement clearIso
      (Inline.statement (τ := Bool × WriterStore) (fun _ : Unit => clearStart stage) (clearFinish stage)
        (PDROC.BitVM.Kernel.Clear.program (clearSlot stage) label)) := by
  cases label
  fin_cases stage <;> rfl

def clearCfg (stage : Fin 4) (extra : Bool × WriterStore)
    (state : PDROC.BitVM.Kernel.Clear.State) : State :=
  StoreIso.cfg clearIso (Inline.cfg (fun _ : Unit => clearStart stage) (clearFinish stage) extra state)

theorem clear_call (kind : Kind) (target source : Register) (stage : Fin 4)
    (contents : Stack → List Bool) (saved : Store) :
    ∃ path : Path (program kind target source)
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
      TM2.step (program kind target source) (transform a) = some (transform b) := by
    intro a b actual
    exact iso_inline_edge clearIso (fun _ : Unit => clearStart stage) (clearFinish stage)
      (saved.1.2, saved.2) (PDROC.BitVM.Kernel.Clear.program (clearSlot stage))
      (program kind target source) (clear_agrees kind target source stage) a b actual
  let transported := localPath.transport transform edge
  refine ⟨transported, ?_⟩
  exact (localPath.transport_length transform edge).trans length

theorem reset_step (kind : Kind) (target source : Register) (contents : Stack → List Bool) (saved : Store) :
    TM2.step (program kind target source) (before contents saved) =
      some (⟨some (control 1), clearedStore, contents⟩ : State) := rfl

theorem finish_step (kind : Kind) (target source : Register) (contents : Stack → List Bool) (saved : Store) :
    TM2.step (program kind target source) (⟨some (control 6), saved, contents⟩ : State) =
      some (⟨none, clearedStore, contents⟩ : State) := rfl

theorem field_step (kind : Kind) (target source : Register) (notNegative : kind ≠ .negative)
    (contents : Stack → List Bool) (saved : Store) :
    TM2.step (program kind target source) (⟨some (control 3), saved, contents⟩ : State) =
      some (⟨some (marshalLabels 0), saved, contents⟩ : State) := by
  cases kind with
  | numeratorAbs | denominator => rfl
  | negative => exact False.elim (notNegative rfl)

theorem negative_step (target source : Register) (contents : Stack → List Bool) (saved : Store)
    (empty : contents 0 = []) :
    TM2.step (program .negative target source) (⟨some (control 3), saved, contents⟩ : State) =
      some (⟨some (writerLabels 0), saved, Function.update contents 0 [true, false, saved.1.2]⟩ : State) := by
  change some (TM2.stepAux
    (.push 0 (fun saved : Store => saved.1.2) (.push 0 (fun _ => false)
      (.push 0 (fun _ => true) (.goto (fun _ => writerLabels 0))))) saved contents) = _
  simp only [TM2.stepAux, empty, Function.update_self]
  have updated : Function.update
      (Function.update (Function.update contents 0 [saved.1.2]) 0 [false, saved.1.2])
      0 [true, false, saved.1.2] = Function.update contents 0 [true, false, saved.1.2] := by
    funext role
    by_cases selected : role = 0 <;> simp_all
  rw [updated]

theorem bool_word (bit : Bool) :
    encodeNatBits (if bit then 1 else 0) = [true, false, bit] := by
  cases bit <;> decide

/-- The actual reader is selected ONCE and mapped into the caller. Its
real sign, both canonical field Cells, register frames and time all come
from the same final state, with the caller's writer store retained. -/
theorem reader_call (kind : Kind) (target source : Register) (value : ℚ)
    (contents : Stack → List Bool) (readerSaved : RatMarshal.Store) (writerSaved : WriterStore)
    (sourceCell : contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source) =
      encodeCellBits (.rational value)) (rightEmpty : contents 0 = []) (leftEmpty : contents 24 = []) :
    ∃ (ready : State) (path : Path (program kind target source)
      (⟨some (readerLabels 0), (readerSaved, writerSaved), contents⟩ : State) ready),
      ready.l = some (control 3) ∧ ready.var = ((none, decide (value < 0)), writerSaved) ∧
      ready.stk 0 = [] ∧ ready.stk 24 = [] ∧
      ready.stk 25 = encodeCellBits (.natural value.num.natAbs) ∧
      ready.stk 26 = encodeCellBits (.natural value.den) ∧
      (∀ reg, ready.stk (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot reg) =
        contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot reg)) ∧
      (∀ other, other ≠ 0 → other ≠ 24 → other ≠ 25 → other ≠ 26 → ready.stk other = contents other) ∧
      path.states.length ≤ 32 * (RatMarshal.inputSize source 0 1 contents + 1) := by
  obtain ⟨run, after, head, chain, last, _halt, halted, sign, right, left,
    num, den, frame, registers, time, _occupied⟩ :=
    RatMarshal.runs source 0 1 (by decide) value contents readerSaved sourceCell rightEmpty leftEmpty
  let localPath : Path (RatMarshal.program source 0 1 (by decide)) (RatMarshal.before contents readerSaved) after :=
    ⟨run, head, chain, last⟩
  let transform : RatMarshal.State → State := Inline.cfg readerLabels (control 3) writerSaved
  have edge : ∀ a b, TM2.step (RatMarshal.program source 0 1 (by decide)) a = some b →
      TM2.step (program kind target source) (transform a) = some (transform b) := by
    intro a b actual
    exact Inline.step_edge readerLabels (control 3) (RatMarshal.program source 0 1 (by decide))
      (program kind target source) (reader_agrees kind target source) a b writerSaved actual
  let transported := localPath.transport transform edge
  refine ⟨transform after, transported, ?_, ?_, right, left, num, den, registers, frame, ?_⟩
  · change some (after.l.map readerLabels |>.getD (control 3)) = some (control 3)
    rw [halted]
    rfl
  · change (after.var, writerSaved) = _
    rw [sign]
  · exact (localPath.transport_length transform edge).trans_le time

end PDROC.BitVM.Codec.FieldOps
