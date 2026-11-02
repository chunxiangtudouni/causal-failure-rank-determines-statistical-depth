module

public import Common.PSTR_SYM_OriginalBootstrap_058

/-! SOURCEONLY. ONE fixed finite-source parser loop. The actual zero bit
comes from the real cursor callee's final finite label. No test of an
unknown input TRUE/blank, host-selected machine or free restart is used.
Actual cycle/original remaining-count/EOF correctness is still required. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop

open Turing PSTRTMSeq005 PSTRSymbolicPairedArchive PSTRSymbolicCursorCode
open PSTRSymbolicCursorStages PSTRSymbolicRawBootstrap

inductive LoopLabel where
  | boot : Fin (bootSupport.card + 1) → LoopLabel
  | datum : Fin 110 → LoopLabel
  | cursor : Fin (PSTRSymbolicCursorFinite.support.card + 1) → LoopLabel
  | done : Bool → LoopLabel
  deriving DecidableEq, Fintype

instance : Inhabited LoopLabel := ⟨.boot 0⟩

/-- A static decoder of the callee's finite control. Its argument is the
ACTUAL q reached by the same code, not a ghost counter or output field. -/
noncomputable def cursorFinish (point : Fin (PSTRSymbolicCursorFinite.support.card + 1)) : LoopLabel :=
  match PSTRSymbolicRelabel.finiteDecode PSTRSymbolicCursorFinite.support point with
  | .halt false => .datum 0
  | .halt true => .done true
  | _ => .done false

noncomputable def loopCode : TM0.Machine Bool LoopLabel
  | .boot q, bit => calledCode bootstrapMachine LoopLabel.boot (fun _ => .datum 0) q bit
  | .datum q, bit => calledCode datumCompactMachine LoopLabel.datum (fun _ => .cursor 0) q bit
  | .cursor q, bit => calledCode PSTRSymbolicCursorFinite.cursorMachine LoopLabel.cursor cursorFinish q bit
  | .done _, _ => none

theorem cursor_finish (zero : Bool) :
    cursorFinish (PSTRSymbolicCursorFinite.labels (.halt zero)) =
      if zero then .done true else .datum 0 := by
  unfold cursorFinish
  rw [PSTRSymbolicCursorFinite.inverse_label]
  cases zero <;> rfl

theorem boot_return (final : MachineState bootSupport.card) (halt : TM0.step bootstrapMachine final = none) :
    TM0.step loopCode (tagCfg LoopLabel.boot final) = some ⟨.datum 0,final.Tape⟩ :=
  called_step_none loopCode bootstrapMachine LoopLabel.boot (fun _ => .datum 0)
    (by intro q bit; rfl) final halt

theorem datum_return (final : MachineState 109) (halt : TM0.step datumCompactMachine final = none) :
    TM0.step loopCode (tagCfg LoopLabel.datum final) = some ⟨.cursor 0,final.Tape⟩ :=
  called_step_none loopCode datumCompactMachine LoopLabel.datum (fun _ => .cursor 0)
    (by intro q bit; rfl) final halt

theorem cursor_return (final : MachineState PSTRSymbolicCursorFinite.support.card)
    (halt : TM0.step PSTRSymbolicCursorFinite.cursorMachine final = none) (zero : Bool)
    (port : final.q = PSTRSymbolicCursorFinite.labels (.halt zero)) :
    TM0.step loopCode (tagCfg LoopLabel.cursor final) =
      some ⟨if zero then .done true else .datum 0,final.Tape⟩ := by
  have edge := called_step_none loopCode PSTRSymbolicCursorFinite.cursorMachine LoopLabel.cursor cursorFinish
    (by intro q bit; rfl) final halt
  rw [port,cursor_finish] at edge
  exact edge

theorem loop_halt (zero : Bool) (tape : Tape Bool) : TM0.step loopCode ⟨.done zero,tape⟩ = none := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop
