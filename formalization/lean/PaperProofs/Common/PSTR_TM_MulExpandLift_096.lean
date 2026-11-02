module
public import PaperProofs.Common.PSTR_TM_MulExpandCode_095

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulExpandLift096
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulExpandCode095

theorem pad_command (savedA : Bool) (q next : Fin 41) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMPadInsert034.padMachine q symbol=some (next,statement)) :
    expandMachine (padLabel savedA q) symbol=some (padLabel savedA next,statement) := by
  have hq : q.val<40 := by
    have hb := q.isLt
    by_contra hn
    have he : q=(40 : Fin 41) := Fin.ext (by omega)
    subst q
    simp [PSTRTMPadInsert034.padMachine] at old
  cases savedA with
  | false =>
    simp [expandMachine,padLabel,show ¬11+q.val<11 by omega,show 11+q.val<52 by omega,
      show 11+q.val≠51 by omega,old]
  | true =>
    simp [expandMachine,padLabel,show ¬52+q.val<11 by omega,show ¬52+q.val<52 by omega,
      show 52+q.val<93 by omega,show 52+q.val≠92 by omega,old]

theorem pad_step (savedA : Bool) (before after : MachineState 40)
    (old : Turing.TM0.step PSTRTMPadInsert034.padMachine before=some after) :
    Turing.TM0.step expandMachine (liftPad savedA before)=some (liftPad savedA after) := by
  cases before with
  | mk q tape =>
    unfold Turing.TM0.step at old
    cases hc : PSTRTMPadInsert034.padMachine q tape.head with
    | none => simp [hc] at old
    | some command =>
      obtain ⟨next,statement⟩ := command
      simp only [hc,Option.map_some,Option.some.injEq] at old
      subst after
      have hm := pad_command savedA q next tape.head statement hc
      simp only [Turing.TM0.step,liftPad,hm,Option.map_some]

theorem pad_chain (savedA : Bool) (trace : List (MachineState 40))
    (old : trace.IsChain (fun a b => Turing.TM0.step PSTRTMPadInsert034.padMachine a=some b)) :
    (trace.map (liftPad savedA)).IsChain (fun a b => Turing.TM0.step expandMachine a=some b) :=
  (List.isChain_map _).mpr (old.imp (pad_step savedA))

theorem rewind_step (before : MachineState 3) :
    Turing.TM0.step expandMachine (liftRewind before)=
      (Turing.TM0.step PSTRTMMulRewind085.rewindMachine before).map liftRewind := by
  cases before with
  | mk q tape =>
    simp only [Turing.TM0.step,expandMachine,liftRewind,rewindLabel,
      show ¬108+q.val<11 by omega,show ¬108+q.val<52 by omega,
      show ¬108+q.val<93 by omega,show ¬108+q.val<108 by omega,
      dite_false,Nat.add_sub_cancel_left,Fin.eta]
    cases hc : PSTRTMMulRewind085.rewindMachine q tape.head with
    | none => simp
    | some command => obtain ⟨next,statement⟩ := command; cases statement <;> simp [liftRewind,rewindLabel]

theorem rewind_chain (trace : List (MachineState 3))
    (old : trace.IsChain (fun a b => Turing.TM0.step PSTRTMMulRewind085.rewindMachine a=some b)) :
    (trace.map liftRewind).IsChain (fun a b => Turing.TM0.step expandMachine a=some b) := by
  apply (List.isChain_map _).mpr
  apply old.imp
  intro before after hs
  rw [rewind_step,hs]
  rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulExpandLift096
