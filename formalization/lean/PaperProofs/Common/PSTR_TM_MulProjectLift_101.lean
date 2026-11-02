module
public import PaperProofs.Common.PSTR_TM_MulProjectCode_100
public import PaperProofs.Common.PSTR_TM_MulExpandUnit_097
import Mathlib.Tactic.NormNum

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulProjectLift101
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulProjectCode100

theorem retained_command (q next : Fin 112) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (hq : q.val<93) (old : PSTRTMMulExpandCode095.expandMachine q symbol=some (next,statement)) :
    prepareMachine (oldLabel q) symbol=some (oldLabel next,statement) := by
  simp [prepareMachine,oldLabel,show ¬2+q.val<2 by omega,show 2+q.val<114 by omega,
    show 2+q.val≠101 by omega,show 2+q.val≠102 by omega,
    show 2+q.val≠108 by omega,show 2+q.val≠109 by omega,old]

theorem retained_step (before after : MachineState 111) (hq : before.q.val<93)
    (old : Turing.TM0.step PSTRTMMulExpandCode095.expandMachine before=some after) :
    Turing.TM0.step prepareMachine (liftOld before)=some (liftOld after) := by
  cases before with
  | mk q tape =>
    unfold Turing.TM0.step at old
    cases hc : PSTRTMMulExpandCode095.expandMachine q tape.head with
    | none => simp [hc] at old
    | some command =>
      obtain ⟨next,statement⟩ := command
      simp only [hc,Option.map_some,Option.some.injEq] at old
      subst after
      have hm := retained_command q next tape.head statement hq hc
      simp only [Turing.TM0.step,liftOld,hm,Option.map_some]

def liftPad (a : Bool) (old : MachineState 40) : MachineState 114 :=
  liftOld (PSTRTMMulExpandCode095.liftPad a old)

theorem pad_step (a : Bool) (before after : MachineState 40)
    (old : Turing.TM0.step PSTRTMPadInsert034.padMachine before=some after) :
    Turing.TM0.step prepareMachine (liftPad a before)=some (liftPad a after) := by
  apply retained_step _ _ _ (PSTRTMMulExpandLift096.pad_step a before after old)
  have hq := before.q.isLt
  have ha := Bool.toNat_le a
  change 11+41*a.toNat+before.q.val<93
  omega

theorem pad_chain (a : Bool) (trace : List (MachineState 40))
    (old : trace.IsChain (fun x y => Turing.TM0.step PSTRTMPadInsert034.padMachine x=some y)) :
    (trace.map (liftPad a)).IsChain (fun x y => Turing.TM0.step prepareMachine x=some y) :=
  (List.isChain_map _).mpr (old.imp (pad_step a))

def markTrace (digits : List Bool) (a b : Bool) (tail : List Bool) : List (MachineState 114) :=
  (PSTRTMMulExpandUnit097.markTrace digits a b tail).map liftOld

theorem mark_head (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (markTrace digits a b tail).head?=some (liftOld
      (PSTRTMMulExpandCode095.state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (a::true::b::true::tail))) := by
  simp only [markTrace,List.head?_map,PSTRTMMulExpandUnit097.mark_head,Option.map_some]
theorem mark_last (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (markTrace digits a b tail).getLast?=some (liftOld (PSTRTMMulExpandCode095.state
      (PSTRTMMulExpandUnit097.modeLabel 9 a) (true::PSTRTMRawNat010.leftBlocks digits.reverse) (false::b::true::tail))) := by
  simp only [markTrace,List.getLast?_map,PSTRTMMulExpandUnit097.mark_last,Option.map_some]

theorem mark_chain (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (markTrace digits a b tail).IsChain (fun x y => Turing.TM0.step prepareMachine x=some y) := by
  apply (List.isChain_map _).mpr
  apply (PSTRTMMulExpandUnit097.mark_chain digits a b tail).imp_of_mem_imp
  intro before after hbefore _ hs
  apply retained_step before after _ hs
  simp only [PSTRTMMulExpandUnit097.markTrace,List.mem_cons,List.not_mem_nil,or_false] at hbefore
  rcases hbefore with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    cases a <;> norm_num [PSTRTMMulExpandCode095.state,PSTRTMMulExpandUnit097.modeLabel]

theorem mark_advance (digits : List Bool) (a b : Bool) (tail : List Bool) :
    Turing.TM0.step prepareMachine (liftOld (PSTRTMMulExpandCode095.state
      (PSTRTMMulExpandUnit097.modeLabel 9 a) (true::PSTRTMRawNat010.leftBlocks digits.reverse) (false::b::true::tail)))=
      some (liftPad a (PSTRTMPadInsert034.state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (true::false::b::true::tail))) := by
  apply retained_step _ _ _ (PSTRTMMulExpandUnit097.mark_advance digits a b tail)
  change 9+a.toNat<93
  have ha := Bool.toNat_le a
  omega

def liftRewind (old : MachineState 3) : MachineState 114 :=
  liftOld (PSTRTMMulExpandCode095.liftRewind old)

theorem rewind_step (before : MachineState 3) :
    Turing.TM0.step prepareMachine (liftRewind before)=
      (Turing.TM0.step PSTRTMMulRewind085.rewindMachine before).map liftRewind := by
  cases before with
  | mk q tape =>
    have hq := q.isLt
    simp only [Turing.TM0.step,prepareMachine,liftRewind,liftOld,oldLabel,
      PSTRTMMulExpandCode095.liftRewind,PSTRTMMulExpandCode095.rewindLabel,
      show ¬2+(108+q.val)<2 by omega,show 2+(108+q.val)<114 by omega,
      show 2+(108+q.val)≠101 by omega,show 2+(108+q.val)≠102 by omega,
      show 2+(108+q.val)≠108 by omega,show 2+(108+q.val)≠109 by omega,
      dite_false,dite_true,Nat.add_sub_cancel_left]
    cases hc : PSTRTMMulRewind085.rewindMachine q tape.head with
    | none => simp [PSTRTMMulExpandCode095.expandMachine,
        show ¬108+q.val<11 by omega,show ¬108+q.val<52 by omega,
        show ¬108+q.val<93 by omega,show ¬108+q.val<108 by omega,hc]
    | some command =>
      obtain ⟨next,statement⟩ := command
      cases statement <;> simp [PSTRTMMulExpandCode095.expandMachine,PSTRTMMulExpandCode095.rewindLabel,
        show ¬108+q.val<11 by omega,show ¬108+q.val<52 by omega,
        show ¬108+q.val<93 by omega,show ¬108+q.val<108 by omega,hc,
        liftRewind,liftOld,oldLabel,PSTRTMMulExpandCode095.liftRewind]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulProjectLift101
