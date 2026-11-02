module
public import Common.PSTR_TM_PackRightPadRun_145

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackFrameCode146
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036

/-- SAME194 fixed labels. Only the old embedded left-consuming padding
range is replaced by the genuine right-insertion code144. Every other
command, including unequal-width/zero branches, is the original036 code. -/
def packMachine : Machine 193 := fun q symbol =>
  if h : 145≤q.val ∧ q.val<186 then
    if q.val=185 then some (0,.write symbol)
    else (PSTRTMPackRightPadCode144.padMachine ⟨q.val-145,by omega⟩ symbol).map
      (fun (next,statement) => (embedPad next,statement))
  else PSTRTMPackCode036.packMachine q symbol

def Outside (configuration : MachineState 193) : Prop := configuration.q.val<145 ∨ 186≤configuration.q.val

theorem outside_command (q : Fin 194) (symbol : Bool) (hq : q.val<145 ∨ 186≤q.val) :
    packMachine q symbol=PSTRTMPackCode036.packMachine q symbol := by
  have hn : ¬(145≤q.val ∧ q.val<186) := by omega
  simp only [packMachine,dite_eq_right hn]

theorem outside_step (before : MachineState 193) (hq : Outside before) :
    Turing.TM0.step packMachine before=Turing.TM0.step PSTRTMPackCode036.packMachine before := by
  cases before with
  | mk q tape =>
    simp only [Turing.TM0.step,outside_command q tape.head hq]

theorem transfer_chain (trace : List (MachineState 193))
    (safe : ∀ configuration∈trace,Outside configuration)
    (old : trace.IsChain (fun before after => Turing.TM0.step PSTRTMPackCode036.packMachine before=some after)) :
    trace.IsChain (fun before after => Turing.TM0.step packMachine before=some after) := by
  apply List.IsChain.imp_of_mem_imp (p:=old)
  intro before after hb _ hs
  rw [outside_step before (safe before hb)]
  exact hs

theorem align_outside (before : MachineState 134) : Outside (liftAlign before) := by
  left
  change before.q.val+10<145
  have h := before.q.isLt
  omega

theorem align_step (before after : MachineState 134)
    (old : Turing.TM0.step PSTRTMAlignCode030.alignMachine before=some after) :
    Turing.TM0.step packMachine (liftAlign before)=some (liftAlign after) := by
  rw [outside_step _ (align_outside before)]
  exact PSTRTMPackLift037.align_step before after old

theorem align_chain (trace : List (MachineState 134))
    (old : trace.IsChain (fun before after => Turing.TM0.step PSTRTMAlignCode030.alignMachine before=some after)) :
    (trace.map liftAlign).IsChain (fun before after => Turing.TM0.step packMachine before=some after) := by
  apply (List.isChain_map _).mpr
  exact old.imp align_step

theorem pad_command (q next : Fin 41) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMPackRightPadCode144.padMachine q symbol=some (next,statement)) :
    packMachine (embedPad q) symbol=some (embedPad next,statement) := by
  have hn : q.val≠40 := by
    intro he
    simp [PSTRTMPackRightPadCode144.padMachine,he] at old
  have hlo : 145≤q.val+145 := by omega
  have hhi : q.val+145<186 := by omega
  have halt : q.val+145≠185 := by omega
  simp [packMachine,embedPad,hlo,hhi,halt,old]

theorem pad_step (before after : MachineState 40)
    (old : Turing.TM0.step PSTRTMPackRightPadCode144.padMachine before=some after) :
    Turing.TM0.step packMachine (liftPad before)=some (liftPad after) := by
  cases before with
  | mk q tape =>
    unfold Turing.TM0.step at old
    cases hc : PSTRTMPackRightPadCode144.padMachine q tape.head with
    | none => simp [hc] at old
    | some command =>
      obtain ⟨next,statement⟩ := command
      simp only [hc,Option.map_some,Option.some.injEq] at old
      subst after
      have hm := pad_command q next tape.head statement hc
      simp only [Turing.TM0.step,liftPad,hm,Option.map_some]

theorem pad_chain (trace : List (MachineState 40))
    (old : trace.IsChain (fun before after => Turing.TM0.step PSTRTMPackRightPadCode144.padMachine before=some after)) :
    (trace.map liftPad).IsChain (fun before after => Turing.TM0.step packMachine before=some after) := by
  apply (List.isChain_map _).mpr
  exact old.imp pad_step

theorem align_transfer (left right : List Bool) :
    Turing.TM0.step packMachine (liftAlign (PSTRTMAlignCode030.state 134 left right))=
      some (state 0 left right) := by
  rw [outside_step _ (align_outside _)]
  exact PSTRTMPackLift037.align_transfer _ _

theorem pad_transfer (left right : List Bool) :
    Turing.TM0.step packMachine (liftPad (PSTRTMPackRightPadCode144.state 40 left right))=
      some (state 0 left right) := by
  simp [Turing.TM0.step,packMachine,liftPad,embedPad,PSTRTMPackRightPadCode144.state,state,Turing.Tape.write_self]

theorem pack_halt (left right : List Bool) : Turing.TM0.step packMachine (state 192 left right)=none := by
  have h : Outside (state 192 left right) := by right; norm_num [Outside,state]
  rw [outside_step _ h]
  exact PSTRTMPackCode036.pack_halt _ _

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackFrameCode146
