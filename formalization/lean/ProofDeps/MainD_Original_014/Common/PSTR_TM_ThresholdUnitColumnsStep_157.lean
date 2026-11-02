module
public import Common.PSTR_TM_ThresholdUnitColumnsCode_156

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdUnitColumnsStep157
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdUnitColumnsCode156 PSTRTMOverlap132

attribute [local implicit_reducible] Turing.TM0.Machine padLabel postLabel

theorem pad_command (first bit : Bool) (q : Fin 41) (symbol : Bool) :
    unitMachine (padLabel first bit q) symbol=
      match PSTRTMPackRightPadCode144.padMachine q symbol with
      | none => some (postLabel first bit 0,.write symbol)
      | some (next,statement) => some (padLabel first bit next,statement) := by
  have hs := saved_lt first bit
  have hq := q.isLt
  have h0 : ¬14+41*saved first bit+q.val<2 := by omega
  have h1 : ¬14+41*saved first bit+q.val<6 := by omega
  have h2 : ¬14+41*saved first bit+q.val<10 := by omega
  have h3 : ¬14+41*saved first bit+q.val<14 := by omega
  have h4 : 14+41*saved first bit+q.val<178 := by omega
  have hd : (14+41*saved first bit+q.val-14)/41=saved first bit := by omega
  have hm : (14+41*saved first bit+q.val-14)%41=q.val := by omega
  conv_lhs =>
    unfold unitMachine
    dsimp only [padLabel]
  rw [dite_eq_right h0,dite_eq_right h1,dite_eq_right h2,dite_eq_right h3,dite_eq_left h4]
  simp only [hd,hm,Fin.eta]
  cases h : PSTRTMPackRightPadCode144.padMachine q symbol with
  | none => rfl
  | some value => obtain ⟨next,statement⟩ := value; rfl

theorem pad_step (first bit : Bool) (configuration : MachineState 40) :
    Turing.TM0.step unitMachine (liftPad first bit configuration)=
      match Turing.TM0.step PSTRTMPackRightPadCode144.padMachine configuration with
      | none => some ⟨postLabel first bit 0,configuration.Tape⟩
      | some next => some (liftPad first bit next) := by
  cases configuration with
  | mk q tape =>
    simp only [liftPad,Turing.TM0.step,pad_command]
    cases h : PSTRTMPackRightPadCode144.padMachine q tape.head with
    | none => simp [Turing.Tape.write_self]
    | some value =>
      obtain ⟨next,statement⟩ := value
      cases statement <;> simp

/-- Decode the finite saved-bit modes before reasoning about tape.
This keeps the post trace proof local instead of expanding214-label code
repeatedly under a large conjunction of concrete tape configurations. -/
theorem post_command (first bit : Bool) (phase : Fin 8) (symbol : Bool) :
    unitMachine (postLabel first bit phase) symbol=
      match phase.val with
      | 0 => some (postLabel first bit 1,.write first)
      | 1 => some (postLabel first bit 2,.move .right)
      | 2 => some (postLabel first bit 3,.write true)
      | 3 => some (postLabel first bit 4,.move .right)
      | 4 => some (postLabel first bit 5,.write bit)
      | 5 => some (postLabel first bit 6,.move .right)
      | 6 => some (postLabel first bit 7,.write true)
      | _ => some (1,.move .right) := by
  have hs := saved_lt first bit
  have hp := phase.isLt
  have h0 : ¬178+8*saved first bit+phase.val<2 := by omega
  have h1 : ¬178+8*saved first bit+phase.val<6 := by omega
  have h2 : ¬178+8*saved first bit+phase.val<10 := by omega
  have h3 : ¬178+8*saved first bit+phase.val<14 := by omega
  have h4 : ¬178+8*saved first bit+phase.val<178 := by omega
  have h5 : 178+8*saved first bit+phase.val<210 := by omega
  have hd : (178+8*saved first bit+phase.val-178)/8=saved first bit := by omega
  have hm : (178+8*saved first bit+phase.val-178)%8=phase.val := by omega
  have ha : (if saved first bit<2 then true else false)=first := by cases first <;> cases bit <;> decide
  have hb : (if saved first bit%2=1 then true else false)=bit := by cases first <;> cases bit <;> decide
  conv_lhs =>
    unfold unitMachine
    dsimp only [postLabel]
  rw [dite_eq_right h0,dite_eq_right h1,dite_eq_right h2,dite_eq_right h3,dite_eq_right h4,dite_eq_left h5]
  rw [hd,hm,ha,hb]
  fin_cases phase <;> rfl

def startLabel (first : Bool) : Fin 214 := if first then 0 else 1
def readLabel (first bit : Bool) : Fin 214 := ⟨2+saved first bit,by have hs := saved_lt first bit; omega⟩
def markLabel (first bit : Bool) : Fin 214 := ⟨6+saved first bit,by have hs := saved_lt first bit; omega⟩
def dataLabel (first bit : Bool) : Fin 214 := ⟨10+saved first bit,by have hs := saved_lt first bit; omega⟩

def entryTrace (first bit : Bool) (left later : List Bool) : List (MachineState 213) :=
  [state (startLabel first) left (bit::true::PSTRTMIncrement009.blocks later),
    state (readLabel first bit) (bit::left) (true::PSTRTMIncrement009.blocks later),
    state (markLabel first bit) (bit::left) (false::PSTRTMIncrement009.blocks later),
    state (dataLabel first bit) left (bit::false::PSTRTMIncrement009.blocks later),
    state (padLabel first bit 0) left (true::false::PSTRTMIncrement009.blocks later)]

theorem entry_chain (first bit : Bool) (left later : List Bool) :
    (entryTrace first bit left later).IsChain
      (fun before after => Turing.TM0.step unitMachine before=some after) := by
  cases first <;> cases bit <;>
    simp [entryTrace,List.isChain_cons_cons,state,startLabel,readLabel,markLabel,dataLabel,
      padLabel,saved,Turing.TM0.step,unitMachine,Turing.Tape.mk₂]

def postTrace (first bit : Bool) (left later : List Bool) : List (MachineState 213) :=
  [state (padLabel first bit 40) left (false::false::true::false::PSTRTMIncrement009.blocks later),
    state (postLabel first bit 0) left (false::false::true::false::PSTRTMIncrement009.blocks later),
    state (postLabel first bit 1) left (first::false::true::false::PSTRTMIncrement009.blocks later),
    state (postLabel first bit 2) (first::left) (false::true::false::PSTRTMIncrement009.blocks later),
    state (postLabel first bit 3) (first::left) (true::true::false::PSTRTMIncrement009.blocks later),
    state (postLabel first bit 4) (true::first::left) (true::false::PSTRTMIncrement009.blocks later),
    state (postLabel first bit 5) (true::first::left) (bit::false::PSTRTMIncrement009.blocks later),
    state (postLabel first bit 6) (bit::true::first::left) (false::PSTRTMIncrement009.blocks later),
    state (postLabel first bit 7) (bit::true::first::left) (true::PSTRTMIncrement009.blocks later),
    state 1 (true::bit::true::first::left) (PSTRTMIncrement009.blocks later)]

theorem post_chain (first bit : Bool) (left later : List Bool) :
    (postTrace first bit left later).IsChain
      (fun before after => Turing.TM0.step unitMachine before=some after) := by
  unfold postTrace
  apply List.isChain_cons_cons.mpr
  constructor
  · change Turing.TM0.step unitMachine
      (liftPad first bit (PSTRTMPackRightPadCode144.state 40 left
        (false::false::true::false::PSTRTMIncrement009.blocks later)))=_
    rw [pad_step,PSTRTMPackRightPadCode144.pad_halt]
    rfl
  · simp [List.isChain_cons_cons,Turing.TM0.step,post_command,state,Turing.Tape.mk₂]

def padTrace (first bit : Bool) (left later : List Bool) : List (MachineState 213) :=
  (PSTRTMPackRightPadRun145.padTrace left later).map (liftPad first bit)

theorem pad_head (first bit : Bool) (left later : List Bool) :
    (padTrace first bit left later).head?=some
      (state (padLabel first bit 0) left (true::false::PSTRTMIncrement009.blocks later)) := by
  simpa only [padTrace,List.head?_map,liftPad,state,PSTRTMPackRightPadCode144.state,Option.map_some] using
    congrArg (Option.map (liftPad first bit)) (PSTRTMPackRightPadRun145.pad_runsFrom left later).1

theorem pad_last (first bit : Bool) (left later : List Bool) :
    (padTrace first bit left later).getLast?=some
      (state (padLabel first bit 40) left (false::false::true::false::PSTRTMIncrement009.blocks later)) := by
  simpa only [padTrace,List.getLast?_map,liftPad,state,PSTRTMPackRightPadCode144.state,Option.map_some] using
    congrArg (Option.map (liftPad first bit)) (PSTRTMPackRightPadRun145.pad_runsFrom left later).2.2.1

theorem pad_chain (first bit : Bool) (left later : List Bool) :
    (padTrace first bit left later).IsChain
      (fun before after => Turing.TM0.step unitMachine before=some after) := by
  apply (List.isChain_map _).mpr
  apply (PSTRTMPackRightPadRun145.pad_runsFrom left later).2.1.imp
  intro before after h
  simp only [pad_step,h]

def unitTrace (first bit : Bool) (left later : List Bool) : List (MachineState 213) :=
  glue (entryTrace first bit left later) (glue (padTrace first bit left later) (postTrace first bit left later))

theorem unit_head (first bit : Bool) (left later : List Bool) :
    (unitTrace first bit left later).head?=some
      (state (startLabel first) left (bit::true::PSTRTMIncrement009.blocks later)) :=
  glue_head _ _ _ _ rfl rfl (glue_head _ _ _ _ (pad_head _ _ _ _) (pad_last _ _ _ _) rfl)

theorem unit_last (first bit : Bool) (left later : List Bool) :
    (unitTrace first bit left later).getLast?=some
      (state 1 (true::bit::true::first::left) (PSTRTMIncrement009.blocks later)) :=
  glue_last _ _ _ (glue_last _ _ _ rfl)

theorem unit_chain (first bit : Bool) (left later : List Bool) :
    (unitTrace first bit left later).IsChain
      (fun before after => Turing.TM0.step unitMachine before=some after) :=
  glue_chain unitMachine _ _ _ (entry_chain _ _ _ _)
    (glue_chain unitMachine _ _ _ (pad_chain _ _ _ _) (post_chain _ _ _ _) (pad_last _ _ _ _) rfl)
    rfl (glue_head _ _ _ _ (pad_head _ _ _ _) (pad_last _ _ _ _) rfl)

theorem unit_length (first bit : Bool) (left later : List Bool) :
    (unitTrace first bit left later).length=12*later.length+30 := by
  simp only [unitTrace,glue_length,entryTrace,postTrace,padTrace,List.length_map,
    List.length_cons,List.length_nil,PSTRTMPackRightPadRun145.pad_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdUnitColumnsStep157
