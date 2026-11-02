module
public import Structure.B23_5_RawInit_Public029

/-! Actual final-format branch at the common front port. A nonempty archive
has only TRUE EOF to the right and then blank FALSE; the empty Fin16 output
has TRUE in its next real row cell. One RIGHT/read/LEFT restores the whole
tape and either halts or enters the one statically installed callee. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.FinalSwitch
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
variable {a : Nat}

def bodyLabel (q : Fin (a+1)) : Fin ((a+3)+1) := ⟨3+q.val,by omega⟩
def bodyCfg (cfg : MachineState a) : MachineState (a+3) := ⟨bodyLabel cfg.q,cfg.Tape⟩

def machine (positive : Machine a) : Machine (a+3) := fun q bit =>
  if gate : q.val<3 then match q.val with
    | 0 => some (1,.move .right)
    | 1 => some ((if bit then 2 else bodyLabel (0 : Fin (a+1))),.move .left)
    | _ => none
  else (positive ⟨q.val-3,by omega⟩ bit).map (fun (next,op) => (bodyLabel next,op))

theorem step_body (positive : Machine a) (cfg : MachineState a) :
    TM0.step (machine positive) (bodyCfg cfg)=(TM0.step positive cfg).map bodyCfg := by
  cases cfg with
  | mk q tape =>
    simp only [TM0.step,machine,bodyCfg,bodyLabel,show ¬3+q.val<3 by omega,
      ↓reduceDIte,Nat.add_sub_cancel_left,Fin.eta]
    cases action : positive q tape.head with
    | none => rfl
    | some pair => obtain ⟨next,op⟩:=pair; cases op <;> rfl

def state (q : Fin ((a+3)+1)) (left right : List Bool) : MachineState (a+3) :=
  ⟨q,Tape.mk₂ left right⟩

theorem empty_actual (positive : Machine a) (left suffix : List Bool) :
    ∃ path, RunsFrom (machine positive) ⟨0,Tape.mk₂ left (true::true::suffix)⟩ path
      ⟨2,Tape.mk₂ left (true::true::suffix)⟩ ∧ path.length=3 := by
  refine ⟨[state 0 left (true::true::suffix),state 1 (true::left) (true::suffix),
    state 2 left (true::true::suffix)],⟨rfl,?_,rfl,?_⟩,rfl⟩
  · simp [List.isChain_cons_cons,state,TM0.step,machine,Tape.mk₂]
  · simp [TM0.step,machine,Tape.mk₂,Nat.mod_eq_of_lt (show 2<a+3+1 by omega)]

theorem empty_fin16 (positive : Machine a) :
    ∃ path, RunsFrom (machine positive)
      ⟨0,Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode []))⟩ path
      ⟨2,Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode []))⟩ ∧ path.length=3 := by
  let tail:=(FiniteTrackCodec.encodedInput (0 : Fin 16) (encode [])).drop 2
  have shape : FiniteTrackCodec.encodedInput (0 : Fin 16) (encode [])=true::true::tail := by
    rw [encoded_raw_shape]
    rfl
  obtain ⟨path,run,time⟩:=empty_actual positive [] tail
  exact ⟨path,by simpa only [←shape,Tape.mk₁] using run,time⟩

theorem positive_actual (positive : Machine a) (left : List Bool)
    (back : List (MachineState a)) (final : MachineState a)
    (run : RunsFrom positive ⟨0,Tape.mk₂ left [true]⟩ back final) :
    ∃ path, RunsFrom (machine positive) ⟨0,Tape.mk₂ left [true]⟩ path (bodyCfg final) ∧
      path.length=back.length+2 := by
  let lead : List (MachineState (a+3)) := [state 0 left [true],state 1 (true::left) []]
  let path:=lead++back.map bodyCfg
  have chain : path.IsChain (fun before after => TM0.step (machine positive) before=some after) := by
    apply List.IsChain.append
    · simp [lead,List.isChain_cons_cons,state,TM0.step,machine,Tape.mk₂]
    · apply (List.isChain_map _).mpr
      exact run.2.1.imp (fun before after edge => by simp only [step_body,edge,Option.map_some])
    · intro before beforeLast after afterHead
      simp only [lead,List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at beforeLast
      simp only [List.head?_map,run.1,Option.map_some,Option.mem_some_iff] at afterHead
      subst before
      subst after
      simp [state,TM0.step,machine,bodyCfg,bodyLabel,Tape.mk₂]
  refine ⟨path,⟨?_,chain,?_,?_⟩,?_⟩
  · simp only [path,lead,List.head?_append,List.head?_cons,Option.some_or]
    rfl
  · simp only [path,List.getLast?_append,List.getLast?_map,run.2.2.1,Option.map_some,Option.some_or]
  · simp only [step_body,run.2.2.2,Option.map_none]
  · simp only [path,lead,List.length_append,List.length_cons,List.length_nil,List.length_map]
    omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.FinalSwitch
