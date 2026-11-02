module
public import RootB235_ArchiveStaging_Macro003

/-! Actual flag-parity walks for the serializer's finite controller.
Both directions preserve every payload and stop at the first real TRUE flag.
The caller supplies only its static table lookup, never a runtime length. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
open Turing RationalControllerComputation

namespace Navigation

def state {L : Type} (q : L) (left right : List Bool) : TM0.Cfg Bool (Macro.Label L) :=
  ⟨.at q,Tape.mk₂ left right⟩

def leftStart {L : Type} (q : L) (left : List Bool) (boundary : Bool) :
    List Bool → List Bool → TM0.Cfg Bool (Macro.Label L)
  | [],suffix => state q left (true::boundary::suffix)
  | bit::later,suffix => state q (Restore.reversePairs later++boundary::true::left) (false::bit::suffix)

def left {L : Type} [Inhabited L] (program : L → Macro.Instruction L)
    (flag payload one yes : L)
    (read : program flag=.branch payload yes)
    (payloadStep : program payload=.action (.move .left) one)
    (oneStep : program one=.action (.move .left) flag)
    (west bits suffix : List Bool) (boundary : Bool) :
    Segment (Macro.code program) (leftStart flag west boundary bits suffix)
      (state yes west (true::boundary::(MarkSeek.pairs bits.reverse++suffix))) (6*bits.length+2) := by
  induction bits generalizing suffix with
  | nil =>
    exact Segment.edge (by
      simp [leftStart,state,Macro.code,read,TM0.step,Tape.mk₂,MarkSeek.pairs])
  | cons bit later ih =>
    let older := Restore.reversePairs later++boundary::true::west
    let a := leftStart flag west boundary (bit::later) suffix
    let b := state payload older (false::bit::suffix)
    let c := state one older.tail (older.headD false::false::bit::suffix)
    have ab : TM0.step (Macro.code program) a=some b := by
      simp [a,b,leftStart,older,state,Macro.code,read,TM0.step,Tape.mk₂]
    have bc : TM0.step (Macro.code program) b=some c := by
      cases later <;> simp [b,c,older,Restore.reversePairs,state,Macro.code,payloadStep,TM0.step,Tape.mk₂]
    have cd : TM0.step (Macro.code program) c=
        some (leftStart flag west boundary later (false::bit::suffix)) := by
      cases later <;> simp [c,older,leftStart,Restore.reversePairs,state,Macro.code,oneStep,TM0.step,Tape.mk₂]
    have result := (((Segment.edge ab).trans (Segment.edge bc)).trans (Segment.edge cd)).trans
      (ih (false::bit::suffix))
    have layout : MarkSeek.pairs (bit::later).reverse++suffix=
        MarkSeek.pairs later.reverse++false::bit::suffix := by
      simp [MarkSeek.pairs,List.reverse_cons,List.flatMap_append,List.append_assoc]
    rw [layout]
    exact result.weaken (by simp only [List.length_cons];omega)

def right {L : Type} [Inhabited L] (program : L → Macro.Instruction L)
    (flag payload one yes : L)
    (read : program flag=.branch payload yes)
    (payloadStep : program payload=.action (.move .right) one)
    (oneStep : program one=.action (.move .right) flag)
    (west bits suffix : List Bool) :
    Segment (Macro.code program) (state flag west (MarkSeek.pairs bits++true::suffix))
      (state yes ((MarkSeek.pairs bits).reverse++west) (true::suffix)) (6*bits.length+2) := by
  induction bits generalizing west with
  | nil =>
    exact Segment.edge (by simp [state,Macro.code,read,TM0.step,Tape.mk₂,MarkSeek.pairs])
  | cons bit later ih =>
    let tail := MarkSeek.pairs later++true::suffix
    let a := state flag west (false::bit::tail)
    let b := state payload west (false::bit::tail)
    let c := state one (false::west) (bit::tail)
    let d := state flag (bit::false::west) tail
    have ab : TM0.step (Macro.code program) a=some b := by
      simp [a,b,state,Macro.code,read,TM0.step,Tape.mk₂]
    have bc : TM0.step (Macro.code program) b=some c := by
      simp [b,c,state,Macro.code,payloadStep,TM0.step,Tape.mk₂]
    have cd : TM0.step (Macro.code program) c=some d := by
      simp [c,d,state,Macro.code,oneStep,TM0.step,Tape.mk₂]
    have result := (((Segment.edge ab).trans (Segment.edge bc)).trans (Segment.edge cd)).trans
      (ih (bit::false::west))
    simpa [a,tail,MarkSeek.pairs,List.append_assoc] using
      result.weaken (t:=6*(bit::later).length+2) (by simp only [List.length_cons];omega)

end Navigation
end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
