module
public import RootB235_ArchiveStaging_Control006
public import RootB235_ArchiveStaging_Navigation008

/-! The original controller's actual count preparation path q0 to q94.
Every work payload is erased, while every retained original-count payload
is preserved in physical digit order. No numeric work invariant is used. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
open RationalControllerComputation.PSTRTMRawNat010

namespace CountPrepare

abbrev sourceCode := Macro.code Control.program
def state (loc : Fin 98) (left right : List Bool) : TM0.Cfg Bool (Macro.Label (Fin 98)) :=
  ⟨.at loc,Tape.mk₂ left right⟩

def eraseStart (base : List Bool) : List Bool → List Bool → TM0.Cfg Bool (Macro.Label (Fin 98))
  | [],suffix => state 71 base (false::suffix)
  | bit::later,suffix => state 71 (bit::(leftBlocks later++false::base)) (true::suffix)

def enter (base : List Bool) (first second : Bool) (later suffix : List Bool) :
    Segment sourceCode (state 0 (leftBlocks (first::second::later)++false::base) (false::suffix))
      (eraseStart base (first::second::later) (false::suffix)) 19 := by
  apply follow_actual sourceCode 9
  simp [follow,state,eraseStart,leftBlocks,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂]

def eraseWork (base todo suffix : List Bool) :
    Segment sourceCode (eraseStart base todo suffix)
      (state 76 base (false::(List.replicate (2*todo.length) false++suffix))) (10*todo.length+2) := by
  induction todo generalizing suffix with
  | nil =>
    exact Segment.edge (by simp [eraseStart,state,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂])
  | cons bit later ih =>
    let west := leftBlocks later++false::base
    let a := eraseStart base (bit::later) suffix
    let b := state 72 (bit::west) (true::suffix)
    let c := state 73 (bit::west) (false::suffix)
    let d := state 74 west (bit::false::suffix)
    let e := state 75 west (false::false::suffix)
    have ab : TM0.step sourceCode a=some b := by
      simp [a,b,eraseStart,west,state,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂]
    have bc : TM0.step sourceCode b=some c := by
      simp [b,c,state,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂]
    have cd : TM0.step sourceCode c=some d := by
      simp [c,d,state,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂]
    have de : TM0.step sourceCode d=some e := by
      simp [d,e,state,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂]
    have ef : TM0.step sourceCode e=some (eraseStart base later (false::false::suffix)) := by
      cases later <;> simp [e,west,eraseStart,leftBlocks,state,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂]
    have result := (((((Segment.edge ab).trans (Segment.edge bc)).trans (Segment.edge cd)).trans
      (Segment.edge de)).trans (Segment.edge ef)).trans (ih (false::false::suffix))
    have padding : List.replicate (2*later.length) false++false::false::suffix=
        List.replicate (2*(bit::later).length) false++suffix := by
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one,List.replicate_succ,List.cons_append]
      rw [ReverseCleanup.zeros_succ,ReverseCleanup.zeros_succ]
    rw [padding] at result
    exact result.weaken (by simp only [List.length_cons];omega)

def shiftStart : List Bool → List Bool → TM0.Cfg Bool (Macro.Label (Fin 98))
  | [],suffix => state 80 [] (false::suffix)
  | bit::later,suffix => state 80 (bit::leftBlocks later) (true::suffix)

def bankEntry (last : Bool) (older suffix : List Bool) :
    Segment sourceCode (state 76 (false::true::last::leftBlocks older) (false::suffix))
      (shiftStart older (last::true::false::false::suffix)) 9 := by
  apply follow_actual sourceCode 4
  cases older <;> simp [follow,state,shiftStart,leftBlocks,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂]

def clearFlags (todo suffix : List Bool) :
    Segment sourceCode (shiftStart todo suffix)
      (state 84 [] (MarkSeek.pairs todo.reverse++false::suffix)) (8*todo.length+2) := by
  induction todo generalizing suffix with
  | nil =>
    exact Segment.edge (by simp [shiftStart,state,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂,MarkSeek.pairs])
  | cons bit later ih =>
    let a := shiftStart (bit::later) suffix
    let b := state 81 (bit::leftBlocks later) (true::suffix)
    let c := state 82 (bit::leftBlocks later) (false::suffix)
    let d := state 83 (leftBlocks later) (bit::false::suffix)
    have ab : TM0.step sourceCode a=some b := by
      simp [a,b,shiftStart,state,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂]
    have bc : TM0.step sourceCode b=some c := by
      simp [b,c,state,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂]
    have cd : TM0.step sourceCode c=some d := by
      simp [c,d,state,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂]
    have de : TM0.step sourceCode d=some (shiftStart later (bit::false::suffix)) := by
      cases later <;> simp [d,shiftStart,leftBlocks,state,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂]
    have result := ((((Segment.edge ab).trans (Segment.edge bc)).trans (Segment.edge cd)).trans
      (Segment.edge de)).trans (ih (bit::false::suffix))
    have layout : MarkSeek.pairs (bit::later).reverse++false::suffix=
        MarkSeek.pairs later.reverse++false::bit::false::suffix := by
      simp [MarkSeek.pairs,List.reverse_cons,List.flatMap_append,List.append_assoc]
    rw [layout]
    exact result.weaken (by simp only [List.length_cons];omega)

theorem zero_pairs (n : Nat) : MarkSeek.pairs (List.replicate n false)=List.replicate (2*n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change false::false::MarkSeek.pairs (List.replicate n false)=List.replicate (2*(n+1)) false
    rw [ih,show 2*(n+1)=2*n+1+1 by omega,List.replicate_succ,List.replicate_succ]

theorem padding (n : Nat) (suffix : List Bool) :
    false::false::(List.replicate (2*n) false++false::suffix)=
      false::(List.replicate (2*(n+1)) false++suffix) := by
  rw [show 2*(n+1)=2*n+1+1 by omega,List.replicate_succ,List.replicate_succ]
  simp only [List.cons_append]
  rw [ReverseCleanup.zeros_succ]

theorem suffix_layout (work higher output : List Bool) (gap : Nat) :
    false::false::(List.replicate (2*work.length) false++false::Macro.suffix higher output gap)=
      false::Macro.suffix (List.replicate (work.length+1) false++higher) output gap := by
  have appendPairs : MarkSeek.pairs (List.replicate (work.length+1) false++higher)=
      List.replicate (2*(work.length+1)) false++MarkSeek.pairs higher := by
    rw [show MarkSeek.pairs (List.replicate (work.length+1) false++higher)=
        MarkSeek.pairs (List.replicate (work.length+1) false)++MarkSeek.pairs higher by
      simp [MarkSeek.pairs,List.flatMap_append],zero_pairs]
  simpa only [Macro.suffix,appendPairs,List.append_assoc] using
    padding work.length (Macro.suffix higher output gap)

def markBoundary (right : List Bool) :
    Segment sourceCode (state 84 [] right) (Navigation.state (89 : Fin 98) [false,true] right) 11 := by
  apply follow_actual sourceCode 5
  cases right <;> simp [follow,state,Navigation.state,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂]

def finishEntry (original higher output : List Bool) (gap : Nat) (nonempty : original≠[]) :
    Segment sourceCode
      (Navigation.state (92 : Fin 98) ((MarkSeek.pairs original).reverse++[false,true])
        (true::false::Macro.suffix higher output gap))
      ⟨.at 94,(NumberField.input [] higher output false gap original).Tape⟩ 5 := by
  apply follow_actual sourceCode 2
  cases shape : original.reverse with
  | nil =>
    have empty := congrArg List.reverse shape
    simp only [List.reverse_reverse,List.reverse_nil] at empty
    exact False.elim (nonempty empty)
  | cons last older =>
    rw [Restore.pairs_reverse,shape]
    simp [follow,Navigation.state,sourceCode,Macro.code,Control.program,TM0.step,Tape.mk₂,
      NumberField.input,NumberField.loopCfg,NumberField.cfg,Macro.cfg,Macro.source,
      shape,Restore.reversePairs,Macro.suffix,MarkSeek.pairs]

def input (original work higher output : List Bool) (gap : Nat) : TM0.Cfg Bool Control.Label :=
  Control.state 0 (Tape.mk₂ (leftBlocks work.reverse++false::false::HeaderCopy.bank original)
    (false::Macro.suffix higher output gap))

def target (original work higher output : List Bool) (gap : Nat) : TM0.Cfg Bool Control.Label :=
  Control.state 94 (NumberField.input [] (List.replicate (work.length+1) false++higher)
    output false gap original).Tape

def actual (original work higher output : List Bool) (gap : Nat)
    (nonempty : original≠[]) (width : 2≤work.length) :
    Segment Control.code (input original work higher output gap) (target original work higher output gap)
      (100*(work.length+original.length+1)) := by
  cases workShape : work.reverse with
  | nil =>
    have sizes := congrArg List.length workShape
    simp only [List.length_reverse,List.length_nil] at sizes
    omega
  | cons first rest =>
    cases rest with
    | nil =>
      have sizes := congrArg List.length workShape
      simp only [List.length_reverse,List.length_cons,List.length_nil] at sizes
      omega
    | cons second later =>
      cases originalShape : original.reverse with
      | nil =>
        have empty := congrArg List.reverse originalShape
        simp only [List.reverse_reverse,List.reverse_nil] at empty
        exact False.elim (nonempty empty)
      | cons last older =>
        let base := false::HeaderCopy.bank original
        let suffix := Macro.suffix higher output gap
        let pad := List.replicate (2*work.length) false++false::suffix
        let tail := false::false::pad
        have entered := enter base first second later suffix
        have erased := eraseWork base work.reverse (false::suffix)
        rw [workShape] at erased
        have bank := bankEntry last older pad
        have bankShape : base=false::true::last::leftBlocks older := by
          simp [base,HeaderCopy.bank,originalShape,leftBlocks]
        have workLength : (first::second::later).length=work.length := by
          rw [←workShape,List.length_reverse]
        rw [workLength] at erased
        rw [←bankShape] at bank
        have cleared := clearFlags older (last::true::tail)
        have originalEq : original=older.reverse++[last] := by
          have reversed := congrArg List.reverse originalShape
          simpa only [List.reverse_reverse,List.reverse_cons,List.reverse_nil,List.nil_append] using reversed
        have clearedEnd : MarkSeek.pairs older.reverse++false::last::true::tail=
            MarkSeek.pairs original++true::tail := by
          rw [originalEq]
          simp [MarkSeek.pairs,List.flatMap_append,List.append_assoc]
        rw [clearedEnd] at cleared
        have tailShape : tail=false::Macro.suffix (List.replicate (work.length+1) false++higher) output gap :=
          suffix_layout work higher output gap
        have prepared := (((entered.trans erased).trans bank).trans cleared)
        rw [tailShape] at prepared
        have mark := markBoundary (MarkSeek.pairs original++true::false::
          Macro.suffix (List.replicate (work.length+1) false++higher) output gap)
        have scan := Navigation.right Control.program (89 : Fin 98) 90 91 92 rfl rfl rfl
          [false,true] original (false::Macro.suffix (List.replicate (work.length+1) false++higher) output gap)
        have ending := finishEntry original (List.replicate (work.length+1) false++higher) output gap nonempty
        have result := ((prepared.trans mark).trans scan).trans ending
        have lifted := Control.liftControl result
        have originalLength : older.length+1=original.length := by
          have sizes := congrArg List.length originalShape
          simp only [List.length_reverse,List.length_cons] at sizes
          omega
        simpa only [input,target,Control.state,embed,state,←workShape] using
          lifted.weaken (show 19+(10*work.length+2)+9+(8*older.length+2)+11+(6*original.length+2)+5≤
            100*(work.length+original.length+1) by omega)

end CountPrepare
end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
