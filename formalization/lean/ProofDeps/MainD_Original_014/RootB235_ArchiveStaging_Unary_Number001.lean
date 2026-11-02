module
public import RootB235_ArchiveStaging_Macro003
public import Common.PSTR_SYM_FiniteRelabel_007

/-! A fixed finite Bool machine reads a physical number field, exports its
original digits, emits the physical width in unary, and erases the field.
Neither the digits nor the width occurs in its transition table. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
open RationalControllerComputation.PSTRSymbolicRelabel

namespace NumberField

def program (q : Fin 20) : Macro.Instruction (Fin 20) :=
  match q.val with
  | 0 => .action (.move .left) 1
  | 1 => .branch 2 6
  | 2 => .action (.move .right) 3
  | 3 => .export .digit 4
  | 4 => .action (.move .left) 5
  | 5 => .action (.move .left) 0
  | 6 => .action (.move .right) 7
  | 7 => .export .emitFalse 8
  | 8 => .action (.move .right) 9
  | 9 => .action (.move .right) 10
  | 10 => .branch 13 11
  | 11 => .export .unary 12
  | 12 => .action (.move .right) 19
  | 13 => .action (.move .left) 14
  | 14 => .branch 15 17
  | 15 => .action (.move .left) 16
  | 16 => .action (.move .left) 14
  | 17 => .action (.move .right) 18
  | 19 => .action (.move .right) 10
  | _ => .halt

abbrev Label := Macro.Label (Fin 20)
def code : TM0.Machine Bool Label := Macro.code program
def cfg (loc : Fin 20) (left higher output : List Bool) (flag bit : Bool) (gap : Nat) :
    TM0.Cfg Bool Label := Macro.cfg loc left higher output flag bit gap

def state (q : Fin 20) (left right : List Bool) : TM0.Cfg Bool Label :=
  ⟨.at q,Tape.mk₂ left right⟩

def rate (remaining processed higher output gap : Nat) : Nat :=
  4*(processed+remaining+higher+2)+3*gap+10*(output+remaining)+100

theorem rate_shift (n k h o g : Nat) : rate n (k+1) h (o+1) g=rate (n+1) k h o g := by
  unfold rate
  omega

def loopCfg (left higher output : List Bool) (boundary : Bool) (gap processed : Nat) :
    List Bool → TM0.Cfg Bool Label
  | [] => cfg 0 left (List.replicate processed true++false::higher) output true boundary gap
  | bit::older => cfg 0 (Restore.reversePairs older++boundary::true::left)
      (List.replicate processed true++false::higher) output false bit gap

noncomputable def digitLoop (left higher output : List Bool) (boundary : Bool)
    (gap processed : Nat) (todo : List Bool) :
    Segment code (loopCfg left higher output boundary gap processed todo)
      (cfg 7 left (List.replicate (processed+todo.length) true++false::higher)
        (todo.reverse++output) true boundary gap)
      ((todo.length+1)*rate todo.length processed higher.length output.length gap) := by
  induction todo generalizing processed output with
  | nil =>
    let a := loopCfg left higher output boundary gap processed []
    let b := state 1 left (true::boundary::Macro.suffix
      (List.replicate processed true++false::higher) output gap)
    let c := state 6 left (true::boundary::Macro.suffix
      (List.replicate processed true++false::higher) output gap)
    let d := cfg 7 left (List.replicate processed true++false::higher) output true boundary gap
    have ab : TM0.step code a=some b := by
      simp [a,b,loopCfg,cfg,Macro.cfg,Macro.source,state,code,Macro.code,program,TM0.step,Tape.mk₂]
    have bc : TM0.step code b=some c := by
      simp [b,c,state,code,Macro.code,program,TM0.step,Tape.mk₂]
    have cd : TM0.step code c=some d := by
      simp [c,d,cfg,Macro.cfg,Macro.source,state,code,Macro.code,program,TM0.step,Tape.mk₂]
    simpa only [a,d,List.length_nil,List.reverse_nil,List.nil_append,Nat.add_zero,Nat.zero_add,
      Nat.one_mul] using
      (((Segment.edge ab).trans (Segment.edge bc)).trans (Segment.edge cd)).weaken
        (show 6≤rate 0 processed higher.length output.length gap by unfold rate;omega)
  | cons bit older ih =>
    let west := Restore.reversePairs older++boundary::true::left
    let east := List.replicate processed true++false::higher
    let a := loopCfg left higher output boundary gap processed (bit::older)
    let b := state 1 west (false::bit::Macro.suffix east output gap)
    let c := state 2 west (false::bit::Macro.suffix east output gap)
    let d := cfg 3 west east output false bit gap
    have ab : TM0.step code a=some b := by
      simp [a,b,loopCfg,cfg,Macro.cfg,Macro.source,state,code,Macro.code,program,TM0.step,Tape.mk₂,west,east]
    have bc : TM0.step code b=some c := by
      simp [b,c,state,code,Macro.code,program,TM0.step,Tape.mk₂]
    have cd : TM0.step code c=some d := by
      simp [c,d,cfg,Macro.cfg,Macro.source,state,code,Macro.code,program,TM0.step,Tape.mk₂]
    have copied := Macro.export_actual program 3 4 .digit rfl west east output false bit gap
    let e := cfg 4 west east (bit::output) false true gap
    let f := state 5 west (false::true::Macro.suffix east (bit::output) gap)
    have ef : TM0.step code e=some f := by
      simp [e,f,cfg,Macro.cfg,Macro.source,state,code,Macro.code,program,TM0.step,Tape.mk₂]
    have fg : TM0.step code f=some (loopCfg left higher (bit::output) boundary gap (processed+1) older) := by
      cases older <;>
        simp [f,west,east,loopCfg,Restore.reversePairs,cfg,Macro.cfg,Macro.source,Macro.suffix,
          MarkSeek.pairs,List.replicate_succ,state,code,Macro.code,program,TM0.step,Tape.mk₂]
    have front := (((((Segment.edge ab).trans (Segment.edge bc)).trans (Segment.edge cd)).trans
      copied).trans (Segment.edge ef)).trans (Segment.edge fg)
    have rest := ih (bit::output) (processed+1)
    have result := front.trans rest
    have outputEq : older.reverse++bit::output=(bit::older).reverse++output := by
      simp [List.reverse_cons,List.append_assoc]
    have processedEq : processed+1+older.length=processed+(bit::older).length := by
      simp only [List.length_cons];omega
    rw [outputEq,processedEq] at result
    have sameRate : rate older.length (processed+1) higher.length (bit::output).length gap=
        rate (bit::older).length processed higher.length output.length gap := by
      simpa only [List.length_cons] using rate_shift older.length processed higher.length output.length gap
    have frontRoom : 2+2+2+(4*east.length+3*gap+10*output.length+80)+2+2≤
        rate (bit::older).length processed higher.length output.length gap := by
      simp only [east,List.length_append,List.length_replicate,List.length_cons,rate]
      omega
    exact result.weaken (by
      rw [sameRate]
      simp only [List.length_cons]
      simp only [List.length_cons] at frontRoom
      nlinarith only [frontRoom])

def unaryCfg (left higher output : List Bool) (boundary : Bool) (gap processed : Nat) :
    Nat → TM0.Cfg Bool Label
  | 0 => cfg 10 (Restore.reversePairs (List.replicate processed false)++boundary::true::left)
      higher output false false gap
  | n+1 => cfg 10 (Restore.reversePairs (List.replicate processed false)++boundary::true::left)
      (List.replicate n true++false::higher) output false true gap

noncomputable def unaryLoop (left higher output : List Bool) (boundary : Bool)
    (gap processed count : Nat) :
    Segment code (unaryCfg left higher output boundary gap processed count)
      (cfg 13 (Restore.reversePairs (List.replicate (processed+count) false)++boundary::true::left)
        higher (List.replicate count true++output) false false gap)
      ((count+1)*rate count processed higher.length output.length gap) := by
  induction count generalizing processed output with
  | zero =>
    have step : TM0.step code (unaryCfg left higher output boundary gap processed 0)=
        some (cfg 13 (Restore.reversePairs (List.replicate processed false)++boundary::true::left)
          higher output false false gap) := by
      simp [unaryCfg,cfg,Macro.cfg,Macro.source,code,Macro.code,program,TM0.step,Tape.mk₂]
    simpa only [Nat.add_zero,Nat.zero_add,Nat.one_mul,List.replicate_zero,List.nil_append] using
      (Segment.edge step).weaken (show 2≤rate 0 processed higher.length output.length gap by unfold rate;omega)
  | succ count ih =>
    let west := Restore.reversePairs (List.replicate processed false)++boundary::true::left
    let east := List.replicate count true++false::higher
    let a := unaryCfg left higher output boundary gap processed (count+1)
    let b := cfg 11 west east output false true gap
    have ab : TM0.step code a=some b := by
      simp [a,b,unaryCfg,west,east,cfg,Macro.cfg,Macro.source,code,Macro.code,program,TM0.step,Tape.mk₂]
    have copied := Macro.export_actual program 11 12 .unary rfl west east output false true gap
    let c := cfg 12 west east (true::output) false false gap
    let d := state 19 (false::false::west) (Macro.suffix east (true::output) gap)
    have cd : TM0.step code c=some d := by
      simp [c,d,cfg,Macro.cfg,Macro.source,state,code,Macro.code,program,TM0.step,Tape.mk₂]
    have de : TM0.step code d=some (unaryCfg left higher (true::output) boundary gap (processed+1) count) := by
      cases count <;>
        simp [d,west,east,unaryCfg,Restore.reversePairs,cfg,Macro.cfg,Macro.source,Macro.suffix,
          MarkSeek.pairs,List.replicate_succ,state,code,Macro.code,program,TM0.step,Tape.mk₂]
    have front := (((Segment.edge ab).trans copied).trans (Segment.edge cd)).trans (Segment.edge de)
    have rest := ih (true::output) (processed+1)
    have result := front.trans rest
    have outputEq : List.replicate count true++true::output=List.replicate (count+1) true++output := by
      simp [List.replicate_add,List.append_assoc]
    have processedEq : processed+1+count=processed+(count+1) := by omega
    rw [outputEq,processedEq] at result
    have sameRate : rate count (processed+1) higher.length (true::output).length gap=
        rate (count+1) processed higher.length output.length gap := by
      simpa only [List.length_cons] using rate_shift count processed higher.length output.length gap
    have frontRoom : 2+(4*east.length+3*gap+10*output.length+80)+2+2≤
        rate (count+1) processed higher.length output.length gap := by
      simp only [east,List.length_append,List.length_replicate,List.length_cons,rate]
      omega
    exact result.weaken (by rw [sameRate];nlinarith only [frontRoom])

def backStart (left : List Bool) (boundary : Bool) : List Bool → List Bool → TM0.Cfg Bool Label
  | [],suffix => state 14 left (true::boundary::suffix)
  | bit::later,suffix => state 14 (Restore.reversePairs later++boundary::true::left) (false::bit::suffix)

def backward (left : List Bool) (boundary : Bool) (bits suffix : List Bool) :
    Segment code (backStart left boundary bits suffix)
      (state 18 (true::left) (boundary::(MarkSeek.pairs bits.reverse++suffix))) (6*bits.length+4) := by
  induction bits generalizing suffix with
  | nil =>
    let a := backStart left boundary [] suffix
    let b := state 17 left (true::boundary::suffix)
    let c := state 18 (true::left) (boundary::suffix)
    have ab : TM0.step code a=some b := by
      simp [a,b,backStart,state,code,Macro.code,program,TM0.step,Tape.mk₂]
    have bc : TM0.step code b=some c := by
      simp [b,c,state,code,Macro.code,program,TM0.step,Tape.mk₂]
    exact (Segment.edge ab).trans (Segment.edge bc)
  | cons bit later ih =>
    let west := Restore.reversePairs later++boundary::true::left
    let a := backStart left boundary (bit::later) suffix
    let b := state 15 west (false::bit::suffix)
    let c := state 16 west.tail (west.headD false::false::bit::suffix)
    have ab : TM0.step code a=some b := by
      simp [a,b,backStart,state,code,Macro.code,program,TM0.step,Tape.mk₂,west]
    have bc : TM0.step code b=some c := by
      cases later <;> simp [b,c,west,Restore.reversePairs,state,code,Macro.code,program,TM0.step,Tape.mk₂]
    have cd : TM0.step code c=some (backStart left boundary later (false::bit::suffix)) := by
      cases later <;> simp [c,west,backStart,Restore.reversePairs,state,code,Macro.code,program,TM0.step,Tape.mk₂]
    have result := (((Segment.edge ab).trans (Segment.edge bc)).trans (Segment.edge cd)).trans
      (ih (false::bit::suffix))
    have layout : MarkSeek.pairs (bit::later).reverse++suffix=
        MarkSeek.pairs later.reverse++false::bit::suffix := by
      simp [MarkSeek.pairs,List.reverse_cons,List.flatMap_append,List.append_assoc]
    rw [layout]
    exact result.weaken (by simp only [List.length_cons];omega)

def input (left higher output : List Bool) (boundary : Bool) (gap : Nat) (digits : List Bool) :
    TM0.Cfg Bool Label := loopCfg left higher output boundary gap 0 digits.reverse

def finish (left higher output : List Bool) (boundary : Bool) (gap : Nat) (digits : List Bool) :
    TM0.Cfg Bool Label :=
  cfg 18 left (List.replicate (digits.length+1) false++higher)
    (List.replicate digits.length true++false::(digits++output)) true boundary gap

noncomputable def actual (left higher output : List Bool) (boundary : Bool) (gap : Nat) (digits : List Bool) :
    Segment code (input left higher output boundary gap digits) (finish left higher output boundary gap digits)
      (1000*(digits.length+higher.length+output.length+gap+1)^2) := by
  let n := digits.length
  let out := digits++output
  let units := List.replicate n true++false::higher
  have front := digitLoop left higher output boundary gap 0 digits.reverse
  simp only [List.length_reverse,List.reverse_reverse,Nat.zero_add] at front
  have copied := Macro.export_actual program 7 8 .emitFalse rfl left units out true boundary gap
  let a := cfg 8 left units (false::out) true boundary gap
  let b := state 9 (boundary::true::left) (Macro.suffix units (false::out) gap)
  have ab : TM0.step code a=some b := by
    simp [a,b,cfg,Macro.cfg,Macro.source,state,code,Macro.code,program,TM0.step,Tape.mk₂]
  have bc : TM0.step code b=some (unaryCfg left higher (false::out) boundary gap 0 n) := by
    dsimp only [b,units]
    cases n <;> simp [unaryCfg,Restore.reversePairs,cfg,Macro.cfg,Macro.source,Macro.suffix,
      MarkSeek.pairs,List.replicate_succ,state,code,Macro.code,program,TM0.step,Tape.mk₂]
  have unary := unaryLoop left higher (false::out) boundary gap 0 n
  simp only [Nat.zero_add] at unary
  let newOutput := List.replicate n true++false::out
  let west := Restore.reversePairs (List.replicate n false)++boundary::true::left
  let c := cfg 13 west higher newOutput false false gap
  let d := backStart left boundary (List.replicate (n+1) false) (Macro.suffix higher newOutput gap)
  have cd : TM0.step code c=some d := by
    simp [c,d,west,backStart,List.replicate_succ,cfg,Macro.cfg,Macro.source,state,
      code,Macro.code,program,TM0.step,Tape.mk₂]
  have back := backward left boundary (List.replicate (n+1) false) (Macro.suffix higher newOutput gap)
  have backEnd : state 18 (true::left)
      (boundary::(MarkSeek.pairs (List.replicate (n+1) false).reverse++Macro.suffix higher newOutput gap))=
      finish left higher output boundary gap digits := by
    simp [finish,state,cfg,Macro.cfg,Macro.source,Macro.suffix,MarkSeek.pairs,n,newOutput,out,
      List.flatMap_append,List.append_assoc]
  rw [backEnd] at back
  have result := (((((front.trans copied).trans (Segment.edge ab)).trans (Segment.edge bc)).trans unary).trans
    (Segment.edge cd)).trans back
  exact result.weaken (by
    simp only [units,out,n,List.length_append,List.length_replicate,List.length_cons,rate]
    nlinarith [Nat.zero_le (digits.length^2),Nat.zero_le (higher.length^2),
      Nat.zero_le (output.length^2),Nat.zero_le (gap^2)])

theorem halt (left higher output : List Bool) (boundary : Bool) (gap : Nat) (digits : List Bool) :
    TM0.step code (finish left higher output boundary gap digits)=none := by
  simp [finish,cfg,Macro.cfg,TM0.step,code,Macro.code,program]

noncomputable def support : Finset Label := Finset.univ
noncomputable def machine : Machine support.card := finiteMachine code support
noncomputable def liftCfg (cfg : TM0.Cfg Bool Label) : MachineState support.card :=
  relabelCfg (finiteLabels support) cfg
noncomputable def haltPort : Fin (support.card+1) := finiteLabels support (.at 18)

theorem step_lift (cfg : TM0.Cfg Bool Label) :
    TM0.step machine (liftCfg cfg)=(TM0.step code cfg).map liftCfg := by
  classical
  exact (relabel_step code (support : Set Label) (finiteLabels support) (finiteDecode support)
    (finite_inverse support) cfg (Finset.mem_univ _)).symm

theorem entry (left higher output : List Bool) (boundary : Bool) (gap : Nat) (digits : List Bool) :
    (liftCfg (input left higher output boundary gap digits)).q=0 := by
  classical
  have first : (input left higher output boundary gap digits).q=default := by
    unfold input
    cases digits.reverse <;> rfl
  change finiteLabels support (input left higher output boundary gap digits).q=0
  rw [first]
  simp [finiteLabels]

theorem actual_finite (left higher output : List Bool) (boundary : Bool) (gap : Nat) (digits : List Bool)
    (inputLength : Nat) :
    ∃ path, RunsFrom machine (liftCfg (input left higher output boundary gap digits)) path
      (liftCfg (finish left higher output boundary gap digits)) ∧
      (liftCfg (finish left higher output boundary gap digits)).q=haltPort ∧
      path.length≤1000*(digits.length+higher.length+output.length+gap+1)^2 ∧ ∀ clock,
        visitedSpace machine inputLength (path.take clock)≤
          inputLength+2000*(digits.length+higher.length+output.length+gap+1)^2+1 := by
  let source := actual left higher output boundary gap digits
  let path := source.trace.map liftCfg
  have first : path.head?=some (liftCfg (input left higher output boundary gap digits)) := by
    simp only [path,List.head?_map,source.head,Option.map_some]
  have chain : path.IsChain (fun a b => TM0.step machine a=some b) :=
    (List.isChain_map _).mpr (source.chain.imp (fun a b edge => by rw [step_lift,edge];rfl))
  have last : path.getLast?=some (liftCfg (finish left higher output boundary gap digits)) := by
    simp only [path,List.getLast?_map,source.tail,Option.map_some]
  have stopped : TM0.step machine (liftCfg (finish left higher output boundary gap digits))=none := by
    rw [step_lift,halt];rfl
  have time : path.length≤1000*(digits.length+higher.length+output.length+gap+1)^2 := by
    simpa only [path,List.length_map] using source.time
  refine ⟨path,⟨first,chain,last,stopped⟩,rfl,time,?_⟩
  intro clock
  have cells := PSTRTMTrace002.visitedSpace_le machine inputLength (path.take clock)
  have take := (List.length_take_le' clock path).trans time
  omega

end NumberField
end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
