module
public import RootB235_ArchiveStaging_Core001

/-! Actual final disposal and source positioning. The paired-output word
becomes the exact ReverseLoop staged tape, including both boundaries and
the fixed TRUE footer row. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005

namespace Terminal

def sourceTape (higher output : List Bool) (gap : Nat) : Tape Bool :=
  Tape.mk₂ [true] (true::(MarkSeek.pairs higher++true::false::
    (List.replicate gap false++PairPrepend.word output)))

theorem cleanup (bits output : List Bool) (gap inputLength : Nat) :
    ∃ path, RunsFrom ReverseCleanup.machine ⟨0,sourceTape bits output gap⟩ path
      ⟨9,Tape.mk₁ (PairPrepend.word output)⟩ ∧
      path.length=3*bits.length+gap+9 ∧ ∀ clock,
        visitedSpace ReverseCleanup.machine inputLength (path.take clock)≤
          inputLength+2*(3*bits.length+gap+9)+1 := by
  let right := MarkSeek.pairs bits++true::(List.replicate (gap+1) false++PairPrepend.word output)
  let initial : MachineState 9 := ⟨0,sourceTape bits output gap⟩
  let final : MachineState 9 := ⟨9,Tape.mk₁ (PairPrepend.word output)⟩
  let lead := [initial,
    ReverseCleanup.state 1 [] (true::true::right),
    ReverseCleanup.state 2 [] (false::true::right),
    ReverseCleanup.state 3 [false] (true::right),ReverseCleanup.state 4 [false] (false::right)]
  let body := ReverseCleanup.pairTrace [false,false] bits (PairPrepend.word output).tail gap
  have wordHead : true::(PairPrepend.word output).tail=PairPrepend.word output := by rfl
  have initialEq : initial=ReverseCleanup.state 0 [true] (true::right) := by
    rfl
  have leadChain : lead.IsChain (fun a b => TM0.step ReverseCleanup.machine a=some b) := by
    simp [lead,initialEq,List.isChain_cons_cons,ReverseCleanup.state,TM0.step,
      ReverseCleanup.machine,Tape.mk₂]
  have bodyChain := ReverseCleanup.pair_chain [false,false] bits (PairPrepend.word output).tail gap
  have chain : (lead++body).IsChain (fun a b => TM0.step ReverseCleanup.machine a=some b) := by
    apply List.IsChain.append leadChain bodyChain
    intro before hb after ha
    simp only [lead,List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
    simp only [ReverseCleanup.pair_head,Option.mem_some_iff] at ha
    subst before;subst after
    simp [right,wordHead,ReverseCleanup.state,TM0.step,ReverseCleanup.machine,Tape.mk₂]
  have last := ReverseCleanup.pair_last [false,false] bits (PairPrepend.word output).tail gap
  have leftBlank : ListBlank.mk
      (List.replicate (gap+1) false++false::(List.replicate (2*bits.length) false++[false,false]))=
        ListBlank.mk ([] : List Bool) := by
    have empty (n : Nat) : ListBlank.mk (List.replicate n false)=ListBlank.mk ([] : List Bool) :=
      Quotient.sound (Or.inr ⟨n,rfl⟩)
    have padding : List.replicate (gap+1) false++false::(List.replicate (2*bits.length) false++[false,false])=
        List.replicate (gap+1+(1+(2*bits.length+2))) false := by
      rw [show ([false,false] : List Bool)=List.replicate 2 false by rfl,←List.replicate_add]
      change List.replicate (gap+1) false++List.replicate (2*bits.length+2+1) false=_
      rw [←List.replicate_add]
      congr 1
      omega
    rw [padding]
    exact empty _
  have lastEq : body.getLast?=some final := by
    change (ReverseCleanup.pairTrace [false,false] bits (PairPrepend.word output).tail gap).getLast?=_
    rw [last]
    simp only [final,ReverseCleanup.state,Tape.mk₂,Tape.mk₁,wordHead]
    rw [leftBlank]
  have time : (lead++body).length=3*bits.length+gap+9 := by
    simp only [lead,body,List.length_append,List.length_cons,List.length_nil,ReverseCleanup.pair_length]
    omega
  refine ⟨lead++body,⟨?_,chain,?_,?_⟩,time,?_⟩
  · simp only [lead,List.head?_append,List.head?_cons,Option.some_or,initial]
  · simp only [List.getLast?_append,lastEq,Option.some_or,final]
  · simp [TM0.step,ReverseCleanup.machine,PairPrepend.word,Tape.mk₁,Tape.mk₂]
  · intro clock
    have cells := PSTRTMTrace002.visitedSpace_le ReverseCleanup.machine inputLength ((lead++body).take clock)
    have take := List.length_take_le' clock (lead++body)
    rw [time] at take
    omega

def stageMachine : Machine 15 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (2,.move .right)
  | 2 => if symbol then some (4,.move .right) else some (3,.move .right)
  | 3 => some (2,.move .right)
  | 4 => some (5,.move .right)
  | 5 => some (6,.write true)
  | 6 => some (7,.move .right)
  | 7 => some (8,.write true)
  | 8 => some (9,.move .right)
  | 9 => some (10,.write true)
  | 10 => some (11,.move .left)
  | 11 => some (12,.move .left)
  | 12 => some (13,.move .left)
  | 13 => some (14,.move .left)
  | 14 => some (15,.move .left)
  | _ => none

def state (q : Fin 16) (left right : List Bool) : MachineState 15 := ⟨q,Tape.mk₂ left right⟩

def scan (left bits : List Bool) :
    Segment stageMachine (state 2 left (MarkSeek.pairs bits++[true]))
      (state 2 ((MarkSeek.pairs bits).reverse++left) [true]) (4*bits.length+1) := by
  induction bits generalizing left with
  | nil => exact Segment.point _ _
  | cons bit later ih =>
    let suffix := MarkSeek.pairs later++[true]
    let a := state 2 left (false::bit::suffix)
    let b := state 3 (false::left) (bit::suffix)
    let c := state 2 (bit::false::left) suffix
    have ab : TM0.step stageMachine a=some b := by simp [a,b,state,TM0.step,stageMachine,Tape.mk₂]
    have bc : TM0.step stageMachine b=some c := by simp [b,c,state,TM0.step,stageMachine,Tape.mk₂]
    have result := ((Segment.edge ab).trans (Segment.edge bc)).trans (ih (bit::false::left))
    simpa [a,suffix,MarkSeek.pairs,List.append_assoc] using
      result.weaken (t:=4*(bit::later).length+1) (by simp only [List.length_cons];omega)

def fixedFooter (left : List Bool) :
    Segment stageMachine (state 2 left [true])
      ⟨15,(Tape.mk₂ left [true,false,true,true,true]).move .left⟩ 24 := by
  let a := state 2 left [true]
  let b := state 4 (true::left) []
  let c := state 5 (false::true::left) []
  let d := state 6 (false::true::left) [true]
  let e := state 7 (true::false::true::left) []
  let f := state 8 (true::false::true::left) [true]
  let g := state 9 (true::true::false::true::left) []
  let h := state 10 (true::true::false::true::left) [true]
  let i := state 11 (true::false::true::left) [true,true]
  let j := state 12 (false::true::left) [true,true,true]
  let k := state 13 (true::left) [false,true,true,true]
  let l := state 14 left [true,false,true,true,true]
  let m : MachineState 15 := ⟨15,(Tape.mk₂ left [true,false,true,true,true]).move .left⟩
  have ab : TM0.step stageMachine a=some b := by simp [a,b,state,TM0.step,stageMachine,Tape.mk₂]
  have bc : TM0.step stageMachine b=some c := by simp [b,c,state,TM0.step,stageMachine,Tape.mk₂]
  have cd : TM0.step stageMachine c=some d := by simp [c,d,state,TM0.step,stageMachine,Tape.mk₂]
  have de : TM0.step stageMachine d=some e := by simp [d,e,state,TM0.step,stageMachine,Tape.mk₂]
  have ef : TM0.step stageMachine e=some f := by simp [e,f,state,TM0.step,stageMachine,Tape.mk₂]
  have fg : TM0.step stageMachine f=some g := by simp [f,g,state,TM0.step,stageMachine,Tape.mk₂]
  have gh : TM0.step stageMachine g=some h := by simp [g,h,state,TM0.step,stageMachine,Tape.mk₂]
  have hi : TM0.step stageMachine h=some i := by simp [h,i,state,TM0.step,stageMachine,Tape.mk₂]
  have ij : TM0.step stageMachine i=some j := by simp [i,j,state,TM0.step,stageMachine,Tape.mk₂]
  have jk : TM0.step stageMachine j=some k := by simp [j,k,state,TM0.step,stageMachine,Tape.mk₂]
  have kl : TM0.step stageMachine k=some l := by simp [k,l,state,TM0.step,stageMachine,Tape.mk₂]
  have lm : TM0.step stageMachine l=some m := by simp [l,m,state,TM0.step,stageMachine]
  exact (((((((((((Segment.edge ab).trans (Segment.edge bc)).trans (Segment.edge cd)).trans
    (Segment.edge de)).trans (Segment.edge ef)).trans (Segment.edge fg)).trans (Segment.edge gh)).trans
    (Segment.edge hi)).trans (Segment.edge ij)).trans (Segment.edge jk)).trans (Segment.edge kl)).trans
    (Segment.edge lm)

theorem staged_shape (bits : List Bool) :
    (Tape.mk₂ ((MarkSeek.pairs bits).reverse++[true,true]) [true,false,true,true,true]).move .left=
      ReverseLoop.tape bits.reverse [] 0 [] := by
  have padding : ListBlank.mk ([true,false,true,true,true] : List Bool)=
      ListBlank.mk (true::false::RowEnd.rows []) :=
    Quotient.sound (Or.inl ⟨30,rfl⟩)
  have padded : Tape.mk₂ ((MarkSeek.pairs bits).reverse++[true,true]) [true,false,true,true,true]=
      Tape.mk₂ ((MarkSeek.pairs bits).reverse++[true,true]) (true::false::RowEnd.rows []) := by
    change Tape.mk' _ (ListBlank.mk [true,false,true,true,true])=Tape.mk' _ _
    rw [padding]
  rw [padded,Restore.pairs_reverse]
  cases shape : bits.reverse with
  | nil => simp [Restore.reversePairs,ReverseLoop.tape,ReverseLoop.suffix,MarkSeek.pairs,Tape.mk₂]
  | cons bit later =>
    simp [Restore.reversePairs,ReverseLoop.tape,ReverseLoop.suffix,MarkSeek.pairs,Tape.mk₂]

theorem stage_actual (bits : List Bool) (inputLength : Nat) :
    ∃ path, RunsFrom stageMachine ⟨0,Tape.mk₁ (PairPrepend.word bits)⟩ path
      ⟨15,ReverseLoop.tape bits.reverse [] 0 []⟩ ∧
      path.length≤4*bits.length+30 ∧ ∀ clock,
        visitedSpace stageMachine inputLength (path.take clock) ≤ inputLength+2*(4*bits.length+30)+1 := by
  let a : MachineState 15 := ⟨0,Tape.mk₁ (PairPrepend.word bits)⟩
  let b := state 1 [true] (true::(MarkSeek.pairs bits++[true]))
  let c := state 2 [true,true] (MarkSeek.pairs bits++[true])
  have ab : TM0.step stageMachine a=some b := by
    simp [a,b,PairPrepend.word,state,TM0.step,stageMachine,Tape.mk₁,Tape.mk₂]
  have bc : TM0.step stageMachine b=some c := by simp [b,c,state,TM0.step,stageMachine,Tape.mk₂]
  have result := (((Segment.edge ab).trans (Segment.edge bc)).trans (scan [true,true] bits)).trans
    (fixedFooter ((MarkSeek.pairs bits).reverse++[true,true]))
  have result' : Segment stageMachine a ⟨15,ReverseLoop.tape bits.reverse [] 0 []⟩
      (4*bits.length+30) := by
    rw [staged_shape] at result
    exact result.weaken (by omega)
  refine ⟨result'.trace,⟨result'.head,result'.chain,result'.tail,?_⟩,result'.time,?_⟩
  · simp [TM0.step,stageMachine]
  · intro clock
    have cells := PSTRTMTrace002.visitedSpace_le stageMachine inputLength (result'.trace.take clock)
    have take := (List.length_take_le' clock result'.trace).trans result'.time
    omega

def machine : Machine 25 := seqMachine ReverseCleanup.machine stageMachine
def haltPort : Fin 26 := rightLabel (a:=9) (b:=15) 15

theorem actual (higher output : List Bool) (gap inputLength : Nat) :
    ∃ path final, RunsFrom machine ⟨0,sourceTape higher output gap⟩ path final ∧
      final.q=haltPort ∧ final.Tape=ReverseLoop.tape output.reverse [] 0 [] ∧
      path.length≤3*higher.length+gap+4*output.length+40 ∧ ∀ clock,
        visitedSpace machine inputLength (path.take clock)≤
          inputLength+2*(3*higher.length+gap+4*output.length+40)+1 := by
  obtain ⟨front,frontRun,frontTime,_frontSpace⟩ := cleanup higher output gap inputLength
  obtain ⟨back,backRun,backTime,_backSpace⟩ := stage_actual output inputLength
  let path := front.map (leftCfg (b:=15))++back.map (rightCfg (a:=9))
  let final := rightCfg (a:=9) (⟨15,ReverseLoop.tape output.reverse [] 0 []⟩ : MachineState 15)
  have run := seq_runsFrom ReverseCleanup.machine stageMachine _ _ _ front back frontRun backRun
  have time : path.length≤3*higher.length+gap+4*output.length+40 := by
    simp only [path,List.length_append,List.length_map]
    omega
  refine ⟨path,final,run,rfl,rfl,time,?_⟩
  intro clock
  have cells := PSTRTMTrace002.visitedSpace_le machine inputLength (path.take clock)
  have take := (List.length_take_le' clock path).trans time
  omega

end Terminal
end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
