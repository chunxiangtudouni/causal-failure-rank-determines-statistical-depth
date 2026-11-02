module
public import Structure.B23_5_RawInit_StagedFin16_012
public import Structure.B23_5_RawInit_LargeArchive010
public import Common.PSTR_WordBool_NativeTrace_006

/-! Actual paired-output prepend primitive for the original archive serializer.
The carry is read from a real output payload before that cell is overwritten.
No output list or input length occurs in the transition table. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005

structure Segment {L : Type} [Inhabited L] (code : TM0.Machine Bool L)
    (first last : TM0.Cfg Bool L) (budget : Nat) where
  trace : List (TM0.Cfg Bool L)
  head : trace.head?=some first
  chain : trace.IsChain (fun a b => TM0.step code a=some b)
  tail : trace.getLast?=some last
  time : trace.length≤budget

namespace Segment
variable {L : Type} [Inhabited L] {code : TM0.Machine Bool L} {a b c : TM0.Cfg Bool L} {s t : Nat}

def point (code : TM0.Machine Bool L) (a : TM0.Cfg Bool L) : Segment code a a 1 :=
  ⟨[a],rfl,.singleton _,rfl,by rfl⟩

def edge (step : TM0.step code a=some b) : Segment code a b 2 :=
  ⟨[a,b],rfl,List.isChain_cons_cons.mpr ⟨step,.singleton _⟩,rfl,by rfl⟩

def trans (front : Segment code a b s) (back : Segment code b c t) : Segment code a c (s+t) := by
  have shape : b::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.head
    rw [same]
    rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.head]; rfl
  · exact NativeTrace.join_chain _ _ _ front.tail front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.tail).trans (shape.symm ▸ back.tail)
  · have size := congrArg List.length shape
    have first := front.time
    have second := back.time
    simp only [List.length_cons] at size
    simp only [List.length_append]
    omega

def weaken (path : Segment code a b s) (room : s≤t) : Segment code a b t :=
  ⟨path.trace,path.head,path.chain,path.tail,path.time.trans room⟩

end Segment

namespace PairPrepend

inductive Label where
  | entry : Bool → Label
  | skip : Bool → Label
  | flag : Bool → Label
  | payload : Bool → Label
  | advance : Bool → Label
  | endMove : Bool → Label
  | endWrite : Bool → Label
  | endAdvance
  | endMarker
  | backData
  | backFlag
  | back
  | backPayload
  | done
  deriving DecidableEq,Fintype

instance : Inhabited Label := ⟨.entry false⟩

def code : TM0.Machine Bool Label
  | .entry bit,_ => some (.skip bit,.move .right)
  | .skip bit,_ => some (.flag bit,.move .right)
  | .flag bit,symbol => if symbol then some (.endMove bit,.write false)
      else some (.payload bit,.move .right)
  | .payload bit,symbol => some (.advance symbol,.write bit)
  | .advance carry,_ => some (.flag carry,.move .right)
  | .endMove bit,_ => some (.endWrite bit,.move .right)
  | .endWrite bit,_ => some (.endAdvance,.write bit)
  | .endAdvance,_ => some (.endMarker,.move .right)
  | .endMarker,_ => some (.backData,.write true)
  | .backData,_ => some (.backFlag,.move .left)
  | .backFlag,_ => some (.back,.move .left)
  | .back,symbol => if symbol then some (.done,.write true)
      else some (.backPayload,.move .left)
  | .backPayload,_ => some (.back,.move .left)
  | .done,_ => none

def state (q : Label) (left right : List Bool) : TM0.Cfg Bool Label := ⟨q,Tape.mk₂ left right⟩
def word (bits : List Bool) : List Bool := true::true::(MarkSeek.pairs bits++[true])

def carry (left bits : List Bool) (bit : Bool) :
    Segment code (state (.flag bit) left (MarkSeek.pairs bits++[true]))
      (state .backData ((MarkSeek.pairs (bit::bits)).reverse++left) [true])
      (6*bits.length+12) := by
  induction bits generalizing left bit with
  | nil =>
    let a := state (.flag bit) left [true]
    let b := state (.endMove bit) left [false]
    let c := state (.endWrite bit) (false::left) []
    let d := state .endAdvance (false::left) [bit]
    let e := state .endMarker (bit::false::left) []
    let f := state .backData (bit::false::left) [true]
    have ab : TM0.step code a=some b := by simp [a,b,state,code,TM0.step,Tape.mk₂]
    have bc : TM0.step code b=some c := by simp [b,c,state,code,TM0.step,Tape.mk₂]
    have cd : TM0.step code c=some d := by simp [c,d,state,code,TM0.step,Tape.mk₂]
    have de : TM0.step code d=some e := by simp [d,e,state,code,TM0.step,Tape.mk₂]
    have ef : TM0.step code e=some f := by simp [e,f,state,code,TM0.step,Tape.mk₂]
    simpa [a,f,MarkSeek.pairs] using
      (((((Segment.edge ab).trans (Segment.edge bc)).trans (Segment.edge cd)).trans
        (Segment.edge de)).trans (Segment.edge ef)).weaken (by omega)
  | cons old later ih =>
    let suffix := MarkSeek.pairs later++[true]
    let a := state (.flag bit) left (false::old::suffix)
    let b := state (.payload bit) (false::left) (old::suffix)
    let c := state (.advance old) (false::left) (bit::suffix)
    let d := state (.flag old) (bit::false::left) suffix
    have ab : TM0.step code a=some b := by simp [a,b,state,code,TM0.step,Tape.mk₂]
    have bc : TM0.step code b=some c := by simp [b,c,state,code,TM0.step,Tape.mk₂]
    have cd : TM0.step code c=some d := by simp [c,d,state,code,TM0.step,Tape.mk₂]
    have rest := ih (bit::false::left) old
    have result := (((Segment.edge ab).trans (Segment.edge bc)).trans (Segment.edge cd)).trans rest
    have layout : (MarkSeek.pairs (bit::old::later)).reverse++left =
        (MarkSeek.pairs (old::later)).reverse++bit::false::left := by
      simp [MarkSeek.pairs,List.append_assoc]
    rw [layout]
    exact result.weaken (by simp only [List.length_cons];omega)

def backStart (left : List Bool) : List Bool → List Bool → TM0.Cfg Bool Label
  | [],suffix => state .back left (true::true::suffix)
  | bit::later,suffix =>
      state .back (Restore.reversePairs later++true::true::left) (false::bit::suffix)

def backward (left bits : List Bool) (suffix : List Bool) :
    Segment code (backStart left bits suffix)
      (state .done left (true::true::(MarkSeek.pairs bits.reverse++suffix))) (4*bits.length+2) := by
  induction bits generalizing suffix with
  | nil =>
    simpa [backStart,word,MarkSeek.pairs] using
      (Segment.edge (show TM0.step code (state .back left (true::true::suffix))=
        some (state .done left (true::true::suffix)) by simp [state,code,TM0.step,Tape.mk₂]))
  | cons bit later ih =>
    let older := Restore.reversePairs later++true::true::left
    let a := state .back older (false::bit::suffix)
    let b := state .backPayload older.tail (older.headD false::false::bit::suffix)
    have ab : TM0.step code a=some b := by
      cases later <;> simp [a,b,older,Restore.reversePairs,state,code,TM0.step,Tape.mk₂]
    have bc : TM0.step code b=some (backStart left later (false::bit::suffix)) := by
      cases later <;> simp [b,older,backStart,Restore.reversePairs,state,code,TM0.step,Tape.mk₂]
    have result := ((Segment.edge ab).trans (Segment.edge bc)).trans (ih (false::bit::suffix))
    have layout : true::true::(MarkSeek.pairs (bit::later).reverse++suffix) =
        true::true::(MarkSeek.pairs later.reverse++false::bit::suffix) := by
      simp [MarkSeek.pairs,List.reverse_cons,List.flatMap_append,List.append_assoc]
    rw [layout]
    exact result.weaken (by simp only [List.length_cons];omega)

theorem actual (left bits : List Bool) (bit : Bool) :
    ∃ path : List (TM0.Cfg Bool Label), path.head?=some (state (.entry bit) left (word bits)) ∧
      path.IsChain (fun a b => TM0.step code a=some b) ∧
      path.getLast?=some (state .done left (word (bit::bits))) ∧
      TM0.step code (state .done left (word (bit::bits)))=none ∧
      path.length≤10*bits.length+30 := by
  let a := state (.entry bit) left (word bits)
  let b := state (.skip bit) (true::left) (true::(MarkSeek.pairs bits++[true]))
  let c := state (.flag bit) (true::true::left) (MarkSeek.pairs bits++[true])
  have ab : TM0.step code a=some b := by simp [a,b,state,word,code,TM0.step,Tape.mk₂]
  have bc : TM0.step code b=some c := by simp [b,c,state,code,TM0.step,Tape.mk₂]
  have copied := carry (true::true::left) bits bit
  let d := state .backData ((MarkSeek.pairs (bit::bits)).reverse++true::true::left) [true]
  let older := (MarkSeek.pairs (bit::bits)).reverse++true::true::left
  let e := state .backFlag older.tail (older.headD false::[true])
  have de : TM0.step code d=some e := by
    cases shape : (bit::bits).reverse with
    | nil => have size := congrArg List.length shape; simp at size
    | cons near rest =>
      have reversed := Restore.pairs_reverse (bit::bits)
      rw [shape] at reversed
      simp [d,e,older,reversed,Restore.reversePairs,state,code,TM0.step,Tape.mk₂]
  have ef : TM0.step code e=some (backStart left (bit::bits).reverse [true]) := by
    cases shape : (bit::bits).reverse with
    | nil => have size := congrArg List.length shape; simp at size
    | cons near rest =>
      have reversed := Restore.pairs_reverse (bit::bits)
      rw [shape] at reversed
      simp [e,older,reversed,backStart,Restore.reversePairs,state,code,TM0.step,Tape.mk₂]
  have back := backward left (bit::bits).reverse [true]
  have result := (((((Segment.edge ab).trans (Segment.edge bc)).trans copied).trans
    (Segment.edge de)).trans (Segment.edge ef)).trans back
  have finalPath : Segment code a (state .done left (word (bit::bits)))
      (10*bits.length+30) := by
    simpa only [List.reverse_reverse,word,List.length_reverse,List.length_cons] using
      result.weaken (by simp only [List.length_reverse,List.length_cons];omega)
  exact ⟨finalPath.trace,finalPath.head,finalPath.chain,finalPath.tail,
    by simp [state,code,TM0.step],finalPath.time⟩

end PairPrepend
end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
