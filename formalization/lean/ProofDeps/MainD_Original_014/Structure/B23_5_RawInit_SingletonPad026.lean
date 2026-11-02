module
public import Structure.B23_5_RawInit_Small1_004

/-! Fixed nine-cell singleton header rewrite. Every WRITE and LEFT/RIGHT
is real and restores the original unread Datum head; no payload bit or
length is an argument of the transition table. The original count bank
and entire right tape survive. Only work bank [true] becomes [true,false]. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.SingletonPad
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
open RationalControllerComputation.PSTRSymbolicPairedArchive

def header : List Bool := false::(HeaderCopy.bank [true,false]++
  false::false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload 1))

theorem old_header : Small1.singletonHeader=[false,true,true,false,false,true,true] := by decide
theorem new_header : header=[false,true,false,true,true,false,false,true,true] := by decide

def patch : Machine 27 := fun q _ => match q.val with
  | 0 => some (1,.move .left)
  | 1 => some (2,.write false)
  | 2 => some (3,.move .left)
  | 3 => some (4,.write true)
  | 4 => some (5,.move .left)
  | 5 => some (6,.write false)
  | 6 => some (7,.move .left)
  | 7 => some (8,.write true)
  | 8 => some (9,.move .left)
  | 9 => some (10,.write true)
  | 10 => some (11,.move .left)
  | 11 => some (12,.write false)
  | 12 => some (13,.move .left)
  | 13 => some (14,.write false)
  | 14 => some (15,.move .left)
  | 15 => some (16,.write true)
  | 16 => some (17,.move .left)
  | 17 => some (18,.write true)
  | 18 => some (19,.move .right)
  | 19 => some (20,.move .right)
  | 20 => some (21,.move .right)
  | 21 => some (22,.move .right)
  | 22 => some (23,.move .right)
  | 23 => some (24,.move .right)
  | 24 => some (25,.move .right)
  | 25 => some (26,.move .right)
  | 26 => some (27,.move .right)
  | _ => none

def state (q : Fin 28) (left right : List Bool) : MachineState 27 := ⟨q,Tape.mk₂ left right⟩
def trace (head : Bool) (tail : List Bool) : List (MachineState 27) := [
    state 0 [false,true,true,false,false,true,true,false,false] (head::tail),
    state 1 [true,true,false,false,true,true,false,false] ([false]++head::tail),
    state 2 [true,true,false,false,true,true,false,false] ([false]++head::tail),
    state 3 [true,false,false,true,true,false,false] ([true,false]++head::tail),
    state 4 [true,false,false,true,true,false,false] ([true,false]++head::tail),
    state 5 [false,false,true,true,false,false] ([true,true,false]++head::tail),
    state 6 [false,false,true,true,false,false] ([false,true,false]++head::tail),
    state 7 [false,true,true,false,false] ([false,false,true,false]++head::tail),
    state 8 [false,true,true,false,false] ([true,false,true,false]++head::tail),
    state 9 [true,true,false,false] ([false,true,false,true,false]++head::tail),
    state 10 [true,true,false,false] ([true,true,false,true,false]++head::tail),
    state 11 [true,false,false] ([true,true,true,false,true,false]++head::tail),
    state 12 [true,false,false] ([false,true,true,false,true,false]++head::tail),
    state 13 [false,false] ([true,false,true,true,false,true,false]++head::tail),
    state 14 [false,false] ([false,false,true,true,false,true,false]++head::tail),
    state 15 [false] ([false,false,false,true,true,false,true,false]++head::tail),
    state 16 [false] ([true,false,false,true,true,false,true,false]++head::tail),
    state 17 [] ([false,true,false,false,true,true,false,true,false]++head::tail),
    state 18 [] ([true,true,false,false,true,true,false,true,false]++head::tail),
    state 19 [true] ([true,false,false,true,true,false,true,false]++head::tail),
    state 20 [true,true] ([false,false,true,true,false,true,false]++head::tail),
    state 21 [false,true,true] ([false,true,true,false,true,false]++head::tail),
    state 22 [false,false,true,true] ([true,true,false,true,false]++head::tail),
    state 23 [true,false,false,true,true] ([true,false,true,false]++head::tail),
    state 24 [true,true,false,false,true,true] ([false,true,false]++head::tail),
    state 25 [false,true,true,false,false,true,true] ([true,false]++head::tail),
    state 26 [true,false,true,true,false,false,true,true] ([false]++head::tail),
    state 27 [false,true,false,true,true,false,false,true,true] (head::tail)]

theorem extend_blank (suffix : List Bool) :
    Tape.mk₂ [false,true,true,false,false,true,true,false,false] suffix=
      Tape.mk₂ Small1.singletonHeader suffix := by
  rw [old_header]
  have blank : ListBlank.mk ([false,true,true,false,false,true,true,false,false] : List Bool)=
      ListBlank.mk [false,true,true,false,false,true,true] :=
    Quotient.sound (Or.inr ⟨2,rfl⟩)
  simp only [Tape.mk₂,blank]

theorem patch_actual (head : Bool) (tail : List Bool) (inputLength : Nat) :
    ∃ path, RunsFrom patch ⟨0,Tape.mk₂ Small1.singletonHeader (head::tail)⟩ path
      ⟨27,Tape.mk₂ header (head::tail)⟩ ∧ path.length=28 ∧ ∀ clock,
        visitedSpace patch inputLength (path.take clock) ≤ inputLength+57 := by
  refine ⟨trace head tail,⟨?_,?_,?_,?_⟩,rfl,?_⟩
  · simp only [trace,List.head?_cons,state,extend_blank]
  · simp [trace,List.isChain_cons_cons,state,TM0.step,patch,Tape.mk₂]
  · rw [new_header]
    rfl
  · simp [TM0.step,patch]
  · intro clock
    have cells:=PSTRTMTrace002.visitedSpace_le patch inputLength ((trace head tail).take clock)
    have short:=List.length_take_le' clock (trace head tail)
    have length : (trace head tail).length=28 := rfl
    rw [length] at short
    omega

def headerMachine : Machine 131 := seqMachine retainedHeaderMachine patch
def machine : Machine 241 := seqMachine headerMachine datumCompactMachine

theorem actual (value : Datum) : ∃ path final,
    Runs machine (encode [value]) path final ∧
      final.Tape=Tape.mk₂ ((pairedDatum value).reverse++header) [true] ∧
      path.length≤1200*((encode [value]).length+1)^2 ∧ ∀ clock,
        visitedSpace machine (encode [value]).length (path.take clock)≤
          4096*((encode [value]).length+1)^2 := by
  obtain ⟨front,mid,frontRun,_port,frontTape,frontTime,_frontSpace⟩:=actual_retained_header [value]
  have nonempty : rawTail [value]≠[] := by simp [rawTail]
  obtain ⟨head,tail,shape⟩:=List.exists_cons_of_ne_nil nonempty
  obtain ⟨padded,padRun,padTime,_padSpace⟩:=patch_actual head tail (encode [value]).length
  have patchFrom : RunsFrom patch ⟨0,mid.Tape⟩ padded ⟨27,Tape.mk₂ header (rawTail [value])⟩ := by
    rw [frontTape]
    simpa only [List.length_singleton,shape,Small1.singletonHeader] using padRun
  let frontPath:=front.map (leftCfg (b:=27))++padded.map (rightCfg (a:=103))
  let frontFinal:=rightCfg (a:=103) (b:=27) ⟨27,Tape.mk₂ header (rawTail [value])⟩
  have headerRun : Runs headerMachine (encode [value]) frontPath frontFinal :=
    seq_runs retainedHeaderMachine patch (encode [value]) mid _ front padded frontRun patchFrom
  obtain ⟨back,backFinal,backRun,backTape,backTime,_backSpace⟩:=raw_datum_parse_compact header value [true]
  have backFrom : RunsFrom datumCompactMachine ⟨0,frontFinal.Tape⟩ back backFinal := by
    simpa only [frontFinal,rightCfg,rawTail,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.nil_append] using backRun
  let path:=frontPath.map (leftCfg (b:=109))++back.map (rightCfg (a:=131))
  let final:=rightCfg (a:=131) backFinal
  have run:=seq_runs headerMachine datumCompactMachine (encode [value]) frontFinal backFinal
    frontPath back headerRun backFrom
  have room : (encodeDatum value).length+1≤(encode [value]).length+1 := by
    simp only [encode,List.length_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.length_singleton]
    omega
  have backBound:=backTime.trans (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left room 2))
  have time : path.length≤1200*((encode [value]).length+1)^2 := by
    simp only [path,frontPath,List.length_append,List.length_map,padTime]
    have positive : 0<((encode [value]).length+1)^2 := by positivity
    omega
  refine ⟨path,final,run,backTape,time,?_⟩
  intro clock
  have cells:=PSTRTMTrace002.visitedSpace_le machine (encode [value]).length (path.take clock)
  have short:=(List.length_take_le' clock path).trans time
  have inputRoom : (encode [value]).length≤((encode [value]).length+1)^2 := by nlinarith
  have positive : 0<((encode [value]).length+1)^2 := by positivity
  omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.SingletonPad
