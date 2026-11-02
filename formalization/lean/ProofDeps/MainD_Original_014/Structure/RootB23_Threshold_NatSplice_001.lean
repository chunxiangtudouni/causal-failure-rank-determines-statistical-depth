module
public import Structure.PA17_TM_RatArithmetic_Unblock_004d
public import Structure.PA17_TM_RatArithmetic_Parse_002g
public import Structure.PA17_TM_RatArithmetic_Width_018f
public import Common.PSTR_TM_PairRewind_105
public import Common.PSTR_TM_Prepend_022
public import Common.PSTR_TM_ThresholdBDatum_224

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
@[expose] public section
namespace RootB23.Threshold.NatSplice
open PaperProofs.Common.Native.RationalControllerComputation
open Turing

def dataMode (saved : Bool) : Fin 10 := if saved then 1 else 0
def moveMode (saved : Bool) : Fin 10 := if saved then 3 else 2
def flagMode (saved : Bool) : Fin 10 := if saved then 5 else 4

/-- One-bit FIFO. The two actual END/OWN false cells are used; the TRUE
next-Rat tag is temporarily made false, and will be restored by004d.
Only one Bool is stored in control. No width/room/value enters the code. -/
def shiftMachine : Machine 9 := fun q symbol =>
  match q.val with
  | 0 => some (moveMode symbol,.write false)
  | 1 => some (moveMode symbol,.write true)
  | 2 => some (flagMode false,.move .right)
  | 3 => some (flagMode true,.move .right)
  | 4 => some ((if symbol then 6 else 7),.write false)
  | 5 => some ((if symbol then 6 else 7),.write true)
  | 6 => some (1,.move .right)
  | 7 => some (8,.move .right)
  | 8 => some (9,.write false)
  | _ => none

def state (q : Fin 10) (left right : List Bool) : MachineState 9 := ⟨q,Tape.mk₂ left right⟩

def pairPrefix (saved bit : Bool) (left right : List Bool) : List (MachineState 9) :=
  [state (dataMode saved) left (bit::true::right),
   state (moveMode bit) left (saved::true::right),
   state (flagMode bit) (saved::left) (true::right),
   state 6 (saved::left) (bit::right)]

def shiftTrace (saved : Bool) (left : List Bool) (suffix : List Bool) :
    List Bool → List (MachineState 9)
  | [] =>
      [state (dataMode saved) left (false::false::true::suffix),
       state (moveMode false) left (saved::false::true::suffix),
       state (flagMode false) (saved::left) (false::true::suffix),
       state 7 (saved::left) (false::true::suffix),
       state 8 (false::saved::left) (true::suffix),
       state 9 (false::saved::left) (false::suffix)]
  | bit::later =>
      pairPrefix saved bit left (PSTRTMIncrement009.blocks later++false::false::true::suffix)++
        shiftTrace true (bit::saved::left) suffix later

theorem shift_head (saved : Bool) (left suffix digits : List Bool) :
    (shiftTrace saved left suffix digits).head?=some
      (state (dataMode saved) left (PSTRTMIncrement009.blocks digits++false::false::true::suffix)) := by
  cases digits <;> rfl

theorem shift_last (saved : Bool) (left suffix digits : List Bool) :
    (shiftTrace saved left suffix digits).getLast?=some
      (state 9 (false::((PSTRTMIncrement009.blocks digits).reverse++saved::left)) (false::suffix)) := by
  induction digits generalizing saved left with
  | nil => rfl
  | cons bit later ih =>
    simp only [shiftTrace,List.getLast?_append,ih]
    simp [PSTRTMIncrement009.blocks,List.append_assoc]

theorem pairPrefix_chain (saved bit : Bool) (left right : List Bool) :
    (pairPrefix saved bit left right).IsChain (fun first later=>TM0.step shiftMachine first=some later) := by
  cases saved <;> cases bit <;>
    simp [pairPrefix,List.isChain_cons_cons,TM0.step,shiftMachine,state,dataMode,moveMode,flagMode,Tape.mk₂]

theorem shift_chain (saved : Bool) (left suffix digits : List Bool) :
    (shiftTrace saved left suffix digits).IsChain (fun first later=>TM0.step shiftMachine first=some later) := by
  induction digits generalizing saved left with
  | nil =>
    cases saved <;>
      simp [shiftTrace,List.isChain_cons_cons,TM0.step,shiftMachine,state,dataMode,moveMode,flagMode,Tape.mk₂]
  | cons bit later ih =>
    apply (pairPrefix_chain saved bit left _).append (ih true (bit::saved::left))
    intro last lastMember first firstMember
    change last∈some (state 6 (saved::left)
      (bit::(PSTRTMIncrement009.blocks later++false::false::true::suffix))) at lastMember
    have lastEq:=Option.mem_some_iff.mp lastMember
    rw [shift_head] at firstMember
    have firstEq:=Option.mem_some_iff.mp firstMember
    subst last
    subst first
    simp [TM0.step,shiftMachine,state,dataMode,Tape.mk₂]

theorem shift_length (saved : Bool) (left suffix digits : List Bool) :
    (shiftTrace saved left suffix digits).length=4*digits.length+6 := by
  induction digits generalizing saved left with
  | nil => rfl
  | cons bit later ih =>
    simp only [shiftTrace,List.length_append,pairPrefix,List.length_cons,List.length_nil,ih]
    omega

theorem reverse_blocks (digits : List Bool) :
    (PSTRTMIncrement009.blocks digits).reverse=PSTRTMRawNat010.leftBlocks digits.reverse := by
  induction digits with
  | nil => rfl
  | cons bit later ih =>
    simp [PSTRTMIncrement009.blocks,PSTRTMRawNat010.leftBlocks,List.reverse_cons,
      List.flatMap_append,List.append_assoc] at ih ⊢
    exact ih

theorem shift_runsFrom (left digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom shiftMachine
      (state 0 left (PSTRTMIncrement009.blocks digits++false::false::true::suffix))
      (shiftTrace false left suffix digits)
      (state 9 (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::left)) (false::suffix)) := by
  refine ⟨shift_head false left suffix digits,shift_chain false left suffix digits,?_,?_⟩
  · rw [←reverse_blocks]
    exact shift_last false left suffix digits
  · simp [TM0.step,shiftMachine,state]

/-- Fixed code: shift -> real LEFT -> actual pair rewind -> marker inverse
-> real LEFT/natural tag. All current Tape cells are carried by Seq005. -/
def backMachine : Machine 5 := PA17TMRatArithmeticParse002.fieldBackMachine

def encodeMachine : Machine 25 := PSTRTMSeq005.seqMachine backMachine PA17TMRatArithmeticUnblock004.markerMachine
def taggedMachine : Machine 28 := PSTRTMSeq005.seqMachine encodeMachine (PSTRTMPrepend022.bitMachine false)
def spliceMachine : Machine 38 := PSTRTMSeq005.seqMachine shiftMachine taggedMachine

open PA17TMRatArithmeticWidth018 (BoundedRun)

/-- Genuine adjacent serialization: the next TRUE tag is restored, not
duplicated or silently absorbed into a blank tail. Every old cell outside
the consumed flagged Nat/00 region is retained at its physical location. -/
theorem splice_bounded (n : ℕ) (left suffix : List Bool) :
    BoundedRun spliceMachine
      (Tape.mk₂ left (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n)++false::false::true::suffix))
      38 (Tape.mk₂ left (encodeDatum (.natural n)++true::suffix)) (64*(natBits n+1)^2) := by
  let digits:=PSTRTMNatValue017.rawPayload n
  have width : digits.length=natBits n := by simp only [digits,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have shifted : BoundedRun shiftMachine
      (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++false::false::true::suffix)) 9
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::left)) (false::suffix))
      (4*digits.length+6) :=
    ⟨shiftTrace false left suffix digits,shift_runsFrom left digits suffix,by rw [shift_length]⟩
  have returned : BoundedRun backMachine
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::left)) (false::suffix)) 5
      (Tape.mk₂ (false::left) (PSTRTMIncrement009.blocks digits++false::false::suffix))
      (2*digits.length+5) := by
    refine ⟨PA17TMRatArithmeticParse002.fieldBackTrace left digits (false::suffix),?_,?_⟩
    · have finalEq : PA17TMRatArithmeticParse002.fieldBackFinal left digits (false::suffix)=
          (⟨5,Tape.mk₂ (false::left) (PSTRTMIncrement009.blocks digits++false::false::suffix)⟩ : MachineState 5) := by
        change (⟨PSTRTMSeq005.rightLabel (a:=1) (3 : Fin 4),_⟩ : MachineState 5)=_
        have labelEq : PSTRTMSeq005.rightLabel (a:=1) (3 : Fin 4)=(5 : Fin 6) := by decide
        rw [labelEq]
        rfl
      have actualBack:=PA17TMRatArithmeticParse002.fieldBack_runsFrom left digits (false::suffix)
      rw [finalEq] at actualBack
      exact actualBack
    · rw [PA17TMRatArithmeticParse002.fieldBackTrace_length]
  have encoded : BoundedRun PA17TMRatArithmeticUnblock004.markerMachine
      (Tape.mk₂ (false::left) (PSTRTMIncrement009.blocks digits++false::false::suffix)) 19
      (Tape.mk₂ (false::left) (encodeNat n++true::suffix))
      (digits.length^2+11*digits.length+6) :=
    ⟨PA17TMRatArithmeticUnblock004.markerTrace left digits suffix,
      PA17TMRatArithmeticUnblock004.marker_originalNat_runsFrom n left suffix,
      by rw [PA17TMRatArithmeticUnblock004.marker_length]⟩
  have tagged : BoundedRun (PSTRTMPrepend022.bitMachine false)
      (Tape.mk₂ (false::left) (encodeNat n++true::suffix)) 2
      (Tape.mk₂ left (false::(encodeNat n++true::suffix))) 3 :=
    ⟨PSTRTMThresholdBDatum224.tagTrace left (encodeNat n++true::suffix),
      PSTRTMThresholdBDatum224.tag_runsFrom left (encodeNat n++true::suffix),by exact le_rfl⟩
  have actual:=shifted.seq ((returned.seq encoded).seq tagged)
  have time : (4*digits.length+6)+((2*digits.length+5+(digits.length^2+11*digits.length+6))+3)
      ≤64*(natBits n+1)^2 := by rw [width];nlinarith [Nat.zero_le ((natBits n)^2)]
  exact actual.mono time

theorem splice_contract (n : ℕ) (left suffix : List Bool) (originalInputLength : ℕ) :
    ∃ trace, PSTRTMSeq005.RunsFrom spliceMachine
      ⟨0,Tape.mk₂ left (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n)++false::false::true::suffix)⟩
      trace ⟨38,Tape.mk₂ left (encodeDatum (.natural n)++true::suffix)⟩ ∧
      trace.length≤64*(natBits n+1)^2 ∧
      ∀ clock, visitedSpace spliceMachine originalInputLength (trace.take clock)≤
        originalInputLength+128*(natBits n+1)^2+1 := by
  obtain ⟨trace,actual,time⟩:=splice_bounded n left suffix
  refine ⟨trace,actual,time,?_⟩
  intro clock
  have space:=PSTRTMTrace002.visitedSpace_le spliceMachine originalInputLength (trace.take clock)
  have taken : (trace.take clock).length≤trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  omega

end RootB23.Threshold.NatSplice
