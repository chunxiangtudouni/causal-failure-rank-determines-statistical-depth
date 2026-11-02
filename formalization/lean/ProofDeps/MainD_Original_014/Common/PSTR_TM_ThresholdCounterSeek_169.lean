module
public import Common.PSTR_TM_ThresholdDepthZeroRun_168

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCounterSeek169
open PaperProofs.Common.Native.RationalControllerComputation

/-- Read aligned real00 pairs until the next true B flag. It actually
returns one cell left to that B digit, even when the digit itself is
FALSE. No code parameter contains the gap, B value, branch or answer. -/
def seekMachine : Machine 2 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (if symbol then 2 else 0,if symbol then .move .left else .move .right)
  | _ => none

def state (q : Fin 3) (left right : List Bool) : MachineState 2 := ⟨q,Turing.Tape.mk₂ left right⟩

def gaps : Nat → List Bool
  | 0 => []
  | count+1 => false::false::gaps count

def gapLeft : Nat → List Bool → List Bool
  | 0,left => left
  | count+1,left => gapLeft count (false::false::left)

theorem gaps_replicate (count : Nat) : gaps count=List.replicate (2*count) false := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have he : 2*(count+1)=2+2*count := by omega
    simp [gaps,ih,he,List.replicate_add]

theorem gaps_snoc (count : Nat) : gaps count++[false,false]=gaps (count+1) := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [gaps,List.cons_append] using congrArg (fun tail => false::false::tail) ih

theorem gapLeft_eq (count : Nat) (left : List Bool) : gapLeft count left=gaps count++left := by
  induction count generalizing left with
  | zero => rfl
  | succ count ih =>
    rw [gapLeft,ih,←gaps_snoc]
    simp only [List.append_assoc,List.cons_append,List.nil_append]

def seekTrace (bit : Bool) (suffix : List Bool) : Nat → List Bool → List (MachineState 2)
  | 0,left => [state 0 left (bit::true::suffix),state 1 (bit::left) (true::suffix),state 2 left (bit::true::suffix)]
  | count+1,left =>
    state 0 left (false::false::(gaps count++bit::true::suffix)) ::
      state 1 (false::left) (false::(gaps count++bit::true::suffix)) ::
        seekTrace bit suffix count (false::false::left)

theorem seek_head (bit : Bool) (suffix : List Bool) (count : Nat) (left : List Bool) :
    (seekTrace bit suffix count left).head?=some (state 0 left (gaps count++bit::true::suffix)) := by
  cases count <;> rfl

theorem seek_last (bit : Bool) (suffix : List Bool) (count : Nat) (left : List Bool) :
    (seekTrace bit suffix count left).getLast?=some (state 2 (gapLeft count left) (bit::true::suffix)) := by
  induction count generalizing left with
  | zero => rfl
  | succ count ih =>
    have hn : seekTrace bit suffix count (false::false::left)≠[] := by
      intro h
      have hh := seek_head bit suffix count (false::false::left)
      simp only [h,List.head?_nil,reduceCtorEq] at hh
    simp only [seekTrace,List.getLast?_cons_cons,List.getLast?_cons_of_ne_nil hn,gapLeft]
    exact ih _

theorem seek_chain (bit : Bool) (suffix : List Bool) (count : Nat) (left : List Bool) :
    (seekTrace bit suffix count left).IsChain
      (fun before after => Turing.TM0.step seekMachine before=some after) := by
  induction count generalizing left with
  | zero => simp [seekTrace,List.isChain_cons_cons,Turing.TM0.step,seekMachine,state,Turing.Tape.mk₂]
  | succ count ih =>
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step,seekMachine,state,Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [seek_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      simp [Turing.TM0.step,seekMachine,state,Turing.Tape.mk₂]
    · exact ih _

theorem seek_runsFrom (bit : Bool) (suffix : List Bool) (count : Nat) (left : List Bool) :
    PSTRTMSeq005.RunsFrom seekMachine (state 0 left (gaps count++bit::true::suffix))
      (seekTrace bit suffix count left) (state 2 (gapLeft count left) (bit::true::suffix)) :=
  ⟨seek_head _ _ _ _,seek_chain _ _ _ _,seek_last _ _ _ _,by simp [Turing.TM0.step,seekMachine,state]⟩

theorem seek_length (bit : Bool) (suffix : List Bool) (count : Nat) (left : List Bool) :
    (seekTrace bit suffix count left).length=2*count+3 := by
  induction count generalizing left with
  | zero => rfl
  | succ count ih => simp only [seekTrace,List.length_cons,ih]; omega

theorem seek_visitedSpace_le (bit : Bool) (suffix : List Bool) (count : Nat) (left : List Bool) :
    visitedSpace seekMachine (left.length+2*count+2+suffix.length) (seekTrace bit suffix count left)≤
      left.length+suffix.length+6*count+9 := by
  have h := PSTRTMTrace002.visitedSpace_le seekMachine (left.length+2*count+2+suffix.length) (seekTrace bit suffix count left)
  rw [seek_length] at h
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCounterSeek169
