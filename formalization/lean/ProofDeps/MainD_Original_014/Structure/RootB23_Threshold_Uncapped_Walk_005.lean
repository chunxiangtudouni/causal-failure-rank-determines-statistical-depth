module
public import Structure.RootB23_Threshold_Uncapped_Erase_004
public import Structure.PA17_TM_RatArithmetic_Allocate_013d

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section
namespace RootB23.Threshold.Uncapped.Walk
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMRawNat010 PSTRTMIncrement009

/-- Read actual alternating field flags without changing any tape cell. -/
def code : Machine 2 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (if symbol then 0 else 2,if symbol then .move .right else .move .left)
  | _ => none

def state (q : Fin 3) (left right : List Bool) : MachineState 2 := ⟨q,Turing.Tape.mk₂ left right⟩

def actualTrace (left : List Bool) : List Bool → List Bool → List (MachineState 2)
  | [],tail => [state 0 left (false::false::tail),state 1 (false::left) (false::tail),
      state 2 left (false::false::tail)]
  | bit::later,tail => state 0 left (bit::true::(blocks later++false::false::tail)) ::
      state 1 (bit::left) (true::(blocks later++false::false::tail)) ::
      actualTrace (true::bit::left) later tail

theorem actual_head (left bits tail : List Bool) :
    (actualTrace left bits tail).head? = some (state 0 left (blocks bits++false::false::tail)) := by
  cases bits <;> rfl

theorem actual_last (left bits tail : List Bool) :
    (actualTrace left bits tail).getLast? = some
      (state 2 (leftBlocks bits.reverse++left) (false::false::tail)) := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    have nonempty : actualTrace (true::bit::left) later tail ≠ [] := by
      intro h
      have hh := actual_head (true::bit::left) later tail
      simp only [h,List.head?_nil,reduceCtorEq] at hh
    simp only [actualTrace,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil nonempty,ih]
    simp [List.reverse_cons,leftBlocks,List.flatMap_append,List.append_assoc]

theorem actual_length (left bits tail : List Bool) :
    (actualTrace left bits tail).length = 2*bits.length+3 := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit later ih => simp only [actualTrace,List.length_cons,ih]; omega

theorem actual_chain (left bits tail : List Bool) :
    (actualTrace left bits tail).IsChain (fun a b => Turing.TM0.step code a = some b) := by
  induction bits generalizing left with
  | nil => simp [actualTrace,List.isChain_cons_cons,state,code,Turing.TM0.step,Turing.Tape.mk₂]
  | cons bit later ih =>
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [state,code,Turing.TM0.step,Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [actual_head] at ha
      have same := Option.mem_some_iff.mp ha
      subst after
      simp [state,code,Turing.TM0.step,Turing.Tape.mk₂]
    · exact ih _

theorem field_runsFrom (left bits tail : List Bool) :
    PSTRTMSeq005.RunsFrom code (state 0 left (blocks bits++false::false::tail))
      (actualTrace left bits tail)
      (state 2 (leftBlocks bits.reverse++left) (false::false::tail)) :=
  ⟨actual_head _ _ _,actual_chain _ _ _,actual_last _ _ _,by simp [state,code,Turing.TM0.step]⟩

/-- The left eraser starts at the real stream-parser endpoint, crosses
its actual FALSE guard, and clears the flagged payload back to its guard. -/
def eraseLeftTrace (base bits tail : List Bool) : List (MachineState 7) :=
  [Erase.lstate 0 (false::(leftBlocks bits.reverse++false::base)) tail,
   Erase.lstate 1 (leftBlocks bits.reverse++false::base) (false::tail)] ++
  Erase.leftTrace base bits.reverse (false::tail)

theorem eraseLeft_runsFrom (base bits tail : List Bool) :
    PSTRTMSeq005.RunsFrom Erase.leftCode
      (Erase.lstate 0 (false::(leftBlocks bits.reverse++false::base)) tail)
      (eraseLeftTrace base bits tail)
      (Erase.lstate 7 base (false::(List.replicate (2*bits.length) false++false::tail))) := by
  refine ⟨rfl,?_,?_,by simp [Erase.lstate,Erase.leftCode,Turing.TM0.step]⟩
  · apply List.IsChain.append
    · simp [List.isChain_cons_cons,Erase.lstate,Erase.leftCode,Turing.TM0.step,Turing.Tape.mk₂]
    · exact Erase.left_chain _ _ _
    · intro a ha b hb
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at ha
      rw [Erase.left_head] at hb
      have same := Option.mem_some_iff.mp hb
      subst a
      subst b
      cases bits.reverse <;>
        simp [Erase.leftInitial,Erase.lstate,Erase.leftCode,Turing.TM0.step,Turing.Tape.mk₂,leftBlocks]
  · simp only [eraseLeftTrace,List.getLast?_append,Erase.left_last,Option.some_or,List.length_reverse]

theorem eraseLeft_length (base bits tail : List Bool) :
    (eraseLeftTrace base bits tail).length = 4*bits.length+4 := by
  simp only [eraseLeftTrace,List.length_append,List.length_cons,List.length_nil,
    Erase.left_length,List.length_reverse]
  omega

open PA17TMRatArithmeticAllocate013

/-- The reused scan's initial move ignores the actual head bit. This
thin real-chain interface includes FALSE heads; no marker is fabricated. -/
def forwardTrace (head : Bool) (gap : Nat) (left tail : List Bool) : List (MachineState 1) :=
  seekState 0 left (head::(List.replicate gap false++true::tail)) ::
    seekRightTrace gap (head::left) tail

theorem forward_runsFrom (head : Bool) (gap : Nat) (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom (gapSeekMachine .right)
      (seekState 0 left (head::(List.replicate gap false++true::tail)))
      (forwardTrace head gap left tail)
      (seekState 1 (List.replicate gap false++head::left) (true::tail)) := by
  refine ⟨rfl,?_,?_,?_⟩
  · apply List.IsChain.cons (seekRight_chain gap (head::left) tail)
    intro next hn
    rw [seekRight_head] at hn
    have same := Option.mem_some_iff.mp hn
    subst next
    simp [Turing.TM0.step,gapSeekMachine,seekState,Turing.Tape.mk₂]
  · change (_ :: seekRightTrace gap (head::left) tail).getLast? = _
    have hn : seekRightTrace gap (head::left) tail ≠ [] := by
      intro h
      have hh := seekRight_head gap (head::left) tail
      simp only [h,List.head?_nil,reduceCtorEq] at hh
    rw [List.getLast?_cons_of_ne_nil hn,seekRight_last]
  · simp [Turing.TM0.step,gapSeekMachine,seekState,Turing.Tape.mk₂]

theorem forward_length (head : Bool) (gap : Nat) (left tail : List Bool) :
    (forwardTrace head gap left tail).length = gap+2 := by
  simp only [forwardTrace,List.length_cons,seekRight_length]

end RootB23.Threshold.Uncapped.Walk

namespace RootB23.Threshold.Uncapped.Gap
open PaperProofs.Common.Native.RationalControllerComputation

/-- Scan the real even-length FALSE gap by pairs and inspect only flag
positions. A zero first data bit never masquerades as an extra gap cell. -/
def code : Machine 2 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (if symbol then 2 else 0,if symbol then .move .left else .move .right)
  | _ => none

def state (q : Fin 3) (left right : List Bool) : MachineState 2 := ⟨q,Turing.Tape.mk₂ left right⟩

def actualTrace (left : List Bool) (bit : Bool) (tail : List Bool) : Nat → List (MachineState 2)
  | 0 => [state 0 left (bit::true::tail),state 1 (bit::left) (true::tail),
      state 2 left (bit::true::tail)]
  | count+1 => state 0 left (false::false::(List.replicate (2*count) false++bit::true::tail)) ::
      state 1 (false::left) (false::(List.replicate (2*count) false++bit::true::tail)) ::
      actualTrace (false::false::left) bit tail count

theorem actual_head (left : List Bool) (bit : Bool) (tail : List Bool) (count : Nat) :
    (actualTrace left bit tail count).head? = some
      (state 0 left (List.replicate (2*count) false++bit::true::tail)) := by
  cases count with
  | zero => rfl
  | succ count =>
    rw [show 2*(count+1)=2+2*count by omega,List.replicate_add]
    rfl

theorem actual_last (left : List Bool) (bit : Bool) (tail : List Bool) (count : Nat) :
    (actualTrace left bit tail count).getLast? = some
      (state 2 (List.replicate (2*count) false++left) (bit::true::tail)) := by
  induction count generalizing left with
  | zero => rfl
  | succ count ih =>
    have hn : actualTrace (false::false::left) bit tail count ≠ [] := by
      intro h
      have hh := actual_head (false::false::left) bit tail count
      simp only [h,List.head?_nil,reduceCtorEq] at hh
    simp only [actualTrace,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hn,ih]
    rw [show 2*(count+1)=2*count+2 by omega,List.replicate_add]
    simp only [List.append_assoc,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append]

theorem actual_chain (left : List Bool) (bit : Bool) (tail : List Bool) (count : Nat) :
    (actualTrace left bit tail count).IsChain (fun a b => Turing.TM0.step code a = some b) := by
  induction count generalizing left with
  | zero => simp [actualTrace,List.isChain_cons_cons,state,code,Turing.TM0.step,Turing.Tape.mk₂]
  | succ count ih =>
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [state,code,Turing.TM0.step,Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [actual_head] at ha
      have same := Option.mem_some_iff.mp ha
      subst after
      simp [state,code,Turing.TM0.step,Turing.Tape.mk₂]
    · exact ih _

theorem actual_length (left : List Bool) (bit : Bool) (tail : List Bool) (count : Nat) :
    (actualTrace left bit tail count).length = 2*count+3 := by
  induction count generalizing left with
  | zero => rfl
  | succ count ih => simp only [actualTrace,List.length_cons,ih]; omega

theorem pair_gap_runsFrom (left : List Bool) (bit : Bool) (tail : List Bool) (count : Nat) :
    PSTRTMSeq005.RunsFrom code
      (state 0 left (List.replicate (2*count) false++bit::true::tail))
      (actualTrace left bit tail count)
      (state 2 (List.replicate (2*count) false++left) (bit::true::tail)) :=
  ⟨actual_head _ _ _ _,actual_chain _ _ _ _,actual_last _ _ _ _,by simp [state,code,Turing.TM0.step]⟩

end RootB23.Threshold.Uncapped.Gap
