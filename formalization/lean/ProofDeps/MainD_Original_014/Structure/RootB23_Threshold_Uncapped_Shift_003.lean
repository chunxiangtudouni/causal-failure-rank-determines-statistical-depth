module
public import Common.PSTR_TM_PairRewind_105

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section
namespace RootB23.Threshold.Uncapped.Shift
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMRawNat010 PSTRTMIncrement009

/-- Copy a flagged field three cells LEFT. The program reads real TRUE
flags and erases all three stale trailing cells before returning. The
blank far-right boundary is an internal physical interface, never an
additional original q-input premise. -/
def code : Machine 30 := fun q symbol =>
  match q.val with
  | 0 => some (if symbol then 2 else 1, .move .right)
  | 1 => some (if symbol then 3 else 20, .move .left)
  | 2 => some (if symbol then 4 else 20, .move .left)
  | 3 => some (5, .move .left)
  | 4 => some (6, .move .left)
  | 5 => some (7, .move .left)
  | 6 => some (8, .move .left)
  | 7 => some (9, .move .left)
  | 8 => some (10, .move .left)
  | 9 => some (11, .write false)
  | 10 => some (11, .write true)
  | 11 => some (12, .move .right)
  | 12 => some (13, .write true)
  | 13 => some (14, .move .right)
  | 14 => some (15, .move .right)
  | 15 => some (16, .move .right)
  | 16 => some (0, .move .right)
  | 20 => some (21, .move .left)
  | 21 => some (22, .move .left)
  | 22 => some (23, .move .left)
  | 23 => some (24, .write false)
  | 24 => some (25, .move .right)
  | 25 => some (26, .write false)
  | 26 => some (27, .move .right)
  | 27 => some (28, .write false)
  | 28 => some (29, .move .left)
  | 29 => some (30, .move .left)
  | _ => none

def state (q : Fin 31) (left right : List Bool) : MachineState 30 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def unitTrace (x y z bit : Bool) (old tail : List Bool) : List (MachineState 30) :=
  [state 0 (x::y::z::old) (bit::true::tail),
   state (if bit then 2 else 1) (bit::x::y::z::old) (true::tail),
   state (if bit then 4 else 3) (x::y::z::old) (bit::true::tail),
   state (if bit then 6 else 5) (y::z::old) (x::bit::true::tail),
   state (if bit then 8 else 7) (z::old) (y::x::bit::true::tail),
   state (if bit then 10 else 9) old (z::y::x::bit::true::tail),
   state 11 old (bit::y::x::bit::true::tail),
   state 12 (bit::old) (y::x::bit::true::tail),
   state 13 (bit::old) (true::x::bit::true::tail),
   state 14 (true::bit::old) (x::bit::true::tail),
   state 15 (x::true::bit::old) (bit::true::tail),
   state 16 (bit::x::true::bit::old) (true::tail)]

def endTrace (x y z : Bool) (old : List Bool) : List (MachineState 30) :=
  [state 0 (x::y::z::old) [],
   state 1 (false::x::y::z::old) [],
   state 20 (x::y::z::old) [],
   state 21 (y::z::old) [x],
   state 22 (z::old) [y,x],
   state 23 old [z,y,x],
   state 24 old [false,y,x],
   state 25 (false::old) [y,x],
   state 26 (false::old) [false,x],
   state 27 (false::false::old) [x],
   state 28 (false::false::old) [],
   state 29 (false::old) [],
   state 30 old []]

def actualTrace (base previous : List Bool) (x y z : Bool) : List Bool → List (MachineState 30)
  | [] => endTrace x y z (leftBlocks previous++base)
  | bit::later => unitTrace x y z bit (leftBlocks previous++base) (blocks later) ++
      actualTrace base (bit::previous) true bit x later

theorem actual_head (base previous bits : List Bool) (x y z : Bool) :
    (actualTrace base previous x y z bits).head? = some
      (state 0 (x::y::z::(leftBlocks previous++base)) (blocks bits)) := by
  cases bits <;> rfl

theorem actual_last (base previous bits : List Bool) (x y z : Bool) :
    (actualTrace base previous x y z bits).getLast? = some
      (state 30 (leftBlocks (bits.reverse++previous)++base) []) := by
  induction bits generalizing previous x y z with
  | nil => rfl
  | cons bit later ih =>
    simp only [actualTrace,List.getLast?_append,ih,Option.some_or,
      List.reverse_cons,List.append_assoc,List.singleton_append]

theorem actual_length (base previous bits : List Bool) (x y z : Bool) :
    (actualTrace base previous x y z bits).length = 12*bits.length+13 := by
  induction bits generalizing previous x y z with
  | nil => rfl
  | cons bit later ih =>
    simp only [actualTrace,List.length_append,unitTrace,List.length_cons,List.length_nil,ih]
    omega

private theorem unit_chain (x y z bit : Bool) (old tail : List Bool) :
    (unitTrace x y z bit old tail).IsChain (fun a b => Turing.TM0.step code a = some b) := by
  cases bit <;> simp [unitTrace,List.isChain_cons_cons,state,code,Turing.TM0.step,Turing.Tape.mk₂]

private theorem end_chain (x y z : Bool) (old : List Bool) :
    (endTrace x y z old).IsChain (fun a b => Turing.TM0.step code a = some b) := by
  have blank : Turing.ListBlank.mk [false] = Turing.ListBlank.mk ([] : List Bool) :=
    PSTRTMRawNat010.blank_append_false []
  simp [endTrace,List.isChain_cons_cons,state,code,Turing.TM0.step,Turing.Tape.mk₂,blank]

theorem actual_chain (base previous bits : List Bool) (x y z : Bool) :
    (actualTrace base previous x y z bits).IsChain (fun a b => Turing.TM0.step code a = some b) := by
  induction bits generalizing previous x y z with
  | nil => exact end_chain x y z _
  | cons bit later ih =>
    apply (unit_chain x y z bit (leftBlocks previous++base) (blocks later)).append (ih _ _ _ _)
    intro a ha b hb
    simp only [unitTrace,List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at ha
    rw [actual_head] at hb
    have eqb := Option.mem_some_iff.mp hb
    subst a
    subst b
    simp [state,code,Turing.TM0.step,Turing.Tape.mk₂,leftBlocks]

theorem shift_runsFrom (base bits : List Bool) (x y z : Bool) :
    PSTRTMSeq005.RunsFrom code
      (state 0 (x::y::z::base) (blocks bits))
      (actualTrace base [] x y z bits)
      (state 30 (leftBlocks bits.reverse++base) []) := by
  refine ⟨?_,actual_chain _ _ _ _ _ _,?_,?_⟩
  · simpa only [leftBlocks,List.flatMap_nil,List.nil_append] using actual_head base [] bits x y z
  · simpa only [List.append_nil] using actual_last base [] bits x y z
  · simp [state,code,Turing.TM0.step]

end RootB23.Threshold.Uncapped.Shift
