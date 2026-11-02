module
public import Structure.RootB23_Threshold_Uncapped_Shift_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section
namespace RootB23.Threshold.Uncapped.MarkedShift
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMRawNat010 PSTRTMIncrement009

abbrev state := Shift.state
abbrev unitTrace := Shift.unitTrace

/-- The SAME shift table with an arbitrary actual suffix. The three
stale cells are really erased; its two old EOF cells remain before the
literal suffix. Nothing is silently deleted or treated as blank. -/
def endTrace (x y z : Bool) (old suffix : List Bool) : List (MachineState 30) :=
  [state 0 (x::y::z::old) (false::false::suffix),
   state 1 (false::x::y::z::old) (false::suffix),
   state 20 (x::y::z::old) (false::false::suffix),
   state 21 (y::z::old) (x::false::false::suffix),
   state 22 (z::old) (y::x::false::false::suffix),
   state 23 old (z::y::x::false::false::suffix),
   state 24 old (false::y::x::false::false::suffix),
   state 25 (false::old) (y::x::false::false::suffix),
   state 26 (false::old) (false::x::false::false::suffix),
   state 27 (false::false::old) (x::false::false::suffix),
   state 28 (false::false::old) (false::false::false::suffix),
   state 29 (false::old) (false::false::false::false::suffix),
   state 30 old (false::false::false::false::false::suffix)]

def actualTrace (base previous : List Bool) (x y z : Bool) (suffix : List Bool) :
    List Bool → List (MachineState 30)
  | [] => endTrace x y z (leftBlocks previous++base) suffix
  | bit::later => unitTrace x y z bit (leftBlocks previous++base)
      (blocks later++false::false::suffix) ++
      actualTrace base (bit::previous) true bit x suffix later

theorem actual_head (base previous bits suffix : List Bool) (x y z : Bool) :
    (actualTrace base previous x y z suffix bits).head? = some
      (state 0 (x::y::z::(leftBlocks previous++base)) (blocks bits++false::false::suffix)) := by
  cases bits <;> rfl

theorem actual_last (base previous bits suffix : List Bool) (x y z : Bool) :
    (actualTrace base previous x y z suffix bits).getLast? = some
      (state 30 (leftBlocks (bits.reverse++previous)++base)
        (false::false::false::false::false::suffix)) := by
  induction bits generalizing previous x y z with
  | nil => rfl
  | cons bit later ih =>
    simp only [actualTrace,List.getLast?_append,ih,Option.some_or,
      List.reverse_cons,List.append_assoc,List.singleton_append]

theorem actual_length (base previous bits suffix : List Bool) (x y z : Bool) :
    (actualTrace base previous x y z suffix bits).length = 12*bits.length+13 := by
  induction bits generalizing previous x y z with
  | nil => rfl
  | cons bit later ih =>
    simp only [actualTrace,List.length_append,unitTrace,Shift.unitTrace,List.length_cons,List.length_nil,ih]
    omega

private theorem unit_chain (x y z bit : Bool) (old tail : List Bool) :
    (unitTrace x y z bit old tail).IsChain (fun a b => Turing.TM0.step Shift.code a = some b) := by
  cases bit <;> simp [unitTrace,Shift.unitTrace,List.isChain_cons_cons,Shift.state,
    Shift.code,Turing.TM0.step,Turing.Tape.mk₂]

private theorem end_chain (x y z : Bool) (old suffix : List Bool) :
    (endTrace x y z old suffix).IsChain (fun a b => Turing.TM0.step Shift.code a = some b) := by
  simp [endTrace,List.isChain_cons_cons,state,Shift.state,Shift.code,Turing.TM0.step,Turing.Tape.mk₂]

theorem actual_chain (base previous bits suffix : List Bool) (x y z : Bool) :
    (actualTrace base previous x y z suffix bits).IsChain (fun a b => Turing.TM0.step Shift.code a = some b) := by
  induction bits generalizing previous x y z with
  | nil => exact end_chain x y z _ _
  | cons bit later ih =>
    apply (unit_chain x y z bit (leftBlocks previous++base)
      (blocks later++false::false::suffix)).append (ih _ _ _ _)
    intro a ha b hb
    simp only [unitTrace,Shift.unitTrace,List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at ha
    rw [actual_head] at hb
    have same := Option.mem_some_iff.mp hb
    subst a
    subst b
    simp [state,Shift.state,Shift.code,Turing.TM0.step,Turing.Tape.mk₂,leftBlocks]

theorem marked_shift_runsFrom (base bits suffix : List Bool) (x y z : Bool) :
    PSTRTMSeq005.RunsFrom Shift.code
      (state 0 (x::y::z::base) (blocks bits++false::false::suffix))
      (actualTrace base [] x y z suffix bits)
      (state 30 (leftBlocks bits.reverse++base) (false::false::false::false::false::suffix)) := by
  refine ⟨?_,actual_chain _ _ _ _ _ _ _,?_,?_⟩
  · simpa only [leftBlocks,List.flatMap_nil,List.nil_append] using actual_head base [] bits suffix x y z
  · simpa only [List.append_nil] using actual_last base [] bits suffix x y z
  · simp [Shift.state,Shift.code,Turing.TM0.step]

end RootB23.Threshold.Uncapped.MarkedShift
