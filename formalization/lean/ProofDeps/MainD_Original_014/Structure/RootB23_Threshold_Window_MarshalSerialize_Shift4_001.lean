module
public import Structure.RootB23_Threshold_Uncapped_MarkedShift_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.Window.MarshalSerialize.Shift4
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PSTRTMRawNat010 PSTRTMIncrement009

/-- The checked LEFT3 field mover's finite read/write protocol, extended
by one real LEFT and RIGHT. Four stale cells are actually erased. The
two old EOF cells and every arbitrary suffix cell remain at their sites. -/
def code : Machine 34 := fun q symbol=>match q.val with
  | 0=>some (if symbol then 2 else 1,.move .right)
  | 1=>some (if symbol then 3 else 20,.move .left)
  | 2=>some (if symbol then 4 else 20,.move .left)
  | 3=>some (5,.move .left)
  | 4=>some (6,.move .left)
  | 5=>some (7,.move .left)
  | 6=>some (8,.move .left)
  | 7=>some (9,.move .left)
  | 8=>some (10,.move .left)
  | 9=>some (11,.move .left)
  | 10=>some (12,.move .left)
  | 11=>some (13,.write false)
  | 12=>some (13,.write true)
  | 13=>some (14,.move .right)
  | 14=>some (15,.write true)
  | 15=>some (16,.move .right)
  | 16=>some (17,.move .right)
  | 17=>some (18,.move .right)
  | 18=>some (19,.move .right)
  | 19=>some (0,.move .right)
  | 20=>some (21,.move .left)
  | 21=>some (22,.move .left)
  | 22=>some (23,.move .left)
  | 23=>some (24,.move .left)
  | 24=>some (25,.write false)
  | 25=>some (26,.move .right)
  | 26=>some (27,.write false)
  | 27=>some (28,.move .right)
  | 28=>some (29,.write false)
  | 29=>some (30,.move .right)
  | 30=>some (31,.write false)
  | 31=>some (32,.move .left)
  | 32=>some (33,.move .left)
  | 33=>some (34,.move .left)
  | _=>none

def state (q : Fin 35) (left right : List Bool) : MachineState 34 := ⟨q,Tape.mk₂ left right⟩
def unitTrace (x y z t bit : Bool) (old tail : List Bool) : List (MachineState 34) :=
  [state 0 (x::y::z::t::old) (bit::true::tail),
   state (if bit then 2 else 1) (bit::x::y::z::t::old) (true::tail),
   state (if bit then 4 else 3) (x::y::z::t::old) (bit::true::tail),
   state (if bit then 6 else 5) (y::z::t::old) (x::bit::true::tail),
   state (if bit then 8 else 7) (z::t::old) (y::x::bit::true::tail),
   state (if bit then 10 else 9) (t::old) (z::y::x::bit::true::tail),
   state (if bit then 12 else 11) old (t::z::y::x::bit::true::tail),
   state 13 old (bit::z::y::x::bit::true::tail),
   state 14 (bit::old) (z::y::x::bit::true::tail),
   state 15 (bit::old) (true::y::x::bit::true::tail),
   state 16 (true::bit::old) (y::x::bit::true::tail),
   state 17 (y::true::bit::old) (x::bit::true::tail),
   state 18 (x::y::true::bit::old) (bit::true::tail),
   state 19 (bit::x::y::true::bit::old) (true::tail)]

def endTrace (x y z t : Bool) (old suffix : List Bool) : List (MachineState 34) :=
  [state 0 (x::y::z::t::old) (false::false::suffix),
   state 1 (false::x::y::z::t::old) (false::suffix),
   state 20 (x::y::z::t::old) (false::false::suffix),
   state 21 (y::z::t::old) (x::false::false::suffix),
   state 22 (z::t::old) (y::x::false::false::suffix),
   state 23 (t::old) (z::y::x::false::false::suffix),
   state 24 old (t::z::y::x::false::false::suffix),
   state 25 old (false::z::y::x::false::false::suffix),
   state 26 (false::old) (z::y::x::false::false::suffix),
   state 27 (false::old) (false::y::x::false::false::suffix),
   state 28 (false::false::old) (y::x::false::false::suffix),
   state 29 (false::false::old) (false::x::false::false::suffix),
   state 30 (false::false::false::old) (x::false::false::suffix),
   state 31 (false::false::false::old) (false::false::false::suffix),
   state 32 (false::false::old) (false::false::false::false::suffix),
   state 33 (false::old) (false::false::false::false::false::suffix),
   state 34 old (false::false::false::false::false::false::suffix)]

def actualTrace (base previous : List Bool) (x y z t : Bool) (suffix : List Bool) :
    List Bool → List (MachineState 34)
  | []=>endTrace x y z t (leftBlocks previous++base) suffix
  | bit::later=>unitTrace x y z t bit (leftBlocks previous++base)
      (blocks later++false::false::suffix)++
      actualTrace base (bit::previous) true bit x y suffix later

theorem actual_head (base previous digits suffix : List Bool) (x y z t : Bool) :
    (actualTrace base previous x y z t suffix digits).head?=some
      (state 0 (x::y::z::t::(leftBlocks previous++base)) (blocks digits++false::false::suffix)) := by
  cases digits <;> rfl
theorem actual_last (base previous digits suffix : List Bool) (x y z t : Bool) :
    (actualTrace base previous x y z t suffix digits).getLast?=some
      (state 34 (leftBlocks (digits.reverse++previous)++base)
        (false::false::false::false::false::false::suffix)) := by
  induction digits generalizing previous x y z t with
  | nil=>rfl
  | cons bit later ih=>
    simp only [actualTrace,List.getLast?_append,ih,Option.some_or,
      List.reverse_cons,List.append_assoc,List.singleton_append]
theorem actual_length (base previous digits suffix : List Bool) (x y z t : Bool) :
    (actualTrace base previous x y z t suffix digits).length=14*digits.length+17 := by
  induction digits generalizing previous x y z t with
  | nil=>rfl
  | cons bit later ih=>
    simp only [actualTrace,List.length_append,unitTrace,List.length_cons,List.length_nil,ih]
    omega

private theorem unit_chain (x y z t bit : Bool) (old tail : List Bool) :
    (unitTrace x y z t bit old tail).IsChain (fun a b=>TM0.step code a=some b) := by
  cases bit <;> simp [unitTrace,List.isChain_cons_cons,state,code,TM0.step,Tape.mk₂]
private theorem end_chain (x y z t : Bool) (old suffix : List Bool) :
    (endTrace x y z t old suffix).IsChain (fun a b=>TM0.step code a=some b) := by
  simp [endTrace,List.isChain_cons_cons,state,code,TM0.step,Tape.mk₂]
theorem actual_chain (base previous digits suffix : List Bool) (x y z t : Bool) :
    (actualTrace base previous x y z t suffix digits).IsChain (fun a b=>TM0.step code a=some b) := by
  induction digits generalizing previous x y z t with
  | nil=>exact end_chain x y z t _ _
  | cons bit later ih=>
    apply (unit_chain x y z t bit (leftBlocks previous++base)
      (blocks later++false::false::suffix)).append (ih _ _ _ _ _)
    intro a ha b hb
    simp only [unitTrace,List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at ha
    rw [actual_head] at hb
    have equal:=Option.mem_some_iff.mp hb
    subst a
    subst b
    simp [state,code,TM0.step,Tape.mk₂,leftBlocks]

theorem shift_runsFrom (base digits suffix : List Bool) (x y z t : Bool) :
    PSTRTMSeq005.RunsFrom code
      (state 0 (x::y::z::t::base) (blocks digits++false::false::suffix))
      (actualTrace base [] x y z t suffix digits)
      (state 34 (leftBlocks digits.reverse++base)
        (false::false::false::false::false::false::suffix)) := by
  refine ⟨?_,actual_chain _ _ _ _ _ _ _ _,?_,?_⟩
  · simpa only [leftBlocks,List.flatMap_nil,List.nil_append] using actual_head base [] digits suffix x y z t
  · simpa only [List.append_nil] using actual_last base [] digits suffix x y z t
  · simp [state,code,TM0.step]

end RootB23.Threshold.Window.MarshalSerialize.Shift4
