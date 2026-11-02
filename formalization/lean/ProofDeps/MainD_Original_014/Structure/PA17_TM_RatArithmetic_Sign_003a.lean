module
public import Common.PSTR_TM_Seq_005
public import Common.PSTR_TM_Codec_001
public import Mathlib.Tactic.Linarith

/-! Fixed sign-only control. The zero decision is physically read from the
canonical numerator header/payload, never supplied by a caller. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSign003

def negateDatumMachine : Machine 15 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (if symbol then 3 else 2,.move .right)
  | 2 => some (4,.move .right)
  | 3 => some (5,.move .right)
  | 4 => some (if symbol then 6 else 8,if symbol then .move .left else .move .right)
  | 5 => some (if symbol then 7 else 9,if symbol then .move .left else .move .right)
  | 6 => some (10,.move .left)
  | 7 => some (11,.move .left)
  | 8 => some (if symbol then 12 else 13,.move .left)
  | 9 => some (13,.move .left)
  | 10 => some (14,.write true)
  | 11 => some (14,.write false)
  | 12 => some (6,.move .left)
  | 13 => some (7,.move .left)
  | 14 => some (15,.move .left)
  | _ => none

def state (q : Fin 16) (left right : List Bool) : MachineState 15 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def headerState (sign : Bool) : Fin 16 := if sign then 3 else 2
def testState (sign : Bool) : Fin 16 := if sign then 5 else 4
def backState (sign : Bool) : Fin 16 := if sign then 7 else 6
def writeState (sign : Bool) : Fin 16 := if sign then 11 else 10
def payloadState (sign : Bool) : Fin 16 := if sign then 9 else 8
def smallSign (sign bit : Bool) : Bool := bit && !sign

def wideTrace (sign : Bool) (left tail : List Bool) : List (MachineState 15) :=
  [state 0 left (true::sign::true::true::tail),
   state 1 (true::left) (sign::true::true::tail),
   state (headerState sign) (sign::true::left) (true::true::tail),
   state (testState sign) (true::sign::true::left) (true::tail),
   state (backState sign) (sign::true::left) (true::true::tail),
   state (writeState sign) (true::left) (sign::true::true::tail),
   state 14 (true::left) ((!sign)::true::true::tail),
   state 15 left (true::(!sign)::true::true::tail)]

theorem wide_runsFrom (sign : Bool) (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom negateDatumMachine
      (state 0 left (true::sign::true::true::tail)) (wideTrace sign left tail)
      (state 15 left (true::(!sign)::true::true::tail)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · cases sign <;> simp [wideTrace,List.isChain_cons_cons,Turing.TM0.step,
      negateDatumMachine,state,headerState,testState,backState,writeState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,negateDatumMachine,state]

def smallTrace (sign bit : Bool) (left tail : List Bool) : List (MachineState 15) :=
  [state 0 left (true::sign::true::false::bit::tail),
   state 1 (true::left) (sign::true::false::bit::tail),
   state (headerState sign) (sign::true::left) (true::false::bit::tail),
   state (testState sign) (true::sign::true::left) (false::bit::tail),
   state (payloadState sign) (false::true::sign::true::left) (bit::tail),
   state (if smallSign sign bit then 12 else 13) (true::sign::true::left) (false::bit::tail),
   state (if smallSign sign bit then 6 else 7) (sign::true::left) (true::false::bit::tail),
   state (if smallSign sign bit then 10 else 11) (true::left) (sign::true::false::bit::tail),
   state 14 (true::left) (smallSign sign bit::true::false::bit::tail),
   state 15 left (true::smallSign sign bit::true::false::bit::tail)]

theorem small_runsFrom (sign bit : Bool) (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom negateDatumMachine
      (state 0 left (true::sign::true::false::bit::tail)) (smallTrace sign bit left tail)
      (state 15 left (true::smallSign sign bit::true::false::bit::tail)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · cases sign <;> cases bit <;> simp [smallTrace,smallSign,List.isChain_cons_cons,
      Turing.TM0.step,negateDatumMachine,state,headerState,testState,payloadState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,negateDatumMachine,state]

theorem wideTrace_length (sign : Bool) (left tail : List Bool) : (wideTrace sign left tail).length = 8 := rfl
theorem smallTrace_length (sign bit : Bool) (left tail : List Bool) : (smallTrace sign bit left tail).length = 10 := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSign003
