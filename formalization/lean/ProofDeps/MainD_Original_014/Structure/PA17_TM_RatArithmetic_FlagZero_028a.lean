module
public import Common.PSTR_TM_NatValue_017
public import Common.PSTR_TM_Seq_005

/-! A fixed ten-label read-only observer. Numerical zero is asserted only
for canonical rawPayload fields in the next module. Physical leading-zero
lists such as [false,false] follow the long-field port without a numeric claim. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFlagZero028

open Turing

def zeroPort : Fin 10 := 6
def nonzeroPort : Fin 10 := 9

attribute [local simp] zeroPort nonzeroPort

def zeroMachine : Machine 9 := fun q symbol =>
  match q.val with
  | 0 => if symbol then some (nonzeroPort,.write true) else some (1,.move .right)
  | 1 => some (2,.move .right)
  | 2 => some (3,.move .right)
  | 3 => some ((if symbol then 7 else 4),.move .left)
  | 4 => some (5,.move .left)
  | 5 => some (zeroPort,.move .left)
  | 7 => some (8,.move .left)
  | 8 => some (nonzeroPort,.move .left)
  | _ => none

def state (q : Fin 10) (left right : List Bool) : MachineState 9 := ⟨q,Tape.mk₂ left right⟩

def firstTrueTrace (archive right : List Bool) : List (MachineState 9) :=
  [state 0 archive (true::right),state nonzeroPort archive (true::right)]

theorem firstTrue_runsFrom (archive right : List Bool) :
    PSTRTMSeq005.RunsFrom zeroMachine (state 0 archive (true::right))
      (firstTrueTrace archive right) (state nonzeroPort archive (true::right)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [firstTrueTrace,List.isChain_cons_cons,TM0.step,zeroMachine,state,Tape.mk₂]
  · simp [TM0.step,zeroMachine,state]

theorem firstTrueTrace_length (archive right : List Bool) : (firstTrueTrace archive right).length = 2 := rfl

def singleFalseTrace (archive suffix : List Bool) : List (MachineState 9) :=
  [state 0 archive (false::true::false::false::suffix),
   state 1 (false::archive) (true::false::false::suffix),
   state 2 (true::false::archive) (false::false::suffix),
   state 3 (false::true::false::archive) (false::suffix),
   state 4 (true::false::archive) (false::false::suffix),
   state 5 (false::archive) (true::false::false::suffix),
   state zeroPort archive (false::true::false::false::suffix)]

/-- Reads the real second OWN false, then takes three actual LEFT steps.
The suffix is arbitrary and never inspected. -/
theorem singleFalse_runsFrom (archive suffix : List Bool) :
    PSTRTMSeq005.RunsFrom zeroMachine (state 0 archive (false::true::false::false::suffix))
      (singleFalseTrace archive suffix) (state zeroPort archive (false::true::false::false::suffix)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [singleFalseTrace,List.isChain_cons_cons,TM0.step,zeroMachine,state,Tape.mk₂]
  · simp [TM0.step,zeroMachine,state]

theorem singleFalseTrace_length (archive suffix : List Bool) : (singleFalseTrace archive suffix).length = 7 := rfl

def laterFalseTrace (archive : List Bool) (second : Bool) (later suffix : List Bool) : List (MachineState 9) :=
  let tail := PSTRTMIncrement009.blocks later++false::false::suffix
  [state 0 archive (false::true::second::true::tail),
   state 1 (false::archive) (true::second::true::tail),
   state 2 (true::false::archive) (second::true::tail),
   state 3 (second::true::false::archive) (true::tail),
   state 7 (true::false::archive) (second::true::tail),
   state 8 (false::archive) (true::second::true::tail),
   state nonzeroPort archive (false::true::second::true::tail)]

/-- A physical long-field branch. It claims its actual port, not a value
theorem for arbitrary leading-zero digit lists. -/
theorem laterFalse_runsFrom (archive : List Bool) (second : Bool) (later suffix : List Bool) :
    PSTRTMSeq005.RunsFrom zeroMachine
      (state 0 archive (false::true::second::true::(PSTRTMIncrement009.blocks later++false::false::suffix)))
      (laterFalseTrace archive second later suffix)
      (state nonzeroPort archive (false::true::second::true::(PSTRTMIncrement009.blocks later++false::false::suffix))) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [laterFalseTrace,List.isChain_cons_cons,TM0.step,zeroMachine,state,Tape.mk₂]
  · simp [TM0.step,zeroMachine,state]

theorem laterFalseTrace_length (archive : List Bool) (second : Bool) (later suffix : List Bool) :
    (laterFalseTrace archive second later suffix).length = 7 := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFlagZero028
