module
public import Common.PSTR_TM_ThresholdCountdownRun_166

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthZeroCode167
open PaperProofs.Common.Native.RationalControllerComputation

/-- Read the real fixed-width countdown field without changing ANY
data. The true flag distinguishes a zero bit from actual00 end; the
control remembers only whether any digit ONE has occurred. Two distinct
halt labels are consumed by the later threshold-loop branch. -/
def zeroMachine : Machine 7 := fun q symbol =>
  match q.val with
  | 0 => some (if symbol then 3 else 2,.move .right)
  | 1 => some (if symbol then 5 else 4,.move .right)
  | 2 => some (if symbol then 0 else 6,if symbol then .move .right else .move .left)
  | 3 => some (if symbol then 1 else 6,if symbol then .move .right else .move .left)
  | 4 => some (if symbol then 1 else 7,if symbol then .move .right else .move .left)
  | 5 => some (if symbol then 1 else 7,if symbol then .move .right else .move .left)
  | _ => none

def state (q : Fin 8) (left right : List Bool) : MachineState 7 := ⟨q,Turing.Tape.mk₂ left right⟩
def modeLabel (hasOne : Bool) : Fin 8 := if hasOne then 1 else 0
def savedLabel (hasOne bit : Bool) : Fin 8 :=
  ⟨2+2*(if hasOne then 1 else 0)+(if bit then 1 else 0),by cases hasOne <;> cases bit <;> decide⟩
def haltLabel (hasOne : Bool) : Fin 8 := if hasOne then 7 else 6

def unitTrace (hasOne bit : Bool) (left right : List Bool) : List (MachineState 7) :=
  [state (modeLabel hasOne) left (bit::true::right),
    state (savedLabel hasOne bit) (bit::left) (true::right),
    state (modeLabel (hasOne||bit)) (true::bit::left) right]

theorem unit_chain (hasOne bit : Bool) (left right : List Bool) :
    (unitTrace hasOne bit left right).IsChain
      (fun before after => Turing.TM0.step zeroMachine before=some after) := by
  cases hasOne <;> cases bit <;> simp [unitTrace,List.isChain_cons_cons,state,modeLabel,savedLabel,
    Turing.TM0.step,zeroMachine,Turing.Tape.mk₂]

/-- The two REAL false cells are essential. No assumption about the
first bit of the following suffix is made, and no01 is mistaken for EOF. -/
def eofTrace (hasOne : Bool) (left suffix : List Bool) : List (MachineState 7) :=
  [state (modeLabel hasOne) left (false::false::suffix),
    state (savedLabel hasOne false) (false::left) (false::suffix),
    state (haltLabel hasOne) left (false::false::suffix)]

theorem eof_chain (hasOne : Bool) (left suffix : List Bool) :
    (eofTrace hasOne left suffix).IsChain
      (fun before after => Turing.TM0.step zeroMachine before=some after) := by
  cases hasOne <;> simp [eofTrace,List.isChain_cons_cons,state,modeLabel,savedLabel,haltLabel,
    Turing.TM0.step,zeroMachine,Turing.Tape.mk₂]

theorem zero_halt (hasOne : Bool) (left right : List Bool) :
    Turing.TM0.step zeroMachine (state (haltLabel hasOne) left right)=none := by
  cases hasOne <;> simp [Turing.TM0.step,zeroMachine,state,haltLabel]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthZeroCode167
