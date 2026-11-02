module
public import Common.PSTR_TM_Codec_001
public import Common.PSTR_TM_Seq_005

/-! The records stream has count0 or count>=4, as derived by the actual
caller. This is ONLY fixed two-bit header control, not another Nat parser.
The mature SYM025 test needs a Natural FALSE tag before the count and so
cannot directly preserve arbitrary retained LEFT at this count-head ABI.
All source HALTs below are real; a later inline/025 return must be paid. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTML01RecordGate251
open PaperProofs.Common.Native.RationalControllerComputation

def gateMachine : Machine 4 := fun q symbol =>
  match q.val with
  | 0 => if symbol then some (1,.move .right) else none
  | 1 => if symbol then some (4,.move .left) else some (2,.move .right)
  | 2 => if symbol then none else some (3,.move .right)
  | _ => none

def state (q : Fin 5) (left right : List Bool) : MachineState 4 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def zeroTrace (left suffix : List Bool) : List (MachineState 4) :=
  [state 0 left (true::false::false::true::suffix),
   state 1 (true::left) (false::false::true::suffix),
   state 2 (false::true::left) (false::true::suffix),
   state 3 (false::false::true::left) (true::suffix)]

def zeroFinal (left suffix : List Bool) : MachineState 4 :=
  state 3 (false::false::true::left) (true::suffix)

def nonzeroTrace (left tail : List Bool) : List (MachineState 4) :=
  [state 0 left (true::true::tail),
   state 1 (true::left) (true::tail),
   state 4 left (true::true::tail)]

def nonzeroFinal (left tail : List Bool) : MachineState 4 := state 4 left (true::true::tail)

theorem zero_header_runsFrom (left suffix : List Bool) :
    PSTRTMSeq005.RunsFrom gateMachine (state 0 left (true::false::false::true::suffix))
      (zeroTrace left suffix) (zeroFinal left suffix) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [zeroTrace,List.isChain_cons_cons,Turing.TM0.step,gateMachine,state,Turing.Tape.mk₂]
  · simp [zeroFinal,Turing.TM0.step,gateMachine,state]

theorem nonzero_header_runsFrom (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom gateMachine (state 0 left (true::true::tail))
      (nonzeroTrace left tail) (nonzeroFinal left tail) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [nonzeroTrace,List.isChain_cons_cons,Turing.TM0.step,gateMachine,state,Turing.Tape.mk₂]
  · simp [nonzeroFinal,Turing.TM0.step,gateMachine,state]

theorem zero_final_tape (left suffix : List Bool) : (zeroFinal left suffix).Tape =
    Turing.Tape.mk₂ (false::false::true::left) (true::suffix) := rfl

theorem zero_three_right (left suffix : List Bool) : (zeroFinal left suffix).Tape =
    (((Turing.Tape.mk₂ left (true::false::false::true::suffix)).move .right).move .right).move .right := by
  simp [zeroFinal,state,Turing.Tape.mk₂]

theorem nonzero_final_tape (left tail : List Bool) : (nonzeroFinal left tail).Tape =
    Turing.Tape.mk₂ left (true::true::tail) := rfl

theorem zero_moves (left suffix : List Bool) :
    (zeroTrace left suffix).map (displacement gateMachine) = [1,1,1,0] := by
  simp [zeroTrace,displacement,gateMachine,state,Turing.Tape.mk₂]

theorem nonzero_moves (left tail : List Bool) :
    (nonzeroTrace left tail).map (displacement gateMachine) = [1,-1,0] := by
  simp [nonzeroTrace,displacement,gateMachine,state,Turing.Tape.mk₂]

theorem zero_length (left suffix : List Bool) : (zeroTrace left suffix).length = 4 := rfl
theorem nonzero_length (left tail : List Bool) : (nonzeroTrace left tail).length = 3 := rfl

theorem zero_port_halt (left suffix : List Bool) : Turing.TM0.step gateMachine (zeroFinal left suffix) = none :=
  (zero_header_runsFrom left suffix).2.2.2

theorem nonzero_port_halt (left tail : List Bool) : Turing.TM0.step gateMachine (nonzeroFinal left tail) = none :=
  (nonzero_header_runsFrom left tail).2.2.2

theorem malformed_first_halt : gateMachine 0 false = none := rfl
theorem malformed_short_halt : gateMachine 2 true = none := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTML01RecordGate251
