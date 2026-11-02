module
public import Common.PSTR_TM_TwoRawOperands_029

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdStrip113
open PaperProofs.Common.Native.RationalControllerComputation

def headerBits : List Bool := [true,true,false,false,true,true,false]
def rawSuffix (risk : Rat) (depth : Nat) : List Bool :=
  encodeNat risk.num.natAbs++encodeNat risk.den++false::(encodeNat depth++[true])

/-- The ORIGINAL two-Datum threshold input has this fixed seven-bit
header for positive risk. No numeric field, width or answer is supplied. -/
theorem original_input (risk : Rat) (depth : Nat) (hr : 0<risk) :
    encode [.rational risk,.natural depth]=headerBits++rawSuffix risk depth := by
  have hs : ¬risk<0 := not_lt.mpr (le_of_lt hr)
  have ht : encodeNat 2=[true,true,false,false,true] := rfl
  simp [encode,encodeDatum,headerBits,rawSuffix,hs,ht,List.append_assoc]

/-- ONE fixed15-label machine. Each original header cell is REALLY
written false, then the head REALLY moves right; HALT14 is at the raw
numerator. The cleared left tape is blank, not a free cursor reset. -/
def stripMachine : Machine 14 := fun q _ =>
  if h : q.val<14 then some (⟨q.val+1,by omega⟩,if q.val%2=0 then .write false else .move .right)
  else none
def state (q : Fin 15) (right : List Bool) : MachineState 14 := ⟨q,Turing.Tape.mk₂ [] right⟩
def stripTrace (tail : List Bool) : List (MachineState 14) :=
  [state 0 (true::true::false::false::true::true::false::tail),
    state 1 (false::true::false::false::true::true::false::tail),
    state 2 (true::false::false::true::true::false::tail),
    state 3 (false::false::false::true::true::false::tail),
    state 4 (false::false::true::true::false::tail),
    state 5 (false::false::true::true::false::tail),
    state 6 (false::true::true::false::tail),state 7 (false::true::true::false::tail),
    state 8 (true::true::false::tail),state 9 (false::true::false::tail),
    state 10 (true::false::tail),state 11 (false::false::tail),
    state 12 (false::tail),state 13 (false::tail),state 14 tail]

theorem strip_head (tail : List Bool) : (stripTrace tail).head?=some (state 0 (headerBits++tail)) := rfl
theorem strip_last (tail : List Bool) : (stripTrace tail).getLast?=some (state 14 tail) := rfl
theorem strip_length (tail : List Bool) : (stripTrace tail).length=15 := rfl
theorem strip_chain (tail : List Bool) :
    (stripTrace tail).IsChain (fun before after => Turing.TM0.step stripMachine before=some after) := by
  simp [stripTrace,List.isChain_cons_cons,Turing.TM0.step,stripMachine,state,Turing.Tape.mk₂,
    PSTRTMRawNat010.blank_single_false]
theorem strip_halt (tail : List Bool) : Turing.TM0.step stripMachine (state 14 tail)=none := by
  simp [Turing.TM0.step,stripMachine,state]

theorem strip_runs (tail : List Bool) : Runs stripMachine (headerBits++tail) (stripTrace tail) (state 14 tail) := by
  apply PSTRTMTrace002.runs_of_chain
  · rfl
  · exact strip_chain tail
  · exact strip_last tail
  · exact strip_halt tail

theorem strip_final_tape (tail : List Bool) : (state 14 tail).Tape=Turing.Tape.mk₁ tail := rfl

theorem threshold_strip_runs (risk : Rat) (depth : Nat) (hr : 0<risk) :
    Runs stripMachine (encode [.rational risk,.natural depth]) (stripTrace (rawSuffix risk depth))
      (state 14 (rawSuffix risk depth)) := by
  rw [original_input risk depth hr]
  exact strip_runs _

/-- Actual original threshold input headerBits consumption. This is a parser
component, not the original five-Datum thresholdOutput computation. -/
theorem threshold_strip_computes (risk : Rat) (depth : Nat) (hr : 0<risk) :
    computes stripMachine (encode [.rational risk,.natural depth]) (rawSuffix risk depth)
      15 ((encode [.rational risk,.natural depth]).length+31) := by
  refine ⟨stripTrace (rawSuffix risk depth),state 14 (rawSuffix risk depth),threshold_strip_runs risk depth hr,?_,
    (strip_length _).le,?_⟩
  · rw [strip_final_tape]
    simp [Turing.Tape.mk₁,Turing.Tape.mk₂]
  · have hs := PSTRTMTrace002.visitedSpace_le stripMachine (encode [.rational risk,.natural depth]).length
      (stripTrace (rawSuffix risk depth))
    rw [strip_length] at hs
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdStrip113
