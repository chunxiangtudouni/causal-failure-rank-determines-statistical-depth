module
public import Common.PSTR_TM_PackRightPadRun_145
public import Common.PSTR_TM_PairRewind_105

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdUnitColumnsCode156
open PaperProofs.Common.Native.RationalControllerComputation

/-- Four finite modes retain the current B digit and whether the A digit
is the first ONE or a subsequent ZERO. No natural datum is in control. -/
def saved (first bit : Bool) : Nat := (if first then 0 else 2)+(if bit then 1 else 0)

theorem saved_lt (first bit : Bool) : saved first bit<4 := by cases first <;> cases bit <;> decide

def padLabel (first bit : Bool) (q : Fin 41) : Fin 214 :=
  ⟨14+41*saved first bit+q.val,by have hs := saved_lt first bit; have hq := q.isLt; omega⟩

def postLabel (first bit : Bool) (phase : Fin 8) : Fin 214 :=
  ⟨178+8*saved first bit+phase.val,by have hs := saved_lt first bit; have hp := phase.isLt; omega⟩

/-- Fixed214-label threshold successor operand loader. It inserts each
real A pair to the RIGHT using144, so the arbitrary left archive is never
consumed. The first A digit is ONE, later A digits ZERO. Source B digits
and all true flags are restored, then105 really rewinds the whole result.
The source is a flagged B word with ACTUAL blank right, not a suffix ABI. -/
def unitMachine : Machine 213 := fun q symbol =>
  if h0 : q.val<2 then
    some (⟨2+2*q.val+(if symbol then 1 else 0),by have hq := q.isLt; split <;> omega⟩,.move .right)
  else if h1 : q.val<6 then
    if symbol then some (⟨6+(q.val-2),by omega⟩,.write false)
    else some (210,.move .left)
  else if h2 : q.val<10 then
    some (⟨q.val+4,by omega⟩,.move .left)
  else if h3 : q.val<14 then
    some (⟨14+41*(q.val-10),by omega⟩,.write true)
  else if h4 : q.val<178 then
    let mode := (q.val-14)/41
    match PSTRTMPackRightPadCode144.padMachine ⟨(q.val-14)%41,Nat.mod_lt _ (by decide)⟩ symbol with
    | none => some (⟨178+8*mode,by dsimp [mode]; omega⟩,.write symbol)
    | some (next,statement) =>
      some (⟨14+41*mode+next.val,by dsimp [mode]; have hn := next.isLt; omega⟩,statement)
  else if h5 : q.val<210 then
    let mode := (q.val-178)/8
    let phase := (q.val-178)%8
    match phase with
    | 0 => some (⟨q.val+1,by omega⟩,.write (if mode<2 then true else false))
    | 1 => some (⟨q.val+1,by omega⟩,.move .right)
    | 2 => some (⟨q.val+1,by omega⟩,.write true)
    | 3 => some (⟨q.val+1,by omega⟩,.move .right)
    | 4 => some (⟨q.val+1,by omega⟩,.write (if mode%2=1 then true else false))
    | 5 => some (⟨q.val+1,by omega⟩,.move .right)
    | 6 => some (⟨q.val+1,by omega⟩,.write true)
    | _ => some (1,.move .right)
  else
    (PSTRTMMulRewind085.rewindMachine ⟨q.val-210,by have hq := q.isLt; omega⟩ symbol).map
      (fun (next,statement) => (⟨210+next.val,by have hn := next.isLt; omega⟩,statement))

def state (q : Fin 214) (left right : List Bool) : MachineState 213 := ⟨q,Turing.Tape.mk₂ left right⟩

def liftPad (first bit : Bool) (configuration : MachineState 40) : MachineState 213 :=
  ⟨padLabel first bit configuration.q,configuration.Tape⟩

def liftRewind (configuration : MachineState 3) : MachineState 213 :=
  ⟨⟨210+configuration.q.val,by have hq := configuration.q.isLt; omega⟩,configuration.Tape⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdUnitColumnsCode156
