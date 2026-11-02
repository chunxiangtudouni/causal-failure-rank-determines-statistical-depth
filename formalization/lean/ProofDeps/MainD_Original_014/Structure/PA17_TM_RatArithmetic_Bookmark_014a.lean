module
public import Structure.PA17_TM_RatArithmetic_FieldNav_012b
public import Structure.PA17_TM_Division_Compose_006a

/-! Actual symbol observation and clamping. The bit is carried by a
finite HALT port selected by the read symbol, never a caller machine field. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBookmark014
open PA17TMRatArithmeticParse002

def readPort (bit : Bool) : Fin 3 := if bit then 2 else 1
def readClearMachine : Machine 2 := fun q symbol =>
  if q.val=0 then some (readPort symbol,.write false) else none
def readState (q : Fin 3) (left right : List Bool) : MachineState 2 := ⟨q,Turing.Tape.mk₂ left right⟩
def readClearTrace (archive : List Bool) (bit : Bool) (suffix : List Bool) : List (MachineState 2) :=
  [readState 0 archive (bit::suffix),readState (readPort bit) archive (false::suffix)]

theorem readClear_runsFrom (archive : List Bool) (bit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom readClearMachine (readState 0 archive (bit::suffix))
      (readClearTrace archive bit suffix) (readState (readPort bit) archive (false::suffix)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · cases bit <;> simp [readClearTrace,List.isChain_cons_cons,Turing.TM0.step,readClearMachine,readState,readPort,Turing.Tape.mk₂]
  · cases bit <;> simp [Turing.TM0.step,readClearMachine,readState,readPort]

def markerMachine : Machine 4 := fun q _ =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (2,.write true)
  | 2 => some (3,.move .left)
  | 3 => some (4,.write false)
  | _ => none
def markerState (q : Fin 5) (left right : List Bool) : MachineState 4 := ⟨q,Turing.Tape.mk₂ left right⟩
def markerTrace (archive : List Bool) : List (MachineState 4) :=
  [markerState 0 archive [true],markerState 1 (true::archive) [],
   markerState 2 (true::archive) [true],markerState 3 archive [true,true],
   markerState 4 archive [false,true]]

/-- The new TRUE is written into the actual blank immediately right of
the original footer; the original footer is then physically clamped FALSE. -/
theorem marker_runsFrom (archive : List Bool) :
    PSTRTMSeq005.RunsFrom markerMachine (markerState 0 archive [true])
      (markerTrace archive) (markerState 4 archive [false,true]) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [markerTrace,List.isChain_cons_cons,Turing.TM0.step,markerMachine,markerState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,markerMachine,markerState]

def observedFirst (digits : List Bool) : Bool := digits.headD false
def clampFirst (digits : List Bool) : List Bool := false::digits.tail

theorem digits_observedFirst (digits : List Bool) (hne : digits≠[]) :
    digits=observedFirst digits::digits.tail := by
  cases digits with
  | nil => exact False.elim (hne rfl)
  | cons bit later => rfl

theorem clampFirst_length (digits : List Bool) (hne : digits≠[]) : (clampFirst digits).length=digits.length := by
  cases digits with
  | nil => exact False.elim (hne rfl)
  | cons bit later => rfl

theorem numerator_ne_nil (x : Rat) : numeratorDigits x≠[] := by
  have h := (field_widths_positive x).1
  intro he
  simp only [he,List.length_nil] at h
  omega

theorem denominator_ne_nil (x : Rat) : denominatorDigits x≠[] := by
  have h := (field_widths_positive x).2
  intro he
  simp only [he,List.length_nil] at h
  omega

theorem blocks_observedFirst (digits : List Bool) (hne : digits≠[]) :
    PSTRTMIncrement009.blocks digits=observedFirst digits::true::PSTRTMIncrement009.blocks digits.tail := by
  cases digits with
  | nil => exact False.elim (hne rfl)
  | cons bit later => rfl

theorem blocks_clampFirst (digits : List Bool) :
    PSTRTMIncrement009.blocks (clampFirst digits)=false::true::PSTRTMIncrement009.blocks digits.tail := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBookmark014
