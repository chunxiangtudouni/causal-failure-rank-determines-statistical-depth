module
public import Structure.PA17_TM_RatArithmetic_FarLoad_031e

/-! Shared finite-control loop, independent of source and destination
transport. The supplied two excursion programs are fixed before all tapes.
Context/work/fee below are specifications, never executable oracle fields. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopyLoop042
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)

variable {s : Nat}

def readerMachine (h : 8≤s) : Machine s :=
  padMachine h PA17TMRatArithmeticFarLoad031.readMarkMachine

def readerPort (h : 8≤s) (bit : Bool) : Fin (s+1) :=
  padLabel h (if bit then (8 : Fin 9) else 5)
def eofPort (h : 8≤s) : Fin (s+1) := padLabel h (3 : Fin 9)

theorem reader_data_bounded (h : 8≤s) (left : List Bool) (bit : Bool) (suffix : List Bool) :
    BoundedRun (readerMachine h) (Tape.mk₂ left (bit::true::suffix)) (readerPort h bit)
      (Tape.mk₂ (false::bit::left) suffix) 5 := by
  have hr := pad_runsFrom h PA17TMRatArithmeticFarLoad031.readMarkMachine _ _ _
    (PA17TMRatArithmeticFarLoad031.readMark_runsFrom left bit suffix)
  refine ⟨(PA17TMRatArithmeticFarLoad031.readMarkTrace left bit suffix).map (padCfg h),?_,?_⟩
  · cases bit <;> exact hr
  · rw [List.length_map,PA17TMRatArithmeticFarLoad031.readMarkTrace_length]

theorem reader_eof_bounded (h : 8≤s) (left suffix : List Bool) :
    BoundedRun (readerMachine h) (Tape.mk₂ left (false::false::suffix)) (eofPort h)
      (Tape.mk₂ (false::left) (false::suffix)) 3 := by
  have hr := pad_runsFrom h PA17TMRatArithmeticFarLoad031.readMarkMachine _ _ _
    (PA17TMRatArithmeticFarLoad031.eof_runsFrom left suffix)
  exact ⟨(PA17TMRatArithmeticFarLoad031.eofTrace left suffix).map (padCfg h),hr,
    by rw [List.length_map,PA17TMRatArithmeticFarLoad031.eofTrace_length]⟩

def rows (h : 8≤s) (excursions : Bool → Machine s) (phase : Fin 3) : Machine s :=
  if phase.val=0 then readerMachine h else excursions (phase.val==2)

def ports (last : Fin (s+1)) (phase : Fin 3) (localLabel : Fin (s+1)) :
    Option (Fin 3 × Fin (s+1)) :=
  if phase.val=0 then
    if localLabel.val=5 then some (1,0)
    else if localLabel.val=8 then some (2,0) else none
  else if localLabel=last then some (0,0) else none

/-- Exactly three compiled rows. Neither lists, widths, work representation
nor fees are arguments of this executable machine. -/
def loopMachine (h : 8≤s) (excursions : Bool → Machine s) (last : Fin (s+1)) :
    Machine (totalStates 2 s) := blockMachine (rows h excursions) (ports last)

def haltLabel (h : 8≤s) : Fin (totalStates 2 s+1) := label (0 : Fin 3) (eofPort h)

theorem haltLabel_value (h : 8≤s) : (haltLabel h).val=3 := by
  simp only [haltLabel,label,Fin.val_zero,Nat.zero_mul,Nat.zero_add,eofPort,padLabel]
  decide

theorem block_eof (h : 8≤s) (tape : Tape Bool) :
    blockCfg (p:=2) (s:=s) 0 (⟨eofPort h,tape⟩ : MachineState s)=
      (⟨haltLabel h,tape⟩ : MachineState (totalStates 2 s)) := rfl

def sourceWord (context : List Bool) (work : List Bool → List Bool) (digits copied : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks digits++false::(context++work copied)

/-- An actual excursion must restore the cleared source flag, advance no
further than NEXT DATA, and produce the specified entire work tape. This
conditional kernel does not assert a new source/destination implementation. -/
def ExcursionCorrect (excursions : Bool → Machine s) (last : Fin (s+1))
    (context : List Bool) (work : List Bool → List Bool) (fee : List Bool → List Bool → Nat) : Prop :=
  ∀ left later copied bit, (copied++[bit]).headD false=false →
    BoundedRun (excursions bit)
      (Tape.mk₂ (false::bit::left) (sourceWord context work later copied)) last
      (Tape.mk₂ (true::bit::left) (sourceWord context work later (copied++[bit]))) (fee later copied)

def loopFee (fee : List Bool → List Bool → Nat) : List Bool → List Bool → Nat
  | _, [] => 3
  | copied, bit::later => 5+fee later copied+loopFee fee (copied++[bit]) later

theorem prefix_false (copied : List Bool) (bit : Bool) (later : List Bool)
    (h : (copied++bit::later).headD false=false) : (copied++[bit]).headD false=false := by
  cases copied with
  | nil => exact h
  | cons head tail => exact h

/-- The complete SOURCE suffix contains a real FALSE cell after END.
head? prevents an empty descriptor being accepted as a supplied OWN cell. -/
theorem suffix_false (word : List Bool) (h : word.head?=some false) : word=false::word.tail := by
  cases word with
  | nil => simp at h
  | cons bit later =>
    have hb : bit=false := Option.some.inj h
    subst bit
    rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopyLoop042
