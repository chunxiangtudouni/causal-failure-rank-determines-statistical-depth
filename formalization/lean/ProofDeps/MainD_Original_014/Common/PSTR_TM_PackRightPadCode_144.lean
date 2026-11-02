module
public import Common.PSTR_TM_PackFinishFrame_143

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackRightPadCode144
open PaperProofs.Common.Native.RationalControllerComputation

/-- Threshold's A-empty packing repair. In contrast to the standalone
old034 code, it moves marker+B RIGHT into real blanks and leaves the
arbitrary left archive untouched. The41-label ABI fits the existing pad
label range; correctness of replacing that range is a separate obligation. -/
def padMachine : Machine 40 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (2,.move .right)
  | 2 => some (3,.move .right)
  | 3 => some (if symbol then 2 else 4,if symbol then .move .right else .move .left)
  | 4 => some (5,.move .left)
  | 5 => some (if symbol then 6 else 24,.move .left)
  | 6 => some (if symbol then 16 else 8,.move .right)
  | 8 => some (9,.move .right)
  | 9 => some (10,.write false)
  | 10 => some (11,.move .right)
  | 11 => some (12,.write true)
  | 12 => some (13,.move .left)
  | 13 => some (14,.move .left)
  | 14 => some (4,.move .left)
  | 16 => some (17,.move .right)
  | 17 => some (18,.write true)
  | 18 => some (19,.move .right)
  | 19 => some (20,.write true)
  | 20 => some (21,.move .left)
  | 21 => some (22,.move .left)
  | 22 => some (4,.move .left)
  | 24 => some (25,.write false)
  | 25 => some (26,.move .right)
  | 26 => some (27,.write false)
  | 27 => some (28,.move .right)
  | 28 => some (29,.write true)
  | 29 => some (30,.move .right)
  | 30 => some (31,.write false)
  | 31 => some (32,.move .left)
  | 32 => some (33,.move .left)
  | 33 => some (40,.move .left)
  | _ => none

def state (q : Fin 41) (left right : List Bool) : MachineState 40 := ⟨q,Turing.Tape.mk₂ left right⟩

def phase (bit : Bool) (offset : Fin 7) : Fin 41 :=
  ⟨(if bit then 16 else 8)+offset.val,by split <;> have h := offset.isLt <;> omega⟩

/-- One actual pair is copied two cells right. The old source pair becomes
the next pair of holes; its Boolean is retained only in finite control. -/
def unitTrace (bit first second : Bool) (left tail : List Bool) : List (MachineState 40) :=
  [state 4 (true::bit::left) (first::second::tail),
    state 5 (bit::left) (true::first::second::tail),
    state 6 left (bit::true::first::second::tail),
    state (phase bit 0) (bit::left) (true::first::second::tail),
    state (phase bit 1) (true::bit::left) (first::second::tail),
    state (phase bit 2) (true::bit::left) (bit::second::tail),
    state (phase bit 3) (bit::true::bit::left) (second::tail),
    state (phase bit 4) (bit::true::bit::left) (true::tail),
    state (phase bit 5) (true::bit::left) (bit::true::tail),
    state (phase bit 6) (bit::left) (true::bit::true::tail),
    state 4 left (bit::true::bit::true::tail)]

theorem unit_head (bit first second : Bool) (left tail : List Bool) :
    (unitTrace bit first second left tail).head?=some (state 4 (true::bit::left) (first::second::tail)) := rfl

theorem unit_last (bit first second : Bool) (left tail : List Bool) :
    (unitTrace bit first second left tail).getLast?=some (state 4 left (bit::true::bit::true::tail)) := rfl

theorem unit_chain (bit first second : Bool) (left tail : List Bool) :
    (unitTrace bit first second left tail).IsChain (fun before after => Turing.TM0.step padMachine before=some after) := by
  cases bit <;> simp [unitTrace,List.isChain_cons_cons,Turing.TM0.step,padMachine,phase,state,Turing.Tape.mk₂]

def finishTrace (first second : Bool) (left tail : List Bool) : List (MachineState 40) :=
  [state 4 (false::true::left) (first::second::tail),
    state 5 (true::left) (false::first::second::tail),
    state 24 left (true::false::first::second::tail),
    state 25 left (false::false::first::second::tail),
    state 26 (false::left) (false::first::second::tail),
    state 27 (false::left) (false::first::second::tail),
    state 28 (false::false::left) (first::second::tail),
    state 29 (false::false::left) (true::second::tail),
    state 30 (true::false::false::left) (second::tail),
    state 31 (true::false::false::left) (false::tail),
    state 32 (false::false::left) (true::false::tail),
    state 33 (false::left) (false::true::false::tail),
    state 40 left (false::false::true::false::tail)]

theorem finish_head (first second : Bool) (left tail : List Bool) :
    (finishTrace first second left tail).head?=some
      (state 4 (false::true::left) (first::second::tail)) := rfl

theorem finish_last (first second : Bool) (left tail : List Bool) :
    (finishTrace first second left tail).getLast?=some
      (state 40 left (false::false::true::false::tail)) := rfl

theorem finish_chain (first second : Bool) (left tail : List Bool) :
    (finishTrace first second left tail).IsChain (fun before after => Turing.TM0.step padMachine before=some after) := by
  simp [finishTrace,List.isChain_cons_cons,Turing.TM0.step,padMachine,state,Turing.Tape.mk₂]

theorem pad_halt (left right : List Bool) : Turing.TM0.step padMachine (state 40 left right)=none := by
  simp [Turing.TM0.step,padMachine,state]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackRightPadCode144
