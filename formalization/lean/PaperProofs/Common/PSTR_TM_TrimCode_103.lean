module
public import PaperProofs.Common.PSTR_TM_Canonical_020
public import PaperProofs.Common.PSTR_TM_MulRewind_085

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTrimCode103
open PaperProofs.Common.Native.RationalControllerComputation

/-- ONE fixed17-label real high-zero trimmer for flagged little-endian
binary digits. It scans actual flags to EOF, walks BACKWARDS, really erases
each high-zero FLAG, and stops on the first true DATA bit. It then physically
rewinds the remaining flagged prefix. If all digits were zero (including
empty input), it really writes ONE false-data/true-flag pair at the original
start. Correctness, canonical value and trace cost are separate obligations;
this definition alone is not an original arithmetic computation claim. -/
def trimMachine : Machine 16 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => if symbol then some (0,.move .right) else some (2,.move .left)
  | 2 => some (3,.move .left)
  | 3 => if symbol then some (4,.move .left) else some (8,.move .right)
  | 4 => some (if symbol then 10 else 5,.move .right)
  | 5 => some (6,.write false)
  | 6 => some (7,.move .left)
  | 7 => some (3,.move .left)
  | 8 => some (9,.write false)
  | 9 => some (15,.move .right)
  | 10 => some (11,.move .right)
  | 11 => some (12,.move .left)
  | 12 => if symbol then some (13,.move .left) else some (14,.move .right)
  | 13 => some (12,.move .left)
  | 15 => some (16,.write true)
  | 16 => some (14,.move .left)
  | _ => none

def state (q : Fin 17) (left right : List Bool) : MachineState 16 := ⟨q,Turing.Tape.mk₂ left right⟩

def keepReverse : List Bool → List Bool
  | [] => []
  | false::earlier => keepReverse earlier
  | true::earlier => true::earlier
def trimmed (digits : List Bool) : List Bool :=
  match keepReverse digits.reverse with
  | [] => [false]
  | first::later => (first::later).reverse

theorem trim_halt (left right : List Bool) : Turing.TM0.step trimMachine (state 14 left right)=none := by
  simp [Turing.TM0.step,trimMachine,state]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTrimCode103
