module
public import Common.PSTR_TM_ThresholdSource_125

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyCode126
open PaperProofs.Common.Native.RationalControllerComputation

/-- A fixed131-label copier for the actual retained original threshold
layout: NUM,0010,DEN,00,DEPTH. The new copy is appended behind REAL00/10.
The old NUM/DEN/DEPTH are preserved. A source flag is temporarily cleared,
with its data bit held in finite control; actual shuttles restore that flag.
The code has no source length, result, bound, padding or fuel argument.
Correctness and cost require the subsequent concrete trace proofs. -/
def copyMachine : Machine 130 := fun q symbol =>
  if q.val<40 then
    match q.val with
    | 0 => some (1,.move .right)
    | 1 => some (if symbol then 0 else 2,.move .right)
    | 2 => some (3,.move .right)
    | 3 => some (4,.move .right)
    | 4 => some (5,.move .right)
    | 5 => some (if symbol then 4 else 6,.move .right)
    | 6 => some (7,.move .right)
    | 7 => some (if symbol then 6 else 8,.move .right)
    | 8 => some (9,.write true)
    | 9 => some (10,.move .right)
    | 10 => some (11,.write false)
    | 11 => some (12,.move .right)
    | 12 => some (13,.move .left)
    | 13 => some (14,.move .left)
    | 14 => some (15,.move .left)
    | 15 => some (16,.move .left)
    | 16 => some (17,.move .left)
    | 17 => some (if symbol then 18 else 20,if symbol then .move .left else .move .right)
    | 18 => some (17,.move .left)
    | 20 => some (21,.move .left)
    | 21 => some (22,.move .left)
    | 22 => some (23,.move .left)
    | 23 => some (if symbol then 24 else 26,if symbol then .move .left else .move .right)
    | 24 => some (23,.move .left)
    | 26 => some (27,.move .left)
    | 27 => some (28,.move .left)
    | 28 => some (29,.move .left)
    | 29 => some (30,.move .left)
    | 30 => some (31,.move .left)
    | 31 => some (if symbol then 32 else 34,if symbol then .move .left else .move .right)
    | 32 => some (31,.move .left)
    | 34 => some (if symbol then 36 else 35,.move .right)
    | 35 => some (if symbol then 40 else 120,if symbol then .write false else .move .left)
    | 36 => some (if symbol then 80 else 120,if symbol then .write false else .move .left)
    | _ => none
  else if q.val<120 then
    let bit : Bool := decide (80 ≤ q.val)
    let base := if bit then 80 else 40
    let label (next : Fin 40) : Fin 131 := ⟨base+next.val,by
      dsimp [base]; split <;> have hn := next.isLt <;> omega⟩
    match (q.val-base) with
    | 0 => some (label 1,.move .right)
    | 1 => some (label 2,.move .right)
    | 2 => some (label (if symbol then 1 else 3),.move .right)
    | 3 => some (label 4,.move .right)
    | 4 => some (label 5,.move .right)
    | 5 => some (label 6,.move .right)
    | 6 => some (label (if symbol then 5 else 7),.move .right)
    | 7 => some (label 8,.move .right)
    | 8 => some (label (if symbol then 7 else 9),.move .right)
    | 9 => some (label 10,.move .right)
    | 10 => some (label 11,.move .right)
    | 11 => some (label 12,.move .right)
    | 12 => some (label (if symbol then 11 else 13),if symbol then .move .right else .move .left)
    | 13 => some (label 14,.write bit)
    | 14 => some (label 15,.move .right)
    | 15 => some (label 16,.write true)
    | 16 => some (label 17,.move .right)
    | 17 => some (label 18,.move .left)
    | 18 => some (label (if symbol then 19 else 20),if symbol then .move .left else .move .right)
    | 19 => some (label 18,.move .left)
    | 20 => some (label 21,.move .left)
    | 21 => some (label 22,.move .left)
    | 22 => some (label 23,.move .left)
    | 23 => some (label 24,.move .left)
    | 24 => some (label 25,.move .left)
    | 25 => some (label (if symbol then 26 else 27),if symbol then .move .left else .move .right)
    | 26 => some (label 25,.move .left)
    | 27 => some (label 28,.move .left)
    | 28 => some (label 29,.move .left)
    | 29 => some (label 30,.move .left)
    | 30 => some (label (if symbol then 31 else 32),if symbol then .move .left else .move .right)
    | 31 => some (label 30,.move .left)
    | 32 => some (label 33,.move .left)
    | 33 => some (label 34,.move .left)
    | 34 => some (label 35,.move .left)
    | 35 => some (label 36,.move .left)
    | 36 => some (label 37,.move .left)
    | 37 => some (label (if symbol then 38 else 39),if symbol then .move .left else .write true)
    | 38 => some (label 37,.move .left)
    | 39 => some (34,.move .right)
    | _ => none
  else
    match q.val with
    | 120 => some (121,.move .right)
    | 121 => some (122,.move .right)
    | 122 => some (123,.move .right)
    | 123 => some (124,.move .right)
    | 124 => some (125,.move .right)
    | 125 => some (if symbol then 124 else 126,.move .right)
    | 126 => some (127,.move .right)
    | 127 => some (if symbol then 126 else 128,.move .right)
    | 128 => some (129,.move .right)
    | 129 => some (130,.move .right)
    | _ => none

def state (q : Fin 131) (left right : List Bool) : MachineState 130 := ⟨q,Turing.Tape.mk₂ left right⟩

theorem copy_halt (left right : List Bool) : Turing.TM0.step copyMachine (state 130 left right)=none := by
  simp [Turing.TM0.step,copyMachine,state]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyCode126
