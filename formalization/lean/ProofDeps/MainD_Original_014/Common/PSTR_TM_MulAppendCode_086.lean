module
public import Common.PSTR_TM_MulRewind_085
public import Common.PSTR_TM_RawNat_010

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulAppendCode086
open PaperProofs.Common.Native.RationalControllerComputation

def embedRewind (q : Fin 4) : Fin 18 := ⟨14+q.val,by have h := q.isLt; omega⟩
def liftRewind (old : MachineState 3) : MachineState 17 := ⟨embedRewind old.q,old.Tape⟩

/-- Fixed18-label actual high-zero allocation used before each binary
multiplication pass. Scans real flags, WRITES all6 cells on blank EOF and
really rewinds. The extra column/width is never an original input field. -/
def appendMachine : Machine 17 := fun q symbol =>
  if h : q.val<14 then
    match q.val with
    | 0 => some (1,.move .right)
    | 1 => some (if symbol then 0 else 2,if symbol then .move .right else .move .left)
    | 2 => some (3,.write false)
    | 3 => some (4,.move .right)
    | 4 => some (5,.write true)
    | 5 => some (6,.move .right)
    | 6 => some (7,.write false)
    | 7 => some (8,.move .right)
    | 8 => some (9,.write true)
    | 9 => some (10,.move .right)
    | 10 => some (11,.write false)
    | 11 => some (12,.move .right)
    | 12 => some (13,.write true)
    | 13 => some (14,.move .right)
    | _ => none
  else (PSTRTMMulRewind085.rewindMachine ⟨q.val-14,by omega⟩ symbol).map
    (fun (next,statement) => (embedRewind next,statement))

def state (q : Fin 18) (left right : List Bool) : MachineState 17 := ⟨q,Turing.Tape.mk₂ left right⟩
def paddedTriples (triples : List PSTRTMMulPassCode079.Triple) : List PSTRTMMulPassCode079.Triple := triples++[(false,false,false)]

theorem rewind_step (before : MachineState 3) :
    Turing.TM0.step appendMachine (liftRewind before)=
      (Turing.TM0.step PSTRTMMulRewind085.rewindMachine before).map liftRewind := by
  cases before with
  | mk q tape =>
    simp only [Turing.TM0.step,appendMachine,liftRewind,embedRewind,
      show ¬14+q.val<14 by omega,dite_false,Nat.add_sub_cancel_left,Fin.eta]
    cases hc : PSTRTMMulRewind085.rewindMachine q tape.head with
    | none => simp
    | some command => obtain ⟨next,statement⟩ := command; cases statement <;> simp [liftRewind,embedRewind]

theorem rewind_chain (trace : List (MachineState 3))
    (hc : trace.IsChain (fun a b => Turing.TM0.step PSTRTMMulRewind085.rewindMachine a=some b)) :
    (trace.map liftRewind).IsChain (fun a b => Turing.TM0.step appendMachine a=some b) := by
  apply (List.isChain_map _).mpr
  apply hc.imp
  intro before after hs
  rw [rewind_step,hs]
  rfl

theorem append_halt (left right : List Bool) : Turing.TM0.step appendMachine (state 17 left right)=none := by
  simp [Turing.TM0.step,appendMachine,state,PSTRTMMulRewind085.rewindMachine]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulAppendCode086
