module
public import PaperProofs.Common.PSTR_TM_TrimCode_103
public import PaperProofs.Common.PSTR_TM_PairRewind_105
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTrimRewind109
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrimCode103

def rewindLabel (q : Fin 4) : Fin 17 := ⟨11+q.val,by have hq := q.isLt; omega⟩
def liftRewind (old : MachineState 3) : MachineState 16 := ⟨rewindLabel old.q,old.Tape⟩

theorem command (q : Fin 4) (symbol : Bool) : trimMachine (rewindLabel q) symbol=
    (PSTRTMMulRewind085.rewindMachine q symbol).map (fun (next,statement) => (rewindLabel next,statement)) := by
  fin_cases q <;> cases symbol <;> rfl

theorem rewind_step (before : MachineState 3) : Turing.TM0.step trimMachine (liftRewind before)=
    (Turing.TM0.step PSTRTMMulRewind085.rewindMachine before).map liftRewind := by
  cases before with
  | mk q tape =>
    simp only [Turing.TM0.step,liftRewind,command]
    cases hc : PSTRTMMulRewind085.rewindMachine q tape.head with
    | none => simp
    | some cmd => obtain ⟨next,statement⟩ := cmd; cases statement <;> simp [liftRewind]

theorem rewind_chain (trace : List (MachineState 3))
    (old : trace.IsChain (fun x y => Turing.TM0.step PSTRTMMulRewind085.rewindMachine x=some y)) :
    (trace.map liftRewind).IsChain (fun x y => Turing.TM0.step trimMachine x=some y) := by
  apply (List.isChain_map _).mpr
  apply old.imp
  intro before after hs
  rw [rewind_step,hs]
  rfl

def rewindTrace (archive reversed tail : List Bool) : List (MachineState 16) :=
  (PSTRTMPairRewind105.fullTrace archive reversed tail).map liftRewind
theorem rewind_head (archive reversed tail : List Bool) :
    (rewindTrace archive reversed tail).head?=some (state 11 (PSTRTMRawNat010.leftBlocks reversed++false::archive) tail) := by
  simp only [rewindTrace,List.head?_map,PSTRTMPairRewind105.full_head,Option.map_some]
  rfl
theorem rewind_last (archive reversed tail : List Bool) :
    (rewindTrace archive reversed tail).getLast?=some
      (state 14 (false::archive) (PSTRTMIncrement009.blocks reversed.reverse++tail)) := by
  simp only [rewindTrace,List.getLast?_map,PSTRTMPairRewind105.full_last,Option.map_some]
  rfl
theorem rewind_length (archive reversed tail : List Bool) :
    (rewindTrace archive reversed tail).length=2*reversed.length+3 := by
  simp only [rewindTrace,List.length_map,PSTRTMPairRewind105.full_length]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTrimRewind109
