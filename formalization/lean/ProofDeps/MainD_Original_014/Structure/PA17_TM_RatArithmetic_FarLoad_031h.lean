module
public import Structure.PA17_TM_RatArithmetic_FarLoad_031g

/-! Actual source navigation and destination first-bit restoration inside
fixed finite memory rows. The incoming memory is an actual entry label;
no Rat value, saved answer bit, width, or gap is a machine parameter. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)

def navigatedCopyMachine (navigation : Machine 16) (route : FarRoute) : Machine 433 :=
  PSTRTMSeq005.seqMachine navigation (copyMachine route)

def restoreRowMachine (navigation : Machine 16) (route : FarRoute) (which memory : Nat) : Machine 435 :=
  PSTRTMSeq005.seqMachine (navigatedCopyMachine navigation route)
    (PA17TMRatArithmeticAllocate013.setMarkerMachine (memory.testBit which))

def copyFee (digits : List Bool) (cost gap : Nat) : Nat :=
  4*digits.length^2+(2*cost+2*gap+41)*digits.length+3*cost+3*gap+29

theorem restoreRow_bounded (navigation : Machine 16) (route : FarRoute)
    (context : List Bool) (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost) (which memory : Nat)
    (input : Tape Bool) (navigationPort : Fin 17) (navigationFee : Nat)
    (archive tail : List Bool) (gap : Nat)
    (nav : BoundedRun navigation input navigationPort
      (Tape.mk₂ (false::archive) (fieldWord context (false::tail) (workSuffix gap []))) navigationFee) :
    BoundedRun (restoreRowMachine navigation route which memory) input 435
      (Tape.mk₂ (destinationLeft gap (finish (false::archive) (false::tail)))
        (PA17TMRatArithmeticCopy006.workspace (memory.testBit which::tail)))
      (navigationFee+copyFee (false::tail) cost gap+2) := by
  have hc := copy_bounded route context finish cost routes archive (false::tail) gap
  have hs : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine (memory.testBit which))
      (Tape.mk₂ (destinationLeft gap (finish (false::archive) (false::tail)))
        (PA17TMRatArithmeticCopy006.workspace (false::tail))) 1
      (Tape.mk₂ (destinationLeft gap (finish (false::archive) (false::tail)))
        (PA17TMRatArithmeticCopy006.workspace (memory.testBit which::tail))) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false (memory.testBit which)
        (destinationLeft gap (finish (false::archive) (false::tail)))
        (true::(PSTRTMIncrement009.blocks tail++[false,false])),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom false (memory.testBit which)
        (destinationLeft gap (finish (false::archive) (false::tail)))
        (true::(PSTRTMIncrement009.blocks tail++[false,false])),by rfl⟩
  exact (nav.seq hc).seq hs

def restoreRows (p which : Nat) (navigation : Machine 16) (route : FarRoute)
    (memory : Fin (p+1)) : Machine 435 := restoreRowMachine navigation route which memory.val

def restorePorts (p : Nat) : Fin (p+1) → Fin 436 → Option (Fin (p+1) × Fin 436) := fun _ _ => none

/-- p and which are fixed finite compile-time choices, like the field
route and its navigation. Runtime row selection is the actual label. -/
def restoreMachine (p which : Nat) (navigation : Machine 16) (route : FarRoute) :
    Machine (totalStates p 435) := blockMachine (restoreRows p which navigation route) (restorePorts p)

theorem restore_contract (p which : Nat) (navigation : Machine 16) (route : FarRoute)
    (context : List Bool) (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost) (memory : Fin (p+1))
    (input : Tape Bool) (navigationPort : Fin 17) (navigationFee : Nat)
    (archive tail : List Bool) (gap inputLength : Nat)
    (nav : BoundedRun navigation input navigationPort
      (Tape.mk₂ (false::archive) (fieldWord context (false::tail) (workSuffix gap []))) navigationFee) :
    ∃ trace, PSTRTMSeq005.RunsFrom (restoreMachine p which navigation route)
      (blockCfg memory (⟨0,input⟩ : MachineState 435)) trace
      (blockCfg memory (⟨435,Tape.mk₂ (destinationLeft gap (finish (false::archive) (false::tail)))
        (PA17TMRatArithmeticCopy006.workspace (memory.val.testBit which::tail))⟩ : MachineState 435)) ∧
      trace.length≤navigationFee+copyFee (false::tail) cost gap+2 ∧
      ∀ k, visitedSpace (restoreMachine p which navigation route) inputLength (trace.take k) ≤
        inputLength+2*(navigationFee+copyFee (false::tail) cost gap+2)+1 := by
  obtain ⟨trace,hr,hl⟩ := restoreRow_bounded navigation route context finish cost routes which memory.val
    input navigationPort navigationFee archive tail gap nav
  have hb := block_runsFrom (restoreRows p which navigation route) (restorePorts p) memory _ _ trace hr rfl
  refine ⟨trace.map (blockCfg memory),hb,?_,?_⟩
  · simpa only [List.length_map] using hl
  · intro k
    have hs := PSTRTMTrace002.visitedSpace_le (restoreMachine p which navigation route) inputLength
      ((trace.map (blockCfg memory)).take k)
    have hk : ((trace.map (blockCfg memory)).take k).length≤trace.length := by
      simp only [List.length_take,List.length_map]
      omega
    omega

theorem restore_entry_label (p : Nat) (memory : Fin (p+1)) (tape : Tape Bool) :
    (blockCfg memory (⟨0,tape⟩ : MachineState 435)).q.val=436*memory.val := by
  simp only [blockCfg,label,Fin.val_zero,Nat.add_zero,Nat.mul_comm]

theorem restore_final_memory (p : Nat) (memory : Fin (p+1)) (tape : Tape Bool) :
    phaseOf (p:=p) (s:=435) (blockCfg memory (⟨435,tape⟩ : MachineState 435)).q=memory :=
  phaseOf_label _ _

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
