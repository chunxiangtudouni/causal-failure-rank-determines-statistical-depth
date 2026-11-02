module
public import Structure.PA17_TM_RatArithmetic_OutputFinish_044a

/-! ONE fixed finite machine installs both sign-carry entries. Pair rows
are identical actual017 programs; their real HALT transitions select the
existing020 positive0/negative11 entry of one common physical tail. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOutputFinish044

open Turing
open PA17TMDivisionCompose006
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticFinalClean039

theorem pair_fits (j : Nat) : 47≤tailCap j := by
  have hc := finalCap_eq j
  dsimp [tailCap]
  omega

def entryPhase (negative : Bool) : Fin 3 := if negative then 1 else 0

def finishFamily (j : Nat) (phase : Fin 3) : Machine (tailCap j) :=
  if phase.val<2 then padMachine (pair_fits j) PA17TMRatArithmeticPairEncode017.markedMachine
  else tailMachine j

def finishPorts (j : Nat) (phase : Fin 3) (_localLabel : Fin (tailCap j+1)) :
    Option (Fin 3 × Fin (tailCap j+1)) :=
  if phase.val=0 then some (2,tailEntry j false)
  else if phase.val=1 then some (2,tailEntry j true) else none

def outputCap (j : Nat) : Nat := totalStates 2 (tailCap j)
attribute [local implicit_reducible] outputCap totalStates

/-- The sole code parameter is j. Both sign entries are present in this
single machine before all input/operand/sign values. A prior real controller
must enter outputEntry j negative; negative is not a new original input bit. -/
def outputFinishMachine (j : Nat) : Machine (outputCap j) := blockMachine (finishFamily j) (finishPorts j)

def outputEntry (j : Nat) (negative : Bool) : Fin (outputCap j+1) :=
  label (p:=2) (s:=tailCap j) (entryPhase negative) (padLabel (pair_fits j) (0 : Fin 48))
def outputPort (j : Nat) : Fin (outputCap j+1) := label (p:=2) (s:=tailCap j) 2 (tailPort j)

def pairLift (j : Nat) (negative : Bool) (state : MachineState 47) : MachineState (outputCap j) :=
  blockCfg (p:=2) (s:=tailCap j) (entryPhase negative) (padCfg (pair_fits j) state)
def tailLift (j : Nat) (state : MachineState (tailCap j)) : MachineState (outputCap j) :=
  blockCfg (p:=2) (s:=tailCap j) 2 state

theorem family_entry (j : Nat) (negative : Bool) :
    finishFamily j (entryPhase negative)=padMachine (pair_fits j) PA17TMRatArithmeticPairEncode017.markedMachine := by
  cases negative <;> rfl

theorem family_tail (j : Nat) : finishFamily j (2 : Fin 3)=tailMachine j := rfl

theorem ports_entry (j : Nat) (negative : Bool) (q : Fin (tailCap j+1)) :
    finishPorts j (entryPhase negative) q=some (2,tailEntry j negative) := by
  cases negative <;> rfl

def pairSize (u v : Nat) : Nat :=
  (PA17TMRatArithmeticPairEncode017.payload u).length+(PA17TMRatArithmeticPairEncode017.payload v).length+1

def outputFee (j : Nat) (first : RecordSpec) (later : List RecordSpec) (nx dxTail ny dyTail : List Bool)
    (gap u v : Nat) : Nat := 64*(pairSize u v)^2+tailFee j first later nx dxTail ny dyTail gap

/-- Pair serialization, the selected prefix entry, real LEFT return and
complete source/cache cleanup occur in ONE trace of ONE fixed machine.
The two initial ports must be selected by a genuine earlier control step. -/
theorem outputFinish_bounded (j : Nat) (negative : Bool) (first : RecordSpec) (later : List RecordSpec)
    (hj : later.length=j) (sx : Bool) (nx dxTail ny dyTail : List Bool)
    (gap : Nat) (hgap : 3≤gap) (u v : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (outputFinishMachine j)
        ⟨outputEntry j negative,pairInput gap (latestLeft sx nx dxTail ny dyTail first later) u v⟩ trace
        ⟨outputPort j,Tape.mk₁ (physicalWord negative u v)⟩ ∧
      trace.length≤outputFee j first later nx dxTail ny dyTail gap u v := by
  let cacheLeft := latestLeft sx nx dxTail ny dyTail first later
  let tp := PA17TMRatArithmeticPairEncode017.markedTrace (workArchive gap cacheLeft) u v []
  have hp := PA17TMRatArithmeticPairEncode017.marked_runsFrom (workArchive gap cacheLeft) u v []
  have hpad := pad_runsFrom (pair_fits j) PA17TMRatArithmeticPairEncode017.markedMachine
    (⟨0,pairInput gap cacheLeft u v⟩ : MachineState 47)
    ⟨47,pairOutput gap cacheLeft u v⟩ tp hp
  have hpFamily : PSTRTMSeq005.RunsFrom (finishFamily j (entryPhase negative))
      (padCfg (pair_fits j) ⟨0,pairInput gap cacheLeft u v⟩)
      (tp.map (padCfg (pair_fits j)))
      (padCfg (pair_fits j) ⟨47,pairOutput gap cacheLeft u v⟩) := by
    rw [family_entry]
    exact hpad
  obtain ⟨tt,ht,hlt⟩ := tail_bounded j negative first later hj sx nx dxTail ny dyTail gap hgap u v
  have htFamily : PSTRTMSeq005.RunsFrom (finishFamily j (2 : Fin 3))
      ⟨tailEntry j negative,pairOutput gap cacheLeft u v⟩ tt
      ⟨tailPort j,Tape.mk₁ (physicalWord negative u v)⟩ := by
    rw [family_tail]
    exact ht
  have sp := block_segment (finishFamily j) (finishPorts j) (entryPhase negative)
    (padCfg (pair_fits j) ⟨0,pairInput gap cacheLeft u v⟩)
    (padCfg (pair_fits j) ⟨47,pairOutput gap cacheLeft u v⟩) (tp.map (padCfg (pair_fits j))) hpFamily
  have st := block_segment (finishFamily j) (finishPorts j) (2 : Fin 3)
    ⟨tailEntry j negative,pairOutput gap cacheLeft u v⟩
    ⟨tailPort j,Tape.mk₁ (physicalWord negative u v)⟩ tt htFamily
  have transfer := block_transfer (finishFamily j) (finishPorts j) (entryPhase negative)
    (padCfg (pair_fits j) ⟨47,pairOutput gap cacheLeft u v⟩)
    (2,tailEntry j negative) hpFamily.2.2.2 (ports_entry j negative _)
  have joined := segment_append (outputFinishMachine j)
    (pairLift j negative ⟨0,pairInput gap cacheLeft u v⟩)
    (pairLift j negative ⟨47,pairOutput gap cacheLeft u v⟩)
    (tailLift j ⟨tailEntry j negative,pairOutput gap cacheLeft u v⟩)
    (tailLift j ⟨tailPort j,Tape.mk₁ (physicalWord negative u v)⟩)
    ((tp.map (padCfg (pair_fits j))).map (blockCfg (p:=2) (s:=tailCap j) (entryPhase negative)))
    (tt.map (blockCfg (p:=2) (s:=tailCap j) (2 : Fin 3))) sp st transfer
  have halted := block_halt (finishFamily j) (finishPorts j) (2 : Fin 3)
    ⟨tailPort j,Tape.mk₁ (physicalWord negative u v)⟩ htFamily.2.2.2 (by rfl)
  have hr := segment_runsFrom (outputFinishMachine j) _ _ _ joined halted
  refine ⟨((tp.map (padCfg (pair_fits j))).map (blockCfg (p:=2) (s:=tailCap j) (entryPhase negative))) ++
    tt.map (blockCfg (p:=2) (s:=tailCap j) (2 : Fin 3)),?_,?_⟩
  · simpa only [pairLift,tailLift,blockCfg,padCfg,outputEntry,outputPort] using hr
  · rw [List.length_append,List.length_map,List.length_map,List.length_map]
    have hlp := PA17TMRatArithmeticPairEncode017.pair_time_le true (workArchive gap cacheLeft) u v []
    change tp.length≤64*(pairSize u v)^2 at hlp
    dsimp [outputFee]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOutputFinish044
