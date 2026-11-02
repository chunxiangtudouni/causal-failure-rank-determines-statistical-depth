module
public import PaperProofs.Common.PSTR_TM_MulProjectPrepare_106

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulProjectRun107
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulProjectCode100
local notation "Triple" => PSTRTMMulPassCode079.Triple
local notation "cols" => PSTRTMMulPassCode079.columns

def firstMachine : Machine 169 := PSTRTMSeq005.seqMachine prepareMachine PSTRTMCompactCode046.compactMachine
/-- ONE fixed225-label actual resident C projection:115-label real8-cell
preparation and TWO real55-label compact calls, with all original moves,
copying, marker clearing, head transfers and whole rewinds included. High
zero trimming remains owed before claiming canonical original Nat output. -/
def projectMachine : Machine 224 := PSTRTMSeq005.seqMachine firstMachine PSTRTMCompactCode046.compactMachine
def compactFinal (digits : List Bool) : MachineState 54 := PSTRTMCompactCode046.state 54 [false] (PSTRTMIncrement009.blocks digits++[false,false])
def firstTrace (triples : List Triple) : List (MachineState 169) :=
  (PSTRTMMulProjectPrepare106.prepareTrace triples).map (PSTRTMSeq005.leftCfg (b:=54)) ++
    (PSTRTMCompactRun051.compactTrace (PSTRTMCompactUnit048.paddedDigits (cBits triples))).map (PSTRTMSeq005.rightCfg (a:=114))
def firstFinal (triples : List Triple) : MachineState 169 :=
  PSTRTMSeq005.rightCfg (a:=114) (compactFinal (PSTRTMCompactUnit048.paddedDigits (cBits triples)))
def projectTrace (triples : List Triple) : List (MachineState 224) :=
  (firstTrace triples).map (PSTRTMSeq005.leftCfg (b:=54)) ++
    (PSTRTMCompactRun051.compactTrace (cBits triples)).map (PSTRTMSeq005.rightCfg (a:=169))
def projectFinal (triples : List Triple) : MachineState 224 := PSTRTMSeq005.rightCfg (a:=169) (compactFinal (cBits triples))

theorem first_runs (triples : List Triple) :
    Runs firstMachine (cols triples) (firstTrace triples) (firstFinal triples) := by
  apply PSTRTMSeq005.seq_runs prepareMachine PSTRTMCompactCode046.compactMachine (cols triples)
    (PSTRTMMulProjectPrepare106.prepareFinal triples) (compactFinal (PSTRTMCompactUnit048.paddedDigits (cBits triples)))
    (PSTRTMMulProjectPrepare106.prepareTrace triples)
    (PSTRTMCompactRun051.compactTrace (PSTRTMCompactUnit048.paddedDigits (cBits triples)))
    (PSTRTMMulProjectPrepare106.prepare_runs triples)
  have hr := PSTRTMCompactRun051.compact_runs (PSTRTMCompactUnit048.paddedDigits (cBits triples))
  rw [PSTRTMMulProjectPrepare106.prepare_final_tape]
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

theorem first_final_tape (triples : List Triple) :
    (firstFinal triples).Tape=Turing.Tape.mk₁ (PSTRTMBinaryAdd024.resultColumns (cBits triples)) := by
  have ht := PSTRTMCompactRun051.compact_final_tape (PSTRTMCompactUnit048.paddedDigits (cBits triples))
  change (firstFinal triples).Tape=Turing.Tape.mk₁ (PSTRTMIncrement009.blocks (PSTRTMCompactUnit048.paddedDigits (cBits triples))) at ht
  rw [first_compact_format] at ht
  exact ht

theorem project_runs (triples : List Triple) :
    Runs projectMachine (cols triples) (projectTrace triples) (projectFinal triples) := by
  apply PSTRTMSeq005.seq_runs firstMachine PSTRTMCompactCode046.compactMachine (cols triples)
    (firstFinal triples) (compactFinal (cBits triples)) (firstTrace triples)
    (PSTRTMCompactRun051.compactTrace (cBits triples)) (first_runs triples)
  have hr := PSTRTMCompactRun051.compact_runs (cBits triples)
  rw [first_final_tape]
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

theorem project_final_tape (triples : List Triple) :
    (projectFinal triples).Tape=Turing.Tape.mk₁ (PSTRTMIncrement009.blocks (cBits triples)) :=
  PSTRTMCompactRun051.compact_final_tape (cBits triples)

theorem cBits_length (triples : List Triple) : (cBits triples).length=triples.length := by
  simp only [cBits,List.length_map]

theorem project_length_le (triples : List Triple) :
    (projectTrace triples).length ≤ 512*(triples.length+1)^2 := by
  have hp := PSTRTMMulProjectPrepare106.prepare_length_le triples
  simp only [projectTrace,firstTrace,List.length_append,List.length_map,PSTRTMCompactRun051.compact_length,
    PSTRTMCompactUnit048.paddedDigits_length,cBits_length]
  nlinarith

theorem project_visitedSpace_le (triples : List Triple) :
    visitedSpace projectMachine (cols triples).length (projectTrace triples) ≤ 2048*(triples.length+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le projectMachine (cols triples).length (projectTrace triples)
  have ht := project_length_le triples
  rw [PSTRTMMulAppendTrace087.columns_length] at hs ⊢
  nlinarith

/-- EXACT complete C-only flagged output. The two compact calls both use
the predecessor's ENTIRE Tape theorem via real seq005 transfers. No freely
reset head, source erase, or marker disposal is assumed. -/
theorem project_computes (triples : List Triple) :
    computes projectMachine (cols triples) (PSTRTMIncrement009.blocks (cBits triples))
      (512*(triples.length+1)^2) (2048*(triples.length+1)^2) := by
  refine ⟨projectTrace triples,projectFinal triples,project_runs triples,?_,project_length_le triples,project_visitedSpace_le triples⟩
  rw [project_final_tape]
  simp [Turing.Tape.mk₁,Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulProjectRun107
