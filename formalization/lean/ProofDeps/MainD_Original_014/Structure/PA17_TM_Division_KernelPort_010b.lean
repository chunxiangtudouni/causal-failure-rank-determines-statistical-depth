module
public import Structure.PA17_TM_Division_KernelPort_010a

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionKernelPort010
open PA17TMDivisionLoop002
open PSTRTMCompareCode054

private theorem compare0_port (relation : Fin 3) :
    loopPorts 0 (PA17TMDivisionCompose006.padLabel (by decide : 20 ≤ 33) (haltLabel relation)) =
      some (compare0Target relation,0) := by
  by_cases he : relation.val = 0
  · simp [loopPorts,compare0Target,PA17TMDivisionCompose006.padLabel,haltLabel,he]
  · simp [loopPorts,compare0Target,PA17TMDivisionCompose006.padLabel,haltLabel,he]

private theorem compare9_port (relation : Fin 3) :
    loopPorts 9 (PA17TMDivisionCompose006.padLabel (by decide : 20 ≤ 33) (haltLabel relation)) =
      some (compare9Target relation,0) := by
  by_cases he : relation.val = 1
  · simp [loopPorts,compare9Target,PA17TMDivisionCompose006.padLabel,haltLabel,he]
  · have hn : 18+relation.val ≠ 19 := by omega
    simp [loopPorts,compare9Target,PA17TMDivisionCompose006.padLabel,haltLabel,he,hn]

/-- The actual nondestructive initial comparison chooses the zero-mode port
only for its real equality HALT, with a charged transfer into phase1/2. -/
theorem compare0_hop (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) :
    Hop (phaseCfg 0 0 (loopTape context archive resident suffix))
      (phaseCfg (compare0Target (resultRelation 0 resident)) 0 (eofTape context archive resident suffix))
      (4*resident.length+4) := by
  have h := component_hop 0 (by decide : 20 ≤ 33) compareMachine rfl
    (state (aState 0) (frameLeft context archive) (PSTRTMBinaryAdd024.operandColumns resident ++ false::false::suffix))
    (state (haltLabel (resultRelation 0 resident)) (leftColumns resident.reverse ++ frameLeft context archive) (false::false::suffix))
    (PSTRTMCompareTrace055.compareTrace 0 (frameLeft context archive) [] resident suffix)
    (PSTRTMCompareTrace055.compare_runsFrom 0 (frameLeft context archive) resident suffix)
    (compare0Target (resultRelation 0 resident)) (compare0_port _)
  simp only [PSTRTMCompareTrace055.compare_length] at h
  exact h

/-- The post-shift real comparison takes its less HALT to phase10, and
equality/greater HALTs to phase11; the tape is wholly nondestructive. -/
theorem compare9_hop (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) :
    Hop (phaseCfg 9 0 (loopTape context archive resident suffix))
      (phaseCfg (compare9Target (resultRelation 0 resident)) 0 (eofTape context archive resident suffix))
      (4*resident.length+4) := by
  have h := component_hop 9 (by decide : 20 ≤ 33) compareMachine rfl
    (state (aState 0) (frameLeft context archive) (PSTRTMBinaryAdd024.operandColumns resident ++ false::false::suffix))
    (state (haltLabel (resultRelation 0 resident)) (leftColumns resident.reverse ++ frameLeft context archive) (false::false::suffix))
    (PSTRTMCompareTrace055.compareTrace 0 (frameLeft context archive) [] resident suffix)
    (PSTRTMCompareTrace055.compare_runsFrom 0 (frameLeft context archive) resident suffix)
    (compare9Target (resultRelation 0 resident)) (compare9_port _)
  simp only [PSTRTMCompareTrace055.compare_length] at h
  exact h

private theorem rewind_component (phase target : Fin 17)
    (heq : loopMachines phase = PA17TMDivisionCompose006.padMachine (by decide : 5 ≤ 33) PSTRTMColumnRewind067.rewindMachine)
    (port : loopPorts phase 5 = some (target,0))
    (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) :
    Hop (phaseCfg phase 0 (eofTape context archive resident suffix))
      (phaseCfg target 0 (loopTape context archive resident suffix)) (4*resident.length+4) := by
  have h := component_hop phase (by decide : 5 ≤ 33) PSTRTMColumnRewind067.rewindMachine heq
    (PSTRTMColumnRewind067.state 0 (leftColumns resident.reverse ++ false::rewindArchive context archive) (false::false::suffix))
    (PSTRTMColumnRewind067.state 5 (false::rewindArchive context archive)
      (PSTRTMBinaryAdd024.operandColumns resident ++ false::false::suffix))
    (PSTRTMColumnRewind067.fullTrace (rewindArchive context archive) resident.reverse (false::false::suffix))
    (PSTRTMColumnRewind067.rewind_runsFrom (rewindArchive context archive) resident (false::false::suffix))
    target (by exact port)
  simp only [PSTRTMColumnRewind067.full_length,List.length_reverse] at h
  exact h

theorem rewind1_hop (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) :
    Hop (phaseCfg 1 0 (eofTape context archive resident suffix)) (phaseCfg 3 0 (loopTape context archive resident suffix))
      (4*resident.length+4) := rewind_component 1 3 rfl rfl context archive resident suffix

theorem rewind2_hop (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) :
    Hop (phaseCfg 2 0 (eofTape context archive resident suffix)) (phaseCfg 4 0 (loopTape context archive resident suffix))
      (4*resident.length+4) := rewind_component 2 4 rfl rfl context archive resident suffix

theorem rewind7_hop (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) :
    Hop (phaseCfg 7 0 (eofTape context archive resident suffix)) (phaseCfg 13 0 (loopTape context archive resident suffix))
      (4*resident.length+4) := rewind_component 7 13 rfl rfl context archive resident suffix

theorem rewind8_hop (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) :
    Hop (phaseCfg 8 0 (eofTape context archive resident suffix)) (phaseCfg 9 0 (loopTape context archive resident suffix))
      (4*resident.length+4) := rewind_component 8 9 rfl rfl context archive resident suffix

theorem rewind10_hop (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) :
    Hop (phaseCfg 10 0 (eofTape context archive resident suffix)) (phaseCfg 14 0 (loopTape context archive resident suffix))
      (4*resident.length+4) := rewind_component 10 14 rfl rfl context archive resident suffix

theorem rewind11_hop (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) :
    Hop (phaseCfg 11 0 (eofTape context archive resident suffix)) (phaseCfg 12 0 (loopTape context archive resident suffix))
      (4*resident.length+4) := rewind_component 11 12 rfl rfl context archive resident suffix

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionKernelPort010

