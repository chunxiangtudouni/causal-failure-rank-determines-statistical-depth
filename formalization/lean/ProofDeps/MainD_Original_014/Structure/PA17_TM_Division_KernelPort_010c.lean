module
public import Structure.PA17_TM_Division_KernelPort_010b

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionKernelPort010
open PA17TMDivisionLoop002
open PSTRTMCompareCode054 (leftColumns)

private theorem shift_component (phase target : Fin 17)
    (heq : loopMachines phase = PA17TMDivisionCompose006.padMachine (by decide : 19 ≤ 33) PSTRTMShiftColumnCode065.shiftMachine)
    (port : ∀ carry, loopPorts phase (PA17TMDivisionCompose006.padLabel (by decide : 19 ≤ 33)
      (PSTRTMShiftColumnCode065.haltLabel carry)) = some (target,0))
    (bit : Bool) (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) :
    Hop (phaseCfg phase (shiftLabel bit) (loopTape context archive resident suffix))
      (phaseCfg target 0 (eofTape context archive (PSTRTMShiftColumnCode065.shiftPairs bit resident) suffix))
      (7*resident.length+4) := by
  have h := component_hop phase (by decide : 19 ≤ 33) PSTRTMShiftColumnCode065.shiftMachine heq
    (PSTRTMShiftColumnCode065.state (PSTRTMShiftColumnCode065.readA bit) (frameLeft context archive)
      (PSTRTMBinaryAdd024.operandColumns resident ++ false::false::suffix))
    (PSTRTMShiftColumnCode065.state (PSTRTMShiftColumnCode065.haltLabel (PSTRTMShiftColumnCode065.finalCarry bit resident))
      (leftColumns (PSTRTMShiftColumnCode065.shiftPairs bit resident).reverse ++ frameLeft context archive) (false::false::suffix))
    (PSTRTMShiftColumnTrace066.shiftTrace bit (frameLeft context archive) [] resident suffix)
    (PSTRTMShiftColumnTrace066.shift_runsFrom bit (frameLeft context archive) resident suffix)
    target (port (PSTRTMShiftColumnCode065.finalCarry bit resident))
  simp only [PSTRTMShiftColumnTrace066.shift_length] at h
  exact h

/-- No overflow/room premise: both actual carry HALTs take the real phase7
port. The stated output is the exact resident finite-width shift. -/
theorem shift5_hop (bit : Bool) (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) :
    Hop (phaseCfg 5 (shiftLabel bit) (loopTape context archive resident suffix))
      (phaseCfg 7 0 (eofTape context archive (PSTRTMShiftColumnCode065.shiftPairs bit resident) suffix))
      (7*resident.length+4) := shift_component 5 7 rfl (fun _ => rfl) bit context archive resident suffix

theorem shift6_hop (bit : Bool) (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) :
    Hop (phaseCfg 6 (shiftLabel bit) (loopTape context archive resident suffix))
      (phaseCfg 8 0 (eofTape context archive (PSTRTMShiftColumnCode065.shiftPairs bit resident) suffix))
      (7*resident.length+4) := shift_component 6 8 rfl (fun _ => rfl) bit context archive resident suffix

/-- The actual fixed resident subtractor, including its own real067 rewind,
then the charged write-self hop into commit-true phase15. Arbitrary operands
and underflow remain allowed here; arithmetic branch invariants belong to009. -/
theorem sub12_hop (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) :
    Hop (phaseCfg 12 0 (loopTape context archive resident suffix))
      (phaseCfg 15 0 (loopTape context archive (PA17TMDivisionSub001.subPairs false resident) suffix))
      (13*resident.length+7) := by
  have h := component_hop 12 (by decide : 33 ≤ 33) PA17TMDivisionSub001.residentSubMachine rfl
    (PA17TMDivisionSub001.residentSubInitial (rewindArchive context archive) resident suffix)
    (PA17TMDivisionSub001.residentSubFinal (rewindArchive context archive) resident suffix)
    (PA17TMDivisionSub001.residentSubTrace (rewindArchive context archive) resident suffix)
    (PA17TMDivisionSub001.residentSub_runsFrom (rewindArchive context archive) resident suffix)
    15 rfl
  simp only [PA17TMDivisionSub001.residentSub_length] at h
  exact h

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionKernelPort010

