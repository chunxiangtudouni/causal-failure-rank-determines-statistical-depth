module

public import Paid.PDCompute_CorePrelude_Layout_001
public import Paid.RootD27Core_InitializeSearch_064
public import Paid.RootD27Core_FinalBoundary_083
public import Paid.PDCompute_CoreFinalTail_Resources_001
public import Paid.PDLower_CoreRuntimeNumeric_Complete_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDCompute.CoreProgram

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open RootD27.Core PDCompute.Solver

def initializationPC : ℕ := PDCompute.CorePrelude.bodyStart
def outerPC : ℕ := initializationPC+164
def bodyOrigin : ℕ := outerPC+4
def decrementOrigin : ℕ := outerPC+520
def backOrigin : ℕ := outerPC+528
def selectorPC : ℕ := outerPC+529
def tailPC : ℕ := selectorPC+180
def haltPC : ℕ := tailPC+71
def solveEntry : ℕ := tailPC+72
def solveReturn : ℕ :=
  (solveEntry+1)+46+(matrixCode .liveHeap (solveEntry+1+46)).length+232
def labels : RoutineLabels := PDCompute.CorePrelude.routineLabels solveEntry solveReturn

def bodyCode : List Instruction := bisectionBodyCode bodyOrigin solveEntry decrementOrigin
def loopCode : List Instruction := PDCompute.CoreSearchLoop.code outerPC bodyCode
def finalCode : List Instruction := finalizationCode selectorPC
def calleeCode : List Instruction := solverCalleeCode .liveHeap (solveEntry+1)
def suffix : List Instruction :=
  initializeSearchCode initializationPC solveEntry++
    (loopCode++(finalCode++([.jump (solveEntry+1)]++calleeCode)))

/-- The SAME original Prelude program. Only its real continuation is
filled; endpoint/calibration/header code is never reconstructed here. -/
def program : Program := PDCompute.CorePrelude.program suffix.toArray
def code : List Instruction := program.toList
def pcUpper : ℕ := program.size

attribute [local irreducible] matrixCode solverCalleeCode PDLower.CalibrationCompute.kernel
  PDCompute.CorePrelude.program PDCompute.CorePrelude.kernelWords PDCompute.CorePrelude.bodyStart
  PDCompute.CorePrelude.afterCalibration program suffix calleeCode initializationPC outerPC bodyOrigin
  decrementOrigin backOrigin selectorPC tailPC haltPC solveEntry solveReturn labels

theorem initialization_position : initializationPC=355+PDCompute.CorePrelude.kernelWords := by
  unfold initializationPC PDCompute.CorePrelude.bodyStart PDCompute.CorePrelude.afterCalibration preparedCalibrationReturnPC
  have size : (PDLower.CalibrationCompute.kernel 316).size=PDCompute.CorePrelude.kernelWords :=
    PDCompute.CorePrelude.kernel_length
  omega

theorem body_length : bodyCode.length=516 := bisectionBody_length _ _ _

theorem loop_length : loopCode.length=529 := by
  rw [loopCode,PDCompute.CoreSearchLoop.code_length,body_length]

theorem loop_addresses :
    PDCompute.CoreSearchLoop.bodyPC outerPC=bodyOrigin ∧
    PDCompute.CoreSearchLoop.decrementPC outerPC bodyCode=decrementOrigin ∧
    PDCompute.CoreSearchLoop.backPC outerPC bodyCode=backOrigin ∧
    PDCompute.CoreSearchLoop.exitPC outerPC bodyCode=selectorPC := by
  refine ⟨?_,?_,?_,?_⟩
  · unfold PDCompute.CoreSearchLoop.bodyPC bodyOrigin
    rfl
  · unfold PDCompute.CoreSearchLoop.decrementPC decrementOrigin
    have length:=body_length
    omega
  · unfold PDCompute.CoreSearchLoop.backPC backOrigin
    have length:=body_length
    omega
  · unfold PDCompute.CoreSearchLoop.exitPC selectorPC
    have length:=body_length
    omega

theorem final_split : finalCode=finalSelectorCode selectorPC++PDCompute.CoreFinalTail.code tailPC := by
  simp only [finalCode,finalizationCode,PDCompute.CoreFinalTail.code,tailPC,List.append_assoc,Nat.add_assoc]

theorem final_length : finalCode.length=252 := finalization_length _

theorem callee_length : calleeCode.length=
    46+(matrixCode .liveHeap (solveEntry+1+46)).length+233 := by
  simp only [calleeCode,solverCalleeCode,List.length_append,solverHeaderCode_length,
    endpointCountHeaderCode_length,matrixPackCode,PDCompute.Pack.serializerCode_length]
  omega

theorem suffix_length : suffix.length=946+calleeCode.length := by
  simp only [suffix,List.length_append,initializeSearch_length,loop_length,final_length,
    List.length_cons,List.length_nil]
  omega

private theorem prelude_size_list (tail : List Instruction) :
    (PDCompute.CorePrelude.program tail.toArray).size=355+PDCompute.CorePrelude.kernelWords+tail.length := by
  simpa only [List.size_toArray] using PDCompute.CorePrelude.program_size tail.toArray

private theorem program_size_arithmetic (total words init count cells entry ending selected outer : ℕ)
    (size : total=355+words+count) (length : count=946+cells)
    (position : init=355+words) (location : entry=ending+72) (tail : ending=selected+180)
    (selection : selected=outer+529) (loop : outer=init+164) :
    total=entry+1+cells := by
  omega

theorem program_length : program.size=solveEntry+1+calleeCode.length := by
  unfold program
  exact program_size_arithmetic _ _ _ _ _ _ _ _ _ (prelude_size_list suffix) suffix_length initialization_position
    (by unfold solveEntry;rfl) (by unfold tailPC;rfl) (by unfold selectorPC;rfl) (by unfold outerPC;rfl)

theorem marker_label : labels.solveReturn=PDLower.CoreRuntimeNumeric.commonSolverMarkerPC labels := by
  simp only [labels,PDCompute.CorePrelude.routineLabels,PDLower.CoreRuntimeNumeric.commonSolverMarkerPC,solveReturn]

theorem fixed_labels : labels.solveEntry=solveEntry ∧ labels.solveReturn=solveReturn ∧
    labels.endpointEntry=52 ∧ labels.calibrationEntry=316 := by
  unfold labels PDCompute.CorePrelude.routineLabels
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- The fixed common solver epilogue is the actual last program opcode;
the real main HALT is immediately BEFORE the common solver stub. -/
theorem last_locations : haltPC+1=solveEntry ∧ solveReturn+1=pcUpper := by
  have size:=program_length
  have length:=callee_length
  change haltPC+1=solveEntry ∧ solveReturn+1=program.size
  unfold haltPC solveReturn at *
  have entry : solveEntry=tailPC+72:=by unfold solveEntry;rfl
  omega

/-- Input-independent geometry paying every static runtime guard. No
program, address constant or routine label depends on P, fee or J. -/
theorem static_bounds :
    316 < initializationPC ∧ initializationPC+164=outerPC ∧
    outerPC+529=selectorPC ∧ selectorPC+252=solveEntry ∧
    initializationPC+164 < solveEntry ∧ outerPC+529 < solveEntry ∧
    selectorPC+180 < solveEntry ∧ haltPC < solveEntry ∧
    solveEntry+1 ≤ pcUpper ∧ calleeCode.length ≤ pcUpper ∧
    solveReturn < pcUpper ∧ 0 < pcUpper := by
  have position:=initialization_position
  have size:=program_length
  have length:=callee_length
  have last:=last_locations
  unfold pcUpper at *
  unfold solveEntry haltPC tailPC selectorPC outerPC at *
  omega

end PDCompute.CoreProgram
