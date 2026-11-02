module
public import Paid.RootD27Core_PreparedCalibration_027
public import Paid.RootD27Core_HeaderActual_042
public import Paid.PDLower_CalibrationCompute_CodeFacts_005
public import Paid.PDCompute_CoreSearchLoop_Code_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
@[expose] public section

namespace PDCompute.CorePrelude
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open RootD27.Core PDCompute.Solver

/-- The actual fixed literal kernel size, independent of all P/fee. -/
def kernelWords : ℕ := (PDLower.CalibrationCompute.labels.map PDLower.CalibrationCompute.blockLength).sum
def endpointEntry : ℕ := 52
def calibrationEntry : ℕ := 316
def afterCalibration : ℕ := preparedCalibrationReturnPC
def bodyStart : ℕ := afterCalibration+39

/-- Exactly the original042 real fresh13, original37 producer, fresh0.
No prefilled metadata or free register restoration is installed. -/
def headerCode (origin : ℕ) : List Instruction :=
  [.constant .fresh (.natural 13)]++(solverHeaderCode (origin+1)++[.constant .fresh (.natural 0)])

/-- Extend the ORIGINAL prepared13 heap endpoint/calibration program,
preserving its actual heap-reading callees and every static PC. -/
def program (suffix : Program) : Program :=
  preparedCalibrationProgram ((headerCode afterCalibration).toArray++suffix)

def routineLabels (solveEntry solveReturn : ℕ) : RoutineLabels :=
  ⟨solveEntry,solveReturn,endpointEntry,calibrationEntry⟩

theorem kernel_length : (PDLower.CalibrationCompute.kernel calibrationEntry).size=kernelWords :=
  PDLower.CalibrationCompute.kernel_size calibrationEntry

theorem header_length (origin : ℕ) : (headerCode origin).length=39 := by
  simp only [headerCode,List.length_append,solverHeaderCode_length,List.length_cons,List.length_nil]

theorem program_toList (suffix : Program) :
    (program suffix).toList=inputCopyCode 13++(endpointHeapOutputCode 39 48 96 302++
      (calibrationHeapArgumentsCode afterCalibration++((PDLower.CalibrationCompute.kernel 316).toList++
        (headerCode afterCalibration++suffix.toList)))) := by
  unfold program
  rw [preparedCalibration_toList]
  simp only [afterCalibration,Array.toList_append]

theorem program_size (suffix : Program) : (program suffix).size=355+kernelWords+suffix.size := by
  have length:=congrArg List.length (program_toList suffix)
  simp only [Array.length_toList,List.length_append,inputCopy_length,endpointHeapOutput_length,
    calibrationHeapArguments_length,header_length] at length
  have kernelLength : (PDLower.CalibrationCompute.kernel 316).size=kernelWords := by
    simpa only [calibrationEntry] using kernel_length
  rw [kernelLength] at length
  omega

theorem kernel_words_actual : kernelWords=427 := by decide

theorem initial_body_start_actual : bodyStart=782 := by
  unfold bodyStart afterCalibration preparedCalibrationReturnPC
  have kernelLength : (PDLower.CalibrationCompute.kernel 316).size=kernelWords := by
    simpa only [calibrationEntry] using kernel_length
  rw [kernelLength,kernel_words_actual]

end PDCompute.CorePrelude
