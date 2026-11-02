module

public import Paid.PDLower_CalibrationCompute_Code_003
public import Paid.PDLower_CalibrationCompute_Linear_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- A first instruction jumps to the caller main routine after the shared
callee. Both original programs can then contain precisely the same bytes. -/
def calibrationOrigin : ℕ := 1

theorem kernel_size (origin : ℕ) : (kernel origin).size = (labels.map blockLength).sum := by
  simp only [kernel,List.size_toArray,List.length_flatMap,compiledBlock_length]

theorem entry_address (origin : ℕ) : labelAddress origin .enter = origin := by
  simp [labelAddress,labels]

end PDLower.CalibrationCompute
