module
public import Paid.PDCompute_Pack_AddressBits_007

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PDCompute.Solver

def naturalCap (base n k : ℕ) : ℕ:=base+workspaceSize n k

theorem naturalCap_result_end (base n k : ℕ) : resultBase base n k+resultCapacity n k=naturalCap base n k := by
  unfold naturalCap resultBase tableBase workspaceSize
  omega

theorem naturalCap_small (base n k : ℕ) : 48 ≤ naturalCap base n k := by
  unfold naturalCap workspaceSize headerWords
  omega

theorem naturalCap_rows (base n k : ℕ) : n+1 ≤ naturalCap base n k := by
  unfold naturalCap workspaceSize entryWords entryCount headerWords resultCapacity
  nlinarith

theorem naturalCap_columns (base n k : ℕ) : k+1 ≤ naturalCap base n k := by
  unfold naturalCap workspaceSize entryWords entryCount headerWords resultCapacity
  nlinarith

theorem naturalCap_header_address (base n k slot : ℕ) (inside : slot<headerWords) : base+slot ≤ naturalCap base n k := by
  unfold naturalCap workspaceSize
  omega

theorem naturalCap_product (base n k : ℕ) : (n+1)*(k+1) ≤ naturalCap base n k := by
  unfold naturalCap workspaceSize entryWords entryCount headerWords
  omega

theorem naturalCap_times_six (base n k : ℕ) : 6*((n+1)*(k+1)) ≤ naturalCap base n k := by
  unfold naturalCap workspaceSize entryWords entryCount headerWords
  omega

theorem naturalCap_plus_header (base n k : ℕ) : 6*((n+1)*(k+1))+48 ≤ naturalCap base n k := by
  unfold naturalCap workspaceSize entryWords entryCount headerWords
  omega

theorem naturalCap_resultBase (base n k : ℕ) : resultBase base n k ≤ naturalCap base n k := by
  have eq:=naturalCap_result_end base n k
  omega

theorem naturalCap_bits (base n k value : ℕ) (bound : value ≤ naturalCap base n k) :
    natBits value ≤ natBits base+natBits n+natBits k+8 := address_bits base n k value bound

end PDCompute.Pack
