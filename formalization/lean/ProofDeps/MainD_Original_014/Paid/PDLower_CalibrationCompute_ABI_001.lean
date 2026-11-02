module

public import PaperProofs.Paid.PDCompute_CodeRefinement_002
public import PaperProofs.Paid.PDCompute_Codec_001
public import PaperProofs.Paid.PDROC_EndpointDP_001
public import PaperProofs.Paid.PDROC_DataBits_CalibrationFormal_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- Both actual DP rows use one reusable maximum-width allocation. -/
def rowWidth (M : ℕ) : ℕ := 2*M+3
def firstRow (base : ℕ) : ℕ := base+16
def secondRow (base M : ℕ) : ℕ := base+16+rowWidth M
def resultBase (base M : ℕ) : ℕ := base+16+2*rowWidth M
def workspaceSize (M : ℕ) : ℕ := 16+3*rowWidth M
def workspace (base M : ℕ) : Finset ℕ := (Finset.range (workspaceSize M)).image (base+·)

theorem rowWidth_positive (M : ℕ) : 0 < rowWidth M := by unfold rowWidth; omega
theorem workspaceSize_linear (M : ℕ) : workspaceSize M = 6*M+25 := by
  unfold workspaceSize rowWidth
  omega
theorem workspaceSize_le (M : ℕ) : workspaceSize M ≤ 25*(M+1) := by
  rw [workspaceSize_linear]
  omega

theorem encodeCalibration_length (constant : CalibrationConstant) : (encodeCalibration constant).length = 2 := rfl

theorem encodeCalibrationCache_length (P : Parameters) :
    (encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList).length = rowWidth P.certificate.M := by
  simp only [encodeList,List.length_cons,List.length_flatMap,encodeCalibration_length,List.map_const',
    List.sum_replicate,Array.length_toList,calibrationWeightCache_size,Nat.nsmul_eq_mul,rowWidth]
  omega

theorem encodeEndpointCache_length (P : Parameters) :
    (encodeList encodeEndpoint P.endpointCache.toList).length = rowWidth P.certificate.M := by
  have element : ∀ endpoint : EndpointConstant,(encodeEndpoint endpoint).length = 2 := fun _ => rfl
  simp only [encodeList,List.length_cons,List.length_flatMap,element,List.map_const',List.sum_replicate,
    Array.length_toList,endpointCache_size,Nat.nsmul_eq_mul,rowWidth]
  omega

/-- The original record measure counts live heap, seven registers AND
the increment to the output stream. This reserves both row buffers, the
result cache and the genuine endpoint input, rather than just labels. -/
theorem standaloneRecordEnvelope (M : ℕ) :
    workspaceSize M + rowWidth M + rowWidth M + registers.length ≤ 38*(M+1) := by
  rw [workspaceSize_linear]
  change 6*M+25+(2*M+3)+(2*M+3)+7 ≤ _
  omega

def HeapList (state : State) (base : ℕ) (values : List Cell) : Prop :=
  (∀ offset < values.length,base+offset ∈ state.live) ∧ heapSegment state base values.length = values

/-- The caller has already computed the endpoint cache. Core's prepared
readonly input does not contain it; the genuine cache therefore enters
through live heap cells, never an extra readonly oracle. -/
def Entry (P : Parameters) (base endpoints returnPC : ℕ) (state : State) : Prop :=
  state.register .fresh = .natural base ∧
  state.register .old = .natural returnPC ∧
  state.register .address = .natural endpoints ∧
  state.register .total = .natural P.certificate.M ∧
  state.register .index = .natural P.certificate.Q ∧
  state.register .value = .rational P.certificate.gamma ∧
  HeapList state endpoints (encodeList encodeEndpoint P.endpointCache.toList) ∧
  Disjoint state.live (workspace base P.certificate.M)

def Frame (before after : State) (base M : ℕ) : Prop :=
  (∀ address ∉ workspace base M,after.heap address = before.heap address) ∧
  (∀ address ∉ workspace base M,address ∈ after.live ↔ address ∈ before.live)

/-- This is an interface specification for the literal routine still
being constructed, not a proof of its existence, cost or phase count. -/
def Return (P : Parameters) (base returnPC : ℕ) (before after : State) : Prop :=
  after.pc = returnPC ∧
  after.register .fresh = .natural base ∧
  after.register .old = .natural returnPC ∧
  after.register .address = .natural (resultBase base P.certificate.M) ∧
  after.register .index = .natural (rowWidth P.certificate.M) ∧
  HeapList after (resultBase base P.certificate.M)
    (encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList) ∧
  after.output = before.output ++ encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList ∧
  Frame before after base P.certificate.M

end PDLower.CalibrationCompute
