module

public import Paid.PDLower_CalibrationCompute_EnterBits_104
public import Paid.PDLower_CalibrationCompute_BasesBits_105
public import Paid.PDLower_CalibrationCompute_CacheHeadBits_106
public import Paid.PDLower_CalibrationCompute_BiasBits_107
public import Paid.PDLower_CalibrationCompute_RowBitBudget_102
public import Paid.PDLower_CalibrationCompute_BiasScalarBits_092

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

/-- All four original entry blocks and their actual jumps, original
leading output and complete old caller carry, on ONE actual bit trace.
No incoming live header, fresh workspace or full execution is assumed. -/
theorem head_bits (P : Parameters) (origin : ℕ) (input : List Cell) (base endpoints returnPC callerBudget Lgamma : ℕ)
    (before : State) (arguments : CallArguments P base endpoints returnPC before)
    (initialSafe : SafeBits before callerBudget) (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma)
    (position : before.pc=labelAddress origin .enter) :
    BitSegment origin input before (headResult origin P base before) 1600 (calleeOperandBudget P origin callerBudget Lgamma) := by
  let budget := calleeOperandBudget P origin callerBudget Lgamma
  have bounds : ControlBudget P origin base budget :=
    calleeOperandBudget_control P origin base endpoints returnPC callerBudget Lgamma before arguments initialSafe
  have safe : SafeBits before budget := calleeOperandBudget_initial P origin callerBudget Lgamma before initialSafe
  let saved : State := {prologueResult before base with pc:=labelAddress origin .enterBases}
  let based : State := {enterBasesResult saved base P.certificate.M with pc:=labelAddress origin .enterCache}
  let counted : State := {enterCacheResult based base P.certificate.M (resultBase base P.certificate.M) with
    pc:=labelAddress origin .enterBias}
  have fs : saved.register .fresh=.natural base := by simpa only [saved,prologue_base] using arguments.fresh
  have ms : saved.register .total=.natural P.certificate.M := by
    simpa [saved,prologueResult,storeSlotResult,State.set] using arguments.total
  have fb : based.register .fresh=.natural base := by simpa only [based,enterBases_fresh] using fs
  have fc : counted.register .fresh=.natural base := by simpa only [counted,enterCache_fresh] using fb
  have length : (savedArguments before).length=5 := rfl
  have savedHeap : HeapList saved base (savedArguments before) := prologue_heapList before base
  have basedHeap : HeapList based base (savedArguments before) :=
    enterBases_arguments (M:=P.certificate.M) savedHeap length
  have countedHeap : HeapList counted base (savedArguments before) :=
    enterCache_arguments (M:=P.certificate.M) basedHeap length
  have sizeLive : base+2∈based.live := basedHeap.1 2 (by simp [savedArguments])
  have sizeValue : based.heap (base+2)=.natural P.certificate.M := by
    have actual : based.heap (base+2)=before.register .total := by
      simpa [savedArguments] using HeapList.value basedHeap 2 (by simp [savedArguments])
    exact actual.trans arguments.total
  have cursorLive : base+15∈based.live := by simp [based,enterBasesResult,storeSlotResult]
  have cursorValue : based.heap (base+15)=.natural (resultBase base P.certificate.M) := by
    simp [based,enterBasesResult,storeSlotResult]
  have gammaLive : base+4∈counted.live := countedHeap.1 4 (by simp [savedArguments])
  have gammaValue : counted.heap (base+4)=.rational P.certificate.gamma := by
    have actual : counted.heap (base+4)=before.register .value := by
      simpa [savedArguments] using HeapList.value countedHeap 4 (by simp [savedArguments])
    exact actual.trans arguments.value
  have halfEncoding : ratEncodingBits (1/2 : ℚ)=4 := by
    norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have positive : 0<(P.certificate.Q+1)*(Lgamma+2) := Nat.mul_pos (by omega) (by omega)
  have halfBound : ratEncodingBits (1/2 : ℚ)≤128*(P.certificate.Q+1)*(Lgamma+2) := by
    rw [halfEncoding]
    simp only [Nat.mul_assoc]
    omega
  have halfBits := calleeOperandBudget_rational P origin callerBudget Lgamma (1/2) halfBound
  have biases := bias_scalar_encodingBits P.certificate.gamma Lgamma gammaBits
  have coefficient : 4≤128*(P.certificate.Q+1) := by omega
  have scaled := Nat.mul_le_mul_right (Lgamma+2) coefficient
  have minusBits := calleeOperandBudget_rational P origin callerBudget Lgamma _ (biases.1.trans scaled)
  have plusBits := calleeOperandBudget_rational P origin callerBudget Lgamma _ (biases.2.trans scaled)
  have one : BitSegment origin input before saved 270 budget :=
    enter_bitSegment origin input before base budget position safe arguments.fresh
      (fun offset bounded => ControlBudget.slot P origin base budget offset bounds (by omega))
      (ControlBudget.pc_prefix P origin base budget bounds before .enter 16 position (by decide))
      (ControlBudget.pc_target P origin base budget bounds .enterBases)
  have two : BitSegment origin input saved based 285 budget :=
    enterBases_bitSegment P origin input saved base budget bounds one.final fs ms rfl
  have cursorBound : resultBase base P.certificate.M+1≤controlNaturalCap P base := by
    rw [controlNaturalCap_eq_resultBase]
    omega
  have three : BitSegment origin input based counted 300 budget :=
    enterCache_bitSegment P origin input based base (resultBase base P.certificate.M) budget bounds two.final fb
      sizeLive sizeValue cursorLive cursorValue cursorBound rfl
  have four := enterBias_bitSegment P origin input counted base budget bounds three.final fc gammaLive gammaValue
    halfBits minusBits plusBits rfl
  exact (((one.trans two).trans three).trans four).mono (by decide)

end PDLower.CalibrationCompute
