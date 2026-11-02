module

public import Paid.PDLower_CalibrationCompute_HeaderState_017
public import Paid.PDLower_CalibrationCompute_Enter_014
public import Paid.PDLower_CalibrationCompute_Bases_019
public import Paid.PDLower_CalibrationCompute_CacheHead_020
public import Paid.PDLower_CalibrationCompute_Bias_023
public import Paid.PDLower_CalibrationCompute_Trace_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- The four REAL straight bodies with their four REAL absolute jumps.
No header cache, successful-run witness or derived result is input. -/
def headResult (origin : ℕ) (P : Parameters) (base : ℕ) (before : State) : State :=
  let saved := {prologueResult before base with pc := labelAddress origin .enterBases}
  let based := {enterBasesResult saved base P.certificate.M with pc := labelAddress origin .enterCache}
  let counted := {enterCacheResult based base P.certificate.M (resultBase base P.certificate.M) with
    pc := labelAddress origin .enterBias}
  {enterBiasResult counted base P.certificate.gamma with pc := labelAddress origin .levelGate}

theorem headResult_pc (origin : ℕ) (P : Parameters) (base : ℕ) (before : State) :
    (headResult origin P base before).pc = labelAddress origin .levelGate := rfl

theorem headResult_output (origin : ℕ) (P : Parameters) (base : ℕ) (before : State) :
    (headResult origin P base before).output = before.output++[Cell.natural (P.certificate.M+1)] := rfl

theorem headResult_fresh (origin : ℕ) (P : Parameters) (base : ℕ) (before : State) :
    (headResult origin P base before).register .fresh = before.register .fresh := by
  simp [headResult,enterBiasResult,enterBiasComputed,constantSlotResult,loadSlotResult,
    storeSlotResult,enterCacheResult,writeCell,enterBasesResult,prologueResult,State.set]

theorem headResult_header (origin : ℕ) (P : Parameters) (base endpoints returnPC : ℕ)
    (before : State) (ret : before.register .old = .natural returnPC)
    (endpoint : before.register .address = .natural endpoints)
    (M : before.register .total = .natural P.certificate.M)
    (Q : before.register .index = .natural P.certificate.Q)
    (gamma : before.register .value = .rational P.certificate.gamma) :
    (Header.initial base endpoints returnPC P.certificate.M P.certificate.Q P.certificate.gamma).At
      (headResult origin P base before) base := by
  have avoidResult (offset : ℕ) (inside : offset<16) : base+offset ≠ resultBase base P.certificate.M := by
    unfold resultBase rowWidth
    omega
  have avoidResultBase : base ≠ resultBase base P.certificate.M := by
    simpa only [Nat.add_zero] using avoidResult 0 (by decide)
  apply HeapList.of_values
  · intro index inside
    have alternatives : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 ∨ index=6 ∨ index=7 ∨
        index=8 ∨ index=9 ∨ index=10 ∨ index=11 ∨ index=12 ∨ index=13 ∨ index=14 ∨ index=15 := by
      simp only [Header.cells_length] at inside
      omega
    rcases alternatives with eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq <;> subst index <;>
      simp [headResult,enterBiasResult,enterBiasComputed,constantSlotResult,loadSlotResult,
        storeSlotResult,enterCacheResult,writeCell,enterBasesResult,prologueResult,State.set]
  · intro index inside
    have alternatives : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 ∨ index=6 ∨ index=7 ∨
        index=8 ∨ index=9 ∨ index=10 ∨ index=11 ∨ index=12 ∨ index=13 ∨ index=14 ∨ index=15 := by
      simp only [Header.cells_length] at inside
      omega
    rcases alternatives with eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq <;> subst index <;>
      simp_all [headResult,Header.initial,Header.cells,enterBiasResult,enterBiasComputed,constantSlotResult,
        loadSlotResult,storeSlotResult,enterCacheResult,writeCell,enterBasesResult,prologueResult,State.set]

end PDLower.CalibrationCompute
