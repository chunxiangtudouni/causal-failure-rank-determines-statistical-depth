module

public import Paid.PDLower_CalibrationCompute_Head_024
public import Paid.PDLower_CalibrationCompute_Segment_025

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- The kernel's real four-block entry does not require a disjoint old
live heap, a supplied header, an initial row or any successful-run oracle.
It writes all sixteen header cells and the original output count itself. -/
theorem headSegment (origin : ℕ) (P : Parameters) (input : List Cell)
    (base : ℕ) (before : State)
    (position : before.pc = labelAddress origin .enter)
    (fresh : before.register .fresh = .natural base)
    (M : before.register .total = .natural P.certificate.M)
    (gamma : before.register .value = .rational P.certificate.gamma) :
    Segment origin input before (headResult origin P base before) 1600 := by
  let saved : State := {prologueResult before base with pc := labelAddress origin .enterBases}
  let based : State := {enterBasesResult saved base P.certificate.M with pc := labelAddress origin .enterCache}
  let counted : State := {enterCacheResult based base P.certificate.M (resultBase base P.certificate.M) with
    pc := labelAddress origin .enterBias}
  have fs : saved.register .fresh = .natural base := by
    simpa only [saved,prologue_base] using fresh
  have ms : saved.register .total = .natural P.certificate.M := by
    simpa [saved,prologueResult,storeSlotResult,State.set] using M
  have fb : based.register .fresh = .natural base := by
    simpa only [based,enterBases_fresh] using fs
  have fc : counted.register .fresh = .natural base := by
    simpa only [counted,enterCache_fresh] using fb
  have sizeLive : base+2 ∈ based.live := by
    simp [based,enterBasesResult,storeSlotResult,saved,prologueResult,State.set]
  have sizeValue : based.heap (base+2) = .natural P.certificate.M := by
    simpa [based,enterBasesResult,storeSlotResult,saved,prologueResult,State.set] using M
  have cursorLive : base+15 ∈ based.live := by
    simp [based,enterBasesResult,storeSlotResult]
  have cursorValue : based.heap (base+15) = .natural (resultBase base P.certificate.M) := by
    simp [based,enterBasesResult,storeSlotResult]
  have gammaLive : base+4 ∈ counted.live := by
    simp [counted,enterCacheResult,loadSlotResult,storeSlotResult,writeCell,based,enterBasesResult,
      saved,prologueResult,State.set]
  have gammaValue : counted.heap (base+4) = .rational P.certificate.gamma := by
    have avoid : base+4 ≠ resultBase base P.certificate.M := by unfold resultBase rowWidth; omega
    simpa [counted,enterCacheResult,loadSlotResult,storeSlotResult,writeCell,
      based,enterBasesResult,saved,prologueResult,State.set,avoid] using gamma
  have one := segment_go origin .enter .enterBases input before (prologueResult before base)
    position (prologue_execute input before base fresh) rfl
  have two := segment_go origin .enterBases .enterCache input saved
    (enterBasesResult saved base P.certificate.M) rfl (enterBases_execute input saved base _ fs ms) rfl
  have three := segment_go origin .enterCache .enterBias input based
    (enterCacheResult based base P.certificate.M (resultBase base P.certificate.M)) rfl
    (enterCache_execute input based base _ _ fb sizeLive sizeValue cursorLive cursorValue) rfl
  have four := segment_go origin .enterBias .levelGate input counted
    (enterBiasResult counted base P.certificate.gamma) rfl
    (enterBias_execute input counted base _ fc gammaLive gammaValue) rfl
  have joined := ((one.trans two).trans three).trans four
  exact joined.mono (by decide)

end PDLower.CalibrationCompute
