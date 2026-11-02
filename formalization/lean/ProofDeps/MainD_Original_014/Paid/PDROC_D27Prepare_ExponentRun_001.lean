module

public import Paid.PDROC_D27Prepare_Q_001
public import Paid.PDROC_D27Prepare_J_005
public import Paid.PDROC_D27Prepare_Search_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.ExponentRun

def region : Finset ℕ := {8,28,31,32}

/-- The real preceding M phase supplies its computed values. No exponent
threshold or final E is present at this original pc7 boundary. -/
structure ExponentInitial (P : Parameters) (fee : ℚ) (state : State) : Prop where
  raw : Search.RawConstants P fee state
  location : state.pc=pc 7
  t0 : Search.SlotHas state 6 (.natural P.certificate.t0)
  M : Search.SlotHas state 7 (.natural P.certificate.M)
  E : Search.SlotHas state 8 (.natural 1)
  ratStages : Search.SlotHas state 22 (.rational P.certificate.stages)
  ratT0 : Search.SlotHas state 23 (.rational P.certificate.t0)
  gammaSquared : Search.SlotHas state 24 (.rational (P.certificate.gamma^2))
  variance : Search.SlotHas state 25 (.rational P.certificate.varianceBase)
  varianceSquared : Search.SlotHas state 26 (.rational (P.certificate.varianceBase^2))
  majorityThreshold : Search.SlotHas state 27
    (.rational ((P.certificate.risk/(2*(P.certificate.stages : ℚ)))^2))
  menuRatio : Search.SlotHas state 29 (.rational P.certificate.menuRatio)
  odds : Search.SlotHas state 30 (.rational P.certificate.odds)

structure ExponentData (P : Parameters) (memory : SlotMemory) (e : ℕ) : Prop where
  counter : Has memory 8 (.natural e)
  one : Has memory 14 (.natural 1)
  half : Has memory 21 (.rational (1/2))
  power : Has memory 28 (.rational ((1/2 : ℚ)^e))
  threshold : Has memory 31 (.rational (P.certificate.gamma*P.certificate.epsilon))

def stepMemory (memory : SlotMemory) (e : ℕ) : SlotMemory :=
  (memory.write 8 (.natural (e+1))).write 28 (.rational ((1/2 : ℚ)^(e+1)))

theorem step_data (P : Parameters) (memory : SlotMemory) (e : ℕ)
    (data : ExponentData P memory e) : ExponentData P (stepMemory memory e) (e+1) := by
  constructor
  · simp [Has,stepMemory,SlotMemory.write]
  · simpa [Has,stepMemory,SlotMemory.write] using data.one
  · simpa [Has,stepMemory,SlotMemory.write] using data.half
  · simp [Has,stepMemory,SlotMemory.write]
  · simpa [Has,stepMemory,SlotMemory.write] using data.threshold

theorem finish_of_progress (P : Parameters) (fee : ℚ) (before after : State)
    (initial : ExponentInitial P fee before) (progress : MemoryProgress region before after)
    (location : after.pc=pc 10) (fresh : after.register .fresh=before.register .fresh)
    (exponent : Search.SlotHas after 8 (.natural P.certificate.E))
    (threshold : Search.SlotHas after 31 (.rational (P.certificate.gamma*P.certificate.epsilon))) :
    QInitial P fee after := by
  have readable (address : ℕ) (inside : address<6 ∨ (13≤address ∧ address≤21)) : address∉region := by
    simp only [region,Finset.mem_insert,Finset.mem_singleton]
    omega
  have raw := Search.RawConstants.transport P fee before after initial.raw
    (fun address inside => progress.1.1 address (readable address inside)) progress.2 fresh
  exact ⟨raw,location,
    progress.slot 6 (by decide) _ initial.t0,
    progress.slot 7 (by decide) _ initial.M,exponent,
    progress.slot 22 (by decide) _ initial.ratStages,
    progress.slot 23 (by decide) _ initial.ratT0,
    progress.slot 24 (by decide) _ initial.gammaSquared,
    progress.slot 25 (by decide) _ initial.variance,
    progress.slot 26 (by decide) _ initial.varianceSquared,
    progress.slot 27 (by decide) _ initial.majorityThreshold,
    progress.slot 29 (by decide) _ initial.menuRatio,
    progress.slot 30 (by decide) _ initial.odds,threshold⟩

end PDROC.D27Prepare.ExponentRun
