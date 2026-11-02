module

public import Paid.PDROC_D27Prepare_EndpointRun_007
public import Paid.PDROC_D27Prepare_ExponentRun_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.EndpointRun

theorem loop_segment (P : Parameters) (fee : ℚ) (input : List Cell) :
    ∀ fuel m (before : State) (memory : SlotMemory), m + fuel = P.certificate.M →
      MemoryMatch before memory → before.pc = pc 5 → StateBounds 64 (operandBudget P fee) before →
      EndpointData P memory m →
      ∃ (after : State) (finalMemory : SlotMemory), MemoryMatch after finalMemory ∧
        EndpointData P finalMemory P.certificate.M ∧ after.pc = pc 7 ∧
        Segment loopRegion input before after 64 (operandBudget P fee) (51 * fuel + 29) := by
  intro fuel
  induction fuel with
  | zero =>
      intro m before memory fits matched location bounded data
      have same : m = P.certificate.M := by omega
      subst m
      obtain ⟨after, afterMatch, afterPc, segment⟩ := guard_segment P fee input before memory matched location bounded
        P.certificate.M le_rfl data
      exact ⟨after, guardMemory P memory P.certificate.M, afterMatch, guard_data P memory _ data,
        by simpa only [↓reduceIte] using afterPc, segment⟩
  | succ fuel ih =>
      intro m before memory fits matched location bounded data
      have rejected : m < P.certificate.M := by omega
      obtain ⟨middle, middleMatch, middlePc, first⟩ := cycle_segment P fee input before memory matched location bounded m rejected data
      obtain ⟨after, finalMemory, afterMatch, afterData, afterPc, later⟩ := ih (m + 1) middle (cycleMemory P memory m)
        (by omega) middleMatch middlePc first.final_bounds (cycle_data P memory m data)
      exact ⟨after, finalMemory, afterMatch, afterData, afterPc, (first.trans later).weaken_budget (by omega)⟩

/-- The complete actual page4--6 M search. The ratio and odds are computed
from raw/t0 values, every rejected candidate executes the real guard and
updates, and the least-M guard exits at the original exponent entry. -/
theorem original_M_segment (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (initial : Search.EndpointInitial P fee before) (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ after : State, ExponentRun.ExponentInitial P fee after ∧
      Segment region input before after 64 (operandBudget P fee) (120 * (P.certificate.M + 1)) := by
  obtain ⟨initialized, initMatch, initPc, initData, first⟩ := setup_segment P fee input before initial bounded
  obtain ⟨after, finalMemory, afterMatch, afterData, afterPc, later⟩ := loop_segment P fee input P.certificate.M 0
    initialized (setupMemory P.certificate (Search.currentMemory before)) (by omega) initMatch initPc first.final_bounds initData
  have subset : loopRegion ⊆ region := by
    intro address member
    simp only [loopRegion, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl <;> decide
  have whole := first.trans (later.widen_region subset)
  have raw := Search.RawConstants.transport P fee before after initial.raw
    (by
      intro address read
      apply whole.final_frame.1.1 address
      simp only [region, Finset.mem_insert, Finset.mem_singleton]
      omega)
    whole.final_frame.2 whole.fresh
  have ratT0Stored : Has (setupMemory P.certificate (Search.currentMemory before)) 23 (.rational P.certificate.t0) := by
    simp [setupMemory, Has, SlotMemory.write]
  have ratT0AtStart := match_has initialized _ 23 _ initMatch ratT0Stored
  have ratT0AtEnd := later.final_frame.slot 23 (by decide) _ ratT0AtStart
  have boundary : ExponentRun.ExponentInitial P fee after :=
    ⟨raw, afterPc,
      whole.final_frame.slot 6 (by decide) _ initial.t0,
      match_has after finalMemory 7 _ afterMatch afterData.counter,
      whole.final_frame.slot 8 (by decide) _ initial.E,
      whole.final_frame.slot 22 (by decide) _ initial.ratStages, ratT0AtEnd,
      whole.final_frame.slot 24 (by decide) _ initial.gammaSquared,
      whole.final_frame.slot 25 (by decide) _ initial.variance,
      whole.final_frame.slot 26 (by decide) _ initial.varianceSquared,
      whole.final_frame.slot 27 (by decide) _ initial.majorityThreshold,
      match_has after finalMemory 29 _ afterMatch afterData.ratio,
      match_has after finalMemory 30 _ afterMatch afterData.odds⟩
  exact ⟨after, boundary, whole.weaken_budget (by omega)⟩

end PDROC.D27Prepare.EndpointRun
