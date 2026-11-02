module

public import Paid.PDCompute_SolverCandidateCode_028

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def initializedHeaderValues (before : State) (base slot : ℕ) : Cell :=
  if slot < 6 then before.heap (base+slot)
  else (denseEncodeEntry finishEntry)[(slot-6)%6]'(by change (slot-6)%6 < 6; omega)

/-- Seven actual six-cell writes make all48 header slots live, retaining
the original six saved arguments. The padding uses the already verified
fixed base-row loop and does not depend on any paper parameter. -/
theorem baseRowLoopResult_header (origin : ℕ) (before : State) (base : ℕ)
    (hfirst : ∀ slot < 6, base+slot ∈ before.live) :
    Header (baseRowLoopResult origin 7 before (base+6)) base (initializedHeaderValues before base) := by
  intro slot inside
  change slot < 48 at inside
  by_cases hs : slot < 6
  · refine ⟨baseRowLoopResult_live_mono origin 7 before (base+6) (hfirst slot hs),?_⟩
    rw [baseRowLoopResult_heap_below origin 7 before (base+6) (base+slot) (by omega)]
    simp only [initializedHeaderValues,ite_eq_left hs]
  · have hrow : (slot-6)/6 < 7 := by omega
    have hcolumn : (slot-6)%6 < (denseEncodeEntry finishEntry).length := by change (slot-6)%6 < 6; omega
    have hposition : base+6+6*((slot-6)/6)+(slot-6)%6=base+slot := by omega
    have represented := baseRowLoopResult_entries origin 7 before (base+6) ((slot-6)/6) hrow
    have hl := represented.1 ((slot-6)%6) hcolumn
    have hv := PDLower.CalibrationCompute.HeapList.value represented ((slot-6)%6) hcolumn
    rw [hposition] at hl hv
    refine ⟨hl,?_⟩
    simpa only [initializedHeaderValues,ite_eq_right hs] using hv

theorem headerPadding_region_inside (base n k : ℕ) :
    ∀ offset < 6*7, base+6+offset ∈ workspace base n k := by
  intro offset inside
  apply Finset.mem_image.mpr
  refine ⟨6+offset,Finset.mem_range.mpr ?_,?_⟩
  · unfold workspaceSize headerWords
    omega
  · omega

/-- A genuine constant-count initialization phase; its entry registers
are subsequently produced by the ordinary caller instructions. The six
argument slots have the actual prologue contents proved in017. -/
theorem initializeHeaderLoop (program : Program) (input : List Cell) (origin : ℕ)
    (hcode : FetchesCode program origin (baseRowCode origin)) (before : State) (base n k : ℕ)
    (hpc : before.pc=origin+1) (hbase : before.register .fresh=.natural base)
    (haddress : before.register .address=.natural (base+6))
    (hcount : before.register .index=.natural 7) (hone : before.register .flag=.natural 1)
    (hfirst : ∀ slot < 6, base+slot ∈ before.live) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 2130 ∧
      Header after base (initializedHeaderValues before base) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+18 ∧
      Frame before after base n k ∧ after.output=before.output := by
  obtain ⟨trace,hh,hl,hchain,ht⟩ := baseRowLoop_trace program input origin hcode 7 before (base+6) hpc haddress hcount hone
  refine ⟨trace,baseRowLoopResult origin 7 before (base+6),hh,hl,hchain,ht,
    baseRowLoopResult_header origin before base hfirst,?_,baseRowLoopResult_pc ..,
    baseRowLoopResult_frame origin 7 before (base+6) base n k (headerPadding_region_inside base n k),
    baseRowLoopResult_output ..⟩
  exact (baseRowLoopResult_unchanged_register origin 7 before (base+6) .fresh (by decide) (by decide) (by decide)).trans hbase

end PDCompute.Solver
