module

public import Paid.PDCompute_SolverConditionalBits_166
public import Paid.PDCompute_SolverLiteralFieldsBits_165

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

theorem minimumUpdateCode_ifLess (origin : ℕ) :
    minimumUpdateCode origin=headerIfLessCode origin minimumUpdateCommands := rfl

/-- Actual original20-op running minimum update. The candidate wins
ONLY under strict comparison; equality retains old level/score. All
prefixes preserve the SAME complete-state bit budget. -/
theorem minimumUpdate_trace_bits (program : Program) (input : List Cell) (origin : ℕ)
    (before : State) (base n k budget : ℕ) (values : ℕ → Cell) (candidate best : ℚ)
    (hpc : before.pc=origin) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hc : values 28=.rational candidate) (hb : values 24=.rational best) (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (counter : natBits (origin+20)≤budget)
    (fetch : FetchesCode program origin (minimumUpdateCode origin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤630 ∧
      Header after base (if candidate<best then minimumUpdateValues values else values) ∧ after.register .fresh=.natural base ∧
      after.pc=origin+20 ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  have bounded:=copyConstantCommands_evaluated_bits minimumUpdateCommands values budget minimumUpdateCommands_valid
    (HeaderValueBits.of_safe header safe) (minimumUpdateCommands_copyBound budget)
  have bodyLength : (headerCode minimumUpdateCommands).length=12 := rfl
  have cost : 135+165*(minimumUpdateCommands.length+1)=630 := rfl
  have actualFetch : FetchesCode program origin (headerIfLessCode origin minimumUpdateCommands) := by
    rw [←minimumUpdateCode_ifLess]
    exact fetch
  simpa only [bodyLength,cost,Nat.add_assoc] using headerIfLess_trace_bits program input origin minimumUpdateCommands values
    (minimumUpdateValues values) actualFetch before base n k budget candidate best minimumUpdateCommands_valid (minimumUpdateCommands_eval values)
    bounded hpc header fresh hc hb safe small addressBits (by simpa only [bodyLength,Nat.add_assoc] using counter)

end PDCompute.Solver
