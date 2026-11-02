module

public import Paid.PDROC_CalibrationRow_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Reusable real-block certificate. The local body proof discharges
every actual store, and all sixteen header cells stay live even when
their offsets belong to the mutable region. The prefix execution
witness is retained for the phase's actual clock/cursor/row formulas. -/
theorem row_block_safe_trace (origin base : ℕ) (region : Finset ℕ) (input : List Cell)
    (label : Label) (row : rowLabel label=true) (before middle after : State)
    (position : before.pc=labelAddress origin label)
    (body : linearExecute input (basicBlock label).body before=some middle)
    (control : (controlInstruction origin (basicBlock label).control).execute input middle=some after)
    (frames : LinearFrames region input (basicBlock label).body before)
    (allLive : ∀ offset<16,base+offset ∈ before.live)
    (lastFrame : MemoryFrame region before after)
    (lastOutput : after.output=before.output)
    (lastFresh : after.register .fresh=before.register .fresh)
    (lastLive : before.live ⊆ after.live) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.length=(basicBlock label).body.length+2 ∧
      trace.IsChain (fun a b => step (locatedBlock origin (kernel origin)) input a=some b) ∧
      time (locatedBlock origin (kernel origin)) trace≤15*((basicBlock label).body.length+2) ∧
      ∀ state∈trace,MemoryFrame region before state ∧ state.output=before.output ∧
        state.register .fresh=before.register .fresh ∧ (∀ offset<16,base+offset ∈ state.live) ∧
        ((∃ count≤(basicBlock label).body.length,
          linearExecute input ((basicBlock label).body.take count) before=some state) ∨ state=after) := by
  obtain ⟨trace,head,last,length,chain,cost,prefixes⟩ :=
    row_block_prefix_trace origin input label before middle after position body control
  refine ⟨trace,head,last,length,chain,cost,?_⟩
  intro state member
  have phase := prefixes state member
  rcases phase with ⟨count,bound,run⟩|equal
  · exact ⟨frames count state run,rowBody_prefix_output input label row before state count run,
      rowBody_prefix_fresh input label before state count run,
      fun offset inside => rowBody_prefix_live input label row before state count run (allLive offset inside),
      Or.inl ⟨count,bound,run⟩⟩
  · subst state
    exact ⟨lastFrame,lastOutput,lastFresh,fun offset inside => lastLive (allLive offset inside),Or.inr rfl⟩

end PDROC.CalibrationRow
