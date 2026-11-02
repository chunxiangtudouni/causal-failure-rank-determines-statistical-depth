module

public import Paid.PDLower_CalibrationCompute_Trace_012

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- A genuine original-step execution fragment. This is only proof-side
bookkeeping; its constructors below must supply the actual fetched chain. -/
def Segment (origin : ℕ) (input : List Cell) (before after : State) (budget : ℕ) : Prop :=
  ∃ trace : List State, trace.head? = some before ∧ trace.getLast? = some after ∧
    trace.IsChain (fun first later =>
      step (PDMenu.ComputeFrame.locatedBlock origin (kernel origin)) input first = some later) ∧
    time (PDMenu.ComputeFrame.locatedBlock origin (kernel origin)) trace ≤ budget

theorem Segment.trans {origin : ℕ} {input : List Cell} {before middle after : State} {first later : ℕ}
    (earlier : Segment origin input before middle first)
    (following : Segment origin input middle after later) :
    Segment origin input before after (first+later) := by
  obtain ⟨left,lh,ll,lc,lt⟩ := earlier
  obtain ⟨right,rh,rl,rc,rt⟩ := following
  refine ⟨PDMenu.ComputeFrame.joinTrace left right,?_,?_,
    PDMenu.ComputeFrame.joinTrace_chain _ _ _ _ middle lc rc ll rh,?_⟩
  · cases left with
    | nil => cases lh
    | cons head tail =>
      cases tail with
      | nil =>
        have hm : head=middle := Option.some.inj ll
        have hb : head=before := Option.some.inj lh
        change right.head?=some before
        exact rh.trans (congrArg some (hm.symm.trans hb))
      | cons next rest =>
        change some head=some before
        exact lh
  · have nonempty : right ≠ [] := by intro eq; rw [eq] at rh; cases rh
    exact (List.getLast?_append_of_ne_nil left.dropLast nonempty).trans rl
  · exact (PDMenu.ComputeFrame.joinTrace_time_le _ left right middle ll).trans (Nat.add_le_add lt rt)

theorem Segment.mono {origin : ℕ} {input : List Cell} {before after : State} {first later : ℕ}
    (run : Segment origin input before after first) (bound : first ≤ later) :
    Segment origin input before after later := by
  obtain ⟨trace,head,last,chain,cost⟩ := run
  exact ⟨trace,head,last,chain,cost.trans bound⟩

/-- Specialize the frozen actual body/fetch theorem to a real absolute
jump. The caller still proves the literal body's typed execution. -/
theorem segment_go (origin : ℕ) (label target : Label) (input : List Cell) (before middle : State)
    (position : before.pc = labelAddress origin label)
    (run : linearExecute input (basicBlock label).body before = some middle)
    (control : (basicBlock label).control = .go target) :
    Segment origin input before {middle with pc := labelAddress origin target}
      (15*((basicBlock label).body.length+1)+15) := by
  exact kernel_block_trace origin label input before middle _ position run (by
    simp only [control,controlInstruction,Instruction.execute]
    rfl)

end PDLower.CalibrationCompute
