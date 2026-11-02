module

public import Paid.PDROC_D27Prepare_Q_002
public import Paid.PDROC_D27Prepare_Resources_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame
open PDROC.D27Prepare.Program PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Q

/-- A certificate for one real fetched segment. Memory and bit bounds
are required at every state, including the first and last states. -/
structure Segment (R : Finset ℕ) (input : List Cell) (before after : State)
    (H B budget : ℕ) : Prop where
  witness : ∃ trace : List State,
    trace.head? = some before ∧ trace.getLast? = some after ∧
    trace.IsChain (fun a b => step Program.program input a = some b) ∧
    trace.length ≤ budget ∧
    (∀ state ∈ trace, StateBounds H B state) ∧
    (∀ state ∈ trace, MemoryProgress R before state)
  output : after.output = before.output
  fresh : after.register .fresh = before.register .fresh

theorem Segment.trans {R : Finset ℕ} {input : List Cell} {before middle after : State}
    {H B firstBudget laterBudget : ℕ}
    (first : Segment R input before middle H B firstBudget)
    (later : Segment R input middle after H B laterBudget) :
    Segment R input before after H B (firstBudget + laterBudget) := by
  obtain ⟨earlierTrace, firstHead, firstLast, firstChain, firstLength, firstBounds, firstFrames⟩ := first.witness
  obtain ⟨laterTrace, laterHead, laterLast, laterChain, laterLength, laterBounds, laterFrames⟩ := later.witness
  have middleFrame := firstFrames middle (List.mem_of_getLast? firstLast)
  refine ⟨?_, later.output.trans first.output, later.fresh.trans first.fresh⟩
  refine ⟨joinTrace earlierTrace laterTrace,
    joinTrace_head earlierTrace laterTrace before middle firstHead firstLast laterHead,
    joinTrace_last earlierTrace laterTrace after laterLast,
    joinTrace_chain Program.program input earlierTrace laterTrace middle firstChain laterChain firstLast laterHead,
    ?_, ?_, ?_⟩
  · simp only [joinTrace, List.length_append, List.length_dropLast]
    omega
  · intro state member
    rcases List.mem_append.mp member with early | late
    · exact firstBounds state (List.mem_of_mem_dropLast early)
    · exact laterBounds state late
  · intro state member
    rcases List.mem_append.mp member with early | late
    · exact firstFrames state (List.mem_of_mem_dropLast early)
    · exact middleFrame.trans (laterFrames state late)

theorem Segment.final_bounds {R : Finset ℕ} {input : List Cell} {before after : State}
    {H B budget : ℕ} (segment : Segment R input before after H B budget) : StateBounds H B after := by
  obtain ⟨trace, _, last, _, _, bounds, _⟩ := segment.witness
  exact bounds after (List.mem_of_getLast? last)

theorem Segment.final_frame {R : Finset ℕ} {input : List Cell} {before after : State}
    {H B budget : ℕ} (segment : Segment R input before after H B budget) : MemoryProgress R before after := by
  obtain ⟨trace, _, last, _, _, _, frames⟩ := segment.witness
  exact frames after (List.mem_of_getLast? last)

theorem Segment.refl (R : Finset ℕ) (input : List Cell) (state : State) (H B : ℕ)
    (bounded : StateBounds H B state) : Segment R input state state H B 1 := by
  refine ⟨⟨[state], rfl, rfl, .singleton state, by simp, ?_, ?_⟩, rfl, rfl⟩
  · intro other member
    have same := List.mem_singleton.mp member
    simpa only [same] using bounded
  · intro other member
    have same := List.mem_singleton.mp member
    simpa only [same] using MemoryProgress.refl R state

theorem Segment.weaken_budget {R : Finset ℕ} {input : List Cell} {before after : State}
    {H B oldBudget newBudget : ℕ} (segment : Segment R input before after H B oldBudget)
    (larger : oldBudget ≤ newBudget) : Segment R input before after H B newBudget := by
  obtain ⟨trace, head, last, chain, length, bounds, frames⟩ := segment.witness
  exact ⟨⟨trace, head, last, chain, length.trans larger, bounds, frames⟩, segment.output, segment.fresh⟩

end PDROC.D27Prepare.Q
