module

public import Paid.PDROC_CalibrationRow_Init_SafeTrace_001
public import Paid.PDLower_CalibrationCompute_Segment_025
public import Paid.PDMenu_ComputeFrame_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Genuine fetched trace with a frame and caller-relative preservation
at EVERY state. Good retains the caller's concrete phase/provenance
certificate, including actual block-prefix execution and row operands.
No bound on an arbitrary incoming scratch register is assumed. -/
def SafeSegment (origin base : ℕ) (region : Finset ℕ) (input : List Cell)
    (Good : State→Prop) (before after : State) (budget : ℕ) : Prop :=
  ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
    trace.IsChain (fun a b => step (locatedBlock origin (kernel origin)) input a=some b) ∧
    time (locatedBlock origin (kernel origin)) trace≤budget ∧
    ∀ state∈trace,MemoryFrame region before state ∧ state.output=before.output ∧
      state.register .fresh=before.register .fresh ∧ (∀ offset<16,base+offset ∈ state.live) ∧ Good state

theorem SafeSegment.toSegment {origin base : ℕ} {region : Finset ℕ} {input : List Cell}
    {Good : State→Prop} {before after : State} {budget : ℕ}
    (run : SafeSegment origin base region input Good before after budget) :
    Segment origin input before after budget := by
  obtain ⟨trace,head,last,chain,cost,_⟩ := run
  exact ⟨trace,head,last,chain,cost⟩

theorem SafeSegment.final {origin base : ℕ} {region : Finset ℕ} {input : List Cell}
    {Good : State→Prop} {before after : State} {budget : ℕ}
    (run : SafeSegment origin base region input Good before after budget) :
    MemoryFrame region before after ∧ after.output=before.output ∧
      after.register .fresh=before.register .fresh ∧ (∀ offset<16,base+offset ∈ after.live) ∧ Good after := by
  obtain ⟨trace,_,last,_,_,states⟩ := run
  exact states after (List.mem_of_getLast? last)

theorem SafeSegment.mono {origin base : ℕ} {region : Finset ℕ} {input : List Cell}
    {Good : State→Prop} {before after : State} {first later : ℕ}
    (run : SafeSegment origin base region input Good before after first) (bound : first≤later) :
    SafeSegment origin base region input Good before after later := by
  obtain ⟨trace,head,last,chain,cost,states⟩ := run
  exact ⟨trace,head,last,chain,cost.trans bound,states⟩

theorem SafeSegment.weaken {origin base : ℕ} {region : Finset ℕ} {input : List Cell}
    {Good Better : State→Prop} {before after : State} {budget : ℕ}
    (run : SafeSegment origin base region input Good before after budget)
    (implies : ∀ state,Good state→Better state) :
    SafeSegment origin base region input Better before after budget := by
  obtain ⟨trace,head,last,chain,cost,states⟩ := run
  refine ⟨trace,head,last,chain,cost,?_⟩
  intro state member
  have safe := states state member
  exact ⟨safe.1,safe.2.1,safe.2.2.1,safe.2.2.2.1,implies state safe.2.2.2.2⟩

theorem SafeSegment.singleton (origin base : ℕ) (region : Finset ℕ) (input : List Cell)
    (Good : State→Prop) (state : State) (allLive : ∀ offset<16,base+offset ∈ state.live)
    (good : Good state) : SafeSegment origin base region input Good state state 15 := by
  refine ⟨[state],rfl,rfl,.singleton state,time_singleton_le _ _,?_⟩
  intro next member
  have same : next=state := List.mem_singleton.mp member
  subst next
  exact ⟨MemoryFrame.refl region state,rfl,rfl,allLive,good⟩

/-- joinTrace drops the earlier terminal occurrence, rather than adding
a fictitious self-step. Good survives unchanged on both actual traces. -/
theorem SafeSegment.trans {origin base : ℕ} {region : Finset ℕ} {input : List Cell}
    {Good : State→Prop} {before middle after : State} {first later : ℕ}
    (earlier : SafeSegment origin base region input Good before middle first)
    (following : SafeSegment origin base region input Good middle after later) :
    SafeSegment origin base region input Good before after (first+later) := by
  obtain ⟨left,lh,ll,lc,lt,ls⟩ := earlier
  obtain ⟨right,rh,rl,rc,rt,rs⟩ := following
  have joined := joinTrace_spec (locatedBlock origin (kernel origin)) input left right
    before middle after first later lh ll rh rl lc rc lt rt
  have atMiddle := ls middle (List.mem_of_getLast? ll)
  refine ⟨joinTrace left right,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,?_⟩
  intro state member
  change state∈left.dropLast++right at member
  rcases List.mem_append.mp member with early|late
  · exact ls state ((List.dropLast_sublist left).subset early)
  · have safe := rs state late
    exact ⟨atMiddle.1.trans safe.1,safe.2.1.trans atMiddle.2.1,
      safe.2.2.1.trans atMiddle.2.2.1,safe.2.2.2.1,safe.2.2.2.2⟩

theorem SafeSegment.trans_or {origin base : ℕ} {region : Finset ℕ} {input : List Cell}
    {First Later : State→Prop} {before middle after : State} {first later : ℕ}
    (earlier : SafeSegment origin base region input First before middle first)
    (following : SafeSegment origin base region input Later middle after later) :
    SafeSegment origin base region input (fun state => First state∨Later state) before after (first+later) :=
  (earlier.weaken (fun _ good => Or.inl good)).trans (following.weaken (fun _ good => Or.inr good))

/-- The phase's provenance is proved from the concrete caller state and
its exact literal prefix. It can remember real clocks, cursor values,
readRow and partialScatter rather than imposing an incoming P-only bound. -/
theorem SafeSegment.ofBlock (origin base : ℕ) (region : Finset ℕ) (input : List Cell)
    (Good : State→Prop) (label : Label) (row : rowLabel label=true) (before middle after : State)
    (position : before.pc=labelAddress origin label)
    (body : linearExecute input (basicBlock label).body before=some middle)
    (control : (controlInstruction origin (basicBlock label).control).execute input middle=some after)
    (frames : LinearFrames region input (basicBlock label).body before)
    (allLive : ∀ offset<16,base+offset ∈ before.live)
    (lastFrame : MemoryFrame region before after) (lastOutput : after.output=before.output)
    (lastFresh : after.register .fresh=before.register .fresh) (lastLive : before.live ⊆ after.live)
    (provenance : ∀ state,
      ((∃ count≤(basicBlock label).body.length,
        linearExecute input ((basicBlock label).body.take count) before=some state) ∨ state=after) → Good state) :
    SafeSegment origin base region input Good before after (15*((basicBlock label).body.length+2)) := by
  obtain ⟨trace,head,last,_,chain,cost,states⟩ := row_block_safe_trace origin base region input
    label row before middle after position body control frames allLive lastFrame lastOutput lastFresh lastLive
  refine ⟨trace,head,last,chain,cost,?_⟩
  intro state member
  have safe := states state member
  exact ⟨safe.1,safe.2.1,safe.2.2.1,safe.2.2.2.1,provenance state safe.2.2.2.2⟩

end PDROC.CalibrationRow
