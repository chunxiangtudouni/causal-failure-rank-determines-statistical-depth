module

public import Paid.PDCompute_Pack_TraceInvariant_055
public import Paid.RootD27Bits_SlotPrefix_004
public import Paid.PDLower_CalibrationCompute_Segment_025
public import Paid.PDROC_CalibrationRow_Init_SafeSegment_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid.Computation PDMenu.ComputeFrame RootD27.Bits

namespace PDLower.CalibrationCompute

/-- Original fetched kernel steps and the original complete stateCellBits
budget on the SAME trace. The numerical budget is fixed by the caller. -/
def BitSegment (origin : ℕ) (input : List Cell) (before after : State) (timeBudget bitBudget : ℕ) : Prop :=
  ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
    trace.IsChain (fun first later => step (locatedBlock origin (kernel origin)) input first=some later) ∧
    time (locatedBlock origin (kernel origin)) trace≤timeBudget ∧
    ∀ state∈trace,SafeBits state bitBudget

theorem BitSegment.toSegment {origin : ℕ} {input : List Cell} {before after : State} {timeBudget bitBudget : ℕ}
    (actual : BitSegment origin input before after timeBudget bitBudget) : Segment origin input before after timeBudget := by
  obtain ⟨trace,head,last,chain,cost,_⟩ := actual
  exact ⟨trace,head,last,chain,cost⟩

theorem BitSegment.final {origin : ℕ} {input : List Cell} {before after : State} {timeBudget bitBudget : ℕ}
    (actual : BitSegment origin input before after timeBudget bitBudget) : SafeBits after bitBudget := by
  obtain ⟨trace,_,last,_,_,states⟩ := actual
  exact states after (List.mem_of_getLast? last)

theorem BitSegment.mono {origin : ℕ} {input : List Cell} {before after : State} {first later bitBudget : ℕ}
    (actual : BitSegment origin input before after first bitBudget) (bound : first≤later) :
    BitSegment origin input before after later bitBudget := by
  obtain ⟨trace,head,last,chain,cost,states⟩ := actual
  exact ⟨trace,head,last,chain,cost.trans bound,states⟩

theorem BitSegment.trans {origin : ℕ} {input : List Cell} {before middle after : State} {first later bitBudget : ℕ}
    (earlier : BitSegment origin input before middle first bitBudget)
    (following : BitSegment origin input middle after later bitBudget) :
    BitSegment origin input before after (first+later) bitBudget := by
  obtain ⟨left,lh,ll,lc,lt,ls⟩ := earlier
  obtain ⟨right,rh,rl,rc,rt,rs⟩ := following
  have joined := joinTrace_spec (locatedBlock origin (kernel origin)) input left right
    before middle after first later lh ll rh rl lc rc lt rt
  exact ⟨joinTrace left right,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    PDCompute.Pack.joinTrace_invariant left right (fun state => SafeBits state bitBudget) ls rs⟩

theorem BitSegment.singleton (origin : ℕ) (input : List Cell) (state : State) (bitBudget : ℕ)
    (safe : SafeBits state bitBudget) : BitSegment origin input state state 15 bitBudget := by
  refine ⟨[state],rfl,rfl,.singleton state,time_singleton_le _ _,?_⟩
  intro later member
  have equal : later=state := List.mem_singleton.mp member
  subst later
  exact safe

/-- Consume the actual closed row provenance trace. The caller proves
its numerical interpretation; no provenance from a different trace is used. -/
theorem BitSegment.ofRow {origin base : ℕ} {region : Finset ℕ} {input : List Cell}
    {Good : State→Prop} {before after : State} {timeBudget bitBudget : ℕ}
    (actual : PDROC.CalibrationRow.SafeSegment origin base region input Good before after timeBudget)
    (interpreted : ∀ state,Good state→SafeBits state bitBudget) :
    BitSegment origin input before after timeBudget bitBudget := by
  obtain ⟨trace,head,last,chain,cost,states⟩ := actual
  refine ⟨trace,head,last,chain,cost,?_⟩
  intro state member
  exact interpreted state (states state member).2.2.2.2

/-- Generic original block lift, valid for sum/weight/emit/outer blocks as
well as row labels. Literal fetched code and actual execution are retained;
all linear-prefix facts use the frozen generic trace invariant theorem. -/
theorem BitSegment.ofBlock (origin : ℕ) (label : Label) (input : List Cell)
    (before middle after : State) (bitBudget : ℕ)
    (position : before.pc=labelAddress origin label)
    (body : linearExecute input (basicBlock label).body before=some middle)
    (control : (controlInstruction origin (basicBlock label).control).execute input middle=some after)
    (prefixes : ∀ count≤(basicBlock label).body.length,∀ state,
      linearExecute input ((basicBlock label).body.take count) before=some state→SafeBits state bitBudget)
    (lastSafe : SafeBits after bitBudget) :
    BitSegment origin input before after (15*((basicBlock label).body.length+1)+15) bitBudget := by
  have fetched : FetchesCode (locatedBlock origin (kernel origin)) before.pc (basicBlock label).body := by
    intro offset inside
    rw [position]
    exact kernel_body_fetch origin label offset inside
  obtain ⟨trace,head,last,chain,cost,states⟩ := PDCompute.Pack.linearExecute_trace_invariant
    (locatedBlock origin (kernel origin)) input (basicBlock label).body (basicBlock_straight label)
    before middle fetched body (fun state => SafeBits state bitBudget) prefixes
  have middlePC : middle.pc=labelAddress origin label+(basicBlock label).body.length := by
    simpa only [position] using linearExecute_pc input (basicBlock label).body (basicBlock_straight label) before middle body
  have next : step (locatedBlock origin (kernel origin)) input middle=some after := by
    rw [kernel_control_step origin label input middle middlePC]
    exact control
  have joined := chain_append_control (locatedBlock origin (kernel origin)) input trace middle after chain last next
  refine ⟨trace++[after],?_,by simp,joined.1,joined.2.trans (Nat.add_le_add_right cost _),?_⟩
  · cases trace with
    | nil => cases head
    | cons first rest => exact head
  · intro state member
    rcases List.mem_append.mp member with earlier|final
    · exact states state earlier
    · have equal : state=after := List.mem_singleton.mp final
      subst state
      exact lastSafe

end PDLower.CalibrationCompute
