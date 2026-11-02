module

public import Paid.PDLower_CalibrationCompute_Callee_080
public import Paid.PDROC_CalibrationRow_053
public import Paid.PDCompute_Pack_TraceInvariant_055

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.CorePreludePC

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute

attribute [local irreducible] kernel

/-- A functional original-kernel fragment with a lower PC certificate on
the SAME trace. No bit, answer, or successful whole-run input is added. -/
def LowerSegment (origin : ℕ) (input : List Cell) (low : ℕ) (before after : State) : Prop :=
  ∃ states : List State, states.head?=some before ∧ states.getLast?=some after ∧
    states.IsChain (fun first later=>step (locatedBlock origin (kernel origin)) input first=some later) ∧
    ∀ state∈states, low ≤ state.pc

theorem LowerSegment.trans {origin low : ℕ} {input : List Cell} {before middle after : State}
    (first : LowerSegment origin input low before middle)
    (later : LowerSegment origin input low middle after) :
    LowerSegment origin input low before after := by
  obtain ⟨left,lh,ll,lc,lowerLeft⟩:=first
  obtain ⟨right,rh,rl,rc,lowerRight⟩:=later
  exact ⟨joinTrace left right,joinTrace_head left right before middle lh ll rh,
    joinTrace_last left right after rl,
    joinTrace_chain _ _ left right middle lc rc ll rh,
    PDCompute.Pack.joinTrace_invariant left right (fun state=>low ≤ state.pc) lowerLeft lowerRight⟩

theorem LowerSegment.weaken {origin first later : ℕ} {input : List Cell} {before after : State}
    (actual : LowerSegment origin input first before after) (bound : later ≤ first) :
    LowerSegment origin input later before after := by
  obtain ⟨states,head,last,chain,lower⟩:=actual
  exact ⟨states,head,last,chain,fun state member=>bound.trans (lower state member)⟩

theorem LowerSegment.singleton (origin low : ℕ) (input : List Cell) (state : State)
    (lower : low ≤ state.pc) : LowerSegment origin input low state state :=
  ⟨[state],rfl,rfl,.singleton state,fun later member=>by
    have same:=List.mem_singleton.mp member
    subst later
    exact lower⟩

theorem label_lower (origin : ℕ) (label : Label) : origin ≤ labelAddress origin label :=
  Nat.le_add_right _ _

/-- A straight body retains every actual literal prefix; then the real
control instruction is appended. The scope is proved on that one trace. -/
theorem block_lower (origin low : ℕ) (label : Label) (input : List Cell)
    (before middle after : State) (position : before.pc=labelAddress origin label)
    (executed : linearExecute input (basicBlock label).body before=some middle)
    (controlled : (controlInstruction origin (basicBlock label).control).execute input middle=some after)
    (bodyLow : low ≤ labelAddress origin label) (afterLow : low ≤ after.pc) :
    LowerSegment origin input low before after := by
  obtain ⟨body,head,last,_length,chain,middlePC,_cost,prefixes⟩:=
    kernel_body_trace origin label input before middle position executed
  have bodyLower : ∀ state∈body, low ≤ state.pc := by
    intro state member
    have split:=List.dropLast_append_getLast? middle (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,inside,run⟩:=prefixes state proper
      have prefixStraight : StraightCode ((basicBlock label).body.take count):=
        fun instruction found=>basicBlock_straight label instruction (List.mem_of_mem_take found)
      have pc:=linearExecute_pc input _ prefixStraight before state run
      rw [List.length_take,Nat.min_eq_left inside.le] at pc
      omega
    · have same:=List.mem_singleton.mp terminal
      subst state
      omega
  have next : step (locatedBlock origin (kernel origin)) input middle=some after := by
    rw [kernel_control_step origin label input middle middlePC]
    exact controlled
  have joined:=chain_append_control (locatedBlock origin (kernel origin)) input body middle after chain last next
  have nonempty : body≠[]:=by intro empty;rw [empty] at head;cases head
  refine ⟨body++[after],?_,by simp,joined.1,?_⟩
  · simpa only [List.head?_append_of_ne_nil body nonempty] using head
  · intro state member
    rcases List.mem_append.mp member with earlier|terminal
    · exact bodyLower state earlier
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact afterLow

theorem block_go_lower (origin low : ℕ) (label target : Label) (input : List Cell)
    (before middle : State) (position : before.pc=labelAddress origin label)
    (executed : linearExecute input (basicBlock label).body before=some middle)
    (control : (basicBlock label).control=.go target)
    (bodyLow : low ≤ labelAddress origin label) (targetLow : low ≤ labelAddress origin target) :
    LowerSegment origin input low before {middle with pc:=labelAddress origin target} := by
  apply block_lower origin low label input before middle _ position executed _ bodyLow targetLow
  simp only [control,controlInstruction,Instruction.execute]
  rfl

/-- Consume the actual closed row trace and interpret only its physical
PC provenance. No numerical row producer is repeated or replaced. -/
theorem row_lower {origin base low : ℕ} {input : List Cell} {region : Finset ℕ}
    {Good : State→Prop} {before after : State} {cost : ℕ}
    (actual : PDROC.CalibrationRow.SafeSegment origin base region input Good before after cost)
    (interpreted : ∀ state, Good state → low ≤ state.pc) :
    LowerSegment origin input low before after := by
  obtain ⟨states,head,last,chain,_time,properties⟩:=actual
  exact ⟨states,head,last,chain,fun state member=>interpreted state (properties state member).2.2.2.2⟩

end PDCompute.CorePreludePC
