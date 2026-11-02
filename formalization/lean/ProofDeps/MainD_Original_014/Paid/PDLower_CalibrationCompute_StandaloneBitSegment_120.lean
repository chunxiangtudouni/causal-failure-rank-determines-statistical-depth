module

public import Paid.PDLower_CalibrationCompute_BitEmbedding_101
public import Paid.PDLower_CalibrationCompute_IOPrefix_090

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid.Computation PDMenu.ComputeFrame RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

def StandaloneBitSegment (input : List Cell) (before after : State) (timeBudget bitBudget : ℕ) : Prop :=
  ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
    trace.IsChain (fun a b => step calibrate input a=some b) ∧ time calibrate trace≤timeBudget ∧
    ∀ state∈trace,SafeBits state bitBudget

theorem StandaloneBitSegment.final {input : List Cell} {before after : State} {timeBudget bitBudget : ℕ}
    (actual : StandaloneBitSegment input before after timeBudget bitBudget) : SafeBits after bitBudget := by
  obtain ⟨trace,_head,last,_chain,_cost,states⟩ := actual
  exact states after (List.mem_of_getLast? last)

theorem StandaloneBitSegment.toSegment {input : List Cell} {before after : State} {timeBudget bitBudget : ℕ}
    (actual : StandaloneBitSegment input before after timeBudget bitBudget) : StandaloneSegment input before after timeBudget := by
  obtain ⟨trace,head,last,chain,cost,_states⟩ := actual
  exact ⟨trace,head,last,chain,cost⟩

theorem StandaloneBitSegment.mono {input : List Cell} {before after : State} {first later bitBudget : ℕ}
    (actual : StandaloneBitSegment input before after first bitBudget) (bounded : first≤later) :
    StandaloneBitSegment input before after later bitBudget := by
  obtain ⟨trace,head,last,chain,cost,states⟩ := actual
  exact ⟨trace,head,last,chain,cost.trans bounded,states⟩

theorem StandaloneBitSegment.trans {input : List Cell} {before middle after : State} {first later bitBudget : ℕ}
    (earlier : StandaloneBitSegment input before middle first bitBudget)
    (following : StandaloneBitSegment input middle after later bitBudget) :
    StandaloneBitSegment input before after (first+later) bitBudget := by
  obtain ⟨left,lh,ll,lc,lt,ls⟩ := earlier
  obtain ⟨right,rh,rl,rc,rt,rs⟩ := following
  have joined := joinTrace_spec calibrate input left right before middle after first later lh ll rh rl lc rc lt rt
  exact ⟨joinTrace left right,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    PDCompute.Pack.joinTrace_invariant left right (fun state => SafeBits state bitBudget) ls rs⟩

theorem standalone_bits_oneStep (input : List Cell) (before after : State) (budget : ℕ)
    (actual : step calibrate input before=some after) (safe : SafeBits before budget) (last : SafeBits after budget) :
    StandaloneBitSegment input before after 30 budget := by
  refine ⟨[before,after],rfl,rfl,?_,?_,?_⟩
  · simpa only [List.isChain_cons_cons,List.isChain_singleton,and_true] using actual
  · exact (time_le_length calibrate [before,after]).trans (by simp only [List.length_cons,List.length_nil];omega)
  · intro state member
    rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using member : state=before∨state=after) with first|second
    · simpa only [first] using safe
    · simpa only [second] using last

theorem standalone_bits_linear (input : List Cell) (code : List Instruction) (before after : State) (budget : ℕ)
    (straight : StraightCode code) (fetched : FetchesCode calibrate before.pc code)
    (actual : linearExecute input code before=some after) (prefixes : PrefixSafe input code before budget) :
    StandaloneBitSegment input before after (15*(code.length+1)) budget := by
  exact PDCompute.Pack.linearExecute_trace_invariant calibrate input code straight before after fetched actual
    (fun state => SafeBits state budget) (fun count _ state executed => prefixes count state executed)

/-- Actual fetched straight-line body followed by its actual jump.
Both portions use the same caller budget and the same produced trace. -/
theorem standalone_bits_linearControl (input : List Cell) (code : List Instruction) (before middle after : State) (budget : ℕ)
    (straight : StraightCode code) (fetched : FetchesCode calibrate before.pc code)
    (actual : linearExecute input code before=some middle) (prefixes : PrefixSafe input code before budget)
    (control : step calibrate input middle=some after) (lastSafe : SafeBits after budget) :
    StandaloneBitSegment input before after (15*(code.length+1)+15) budget := by
  obtain ⟨trace,head,last,chain,cost,states⟩ := standalone_bits_linear input code before middle budget straight fetched actual prefixes
  have joined := chain_append_control calibrate input trace middle after chain last control
  refine ⟨trace++[after],?_,?_,joined.1,joined.2.trans (Nat.add_le_add_right cost 15),?_⟩
  · cases trace with
    | nil => cases head
    | cons first rest => exact head
  · simp only [List.getLast?_append_cons,List.getLast?_singleton]
  · intro state member
    rcases List.mem_append.mp member with prior|finalState
    · exact states state prior
    · have equal := List.mem_singleton.mp finalState
      simpa only [equal] using lastSafe

end PDLower.CalibrationCompute
