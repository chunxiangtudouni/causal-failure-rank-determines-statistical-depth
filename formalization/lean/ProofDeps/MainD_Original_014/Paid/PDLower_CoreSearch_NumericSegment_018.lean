module

public import Paid.PDLower_CoreSearch_ScalarSegment_010
public import Paid.PDCompute_SolverSequenceBits_155

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDROC.CalibrationRow.Operand
open PDLower.CalibrationCompute (linearExecute)

namespace PDLower.CoreSearch

/-- Time, physical memory and every original stateCellBits on ONE
actual trace, under the same fixed caller operand budget. -/
def NumericSegment (program : Program) (input : List Cell) (before after : State) (clock budget : ℕ) : Prop :=
  ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
    trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤clock ∧
    ∀ state∈trace,(MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧ RootD27.Bits.SafeBits state budget

theorem NumericSegment.final {program : Program} {input : List Cell} {before after : State} {clock budget : ℕ}
    (actual : NumericSegment program input before after clock budget) :
    (MemoryFrame scalarRegion before after ∧ HeaderMemory before after 0) ∧ RootD27.Bits.SafeBits after budget := by
  obtain ⟨trace,_head,last,_chain,_cost,properties⟩ := actual
  exact properties after (List.mem_of_getLast? last)

theorem NumericSegment.functional {program : Program} {input : List Cell} {before after : State} {clock budget : ℕ}
    (actual : NumericSegment program input before after clock budget) : ScalarSegment program input before after clock := by
  obtain ⟨trace,head,last,chain,cost,properties⟩ := actual
  exact ⟨trace,head,last,chain,cost,fun state member => (properties state member).1⟩

theorem NumericSegment.mono {program : Program} {input : List Cell} {before after : State} {small large budget : ℕ}
    (actual : NumericSegment program input before after small budget) (bounded : small≤large) :
    NumericSegment program input before after large budget := by
  obtain ⟨trace,head,last,chain,cost,properties⟩ := actual
  exact ⟨trace,head,last,chain,cost.trans bounded,properties⟩

theorem NumericSegment.trans {program : Program} {input : List Cell} {before middle after : State} {first later budget : ℕ}
    (earlier : NumericSegment program input before middle first budget) (following : NumericSegment program input middle after later budget) :
    NumericSegment program input before after (first+later) budget := by
  have middleMemory := earlier.final.1
  obtain ⟨left,lh,ll,lc,lt,lm⟩ := earlier
  obtain ⟨right,rh,rl,rc,rt,rm⟩ := following
  have joined := joinTrace_spec program input left right before middle after first later lh ll rh rl lc rc lt rt
  refine ⟨joinTrace left right,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,?_⟩
  have split := List.dropLast_append_getLast? middle (by rw [ll];simp)
  intro state member
  rcases List.mem_append.mp member with prior|next
  · apply lm state
    rw [←split]
    exact List.mem_append.mpr (Or.inl prior)
  · exact ⟨⟨middleMemory.1.trans (rm state next).1.1,middleMemory.2.trans (rm state next).1.2⟩,(rm state next).2⟩

theorem NumericSegment.control (program : Program) (input : List Cell) (before : State) (instruction : Instruction) (target budget : ℕ)
    (fetched : program[before.pc]?=some instruction)
    (executed : instruction.execute input before=some {before with pc:=target})
    (safe : RootD27.Bits.SafeBits before budget) (pcBits : natBits target≤budget) :
    NumericSegment program input before {before with pc:=target} 30 budget := by
  have actual : step program input before=some {before with pc:=target} := by
    unfold step
    rw [fetched]
    exact executed
  refine ⟨[before,{before with pc:=target}],rfl,rfl,?_,?_,?_⟩
  · simpa only [List.isChain_cons_cons,List.isChain_singleton,and_true] using actual
  · exact (time_le_length program [before,{before with pc:=target}]).trans (by simp only [List.length_cons,List.length_nil];omega)
  · intro state member
    rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using member : state=before∨state={before with pc:=target}) with first|last
    · subst state
      exact ⟨⟨MemoryFrame.refl _ _,HeaderMemory.refl _ _⟩,safe⟩
    · subst state
      exact ⟨⟨⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩,HeaderMemory.of_unchanged 0 rfl rfl rfl⟩,safe.withPC target pcBits⟩

/-- The actual old HeaderCommand sequence, sharing the narrow physical
prefix proof001 and frozen same-B ISA/sequence155. Concrete scripts below
discharge bounded from their literal intrinsic arithmetic, not from runs. -/
theorem commands_segment_bits (commands : List HeaderCommand) (program : Program) (input : List Cell) (before : State)
    (values next : ℕ→Cell) (budget : ℕ) (valid : ∀ command∈commands,command.Valid)
    (targets : ∀ command∈commands,commandTarget command∈scalarRegion)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (evaluated : headerEval commands values=some next) (safe : RootD27.Bits.SafeBits before budget)
    (bounded : HeaderEvaluatedBits budget commands values) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+(headerCode commands).length)≤budget)
    (fetched : FetchesCode program before.pc (headerCode commands)) :
    ∃ after : State,NumericSegment program input before after (15*((headerCode commands).length+1)) budget ∧
      Header after 0 next ∧ after.register .fresh=.natural 0 ∧ after.pc=before.pc+(headerCode commands).length ∧
      linearExecute input (headerCode commands) before=some after := by
  obtain ⟨after,run,afterHeader,afterFresh,pc,_frame,_output⟩ :=
    headerCode_realize commands input before 0 0 0 values next valid header fresh evaluated
  have prefixSafe := headerCode_prefix_safe commands input before 0 budget values valid header fresh safe bounded
    (by simpa only [Nat.zero_add] using addressBits) pcBits
  obtain ⟨trace,head,last,chain,cost,prefixes⟩ := linearExecute_trace_time program input (headerCode commands)
    (headerCode_straight commands) before after fetched run
  refine ⟨after,⟨trace,head,last,chain,cost,?_⟩,afterHeader,afterFresh,pc,run⟩
  intro state member
  have split := List.dropLast_append_getLast? after (by rw [last];simp)
  rw [←split] at member
  rcases List.mem_append.mp member with proper|finalState
  · obtain ⟨count,bound,execute⟩ := prefixes state proper
    exact ⟨commands_prefix_scalar_memory commands input before state values next valid targets header fresh evaluated count bound.le execute,
      prefixSafe count state execute⟩
  · have same := List.mem_singleton.mp finalState
    subst state
    exact ⟨commands_prefix_scalar_memory commands input before after values next valid targets header fresh evaluated
      (headerCode commands).length (le_refl _) (by simpa only [List.take_length] using run),prefixSafe.final run⟩

end PDLower.CoreSearch
