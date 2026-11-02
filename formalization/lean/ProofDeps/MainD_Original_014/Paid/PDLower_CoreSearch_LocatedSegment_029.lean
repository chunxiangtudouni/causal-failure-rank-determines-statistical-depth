module

public import Paid.PDLower_CoreSearch_NumericSegment_018
public import Paid.PDCompute_SolverLinearPC_121

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDROC.CalibrationRow.Operand
open PDLower.CalibrationCompute (linearExecute)

namespace PDLower.CoreSearch

/-- ALL resources and closed/proper PC bounds refer to this ONE actual
trace. No independently chosen location witness or terminal-next premise. -/
def LocatedSegment (program : Program) (input : List Cell) (before after : State) (clock budget low high : ℕ) : Prop :=
  ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
    trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤clock ∧
    (∀ state∈trace,((MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧ RootD27.Bits.SafeBits state budget) ∧
      low≤state.pc ∧ state.pc≤high) ∧ ∀ state∈trace.dropLast,state.pc<high

theorem LocatedSegment.numeric {program : Program} {input : List Cell} {before after : State} {clock budget low high : ℕ}
    (actual : LocatedSegment program input before after clock budget low high) : NumericSegment program input before after clock budget := by
  obtain ⟨trace,head,last,chain,cost,properties,_proper⟩ := actual
  exact ⟨trace,head,last,chain,cost,fun state member => (properties state member).1⟩

theorem LocatedSegment.final {program : Program} {input : List Cell} {before after : State} {clock budget low high : ℕ}
    (actual : LocatedSegment program input before after clock budget low high) :
    (MemoryFrame scalarRegion before after ∧ HeaderMemory before after 0) ∧ RootD27.Bits.SafeBits after budget := actual.numeric.final

theorem LocatedSegment.mono {program : Program} {input : List Cell} {before after : State} {small large budget low high : ℕ}
    (actual : LocatedSegment program input before after small budget low high) (bounded : small≤large) :
    LocatedSegment program input before after large budget low high := by
  obtain ⟨trace,head,last,chain,cost,properties,proper⟩ := actual
  exact ⟨trace,head,last,chain,cost.trans bounded,properties,proper⟩

theorem LocatedSegment.trans {program : Program} {input : List Cell} {before middle after : State} {first later budget low high : ℕ}
    (earlier : LocatedSegment program input before middle first budget low high)
    (following : LocatedSegment program input middle after later budget low high) :
    LocatedSegment program input before after (first+later) budget low high := by
  have middleMemory := earlier.final.1
  obtain ⟨left,lh,ll,lc,lt,lm,lp⟩ := earlier
  obtain ⟨right,rh,rl,rc,rt,rm,rp⟩ := following
  have joined := joinTrace_spec program input left right before middle after first later lh ll rh rl lc rc lt rt
  refine ⟨joinTrace left right,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,?_,?_⟩
  · have split := List.dropLast_append_getLast? middle (by rw [ll];simp)
    intro state member
    rcases List.mem_append.mp member with prior|next
    · apply lm state
      rw [←split]
      exact List.mem_append.mpr (Or.inl prior)
    · have followingProperties := rm state next
      exact ⟨⟨⟨middleMemory.1.trans followingProperties.1.1.1,middleMemory.2.trans followingProperties.1.1.2⟩,
        followingProperties.1.2⟩,followingProperties.2⟩
  · have nonempty : right≠[] := by
      intro empty
      rw [empty] at rh
      cases rh
    have split : (joinTrace left right).dropLast=left.dropLast++right.dropLast := by
      unfold joinTrace
      exact List.dropLast_append_of_ne_nil nonempty
    intro state member
    rw [split] at member
    rcases List.mem_append.mp member with prior|next
    · exact lp state prior
    · exact rp state next

theorem LocatedSegment.control (program : Program) (input : List Cell) (before : State) (instruction : Instruction) (target budget : ℕ)
    (fetched : program[before.pc]?=some instruction) (executed : instruction.execute input before=some {before with pc:=target})
    (safe : RootD27.Bits.SafeBits before budget) (pcBits : natBits target≤budget)
    (low high : ℕ) (lower : low≤before.pc) (proper : before.pc<high) (targetLower : low≤target) (targetUpper : target≤high) :
    LocatedSegment program input before {before with pc:=target} 30 budget low high := by
  have actual : step program input before=some {before with pc:=target} := by unfold step;rw [fetched];exact executed
  refine ⟨[before,{before with pc:=target}],rfl,rfl,?_,?_,?_,?_⟩
  · simpa only [List.isChain_cons_cons,List.isChain_singleton,and_true] using actual
  · exact (time_le_length program [before,{before with pc:=target}]).trans (by simp only [List.length_cons,List.length_nil];omega)
  · intro state member
    rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using member : state=before∨state={before with pc:=target}) with first|last
    · subst state
      exact ⟨⟨⟨MemoryFrame.refl _ _,HeaderMemory.refl _ _⟩,safe⟩,lower,proper.le⟩
    · subst state
      exact ⟨⟨⟨⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩,HeaderMemory.of_unchanged 0 rfl rfl rfl⟩,
        safe.withPC target pcBits⟩,targetLower,targetUpper⟩
  · intro state member
    have same : state=before := by simpa only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] using member
    subst state
    exact proper

/-- Reuse frozen121's successful-prefix witnesses and actual PC facts.
All physical and numerical facts are proved ON THOSE SAME states. -/
theorem LocatedSegment.linear (program : Program) (input : List Cell) (code : List Instruction) (before after : State) (budget : ℕ)
    (straight : StraightCode code) (fetched : FetchesCode program before.pc code) (run : linearExecute input code before=some after)
    (memory : ∀ count≤code.length,∀ state,linearExecute input (code.take count) before=some state →
      MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0)
    (safe : PrefixSafe input code before budget) (low high : ℕ) (lower : low≤before.pc) (upper : before.pc+code.length≤high) :
    LocatedSegment program input before after (15*(code.length+1)) budget low high := by
  obtain ⟨trace,head,last,chain,cost,prefixes,location⟩ := linearExecute_trace_closedPC program input code straight before after fetched run
  refine ⟨trace,head,last,chain,cost,?_,?_⟩
  · intro state member
    have stateLocation := location state member
    have properties : (MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧ RootD27.Bits.SafeBits state budget := by
      have split := List.dropLast_append_getLast? after (by rw [last];simp)
      rw [←split] at member
      rcases List.mem_append.mp member with proper|terminal
      · obtain ⟨count,bounded,executed⟩ := prefixes state proper
        exact ⟨memory count bounded.le state executed,safe count state executed⟩
      · have same := List.mem_singleton.mp terminal
        subst state
        exact ⟨memory code.length (le_refl _) after (by simpa only [List.take_length] using run),safe.final run⟩
    exact ⟨properties,by omega,by omega⟩
  · intro state member
    obtain ⟨count,bounded,executed⟩ := prefixes state member
    have prefixStraight : StraightCode (code.take count) := fun instruction inside => straight instruction (List.mem_of_mem_take inside)
    have position := linearExecute_pc input (code.take count) prefixStraight before state executed
    rw [List.length_take,Nat.min_eq_left bounded.le] at position
    omega

theorem LocatedSegment.commands (commands : List HeaderCommand) (program : Program) (input : List Cell) (before : State)
    (values next : ℕ→Cell) (budget : ℕ) (valid : ∀ command∈commands,command.Valid)
    (targets : ∀ command∈commands,commandTarget command∈scalarRegion)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (evaluated : headerEval commands values=some next) (safe : RootD27.Bits.SafeBits before budget)
    (bounded : HeaderEvaluatedBits budget commands values) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+(headerCode commands).length)≤budget)
    (fetched : FetchesCode program before.pc (headerCode commands))
    (low high : ℕ) (lower : low≤before.pc) (upper : before.pc+(headerCode commands).length≤high) :
    ∃ after : State,LocatedSegment program input before after (15*((headerCode commands).length+1)) budget low high ∧
      Header after 0 next ∧ after.register .fresh=.natural 0 ∧ after.pc=before.pc+(headerCode commands).length ∧
      linearExecute input (headerCode commands) before=some after := by
  obtain ⟨after,run,afterHeader,afterFresh,pc,_frame,_output⟩ := headerCode_realize commands input before 0 0 0 values next valid header fresh evaluated
  have prefixSafe := headerCode_prefix_safe commands input before 0 budget values valid header fresh safe bounded
    (by simpa only [Nat.zero_add] using addressBits) pcBits
  have actual := LocatedSegment.linear program input (headerCode commands) before after budget (headerCode_straight commands) fetched run
    (fun count bounded state executed => commands_prefix_scalar_memory commands input before state values next valid targets header fresh evaluated count bounded executed)
    prefixSafe low high lower upper
  exact ⟨after,actual,afterHeader,afterFresh,pc,run⟩

end PDLower.CoreSearch
