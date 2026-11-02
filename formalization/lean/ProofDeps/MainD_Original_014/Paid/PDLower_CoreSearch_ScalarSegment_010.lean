module

public import Paid.PDLower_CoreSearch_TargetMemory_001
public import Paid.PDMenu_ComputeFrame_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

/-- A proof object for the SAME actual core fragment trace. The incoming
live/output fields stay exactly the caller's, and heap writes stay13..42.
This is neither a new instruction nor an assumed successful search. -/
def ScalarSegment (program : Program) (input : List Cell) (before after : State) (budget : ℕ) : Prop :=
  ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
    trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤budget ∧
    ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0

theorem ScalarSegment.final {program : Program} {input : List Cell} {before after : State} {budget : ℕ}
    (actual : ScalarSegment program input before after budget) :
    MemoryFrame scalarRegion before after ∧ HeaderMemory before after 0 := by
  obtain ⟨trace,_head,last,_chain,_cost,memory⟩ := actual
  exact memory after (List.mem_of_getLast? last)

theorem ScalarSegment.mono {program : Program} {input : List Cell} {before after : State} {small large : ℕ}
    (actual : ScalarSegment program input before after small) (bounded : small≤large) :
    ScalarSegment program input before after large := by
  obtain ⟨trace,head,last,chain,cost,memory⟩ := actual
  exact ⟨trace,head,last,chain,cost.trans bounded,memory⟩

theorem ScalarSegment.trans {program : Program} {input : List Cell} {before middle after : State} {first later : ℕ}
    (earlier : ScalarSegment program input before middle first) (following : ScalarSegment program input middle after later) :
    ScalarSegment program input before after (first+later) := by
  have middleMemory := earlier.final
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
  · exact ⟨middleMemory.1.trans (rm state next).1,middleMemory.2.trans (rm state next).2⟩

/-- Genuine fetched control instruction. Its actual execute equation,
including a conditional flag read when needed, is supplied by the caller
proof. The produced two-state trace has no storage/output side effect. -/
theorem ScalarSegment.control (program : Program) (input : List Cell) (before : State) (instruction : Instruction) (target : ℕ)
    (fetched : program[before.pc]?=some instruction)
    (executed : instruction.execute input before=some {before with pc:=target}) :
    ScalarSegment program input before {before with pc:=target} 30 := by
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
      exact ⟨MemoryFrame.refl _ _,HeaderMemory.refl _ _⟩
    · subst state
      exact ⟨⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩,HeaderMemory.of_unchanged 0 rfl rfl rfl⟩

end PDLower.CoreSearch
