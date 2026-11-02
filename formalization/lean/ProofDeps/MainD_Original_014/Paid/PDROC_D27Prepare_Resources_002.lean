module

public import Paid.PDROC_D27Prepare_Resources_001
public import Paid.PDMenu_ComputeFrame_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits

namespace PDROC.D27Prepare.Resources

theorem foldl_max_le (values : List ℕ) (start bound : ℕ) (hstart : start ≤ bound)
    (hvalues : ∀ value ∈ values, value ≤ bound) : values.foldl max start ≤ bound := by
  induction values generalizing start with
  | nil => exact hstart
  | cons value values ih =>
      apply ih (max start value) (max_le hstart (hvalues value (by simp)))
      intro other member
      exact hvalues other (by simp only [List.mem_cons]; exact Or.inr member)

theorem peakCells_le_of_states (trace : List State) (bound : ℕ)
    (h : ∀ state ∈ trace, workingCells state ≤ bound) : peakCells trace ≤ bound := by
  apply foldl_max_le _ 0 bound (Nat.zero_le _)
  intro value member
  obtain ⟨state, hs, rfl⟩ := List.mem_map.mp member
  exact h state hs

theorem peakOperandBits_le_of_states (trace : List State) (bound : ℕ)
    (h : ∀ state ∈ trace, ∀ bits ∈ stateCellBits state, bits ≤ bound) :
    peakOperandBits trace ≤ bound := by
  apply foldl_max_le _ 0 bound (Nat.zero_le _)
  intro bits member
  obtain ⟨state, hs, hb⟩ := List.mem_flatMap.mp member
  exact h state hs bits hb

theorem workingCells_le_of_region (state : State) (heapBound outputBound : ℕ)
    (heap : state.live ⊆ Finset.range heapBound) (output : state.output.length ≤ outputBound) :
    workingCells state ≤ heapBound + 7 + outputBound := by
  have hc := Finset.card_le_card heap
  simp only [Finset.card_range] at hc
  change state.live.card + 7 + state.output.length ≤ _
  omega

theorem stateCellBits_le (state : State) (heapBound pcBound bound : ℕ)
    (heap : state.live ⊆ Finset.range heapBound) (pc : state.pc ≤ pcBound)
    (registers : ∀ register, (state.register register).bits ≤ bound)
    (heapValues : ∀ address ∈ state.live, (state.heap address).bits ≤ bound)
    (outputs : ∀ cell ∈ state.output, cell.bits ≤ bound)
    (addressBits : natBits heapBound ≤ bound) (pcBits : natBits pcBound ≤ bound) :
    ∀ bits ∈ stateCellBits state, bits ≤ bound := by
  intro bits member
  simp only [stateCellBits, List.append_assoc, List.mem_append] at member
  rcases member with hr | hh | ho | hp
  · obtain ⟨register, _, rfl⟩ := List.mem_map.mp hr
    exact registers register
  · obtain ⟨address, ha, hb⟩ := List.mem_flatMap.mp hh
    have live : address ∈ state.live := Finset.mem_toList.mp ha
    have inside : address < heapBound := Finset.mem_range.mp (heap live)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact (natBits_mono inside.le).trans addressBits
    · exact heapValues address live
  · obtain ⟨cell, hc, rfl⟩ := List.mem_map.mp ho
    exact outputs cell hc
  · have same := List.mem_singleton.mp hp
    subst bits
    exact (natBits_mono pc).trans pcBits

/-- Every state of a genuine successful original Runs has an in-range
actual instruction fetch, including the final fetched halt. -/
theorem chain_pc_lt (program : Program) (input : List Cell) :
    ∀ (trace : List State) (final : State),
      trace.IsChain (fun before after => step program input before = some after) →
      trace.getLast? = some final → program[final.pc]? = some .halt →
      ∀ state ∈ trace, state.pc < program.size := by
  intro trace
  induction trace with
  | nil => intro _ _ _ _ state member; cases member
  | cons before tail ih =>
      intro final chain last halt state member
      cases tail with
      | nil =>
          have same : before = final := Option.some.inj last
          have stateSame : state = before := List.mem_singleton.mp member
          subst state
          subst final
          obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp halt
          exact inside
      | cons after rest =>
          have parts := List.isChain_cons_cons.mp chain
          rcases List.mem_cons.mp member with same | member
          · subst state
            have actualStep := parts.1
            unfold step at actualStep
            obtain ⟨instruction, fetch, _⟩ := Option.bind_eq_some_iff.mp actualStep
            obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp fetch
            exact inside
          · apply ih final parts.2 _ halt state member
            simpa only [List.getLast?_cons_cons] using last

theorem runs_pc_lt (program : Program) (input : List Cell) (trace : List State) (final : State)
    (run : Runs program input trace final) : ∀ state ∈ trace, state.pc < program.size :=
  chain_pc_lt program input trace final run.2.1 run.2.2.1 run.2.2.2.1

/-- A conditional composition lemma about the REAL trace, not a host
label/time claim. The concrete preparation proof must derive each stated
state/length invariant from its actual original Runs. -/
theorem actual_trace_resources (program : Program) (input : List Cell) (trace : List State) (final : State)
    (run : Runs program input trace final) (lengthBound heapBound outputBound valueBits : ℕ)
    (length : trace.length ≤ lengthBound)
    (heap : ∀ state ∈ trace, state.live ⊆ Finset.range heapBound)
    (output : ∀ state ∈ trace, state.output.length ≤ outputBound)
    (registers : ∀ state ∈ trace, ∀ register, (state.register register).bits ≤ valueBits)
    (heapValues : ∀ state ∈ trace, ∀ address ∈ state.live, (state.heap address).bits ≤ valueBits)
    (outputs : ∀ state ∈ trace, ∀ cell ∈ state.output, cell.bits ≤ valueBits) :
    time program trace ≤ 15 * lengthBound ∧
      peakCells trace ≤ heapBound + 7 + outputBound ∧
      peakOperandBits trace ≤ valueBits + natBits heapBound + natBits program.size := by
  refine ⟨(PDMenu.ComputeFrame.time_le_length program trace).trans (Nat.mul_le_mul_left 15 length), ?_, ?_⟩
  · exact peakCells_le_of_states trace _ (fun state hs => workingCells_le_of_region state heapBound outputBound
      (heap state hs) (output state hs))
  · apply peakOperandBits_le_of_states
    intro state hs
    apply stateCellBits_le state heapBound program.size
      (valueBits + natBits heapBound + natBits program.size) (heap state hs) (runs_pc_lt program input trace final run state hs).le
    · intro register
      have h := registers state hs register
      omega
    · intro address live
      have h := heapValues state hs address live
      omega
    · intro cell member
      have h := outputs state hs cell member
      omega
    · omega
    · omega

theorem fixed_prepare_trace_resources (program : Program) (input : List Cell) (trace : List State) (final : State)
    (run : Runs program input trace final) (code : program.size = 11776) (lengthBound valueBits : ℕ)
    (length : trace.length ≤ lengthBound)
    (heap : ∀ state ∈ trace, state.live ⊆ Finset.range 64)
    (output : ∀ state ∈ trace, state.output.length ≤ 13)
    (registers : ∀ state ∈ trace, ∀ register, (state.register register).bits ≤ valueBits)
    (heapValues : ∀ state ∈ trace, ∀ address ∈ state.live, (state.heap address).bits ≤ valueBits)
    (outputs : ∀ state ∈ trace, ∀ cell ∈ state.output, cell.bits ≤ valueBits) :
    time program trace ≤ 15 * lengthBound ∧ peakCells trace ≤ 84 ∧ peakOperandBits trace ≤ valueBits + 21 := by
  have h := actual_trace_resources program input trace final run lengthBound 64 13 valueBits length heap output registers heapValues outputs
  simpa only [code, natBits, show Nat.log2 64 = 6 by decide, show Nat.log2 11776 = 13 by decide,
    Nat.reduceAdd] using h

end PDROC.D27Prepare.Resources
