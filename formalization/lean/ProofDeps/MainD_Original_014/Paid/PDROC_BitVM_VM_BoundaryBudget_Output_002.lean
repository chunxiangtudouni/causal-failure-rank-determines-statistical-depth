module
public import Paid.PDROC_BitVM_VM_BoundaryBudget_History_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
@[expose] public section
namespace PDROC.BitVM.VM.BoundaryBudget
open PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Log

theorem execute_output_same (input : List Cell) (instruction : Instruction) (before after : State)
    (notOutput : ∀ source,instruction≠.output source)
    (executed : instruction.execute input before=some after) : after.output=before.output := by
  cases instruction with
  | output source => exact False.elim (notOutput source rfl)
  | constant target value | move target source | loadInput target pointer
  | load target pointer | store pointer source | release pointer
  | natOp operation target left right | ratOp operation target left right
  | natCompare comparison target left right | ratCompare comparison target left right
  | natToRat target source | numeratorAbs target source | denominator target source
  | negative target source | branchZero test yes no | jump destination
  | jumpIndirect source | halt =>
    simp only [Instruction.execute,State.set,Option.bind_eq_bind,Option.bind_eq_some_iff] at executed
    grind

theorem execute_output_growth (input : List Cell) (instruction : Instruction) (before after : State)
    (executed : instruction.execute input before=some after) :
    after.output.length≤before.output.length+1 := by
  by_cases emits : ∃ source,instruction=.output source
  · obtain ⟨source,rfl⟩:=emits
    change some ({before with pc:=before.pc+1,output:=before.output++[before.register source]} : State)=some after at executed
    have same:=Option.some.inj executed
    subst after
    simpa only [List.length_append,List.length_singleton] using (le_refl (before.output.length+1))
  · have same:=execute_output_same input instruction before after
      (fun source equal=>emits ⟨source,equal⟩) executed
    rw [same]
    omega

theorem step_output_growth (program : Program) (input : List Cell) (before after : State)
    (executed : step program input before=some after) : after.output.length≤before.output.length+1 := by
  simp only [step,Option.bind_eq_bind,Option.bind_eq_some_iff] at executed
  obtain ⟨instruction,_fetched,actual⟩:=executed
  exact execute_output_growth input instruction before after actual

theorem step_cost_positive (program : Program) (input : List Cell) (before after : State)
    (executed : step program input before=some after) :
    1≤(((program[before.pc]?).map Instruction.primitives).getD []).length := by
  simp only [step,Option.bind_eq_bind,Option.bind_eq_some_iff] at executed
  obtain ⟨instruction,fetched,_actual⟩:=executed
  simp only [fetched,Option.map_some,Option.getD_some,Instruction.primitives,
    List.length_append,List.length_replicate,List.length_cons,List.length_nil]
  omega

/-- At most one physical source output cell per actual successful RAM
transition. No output tape count is supplied as an external certificate. -/
theorem chain_output_count (program : Program) (input : List Cell) (before : State) (rest : List State)
    (chain : (before::rest).IsChain (fun a b=>step program input a=some b)) :
    ∀ current∈before::rest,current.output.length≤before.output.length+time program (before::rest) := by
  induction rest generalizing before with
  | nil =>
    intro current member
    have same:=List.mem_singleton.mp member
    subst current
    omega
  | cons next rest ih =>
    have edge:=(List.isChain_cons_cons.mp chain).1
    have growth:=step_output_growth program input before next edge
    have charged:=step_cost_positive program input before next edge
    have later:=ih next chain.tail
    have decomposition : time program (before::next::rest)=
        (((program[before.pc]?).map Instruction.primitives).getD []).length+time program (next::rest) := by
      simp only [time,primitiveTrace,List.flatMap_cons,List.length_append]
    intro current member
    rcases List.mem_cons.mp member with same|inRest
    · subst current
      omega
    · have bound:=later current inRest
      omega

theorem initial_output_count (program : Program) (input : List Cell) (states : List State) (total : ℕ)
    (head : states.head?=some initial)
    (chain : states.IsChain (fun a b=>step program input a=some b))
    (clock : time program states≤total) : ∀ current∈states,current.output.length≤total := by
  cases states with
  | nil => simp at head
  | cons before rest =>
    have same : before=initial:=Option.some.inj head
    subst before
    have bounded:=chain_output_count program input initial rest chain
    intro current member
    have bound:=bounded current member
    simp only [initial,List.length_nil,Nat.zero_add] at bound
    exact bound.trans clock

theorem output_cell_bits (current : State) (budget : ℕ)
    (allBits : ∀ size∈stateCellBits current,size≤budget) (cell : Cell) (member : cell∈current.output) :
    cell.bits≤budget := by
  apply allBits
  have included : cell.bits∈current.output.map Cell.bits:=List.mem_map.mpr ⟨cell,member,rfl⟩
  simp only [stateCellBits,List.mem_append]
  exact Or.inl (Or.inr included)

theorem encoded_cells_length (cells : List Cell) (budget : ℕ)
    (bounded : ∀ cell∈cells,cell.bits≤budget) :
    (cells.flatMap encodeCellBits).length≤cells.length*(2*budget) := by
  induction cells with
  | nil => simp
  | cons cell rest ih =>
    have first:=(cell_word_length cell).trans (Nat.mul_le_mul_left 2 (bounded cell (by simp)))
    have later:=ih (by intro value member;exact bounded value (List.mem_cons_of_mem cell member))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith

/-- Every opcode boundary in the SAME original RAM run has at most T
output ticks and at most2BT output bits, all derived from time/peak bits. -/
theorem runs_output_bounds (program : Program) (input : List Cell) (states : List State) (final : State)
    (run : Runs program input states final) (budget total : ℕ)
    (peak : peakOperandBits states≤budget) (clock : time program states≤total) :
    ∀ current∈states,current.output.length≤total ∧
      (∀ cell∈current.output,cell.bits≤budget) ∧
      (current.output.flatMap encodeCellBits).length≤total*(2*budget) := by
  have counts:=initial_output_count program input states total run.1 run.2.1 clock
  have bits:=state_bits_of_peak states budget peak
  intro current member
  have each : ∀ cell∈current.output,cell.bits≤budget :=output_cell_bits current budget (bits current member)
  exact ⟨counts current member,each,(encoded_cells_length current.output budget each).trans
    (Nat.mul_le_mul_right _ (counts current member))⟩

end PDROC.BitVM.VM.BoundaryBudget
