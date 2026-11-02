module

public import Paid.PDROC_D27Prepare_Assembly_006
public import Paid.RootD27Core_Arguments_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

def rawPreparePrefix : List Instruction :=
  PDROC.D27Prepare.Program.program.toList.take (PDROC.D27Prepare.Program.pc 45)

def rawSpliceProgram (continuation : List Instruction) : Program :=
  (rawPreparePrefix++continuation).toArray

theorem rawPreparePrefix_length :
    rawPreparePrefix.length=PDROC.D27Prepare.Program.pc 45 := by
  apply List.length_take_of_le
  simp only [Array.length_toList,PDROC.D27Prepare.Program.program_size]
  change 11520≤11776
  decide

theorem rawSplice_before_cut (continuation : List Instruction) (address : ℕ)
    (below : address<PDROC.D27Prepare.Program.pc 45) :
    PDROC.D27Prepare.Program.program[address]?=(rawSpliceProgram continuation)[address]? := by
  simp only [rawSpliceProgram,List.getElem?_toArray]
  rw [List.getElem?_append_left (by simpa only [rawPreparePrefix_length] using below)]
  simp only [rawPreparePrefix,List.getElem?_take_of_lt below,Array.getElem?_toList]

theorem rawSplice_continuation (continuation : List Instruction) :
    FetchesCode (rawSpliceProgram continuation) (PDROC.D27Prepare.Program.pc 45) continuation := by
  intro offset _
  simp only [rawSpliceProgram,List.getElem?_toArray]
  rw [List.getElem?_append_right (by rw [rawPreparePrefix_length]; omega),rawPreparePrefix_length]
  simp only [Nat.add_sub_cancel_left]

/-- Transport a true execution with the SAME original readonly input.
Only genuinely executed states require matching code; the returned state
will fetch and execute the new continuation. -/
theorem chain_same_input_of_fetch (oldProgram newProgram : Program) (input : List Cell) :
    ∀ trace : List State,
      (∀ state∈trace.dropLast,oldProgram[state.pc]?=newProgram[state.pc]?) →
      trace.IsChain (fun before after => step oldProgram input before=some after) →
      trace.IsChain (fun before after => step newProgram input before=some after) := by
  intro trace
  induction trace with
  | nil => intro _ _; exact .nil
  | cons before tail ih =>
    intro fetched chain
    cases tail with
    | nil => exact .singleton before
    | cons middle rest =>
      have parts := List.isChain_cons_cons.mp chain
      have member : before∈(before::middle::rest).dropLast := by simp
      apply List.isChain_cons_cons.mpr
      refine ⟨?_,ih ?_ parts.2⟩
      · rw [←step_eq_of_fetch_eq oldProgram newProgram input before (fetched before member)]
        exact parts.1
      · intro state inside
        exact fetched state (by simp only [List.dropLast_cons_cons,List.mem_cons]; exact Or.inr inside)

theorem preparedMemory_heapList (P : Parameters) (fee : ℚ) (state : State)
    (prepared : PDROC.D27Prepare.Assembly.PreparedMemory P fee state) :
    HeapList state 0 (preparedInput P fee) := by
  apply PDLower.CalibrationCompute.HeapList.of_values
  · intro offset inside
    have bound : offset<13 := inside
    simpa only [Nat.zero_add] using
      PDROC.D27Prepare.Assembly.PreparedMemory.live P fee state prepared offset bound
  · intro offset inside
    have lookup := (prepared offset _ (List.getElem?_eq_getElem inside)).2
    simpa only [Nat.zero_add] using lookup

/-- The full original raw preprocessor reaches its actual live heap in
the literal core-spliced program. Scratch, registers, readonly input and
output are unchanged. The new arrival fetch is explicitly charged by15;
executed-prefix primitive cost is exactly the old one. -/
theorem raw_splice_preFinal_certificate (continuation : List Instruction) :
    ∃ C degree : ℕ,0<C ∧ ∀ (P : Parameters) (fee : ℚ),
      ∃ final : State,∃ trace : List State,
        PDROC.D27Prepare.Assembly.PreFinalState P fee final ∧
        trace.head?=some initial ∧ trace.getLast?=some final ∧
        trace.IsChain (fun before after => step (rawSpliceProgram continuation) (rawInput P fee) before=some after) ∧
        time (rawSpliceProgram continuation) trace≤C*(variableGammaSize P fee)^degree+15 ∧
        peakCells trace≤C*(variableGammaSize P fee)^degree ∧
        peakOperandBits trace≤C*(variableGammaSize P fee)^degree ∧
        time (rawSpliceProgram continuation) trace.dropLast=
          time PDROC.D27Prepare.Program.program trace.dropLast ∧
        HeapList final 0 (preparedInput P fee) := by
  obtain ⟨C,degree,positive,actual⟩ := PDROC.D27Prepare.Assembly.raw_preFinal_certificate
  refine ⟨C,degree,positive,?_⟩
  intro P fee
  obtain ⟨final,trace,ready,head,last,chain,_,_,scope,cost,cells,bits⟩ := actual P fee
  have fetched : ∀ state∈trace.dropLast,
      PDROC.D27Prepare.Program.program[state.pc]?=(rawSpliceProgram continuation)[state.pc]? :=
    fun state member => rawSplice_before_cut continuation state.pc (scope state member)
  have chain' := chain_same_input_of_fetch _ _ (rawInput P fee) trace fetched chain
  have cost' := (time_le_of_dropLast_fetch_eq _ _ trace fetched).trans (Nat.add_le_add_right cost 15)
  have executedCost := PDROC.D27Prepare.Prefix.preFinal_executed_time_eq
    (rawSpliceProgram continuation) (rawInput P fee) (rawSplice_before_cut continuation)
      trace final chain last ready.location
  exact ⟨final,trace,ready,head,last,chain',cost',cells,bits,executedCost.symm,
    preparedMemory_heapList P fee final ready.cells⟩

end RootD27.Core
