module
public import Paid.PDROC_BitVM_VM_BoundaryBudget_Output_002
public import Paid.PDROC_BitVM_VM_Source_Representation_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
@[expose] public section
namespace PDROC.BitVM.VM.BoundaryBudget
open PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Log
open PDROC.BitVM.Kernel.RegisterGlobal (Stack registerSlot registerSlot_bounds)
open scoped BigOperators

theorem bank_word_length (input : List Cell) (field : Fin 13) (inputSize : ℕ)
    (bounded : (encodeBits input).length ≤ inputSize) :
    (BankMount.bankWords input field).length ≤ inputSize := by
  unfold BankMount.bankWords
  cases found : input[field.val]? with
  | none  =>  simp only [Option.map_none,Option.getD_none,List.length_nil];exact Nat.zero_le _
  | some value  => 
    simp only [Option.map_some,Option.getD_some]
    exact (InputLoad.input_cell_length input field.val value found).trans bounded

theorem register_cover (role : Stack) (lower : 14 ≤ role.val) (upper : role.val ≤ 20) :
    ∃ reg : Register,registerSlot reg=role := by
  have possibilities : role.val=14 ∨ role.val=15 ∨ role.val=16 ∨ role.val=17 ∨
      role.val=18 ∨ role.val=19 ∨ role.val=20 := by omega
  rcases possibilities with equal|equal|equal|equal|equal|equal|equal
  · refine ⟨.address,Fin.ext ?_⟩;change 14=role.val;exact equal.symm
  · refine ⟨.index,Fin.ext ?_⟩;change 15=role.val;exact equal.symm
  · refine ⟨.value,Fin.ext ?_⟩;change 16=role.val;exact equal.symm
  · refine ⟨.total,Fin.ext ?_⟩;change 17=role.val;exact equal.symm
  · refine ⟨.old,Fin.ext ?_⟩;change 18=role.val;exact equal.symm
  · refine ⟨.fresh,Fin.ext ?_⟩;change 19=role.val;exact equal.symm
  · refine ⟨.flag,Fin.ext ?_⟩;change 20=role.val;exact equal.symm

def boundaryBudget (inputSize total budget : ℕ) : ℕ :=
  128*(inputSize+(total+1)*(budget+1)+1)

/-- Arithmetic aggregation for a genuine canonical boundary. History,
output and input bounds below are INTERNAL components; the public RAM
run theorem immediately derives every one from the actual same trace.
Scratch emptiness is consumed ONLY from actual Ready.workspace. -/
theorem canonical_dataSize (input : List Cell) (current : State) (events : List HeapEvent)
    (contents : Stack → List Bool) (inputSize total budget : ℕ)
    (represented : PDROC.BitVM.VM.Source.Ready input current events contents)
    (allBits : ∀ size ∈ stateCellBits current,size ≤ budget)
    (inputBound : (encodeBits input).length ≤ inputSize)
    (historyBound : (encodeHistory events).length ≤ total*(4*budget+2))
    (outputCount : current.output.length ≤ total)
    (outputBound : (current.output.flatMap encodeCellBits).length ≤ total*(2*budget)) :
    (∑ role : Stack,(contents role).length) ≤ boundaryBudget inputSize total budget := by
  let observable:=represented.toObservables
  let wordCap:=inputSize+4*(total+1)*(budget+1)+1
  have nonnegative : 0 ≤ total*budget:=Nat.zero_le _
  have bankCap : inputSize ≤ wordCap := by unfold wordCap;omega
  have registerCap : 2*budget ≤ wordCap := by unfold wordCap;nlinarith
  have heapCap : total*(4*budget+2) ≤ wordCap := by unfold wordCap;nlinarith
  have outputCap : total*(2*budget) ≤ wordCap := by unfold wordCap;nlinarith
  have ticksCap : total ≤ wordCap := by unfold wordCap;nlinarith
  have each : ∀ role : Stack,(contents role).length ≤ wordCap := by
    intro role
    by_cases zero : role.val=0
    · rw [represented.workspace role (Or.inl zero)]
      exact Nat.zero_le _
    by_cases bank : role.val ≤ 13
    · let field : Fin 13:=⟨role.val-1,by omega⟩
      have same : BankDrain.bankSlot field=role := by
        apply Fin.ext
        change role.val-1+1=role.val
        omega
      rw [←same,observable.bank field]
      exact (bank_word_length input field inputSize inputBound).trans bankCap
    by_cases register : role.val ≤ 20
    · obtain ⟨reg,same⟩:=register_cover role (by omega) register
      rw [←same,observable.registers reg]
      exact ((cell_word_length _).trans (Nat.mul_le_mul_left 2 (register_bits current budget allBits reg))).trans registerCap
    by_cases heap : role.val=21
    · have same : role=(21 : Stack):=Fin.ext heap
      subst role
      rw [observable.history]
      exact historyBound.trans heapCap
    by_cases output : role.val=22
    · have same : role=(22 : Stack):=Fin.ext output
      subst role
      rw [observable.outputWord,List.length_reverse]
      exact outputBound.trans outputCap
    by_cases ticks : role.val=23
    · have same : role=(23 : Stack):=Fin.ext ticks
      subst role
      rw [observable.outputTicks,List.length_replicate]
      exact outputCount.trans ticksCap
    · rw [represented.workspace role (Or.inr (by omega))]
      exact Nat.zero_le _
  calc
    (∑ role : Stack,(contents role).length) ≤ ∑ _role : Stack,wordCap :=
      Finset.sum_le_sum (fun role _ => each role)
    _=32*wordCap := by simp
    _ ≤ boundaryBudget inputSize total budget := by unfold boundaryBudget wordCap;nlinarith

/-- Every actual original RAM opcode boundary has canonical32 physical
data size bounded by one fixed polynomial in original I,T,B. Its event
history is the DETERMINED actual prefix history from EMPTY, never an
arbitrary redundant Refines history. Output bounds and all cell widths
are derived from the SAME Runs/time/peakOperandBits certificate. -/
theorem runs_boundary_dataSize (program : Program) (input : List Cell) (states : List State) (final : State)
    (run : Runs program input states final) (inputSize total budget : ℕ)
    (inputBound : (encodeBits input).length ≤ inputSize)
    (clock : time program states ≤ total) (peak : peakOperandBits states ≤ budget)
    (index : ℕ) (current : State) (atState : states[index]?=some current)
    (contents : Stack → List Bool)
    (represented : PDROC.BitVM.VM.Source.Ready input current
      (actualHistory program (states.take (index+1))) contents) :
    (∑ role : Stack,(contents role).length) ≤ 128*(inputSize+(total+1)*(budget+1)+1) := by
  obtain ⟨inside,equal⟩:=List.getElem?_eq_some_iff.mp atState
  have member : current ∈ states:=List.mem_iff_getElem.mpr ⟨index,inside,equal⟩
  have history:=actual_prefix_history_bounds program states (index+1) budget total peak clock
  have output:=runs_output_bounds program input states final run budget total peak clock current member
  exact canonical_dataSize input current _ contents inputSize total budget represented
    (state_bits_of_peak states budget peak current member) inputBound history.2.2 output.1 output.2.2

/-- Exact original resource parameters, with no supplied numerical or
run-growth oracle. The represented physical boundary alone is internal. -/
theorem runs_boundary_dataSize_exact (program : Program) (input : List Cell) (states : List State) (final : State)
    (run : Runs program input states final) (index : ℕ) (current : State)
    (atState : states[index]?=some current) (contents : Stack → List Bool)
    (represented : PDROC.BitVM.VM.Source.Ready input current
      (actualHistory program (states.take (index+1))) contents) :
    (∑ role : Stack,(contents role).length) ≤ 128*((encodeBits input).length+
      (time program states+1)*(peakOperandBits states+1)+1) :=
  runs_boundary_dataSize program input states final run _ _ _ (le_refl _) (le_refl _) (le_refl _)
    index current atState contents represented

end PDROC.BitVM.VM.BoundaryBudget
