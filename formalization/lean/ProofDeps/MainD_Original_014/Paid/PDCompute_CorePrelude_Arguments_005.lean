module
public import Paid.PDCompute_CorePrelude_Loader_004
public import Paid.PDROC_CoreOperands_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
@[expose] public section

namespace PDCompute.CorePrelude
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDCompute.CoreSearchBudget
open PDCompute.Solver PDMenu.ComputeFrame RootD27.Core RootD27.Bits PDROC.CoreOperands
open PDROC.CalibrationRow.Operand
open PDLower.CalibrationCompute (linearExecute)

theorem base_cell_bits (P : Parameters) (fee : ℚ) :
    (Cell.natural (99+2*P.certificate.M)).bits≤ inputBudget P fee := by
  have count:=prepared_count_cell_bits P fee P.certificate.M (by omega)
  have add:=natBits_add_le 99 (2*P.certificate.M)
  have multiply:=natBits_mul_le 2 P.certificate.M
  have fixed99 : natBits 99=7:=by decide
  have fixed2 : natBits 2=2:=by decide
  have positive:=coreOperandBound_positive P fee
  change 1+natBits P.certificate.M≤_ at count
  change 1+natBits (99+2*P.certificate.M)≤_
  unfold inputBudget
  omega

/-- One canonical fetched straight trace simultaneously exposes readonly
memory, full-state bits, closed PCs and a strict final-PC first exit. -/
theorem readonly_linear_resources (program : Program) (input : List Cell) (code : List Instruction)
    (before after : State) (budget : ℕ) (straight : StraightCode code)
    (fetch : FetchesCode program before.pc code) (run : linearExecute input code before=some after)
    (safe : PrefixSafe input code before budget)
    (memory : ∀ count≤code.length,∀ state,
      linearExecute input (code.take count) before=some state →
      state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤15*(code.length+1) ∧
      (∀ state∈trace,(state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output) ∧ SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+code.length) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+code.length) := by
  obtain ⟨trace,head,last,chain,cost,prefixes,scope⟩:=linearExecute_trace_closedPC program input code straight before after fetch run
  refine ⟨trace,head,last,chain,cost,?_,scope,?_⟩
  · intro state member
    have split:=List.dropLast_append_getLast? after (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,bound,actual⟩:=prefixes state proper
      exact ⟨memory count bound.le state actual,safe count state actual⟩
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact ⟨memory code.length (le_refl _) after (by simpa only [List.take_length] using run),safe.final run⟩
  · intro state member
    obtain ⟨count,bound,actual⟩:=prefixes state member
    have straightPrefix : StraightCode (code.take count):=
      fun instruction inside=>straight instruction (List.mem_of_mem_take inside)
    have pc:=linearExecute_pc input _ straightPrefix before state actual
    simp only [List.length_take,Nat.min_eq_left bound.le] at pc
    omega

theorem endpoint_arguments_memory (P : Parameters) (fee : ℚ) (input : List Cell)
    (before after : State) (base cache returnPC count : ℕ)
    (prepared : HeapList before 0 (preparedInput P fee)) (bound : count≤13)
    (actual : linearExecute input ((endpointHeapArgumentsCode base cache returnPC).take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  have mlive:=prepared.1 7 (by change 7<13;decide)
  have glive:=prepared.1 2 (by change 2<13;decide)
  have flive:=prepared.1 4 (by change 4<13;decide)
  have m:=PDLower.CalibrationCompute.HeapList.value prepared 7 (by change 7<13;decide)
  have g:=PDLower.CalibrationCompute.HeapList.value prepared 2 (by change 2<13;decide)
  have f:=PDLower.CalibrationCompute.HeapList.value prepared 4 (by change 4<13;decide)
  change before.heap 7=.natural P.certificate.M at m
  change before.heap 2=.rational P.certificate.gamma at g
  change before.heap 4=.rational P.reviewFee at f
  simp only [Nat.zero_add] at mlive glive flive
  interval_cases count <;>
    simp [endpointHeapArgumentsCode,PDLower.CalibrationCompute.loadSlot,linearExecute,Instruction.execute,
      State.set,Cell.nat?,NatOp.eval,mlive,glive,flive,m,g,f] at actual <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

/-- The actual fourteen original calibration instructions compute their
variable base and read M/Q/gamma from live prepared heap cells. -/
theorem calibration_arguments_safe (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (returnPC budget : ℕ) (safe : SafeBits before budget)
    (prepared : HeapList before 0 (preparedInput P fee))
    (baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤budget)
    (returnBits : (Cell.natural returnPC).bits≤budget) (pcBits : natBits (before.pc+14)≤budget) :
    PrefixSafe input (calibrationHeapArgumentsCode returnPC) before budget := by
  have live (slot : ℕ) (inside : slot<13) : slot∈before.live:=by
    simpa only [Nat.zero_add] using prepared.1 slot (by change slot<13;exact inside)
  have m:=PDLower.CalibrationCompute.HeapList.value prepared 7 (by change 7<13;decide)
  change before.heap 7=.natural P.certificate.M at m
  let based:=solverBaseResult before P.certificate.M
  let first:=directReadResult based 7 .total
  let second:=directReadResult first 9 .index
  let third:=directReadResult second 2 .value
  have baseRun:=solverBase_execute input before P.certificate.M (live 7 (by decide)) m
  have baseSafe:=solver_base_prefix_safe input before P.certificate.M budget safe (live 7 (by decide)) m baseBits
    ((natBits_mono (by omega : before.pc+6≤before.pc+14)).trans pcBits)
  have natural (n : ℕ) (bound : n≤99+2*P.certificate.M) : (Cell.natural n).bits≤budget:=
    (Nat.add_le_add_left (natBits_mono bound) 1).trans baseBits
  have firstRun:=directRead_execute input based 7 .total (live 7 (by decide))
  have firstSafe:=directRead_prefix_safe input based 7 budget .total (baseSafe.final baseRun) (live 7 (by decide))
    (natural 7 (by omega)) (by simpa only [based,solverBaseResult,Nat.add_assoc] using
      ((natBits_mono (by omega : before.pc+8≤before.pc+14)).trans pcBits))
  have secondRun:=directRead_execute input first 9 .index (live 9 (by decide))
  have secondSafe:=directRead_prefix_safe input first 9 budget .index (firstSafe.final firstRun) (live 9 (by decide))
    (natural 9 (by omega)) (by simpa only [first,based,directReadResult,solverBaseResult,State.set,Nat.add_assoc] using
      ((natBits_mono (by omega : before.pc+10≤before.pc+14)).trans pcBits))
  have thirdRun:=directRead_execute input second 2 .value (live 2 (by decide))
  have thirdSafe:=directRead_prefix_safe input second 2 budget .value (secondSafe.final secondRun) (live 2 (by decide))
    (natural 2 (by omega)) (by simpa only [second,first,based,directReadResult,solverBaseResult,State.set,Nat.add_assoc] using
      ((natBits_mono (by omega : before.pc+12≤before.pc+14)).trans pcBits))
  have tailSafe:=solver_return_prefix_safe input third returnPC budget (thirdSafe.final thirdRun)
    (natural 96 (by omega)) returnBits
    (by simpa only [third,second,first,based,directReadResult,solverBaseResult,State.set,Nat.add_assoc] using pcBits)
  have thirdTail:=PrefixSafe.append input (directReadCode 2 .value) _ second third budget thirdRun thirdSafe tailSafe
  have secondTail:=PrefixSafe.append input (directReadCode 9 .index) _ first second budget secondRun secondSafe thirdTail
  have firstTail:=PrefixSafe.append input (directReadCode 7 .total) _ based first budget firstRun firstSafe secondTail
  exact PrefixSafe.append input (solverHeapArgumentPrefix.take 6) _ before based budget baseRun baseSafe firstTail

end PDCompute.CorePrelude
