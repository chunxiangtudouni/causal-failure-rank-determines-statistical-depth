module

public import Paid.PDLower_CoreRuntimeNumeric_SaveMetadata_001
public import Paid.PDROC_CoreOperands_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList linearExecute linearExecute_append)
open PDROC.CalibrationRow.Operand RootD27.Bits PDROC.CoreOperands

namespace PDLower.CoreRuntimeNumeric

/-- The actual runtime fourteen, without the unused initial penalty
loader. Read values are paid by incoming live-heap SafeBits. -/
theorem arguments_prefix_safe (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (returnPC budget : ℕ) (safe : SafeBits before budget)
    (prepared : HeapList before 0 (preparedInput P fee))
    (small : 4≤budget) (baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤budget)
    (returnBits : (Cell.natural returnPC).bits≤budget) (pcBits : natBits (before.pc+14)≤budget) :
    PrefixSafe input (RootD27.Core.solverRuntimeArgumentsCode returnPC) before budget := by
  have live (slot : ℕ) (inside : slot<13) : slot∈before.live :=
    by simpa only [Nat.zero_add] using prepared.1 slot (by change slot<13;exact inside)
  have valueM := HeapList.value prepared 7 (by change 7<13;decide)
  change before.heap 7=.natural P.certificate.M at valueM
  let first := solverBaseResult before P.certificate.M
  let second := solverReadResult first
  have firstRun := solverBase_execute input before P.certificate.M (live 7 (by decide)) valueM
  have firstSafe := solver_base_prefix_safe input before P.certificate.M budget safe (live 7 (by decide)) valueM baseBits
    ((natBits_mono (by omega : before.pc+6≤before.pc+14)).trans pcBits)
  have secondRun := solverReads_execute input first live
  have secondSafe := solverReads_prefix_safe input first budget (firstSafe.final firstRun) live small
    (by simpa only [first,solverBaseResult,Nat.add_assoc] using
      ((natBits_mono (by omega : before.pc+12≤before.pc+14)).trans pcBits))
  have cacheBits : (Cell.natural 96).bits≤budget :=
    (Nat.add_le_add_left (natBits_mono (by omega : 96≤99+2*P.certificate.M)) 1).trans baseBits
  have tailSafe := solver_return_prefix_safe input second returnPC budget (secondSafe.final secondRun) cacheBits returnBits
    (by simpa only [second,first,solverReadResult,directReadResult,solverBaseResult,State.set,Nat.add_assoc] using pcBits)
  have suffix := PrefixSafe.append input (RootD27.Core.solverHeapArgumentPrefix.drop 6)
    [.constant .address (.natural 96),.constant .old (.natural returnPC)] first second budget secondRun secondSafe tailSafe
  change PrefixSafe input ((RootD27.Core.solverHeapArgumentPrefix.take 6)++
    ((RootD27.Core.solverHeapArgumentPrefix.drop 6)++[.constant .address (.natural 96),.constant .old (.natural returnPC)])) before budget
  exact PrefixSafe.append input _ _ before first budget firstRun firstSafe suffix

/-- Canonical actual readonly segment, including strict proper PC and
unchanged old dirty heap, live set and output, on the same trace. -/
def ReadResources (program : Program) (input : List Cell) (before after : State) (count budget : ℕ) : Prop :=
  ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
    trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤15*(count+1) ∧
    (∀ state∈trace,(state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output) ∧ SafeBits state budget) ∧
    (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+count) ∧
    (∀ state∈trace.dropLast,state.pc<before.pc+count) ∧ peakCells trace≤workingCells before

theorem readonly_resources (program : Program) (input : List Cell) (code : List Instruction)
    (before after : State) (budget : ℕ) (straight : StraightCode code)
    (readonly : code.all PDLower.CalibrationCompute.readOnly=true)
    (fetched : FetchesCode program before.pc code) (run : linearExecute input code before=some after)
    (safe : PrefixSafe input code before budget) : ReadResources program input before after code.length budget := by
  have memory : ∀ count≤code.length,∀ state,linearExecute input (code.take count) before=some state → RegionMemory before state ∅ := by
    intro count _ state executed
    have reads : (code.take count).all PDLower.CalibrationCompute.readOnly=true := by
      apply List.all_eq_true.mpr
      intro instruction member
      exact (List.all_eq_true.mp readonly) instruction (List.mem_of_mem_take member)
    obtain ⟨heap,live,output⟩ := PDLower.CalibrationCompute.linearReadOnly_heap input _ before state reads executed
    simpa only [RegionMemory,heap,live,output] using (RegionMemory.refl before ∅)
  obtain ⟨trace,head,last,chain,cost,properties,location,proper,space⟩ :=
    linear_resources program input code before after ∅ budget straight fetched run memory safe
  refine ⟨trace,head,last,chain,cost,?_,location,proper,by simpa using space⟩
  intro state member
  have mem := (properties state member).1
  have heap : state.heap=before.heap := by
    funext address
    exact mem.1 address (by simp)
  have live : state.live=before.live := by
    apply Finset.Subset.antisymm
    · simpa using mem.2.1
    · exact mem.2.2.1
  exact ⟨⟨heap,live,mem.2.2.2⟩,(properties state member).2⟩

theorem arguments_resources (P : Parameters) (fee : ℚ) (program : Program) (input : List Cell)
    (before : State) (returnPC budget : ℕ) (safe : SafeBits before budget)
    (prepared : HeapList before 0 (preparedInput P fee))
    (small : 4≤budget) (baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤budget)
    (returnBits : (Cell.natural returnPC).bits≤budget) (pcBits : natBits (before.pc+14)≤budget)
    (fetched : FetchesCode program before.pc (RootD27.Core.solverRuntimeArgumentsCode returnPC)) :
    ReadResources program input before (RootD27.Core.solverRuntimeArgumentsResult P fee before returnPC) 14 budget := by
  exact readonly_resources program input _ before _ budget (RootD27.Core.solverRuntimeArguments_straight returnPC) rfl fetched
    (RootD27.Core.solverRuntimeArguments_execute P fee input before returnPC prepared)
    (arguments_prefix_safe P fee input before returnPC budget safe prepared small baseBits returnBits pcBits)

theorem restore_prefix_safe (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (returnPC source count budget : ℕ) (safe : SafeBits before budget)
    (prepared : HeapList before 0 (preparedInput P fee)) (saved : HeapList before 46 [.natural source,.natural count])
    (small : 7≤budget) (baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤budget)
    (returnBits : (Cell.natural returnPC).bits≤budget) (pcBits : natBits (before.pc+18)≤budget) :
    PrefixSafe input (RootD27.Core.restoreSolverResultCode returnPC) before budget := by
  let args := RootD27.Core.solverRuntimeArgumentsResult P fee before returnPC
  let counted := directReadResult args 47 .index
  have argsRun := RootD27.Core.solverRuntimeArguments_execute P fee input before returnPC prepared
  have argsSafe := arguments_prefix_safe P fee input before returnPC budget safe prepared (by omega) baseBits returnBits
    ((natBits_mono (by omega : before.pc+14≤before.pc+18)).trans pcBits)
  have countLive : 47∈before.live := saved.1 1 (by change 1<2;decide)
  have sourceLive : 46∈before.live := saved.1 0 (by change 0<2;decide)
  have countRun := directRead_execute input args 47 .index countLive
  have countSafe := directRead_prefix_safe input args 47 budget .index (argsSafe.final argsRun) countLive
    ((show (Cell.natural 47).bits≤7 by decide).trans small)
    (by simpa only [args,RootD27.Core.solverRuntimeArgumentsResult] using
      ((natBits_mono (by omega : before.pc+16≤before.pc+18)).trans pcBits))
  have sourceSafe := directRead_prefix_safe input counted 46 budget .address (countSafe.final countRun) sourceLive
    ((show (Cell.natural 46).bits≤7 by decide).trans small)
    (by simpa only [counted,args,directReadResult,RootD27.Core.solverRuntimeArgumentsResult,State.set,Nat.add_assoc] using pcBits)
  have suffix := PrefixSafe.append input (directReadCode 47 .index) (directReadCode 46 .address)
    args counted budget countRun countSafe sourceSafe
  change PrefixSafe input (RootD27.Core.solverRuntimeArgumentsCode returnPC++(directReadCode 47 .index++directReadCode 46 .address)) before budget
  exact PrefixSafe.append input _ _ before args budget argsRun argsSafe suffix

theorem restore_resources (P : Parameters) (fee : ℚ) (program : Program) (input : List Cell) (before : State)
    (returnPC source count budget : ℕ) (safe : SafeBits before budget)
    (prepared : HeapList before 0 (preparedInput P fee)) (saved : HeapList before 46 [.natural source,.natural count])
    (small : 7≤budget) (baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤budget)
    (returnBits : (Cell.natural returnPC).bits≤budget) (pcBits : natBits (before.pc+18)≤budget)
    (fetched : FetchesCode program before.pc (RootD27.Core.restoreSolverResultCode returnPC)) :
    ReadResources program input before (RootD27.Core.restoreSolverResult P fee before returnPC source count) 18 budget := by
  exact readonly_resources program input _ before _ budget (RootD27.Core.restoreSolverResult_straight returnPC) rfl fetched
    (RootD27.Core.restoreSolverResult_execute P fee input before returnPC source count prepared saved)
    (restore_prefix_safe P fee input before returnPC source count budget safe prepared saved small baseBits returnBits pcBits)

/-- The inline dispatch jump has its actual terminal solver entry, which
can be outside the inline PC interval. Every proper state is still inline. -/
theorem dispatch_resources (P : Parameters) (fee : ℚ) (program : Program) (input : List Cell)
    (before : State) (returnPC entryPC budget : ℕ) (safe : SafeBits before budget)
    (prepared : HeapList before 0 (preparedInput P fee))
    (small : 4≤budget) (baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤budget)
    (returnBits : (Cell.natural returnPC).bits≤budget) (entryBits : natBits entryPC≤budget)
    (pcBits : natBits (before.pc+14)≤budget)
    (fetched : FetchesCode program before.pc (RootD27.Core.solverRuntimeDispatchCode returnPC entryPC)) :
    let middle := RootD27.Core.solverRuntimeArgumentsResult P fee before returnPC
    let entered := {middle with pc:=entryPC}
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some entered ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤240 ∧
      (∀ state∈trace,(state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output) ∧ SafeBits state budget) ∧
      (∀ state∈trace,(before.pc≤state.pc ∧ state.pc≤before.pc+14) ∨ state.pc=entryPC) ∧
      (∀ state∈trace.dropLast,before.pc≤state.pc ∧ state.pc<before.pc+15) ∧ peakCells trace≤workingCells before := by
  dsimp only
  let middle := RootD27.Core.solverRuntimeArgumentsResult P fee before returnPC
  let entered : State := {middle with pc:=entryPC}
  change FetchesCode program before.pc (RootD27.Core.solverRuntimeArgumentsCode returnPC++[.jump entryPC]) at fetched
  obtain ⟨setup,head,last,chain,cost,properties,location,_proper,_space⟩ :=
    arguments_resources P fee program input before returnPC budget safe prepared small baseBits returnBits pcBits fetched.append_left
  have jumpFetch : program[middle.pc]?=some (.jump entryPC) := by
    change program[before.pc+14]?=some _
    exact (fetched 14 (by change 14<15;decide)).trans (by rfl)
  have jump : step program input middle=some entered := by simp only [step,jumpFetch];rfl
  have controlled := chain_append_control program input setup middle entered chain last jump
  have nonempty : setup≠[] := by intro empty;simp [empty] at head
  have afterSafe : SafeBits entered budget :=
    ((properties middle (List.mem_of_getLast? last)).2).withPC entryPC entryBits
  have allProperties : ∀ state∈setup++[entered],
      (state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output) ∧ SafeBits state budget := by
    intro state member
    rcases List.mem_append.mp member with earlier|arrival
    · exact properties state earlier
    · have same := List.mem_singleton.mp arrival
      subst state
      exact ⟨⟨rfl,rfl,rfl⟩,afterSafe⟩
  refine ⟨setup++[entered],by simpa only [List.head?_append_of_ne_nil setup nonempty] using head,
    by simp [entered,middle],controlled.1,by omega,allProperties,?_,?_,?_⟩
  · intro state member
    rcases List.mem_append.mp member with earlier|arrival
    · exact Or.inl (location state earlier)
    · have same := List.mem_singleton.mp arrival
      subst state
      exact Or.inr rfl
  · intro state member
    have original : state∈setup := by simpa using member
    have bounded := location state original
    omega
  · apply PDLower.CalibrationCompute.peakCells_le_of_forall
    intro state member
    obtain ⟨_heap,live,output⟩ := (allProperties state member).1
    simp only [workingCells,live,output]
    exact le_refl _

end PDLower.CoreRuntimeNumeric
