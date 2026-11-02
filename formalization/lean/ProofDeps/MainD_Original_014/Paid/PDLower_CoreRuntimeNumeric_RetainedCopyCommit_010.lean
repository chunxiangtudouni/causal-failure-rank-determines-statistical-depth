module

public import Paid.PDLower_CoreRuntimeNumeric_CopyLoop_008
public import Paid.PDLower_CoreRuntimeNumeric_RetainedArguments_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDLower.CoreRuntimeNumeric

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame RootD27.Core RootD27.Bits
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList linearExecute)
open PaperProofs.Paid.Parameters PDROC.CalibrationRow.Operand PDROC.CoreOperands

/-- A genuinely computed retained lower/upper table: physically saves
the actual returned pointer/length, reads original N/K, computes the
runtime buffer base, then performs every copy load/store and true return.
No prefilled buffer or additional original-input oracle is assumed. -/
theorem retained_copy_resources (P : Parameters) (fee penalty : ℚ)
    (program : Program) (input : List Cell) (before : State) (base budget : ℕ) (upper : Bool)
    (prepared : HeapList before 0 (preparedInput P fee))
    (fresh : before.register .fresh=.natural base)
    (address : before.register .address=.natural (resultBase base P.certificate.stages P.tools))
    (index : before.register .index=.natural (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length)
    (table : HeapList before (resultBase base P.certificate.stages P.tools)
      (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)))
    (fetched : FetchesCode program before.pc (retainedCopyCode before.pc upper (before.pc+29)))
    (safe : SafeBits before budget) (baseLower : 99≤base)
    (limitBits : (Cell.natural (base+78*PDCompute.Solver.entryCount P.certificate.stages P.tools)).bits≤budget)
    (endBits : (Cell.natural (before.pc+29)).bits≤budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤150*(encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length+360 ∧
      after.pc=before.pc+29 ∧ after.register .old=.natural (before.pc+29) ∧ after.register .index=.natural 0 ∧
      HeapList after (retainedTableBase base P.certificate.stages P.tools upper)
        (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)) ∧
      HeapList after (resultBase base P.certificate.stages P.tools)
        (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)) ∧
      HeapList after 0 (preparedInput P fee) ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+
        (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length+2 ∧
      (∀ state∈trace,RegionMemory before state (retainedCopyRegion base P.certificate.stages P.tools
        (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length upper)) ∧
      HeapList after 46 [.natural (resultBase base P.certificate.stages P.tools),
        .natural (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length] ∧
      (∀ state∈trace,SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+29) ∧
      (∀ state∈trace.dropLast,before.pc≤state.pc ∧ state.pc<before.pc+29) := by
  let returnPC := before.pc+29
  let n:=P.certificate.stages
  let k:=P.tools
  let cells:=encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)
  let source:=resultBase base n k
  let target:=retainedTableBase base n k upper
  let region:=retainedCopyRegion base n k cells.length upper
  let middle:=retainedArgumentsResult before base n k source cells.length returnPC upper
  have nLive : 0∈before.live:=prepared.1 0 (by change 0<13;decide)
  have kLive : 1∈before.live:=prepared.1 1 (by change 1<13;decide)
  have nValue : before.heap 0=.natural n:=PDLower.CalibrationCompute.HeapList.value prepared 0 (by change 0<13;decide)
  have kValue : before.heap 1=.natural k:=PDLower.CalibrationCompute.HeapList.value prepared 1 (by change 1<13;decide)
  have pcBits : PaperProofs.Paid.Parameters.natBits (before.pc+29)≤budget := by
    change 1+PaperProofs.Paid.Parameters.natBits (before.pc+29)≤budget at endBits
    omega
  have setupRun := retainedArguments_execute input before base n k source cells.length returnPC upper
    fresh address index nLive kLive nValue kValue
  obtain ⟨setup,sh,sl,sc,st,setupProperties,setupPC,setupProper,_setupPeak⟩ :=
    linear_resources program input _ before middle {46,47} budget (retainedArguments_straight upper returnPC)
      fetched.append_left setupRun
      (fun steps bounded state actual => retainedArguments_prefix_memory input before state base n k source cells.length returnPC steps upper
        fresh address index nLive kLive nValue kValue (by simpa only [retainedArguments_length] using bounded) actual)
      (retained_arguments_prefix_safe input before base n k source cells.length returnPC budget upper fresh address index
        nLive kLive nValue kValue safe baseLower limitBits endBits
        ((PDROC.DataBits.natBits_mono (by omega : before.pc+20≤before.pc+29)).trans pcBits))
  have sm : ∀ state∈setup,RegionMemory before state {46,47} := fun state member => (setupProperties state member).1
  have middleMemory : RegionMemory before middle {46,47}:=RegionMemory.trace_last sm sl
  have sourceLower : 48≤source := by unfold source resultBase tableBase headerWords;omega
  have middleTable : HeapList middle source cells := by
    apply PDLower.CalibrationCompute.HeapList.regionMemory table middleMemory
    intro offset _inside
    change source+offset∉({46,47} : Finset ℕ)
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have copyFetch : FetchesCode program middle.pc (heapCopyCode middle.pc) := by
    have middlePC : middle.pc=before.pc+20:=rfl
    rw [middlePC]
    simpa only [retainedArguments_length] using fetched.append_right
  have small : 2≤budget := by
    have cap : 1+PaperProofs.Paid.Parameters.natBits (base+78*PDCompute.Solver.entryCount n k)≤budget := limitBits
    have lower : 1+PaperProofs.Paid.Parameters.natBits 0≤1+PaperProofs.Paid.Parameters.natBits (base+78*PDCompute.Solver.entryCount n k) :=
      Nat.add_le_add_left (PDROC.DataBits.natBits_mono (Nat.zero_le _)) 1
    have two : 1+PaperProofs.Paid.Parameters.natBits 0=2 := by decide
    omega
  have sourceEnd : source+cells.length≤base+78*PDCompute.Solver.entryCount n k := by
    have bound := original_table_before_retained P fee penalty base n k true
    change source+cells.length≤base+70*PDCompute.Solver.entryCount n k at bound
    omega
  have targetEnd : target+cells.length≤base+78*PDCompute.Solver.entryCount n k := by
    have bound := (original_table_capacity P fee penalty n k).trans (retained_capacity_enough n k)
    change cells.length≤8*PDCompute.Solver.entryCount n k at bound
    dsimp only [target]
    cases upper <;> simp only [retainedTableBase,Bool.false_eq_true,ite_false,ite_true]
    all_goals omega
  obtain ⟨copied,after,ch,cl,cc,ct,pc,_nextFresh,_nextAddress,nextIndex,nextOld,copiedTable,sourceRetained,_copyOutput,_copyPeak,cm,copySafe,copyPC,copyProper⟩ :=
    copy_loop_resources program input middle.pc middle source target cells rfl rfl rfl rfl rfl middleTable
      (Or.inl (original_table_before_retained P fee penalty base n k upper)) budget _
      (setupProperties middle (List.mem_of_getLast? sl)).2 small limitBits sourceEnd targetEnd
      (by simpa only [middle,retainedArgumentsResult,Nat.add_assoc] using pcBits) copyFetch
  have setupMemory : ∀ state∈setup,RegionMemory before state region :=
    fun state member=>(sm state member).enlarge Finset.subset_union_left
  have copyMemory : ∀ state∈copied,RegionMemory middle state region :=
    fun state member=>(cm state member).enlarge Finset.subset_union_right
  have allMemory:=RegionMemory.join_trace setup copied before middle region sl setupMemory copyMemory
  have joined:=joinTrace_spec program input setup copied before middle after 315 (150*cells.length+45)
    sh sl ch cl sc cc st ct
  have finalMemory:=RegionMemory.trace_last allMemory joined.2.1
  have targetLower : 48≤target := by
    have lower:=retained_base_above_workspace base n k upper
    unfold workspaceSize headerWords at lower
    omega
  have middleSaved : HeapList middle 46 [.natural source,.natural cells.length] := by
    apply PDLower.CalibrationCompute.HeapList.of_values
    · intro offset inside
      change offset<2 at inside
      interval_cases offset <;> simp [middle,retainedArgumentsResult]
    · intro offset inside
      change offset<2 at inside
      interval_cases offset <;> simp [middle,retainedArgumentsResult]
  have savedAfter : HeapList after 46 [.natural source,.natural cells.length] := by
    apply PDLower.CalibrationCompute.HeapList.regionMemory middleSaved (RegionMemory.trace_last cm cl)
    intro offset inside
    change offset<2 at inside
    rw [mem_cellRegion_iff]
    omega
  have preparedRetained : HeapList after 0 (preparedInput P fee) := by
    apply PDLower.CalibrationCompute.HeapList.regionMemory prepared finalMemory
    intro offset inside
    change offset<13 at inside
    change 0+offset∉({46,47}∪cellRegion target cells.length)
    intro member
    rcases Finset.mem_union.mp member with scratch|destination
    · have alternatives : 0+offset=46 ∨ 0+offset=47 := by
        simpa only [Finset.mem_insert,Finset.mem_singleton] using scratch
      omega
    · have bounds:=(mem_cellRegion_iff target cells.length (0+offset)).mp destination
      omega
  have card : region.card≤cells.length+2 := by
    have destination : (cellRegion target cells.length).card≤cells.length := by
      unfold cellRegion
      exact Finset.card_image_le.trans (by rw [Finset.card_range])
    have scratch : ({46,47} : Finset ℕ).card=2:=by decide
    have unionBound:=Finset.card_union_le ({46,47} : Finset ℕ) (cellRegion target cells.length)
    rw [scratch] at unionBound
    exact unionBound.trans (by omega)
  have allSpace : ∀ state∈joinTrace setup copied,workingCells state≤workingCells before+cells.length+2 := by
    intro state member
    have bound:=(allMemory state member).workingCells_le
    omega
  have timeBound : 315+(150*cells.length+45)≤150*cells.length+360:=by omega
  have allSafe := PDCompute.Pack.joinTrace_invariant setup copied (fun state => SafeBits state budget)
    (fun state member => (setupProperties state member).2) copySafe
  have copiedNonempty : copied≠[] := by intro empty;simp [empty] at ch
  have proper : ∀ state∈(joinTrace setup copied).dropLast,before.pc≤state.pc ∧ state.pc<before.pc+29 := by
    intro state member
    change state∈(setup.dropLast++copied).dropLast at member
    rw [List.dropLast_append_of_ne_nil copiedNonempty] at member
    rcases List.mem_append.mp member with setupMember|copyMember
    · have low := (setupPC state (List.mem_of_mem_dropLast setupMember)).1
      have high := setupProper state setupMember
      change state.pc<before.pc+20 at high
      omega
    · have bounds := copyProper state copyMember
      change before.pc+20≤state.pc ∧ state.pc<before.pc+20+9 at bounds
      omega
  have location : ∀ state∈joinTrace setup copied,before.pc≤state.pc ∧ state.pc≤before.pc+29 := by
    intro state member
    rcases joinTrace_member member with setupMember|copyMember
    · have bounds := setupPC state setupMember
      change before.pc≤state.pc ∧ state.pc≤before.pc+20 at bounds
      omega
    · have bounds := copyPC state copyMember
      change before.pc+20≤state.pc ∧ state.pc≤before.pc+20+9 at bounds
      omega
  exact ⟨joinTrace setup copied,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans timeBound,
    pc,nextOld,nextIndex,copiedTable,sourceRetained,preparedRetained,finalMemory.2.2.2,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,savedAfter,allSafe,location,proper⟩

/-- Real count reload followed by real length store and fresh0. -/
theorem commit_prefix_safe (input : List Cell) (before : State) (slot budget : ℕ)
    (safe : SafeBits before budget) (live : 47∈before.live) (small : 7≤budget)
    (slotBits : (Cell.natural slot).bits≤budget) (pcBits : PaperProofs.Paid.Parameters.natBits (before.pc+5)≤budget) :
    PrefixSafe input (retainedCommitCode slot) before budget := by
  let loaded := directReadResult before 47 .index
  let addressed := ({loaded with pc:=loaded.pc+1}).set .address (.natural slot)
  let stored : State := {addressed with heap:=Function.update addressed.heap slot (addressed.register .index),live:=insert slot addressed.live,pc:=addressed.pc+1}
  let after := ({stored with pc:=stored.pc+1}).set .fresh (.natural 0)
  have loadRun := directRead_execute input before 47 .index live
  have loadSafe := directRead_prefix_safe input before 47 budget .index safe live
    ((show (Cell.natural 47).bits≤7 by decide).trans small)
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+2≤before.pc+5)).trans pcBits)
  have addressedSafe : SafeBits addressed budget :=
    ((loadSafe.final loadRun).withPC _ (by simpa only [loaded,directReadResult,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+3≤before.pc+5)).trans pcBits))).set _ _ slotBits
  have slotNat : PaperProofs.Paid.Parameters.natBits slot≤budget := by change 1+PaperProofs.Paid.Parameters.natBits slot≤budget at slotBits;omega
  have storedSafe : SafeBits stored budget :=
    (addressedSafe.withPC _ (by simpa only [addressed,loaded,directReadResult,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+4≤before.pc+5)).trans pcBits))).store slot
      (addressed.register .index) slotNat (addressedSafe.register .index)
  have afterSafe : SafeBits after budget :=
    (storedSafe.withPC _ (by simpa only [stored,addressed,loaded,directReadResult,State.set,Nat.add_assoc] using pcBits)).set _ _
      ((show (Cell.natural 0).bits≤7 by decide).trans small)
  have storeRun : (Instruction.store .address .index).execute input addressed=some stored := by
    simp [Instruction.execute,addressed,stored,State.set,Cell.nat?]
  have tailSafe : PrefixSafe input [.constant .address (.natural slot),.store .address .index,.constant .fresh (.natural 0)] loaded budget := by
    apply PrefixSafe.cons input _ _ loaded addressed budget rfl (loadSafe.final loadRun)
    apply PrefixSafe.cons input _ _ addressed stored budget storeRun addressedSafe
    apply PrefixSafe.cons input _ [] stored after budget rfl storedSafe
    exact PrefixSafe.nil input after budget afterSafe
  exact PrefixSafe.append input (directReadCode 47 .index) _ before loaded budget loadRun loadSafe tailSafe

theorem commit_resources (program : Program) (input : List Cell) (before : State) (slot count budget : ℕ)
    (saved : HeapList before 47 [.natural count]) (safe : SafeBits before budget) (small : 7≤budget)
    (slotBits : (Cell.natural slot).bits≤budget) (pcBits : PaperProofs.Paid.Parameters.natBits (before.pc+5)≤budget)
    (fetched : FetchesCode program before.pc (retainedCommitCode slot)) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (retainedCommitResult before slot count) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤90 ∧
      (∀ state∈trace,RegionMemory before state {slot} ∧ SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+5) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+5) ∧ peakCells trace≤workingCells before+1 ∧
      HeapList (retainedCommitResult before slot count) slot [.natural count] := by
  have live : 47∈before.live := by simpa only [Nat.add_zero] using saved.1 0 (by change 0<1;decide)
  have value := PDLower.CalibrationCompute.HeapList.value saved 0 (by change 0<1;decide)
  change before.heap 47=.natural count at value
  obtain ⟨trace,head,last,chain,cost,properties,location,proper,space⟩ :=
    linear_resources program input _ before _ {slot} budget (retainedCommit_straight slot) fetched
      (retainedCommit_execute input before slot count live value)
      (fun steps bounded state actual => retainedCommit_prefix_memory input before state slot count steps live value
        (by simpa only [retainedCommit_length] using bounded) actual)
      (commit_prefix_safe input before slot budget safe live small slotBits pcBits)
  have stored : HeapList (retainedCommitResult before slot count) slot [.natural count] := by
    apply PDLower.CalibrationCompute.HeapList.of_values
    · intro offset inside
      have zero : offset=0 := by change offset<1 at inside;omega
      subst offset;simp [retainedCommitResult]
    · intro offset inside
      have zero : offset=0 := by change offset<1 at inside;omega
      subst offset;simp [retainedCommitResult]
  exact ⟨trace,head,last,chain,by simpa only [retainedCommit_length] using cost,properties,
    by simpa only [retainedCommit_length] using location,
    by simpa only [retainedCommit_length] using proper,by simpa using space,stored⟩

end PDLower.CoreRuntimeNumeric
