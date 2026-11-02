module

public import Paid.RootD27Core_SelectedMetadata_069
public import Paid.PDLower_CoreSearch_LocatedLiterals_030

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList linearExecute)
open PDROC.CalibrationRow.Operand RootD27.Bits

namespace PDLower.CoreRuntimeNumeric

/-- Resources and actual closed/proper PC bounds on the SAME canonical
straight trace; any finite actual write region is supported. -/
theorem linear_resources (program : Program) (input : List Cell) (code : List Instruction)
    (before after : State) (region : Finset ℕ) (budget : ℕ) (straight : StraightCode code)
    (fetched : FetchesCode program before.pc code) (run : linearExecute input code before=some after)
    (memory : ∀ count≤code.length,∀ state,linearExecute input (code.take count) before=some state → RegionMemory before state region)
    (safe : PrefixSafe input code before budget) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤15*(code.length+1) ∧
      (∀ state∈trace,RegionMemory before state region ∧ SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+code.length) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+code.length) ∧
      peakCells trace≤workingCells before+region.card := by
  obtain ⟨trace,head,last,chain,cost,prefixes,location⟩ := linearExecute_trace_closedPC program input code straight before after fetched run
  have properties : ∀ state∈trace,RegionMemory before state region ∧ SafeBits state budget := by
    intro state member
    have split := List.dropLast_append_getLast? after (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,bounded,executed⟩ := prefixes state proper
      exact ⟨memory count bounded.le state executed,safe count state executed⟩
    · have same := List.mem_singleton.mp terminal
      subst state
      exact ⟨memory code.length (le_refl _) after (by simpa only [List.take_length] using run),safe.final run⟩
  have proper : ∀ state∈trace.dropLast,state.pc<before.pc+code.length := by
    intro state member
    obtain ⟨count,bounded,executed⟩ := prefixes state member
    have prefixStraight : StraightCode (code.take count) := fun instruction inside => straight instruction (List.mem_of_mem_take inside)
    have pc := linearExecute_pc input (code.take count) prefixStraight before state executed
    rw [List.length_take,Nat.min_eq_left bounded.le] at pc
    omega
  have space : ∀ state∈trace,workingCells state≤workingCells before+region.card :=
    fun state member => (properties state member).1.workingCells_le
  exact ⟨trace,head,last,chain,cost,properties,location,proper,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ space⟩

/-- Save arbitrary actual address/index cells. Their old bits already
belong to callerB; only the real literal addresses and new PCs are new. -/
theorem save_prefix_safe (input : List Cell) (before : State) (budget : ℕ)
    (safe : SafeBits before budget) (small : 7≤budget) (pcBits : natBits (before.pc+5)≤budget) :
    PrefixSafe input RootD27.Core.saveSolverResultCode before budget := by
  have pc (count : ℕ) (bounded : count≤5) : natBits (before.pc+count)≤budget :=
    (natBits_mono (by omega : before.pc+count≤before.pc+5)).trans pcBits
  have b46 : (Cell.natural 46).bits≤budget := (show (Cell.natural 46).bits≤7 by decide).trans small
  have b47 : (Cell.natural 47).bits≤budget := (show (Cell.natural 47).bits≤7 by decide).trans small
  have b0 : (Cell.natural 0).bits≤budget := (show (Cell.natural 0).bits≤7 by decide).trans small
  let s1 := ({before with pc:=before.pc+1}).set .total (.natural 46)
  let s2 : State := {s1 with heap:=Function.update s1.heap 46 (s1.register .address),live:=insert 46 s1.live,pc:=s1.pc+1}
  let s3 := ({s2 with pc:=s2.pc+1}).set .total (.natural 47)
  let s4 : State := {s3 with heap:=Function.update s3.heap 47 (s3.register .index),live:=insert 47 s3.live,pc:=s3.pc+1}
  let s5 := ({s4 with pc:=s4.pc+1}).set .fresh (.natural 0)
  have safe1 : SafeBits s1 budget := (safe.withPC _ (pc 1 (by decide))).set .total (.natural 46) b46
  have safe2 : SafeBits s2 budget :=
    ((safe1.withPC _ (pc 2 (by decide))).store 46 (s1.register .address)
      ((show natBits 46≤7 by decide).trans small) (safe1.register .address))
  have safe3 : SafeBits s3 budget :=
    (safe2.withPC _ (by change natBits (before.pc+3)≤budget;exact pc 3 (by decide))).set .total (.natural 47) b47
  have safe4 : SafeBits s4 budget :=
    ((safe3.withPC _ (pc 4 (by decide))).store 47 (s3.register .index)
      ((show natBits 47≤7 by decide).trans small) (safe3.register .index))
  have safe5 : SafeBits s5 budget :=
    (safe4.withPC _ (by change natBits (before.pc+5)≤budget;exact pcBits)).set .fresh (.natural 0) b0
  have first : (Instruction.constant .total (.natural 46)).execute input before=some s1 := rfl
  have second : (Instruction.store .total .address).execute input s1=some s2 := by simp [Instruction.execute,s1,s2,State.set,Cell.nat?]
  have third : (Instruction.constant .total (.natural 47)).execute input s2=some s3 := rfl
  have fourth : (Instruction.store .total .index).execute input s3=some s4 := by simp [Instruction.execute,s3,s4,State.set,Cell.nat?]
  have fifth : (Instruction.constant .fresh (.natural 0)).execute input s4=some s5 := rfl
  exact PrefixSafe.cons input _ _ before s1 budget first safe
    (PrefixSafe.cons input _ _ s1 s2 budget second safe1
      (PrefixSafe.cons input _ _ s2 s3 budget third safe2
        (PrefixSafe.cons input _ _ s3 s4 budget fourth safe3
          (PrefixSafe.cons input _ [] s4 s5 budget fifth safe4 (PrefixSafe.nil input s5 budget safe5)))))

theorem save_resources (program : Program) (input : List Cell) (before : State) (source count budget : ℕ)
    (address : before.register .address=.natural source) (index : before.register .index=.natural count)
    (safe : SafeBits before budget) (small : 7≤budget) (pcBits : natBits (before.pc+5)≤budget)
    (fetched : FetchesCode program before.pc RootD27.Core.saveSolverResultCode) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (RootD27.Core.saveSolverResult before source count) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤90 ∧
      HeapList (RootD27.Core.saveSolverResult before source count) 46 [.natural source,.natural count] ∧
      (RootD27.Core.saveSolverResult before source count).register .fresh=.natural 0 ∧
      (RootD27.Core.saveSolverResult before source count).output=before.output ∧
      (∀ state∈trace,RegionMemory before state {46,47} ∧ SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+5) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+5) ∧ peakCells trace≤workingCells before+2 := by
  have run := RootD27.Core.saveSolverResult_execute input before source count address index
  obtain ⟨trace,head,last,chain,cost,properties,location,proper,space⟩ :=
    linear_resources program input RootD27.Core.saveSolverResultCode before (RootD27.Core.saveSolverResult before source count) {46,47} budget
      RootD27.Core.saveSolverResult_straight fetched run
      (fun steps bounded state executed => RootD27.Core.saveSolverResult_prefix_memory input before state source count steps address index
        (by simpa only [RootD27.Core.saveSolverResult_length] using bounded) executed)
      (save_prefix_safe input before budget safe small pcBits)
  have card : ({46,47}:Finset ℕ).card=2 := by decide
  exact ⟨trace,head,last,chain,by simpa only [RootD27.Core.saveSolverResult_length] using cost,
    RootD27.Core.saveSolverResult_saved before source count,rfl,rfl,properties,
    by simpa only [RootD27.Core.saveSolverResult_length] using location,
    by simpa only [RootD27.Core.saveSolverResult_length] using proper,by simpa only [card] using space⟩

/-- Four actual live-header copies and the real tag literal, with NO
intrinsic arithmetic assumptions on arbitrary old metadata/scratch. -/
theorem selected_metadata_resources (program : Program) (input : List Cell) (before : State)
    (values : ℕ→Cell) (upper isExact : Bool) (budget : ℕ) (header : Header before 0 values)
    (fresh : before.register .fresh=.natural 0) (safe : SafeBits before budget) (small : 7≤budget)
    (pcBits : natBits (before.pc+28)≤budget)
    (fetched : FetchesCode program before.pc (headerCode (RootD27.Core.selectedMetadataCommands upper isExact))) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤435 ∧
      Header after 0 (RootD27.Core.selectedMetadataValues values upper isExact) ∧ after.register .fresh=.natural 0 ∧ after.pc=before.pc+28 ∧
      RegionMemory before after (RootD27.Core.selectedMetadataRegion upper) ∧ after.output=before.output ∧
      (∀ state∈trace,(MemoryFrame PDLower.CoreSearch.scalarRegion before state ∧ HeaderMemory before state 0) ∧ SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+28) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+28) ∧ peakCells trace≤workingCells before := by
  have bounded : ∀ command∈RootD27.Core.selectedMetadataCommands upper isExact,CopyConstantBound budget command := by
    intro command member
    simp only [RootD27.Core.selectedMetadataCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same|same|same|same <;> subst command
    all_goals first
      | trivial
      | cases isExact <;> change 1+natBits _≤budget <;> norm_num [natBits] <;> omega
  have addressBits : 1+natBits headerWords≤budget := (show 1+natBits headerWords≤7 by decide).trans small
  obtain ⟨after,actual,afterHeader,afterFresh,pc⟩ := PDLower.CoreSearch.Located.copyConstant_segment_bits
    (RootD27.Core.selectedMetadataCommands upper isExact) program input before values (RootD27.Core.selectedMetadataValues values upper isExact)
    budget (RootD27.Core.selectedMetadata_valid upper isExact) (RootD27.Core.selectedMetadata_targets upper isExact) header fresh
    (RootD27.Core.selectedMetadata_eval values upper isExact) safe bounded addressBits
    (by simpa only [RootD27.Core.selectedMetadata_length] using pcBits) fetched before.pc (before.pc+28) (le_refl _)
    (by rw [RootD27.Core.selectedMetadata_length])
  have finalMemory := actual.final.1
  have precise := RootD27.Core.header_final_values_region (RootD27.Core.selectedMetadataRegion upper) header afterHeader finalMemory
    (fun slot _inside outside => RootD27.Core.selectedMetadata_outside values upper isExact slot outside)
  obtain ⟨trace,head,last,chain,cost,properties,proper⟩ := actual
  have space : ∀ state∈trace,workingCells state≤workingCells before := by
    intro state member
    have memory := (properties state member).1.1.2
    unfold workingCells
    rw [memory.2.1,memory.2.2]
  exact ⟨trace,after,head,last,chain,by simpa only [RootD27.Core.selectedMetadata_length] using cost,afterHeader,afterFresh,
    by simpa only [RootD27.Core.selectedMetadata_length] using pc,precise,finalMemory.2.2.2,
    (fun state member => (properties state member).1),(fun state member => (properties state member).2),proper,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ space⟩

end PDLower.CoreRuntimeNumeric
