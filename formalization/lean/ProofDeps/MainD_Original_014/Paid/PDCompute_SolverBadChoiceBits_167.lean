module

public import Paid.PDCompute_SolverConditionalBits_166
public import Paid.PDCompute_SolverLiteralFieldsBits_165
public import Paid.PDCompute_SolverBadPreparationBits_158
public import Paid.PDCompute_SolverBadBranchRuntime_078

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- Actual positive-tools bad choice: real repaired candidate, strict
comparison/branch and true selected original fields, all same-trace bits. -/
theorem positiveBadCode_trace_bits (program : Program) (input : List Cell) (origin : ℕ)
    (P : Parameters) (previous : MenuRow) (tools : ℕ) (fee penalty : ℚ) (before : State) (base n k budget S L T : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (hobs : values 16=.rational (previous.getD tools abandonEntry).observation)
    (hrep : values 17=.rational (previous.getD tools abandonEntry).repairs) (hfail : values 18=.rational (previous.getD tools abandonEntry).failure)
    (safe : RootD27.Bits.SafeBits before budget)
    (observation : ratEncodingBits (previous.getD tools abandonEntry).observation≤S)
    (repairs : ratEncodingBits (previous.getD tools abandonEntry).repairs≤S) (failure : ratEncodingBits (previous.getD tools abandonEntry).failure≤S)
    (feeBits : ratEncodingBits fee≤L) (penaltyBits : ratEncodingBits penalty≤T) (room : 1+16*(2*(S+3)+L+T+1)≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (counter : natBits (origin+(positiveBadCode origin).length)≤budget)
    (fetch : FetchesCode program origin (positiveBadCode origin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤3600 ∧
      Header after base (positiveBadValues values fee penalty (previous.getD tools abandonEntry)) ∧
      after.heap (base+31)=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.observation ∧
      after.heap (base+32)=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.repairs ∧
      after.heap (base+33)=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.failure ∧
      after.heap (base+34)=.natural (if (P.menuBadBranch fee penalty previous (tools+1)).1=.repair then 1 else 0) ∧
      after.heap (base+22)=.rational ((P.menuBadBranch fee penalty previous (tools+1)).2.objective fee penalty) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(positiveBadCode origin).length ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let child:=previous.getD tools abandonEntry
  let prepared:=badPreparationValues values fee penalty child
  have fetchPrepare : FetchesCode program before.pc (headerCode badPreparationCommands) := by rw [hpc]; exact fetch.append_left
  have prepareCounter : natBits (before.pc+(headerCode badPreparationCommands).length)≤budget :=
    (natBits_mono (by rw [hpc,positiveBadCode,List.length_append]; omega : before.pc+(headerCode badPreparationCommands).length≤origin+(positiveBadCode origin).length)).trans counter
  obtain ⟨firstTrace,first,firstHead,firstLast,firstChain,firstTime,firstHeader,firstBase,firstPC,firstFrame,firstOutput,firstResources⟩:=
    badPreparation_trace_bits program input before base n k budget S L T values fee penalty child header fresh safe hfee hpenalty hobs hrep hfail
      observation repairs failure feeBits penaltyBits room addressBits prepareCounter fetchPrepare
  have firstMemory : ∀ state∈firstTrace,HeaderMemory before state base := fun state member=>(firstResources state member).1
  have firstSafe : ∀ state∈firstTrace,RootD27.Bits.SafeBits state budget := fun state member=>(firstResources state member).2
  have intermediateSafe:=firstSafe first (List.mem_of_getLast? firstLast)
  have small : 4≤budget := by omega
  have bounded:=copyConstantCommands_evaluated_bits acceptRepairCommands prepared budget acceptRepairCommands_valid
    (HeaderValueBits.of_safe firstHeader intermediateSafe) (acceptRepairCommands_copyBound budget small)
  have candidate : prepared 28=.rational ((repairEntry child).objective fee penalty) := by simp [prepared,badPreparationValues]
  have cutoff : prepared 24=.rational penalty := rfl
  have finalCounter : natBits ((origin+(headerCode badPreparationCommands).length)+8+(headerCode acceptRepairCommands).length)≤budget := by
    simpa only [positiveBadCode,List.length_append,headerIfLessCode_length,Nat.add_assoc] using counter
  obtain ⟨lastTrace,after,lastHead,lastLast,lastChain,lastTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,lastMemory,lastSafe⟩:=
    headerIfLess_trace_bits program input (origin+(headerCode badPreparationCommands).length) acceptRepairCommands prepared (acceptRepairValues prepared)
      fetch.append_right first base n k budget ((repairEntry child).objective fee penalty) penalty acceptRepairCommands_valid (acceptRepairCommands_eval prepared)
      bounded (firstPC.trans (congrArg (·+(headerCode badPreparationCommands).length) hpc)) firstHeader firstBase candidate cutoff intermediateSafe small addressBits finalCounter
  have lastBound : time program lastTrace≤1125 := by
    have cost : 135+165*(acceptRepairCommands.length+1)=1125 := rfl
    simpa only [cost] using lastTime
  have joined:=joinTrace_spec program input firstTrace lastTrace before first after 2475 1125 firstHead firstLast lastHead lastLast
    firstChain lastChain firstTime lastBound
  have original:=badChoice_original P values fee penalty previous tools
  refine ⟨joinTrace firstTrace lastTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,afterHeader,
    (afterHeader.value 31 (by decide)).trans original.1,(afterHeader.value 32 (by decide)).trans original.2.1,
    (afterHeader.value 33 (by decide)).trans original.2.2.1,(afterHeader.value 34 (by decide)).trans original.2.2.2.1,
    (afterHeader.value 22 (by decide)).trans original.2.2.2.2,afterBase,?_,firstFrame.trans afterFrame,afterOutput.trans firstOutput,
    joinTrace_memory firstTrace lastTrace before first base firstLast firstMemory lastMemory,
    PDCompute.Pack.joinTrace_invariant firstTrace lastTrace (fun state=>RootD27.Bits.SafeBits state budget) firstSafe lastSafe⟩
  simpa only [positiveBadCode,List.length_append,headerIfLessCode_length,Nat.add_assoc] using afterPC

end PDCompute.Solver
