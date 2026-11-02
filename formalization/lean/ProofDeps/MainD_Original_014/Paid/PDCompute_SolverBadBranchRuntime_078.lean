module

public import Paid.PDCompute_SolverEntryObjectives_073

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def positiveBadCode (origin : ℕ) : List Instruction :=
  headerCode badPreparationCommands++
    headerIfLessCode (origin+(headerCode badPreparationCommands).length) acceptRepairCommands

def positiveBadValues (values : ℕ → Cell) (fee penalty : ℚ) (entry : MenuEntry) : ℕ → Cell :=
  let prepared:=badPreparationValues values fee penalty entry
  if (repairEntry entry).objective fee penalty < penalty then acceptRepairValues prepared else prepared

/-- The positive-tool bad branch uses actual loaded preceding-row
statistics, constructs the repaired candidate, and follows a real strict
comparison branch. Equality really retains abandonment. -/
theorem positiveBadCode_trace_memory (program : Program) (input : List Cell) (origin : ℕ)
    (P : Parameters) (previous : MenuRow) (tools : ℕ) (fee penalty : ℚ)
    (before : State) (base n k : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (hobs : values 16=.rational (previous.getD tools abandonEntry).observation)
    (hrep : values 17=.rational (previous.getD tools abandonEntry).repairs)
    (hfail : values 18=.rational (previous.getD tools abandonEntry).failure)
    (fetched : FetchesCode program origin (positiveBadCode origin)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 3600 ∧ Header after base (positiveBadValues values fee penalty (previous.getD tools abandonEntry)) ∧
      after.heap (base+31)=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.observation ∧
      after.heap (base+32)=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.repairs ∧
      after.heap (base+33)=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.failure ∧
      after.heap (base+34)=.natural (if (P.menuBadBranch fee penalty previous (tools+1)).1=.repair then 1 else 0) ∧
      after.heap (base+22)=.rational ((P.menuBadBranch fee penalty previous (tools+1)).2.objective fee penalty) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(positiveBadCode origin).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base := by
  let child:=previous.getD tools abandonEntry
  let prepared:=badPreparationValues values fee penalty child
  have fetchPrepare : FetchesCode program before.pc (headerCode badPreparationCommands) := by
    rw [hpc]
    exact fetched.append_left
  obtain ⟨firstTrace,first,firstHead,firstLast,firstChain,firstTime,firstHeader,firstBase,firstPC,firstFrame,firstOutput,firstMemory⟩ :=
    headerCode_trace_memory badPreparationCommands program input before base n k values prepared
      badPreparationCommands_valid header hbase (badPreparationCommands_eval values fee penalty child hfee hpenalty hobs hrep hfail) fetchPrepare
  have candidate : prepared 28=.rational ((repairEntry child).objective fee penalty) := by
    simp [prepared,badPreparationValues]
  have cutoff : prepared 24=.rational penalty := rfl
  have fetchCompare : FetchesCode program (origin+(headerCode badPreparationCommands).length)
      (headerIfLessCode (origin+(headerCode badPreparationCommands).length) acceptRepairCommands) := fetched.append_right
  obtain ⟨lastTrace,after,lastHead,lastLast,lastChain,lastTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,lastMemory⟩ :=
    headerIfLess_trace_memory program input (origin+(headerCode badPreparationCommands).length) acceptRepairCommands
      prepared (acceptRepairValues prepared) fetchCompare first base n k ((repairEntry child).objective fee penalty) penalty
      acceptRepairCommands_valid (acceptRepairCommands_eval prepared) (firstPC.trans (congrArg (·+(headerCode badPreparationCommands).length) hpc))
      firstHeader firstBase candidate cutoff
  have firstBound : time program firstTrace ≤ 2475 := firstTime
  have lastBound : time program lastTrace ≤ 1125 := lastTime
  have joined:=joinTrace_spec program input firstTrace lastTrace before first after 2475 1125
    firstHead firstLast lastHead lastLast firstChain lastChain firstBound lastBound
  have original:=badChoice_original P values fee penalty previous tools
  refine ⟨joinTrace firstTrace lastTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,afterHeader,
    (afterHeader.value 31 (by decide)).trans original.1,
    (afterHeader.value 32 (by decide)).trans original.2.1,
    (afterHeader.value 33 (by decide)).trans original.2.2.1,
    (afterHeader.value 34 (by decide)).trans original.2.2.2.1,
    (afterHeader.value 22 (by decide)).trans original.2.2.2.2,
    afterBase,?_,firstFrame.trans afterFrame,afterOutput.trans firstOutput,
    joinTrace_memory firstTrace lastTrace before first base firstLast firstMemory lastMemory⟩
  rw [afterPC,positiveBadCode,List.length_append,headerIfLessCode_length]
  omega

end PDCompute.Solver
