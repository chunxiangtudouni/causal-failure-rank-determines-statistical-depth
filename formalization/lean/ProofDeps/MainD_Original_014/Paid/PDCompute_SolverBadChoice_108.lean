module

public import Paid.PDCompute_SolverLoadedBad_107
public import Paid.PDCompute_SolverHeaderBlock_102
public import Paid.PDCompute_SolverNatBranch_089
public import Paid.PDCompute_SolverZeroBadRuntime_083

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def badChoiceCode (origin : ℕ) : List Instruction :=
  choiceCode (naturalBranchCode .equal 20 46) (fun _ => headerCode zeroBadCommands) loadedBadCode origin

def badChoiceValues (values : ℕ → Cell) (fee penalty : ℚ) (previous : MenuRow) (tools : ℕ) : ℕ → Cell :=
  if tools=0 then zeroBadValues values penalty else loadedBadValues values fee penalty (previous.getD (tools-1) abandonEntry)

/-- A single fixed natural branch chooses tools-zero abandonment or
the real preceding-tools read. The preceding entry is required ONLY for
the actually positive tools case. -/
theorem badChoice_trace_memory (program : Program) (input : List Cell) (origin : ℕ)
    (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (tools pointer : ℕ)
    (before : State) (base n k : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (htools : values 20=.natural tools) (hzero : values 46=.natural 0) (hpointer : values 36=.natural pointer)
    (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (source : tools ≠ 0 → PDLower.CalibrationCompute.HeapList before pointer (denseEncodeEntry (previous.getD (tools-1) abandonEntry)))
    (outside : tools ≠ 0 → ∀ offset < 6,pointer+offset < base ∨ base+headerWords ≤ pointer+offset)
    (fetch : FetchesCode program origin (badChoiceCode origin)) :
    HeaderBlockRun program input before base n k (badChoiceValues values fee penalty previous tools)
      (origin+(badChoiceCode origin).length) 5460 := by
  let guard:=naturalBranchCode .equal 20 46
  let first : ℕ → List Instruction:=fun _ => headerCode zeroBadCommands
  let second:=loadedBadCode
  have size : ∀ a b,(guard a b).length=8 := by intro a b; rfl
  have codeFetch : FetchesCode program origin (choiceCode guard first second origin) := fetch
  have guarded : HeaderBlockRun program input before base n k values
      (if decide (tools=0) then choiceFirstPC origin else choiceSecondPC first origin) 135 := by
    have guardFetch : FetchesCode program before.pc (guard (choiceSecondPC first origin) (choiceFirstPC origin)) := by
      rw [hpc]
      exact choice_guard_fetch guard first second program origin codeFetch
    have run:=naturalBranch_trace_memory program input before base n k 20 46 tools 0
      (choiceSecondPC first origin) (choiceFirstPC origin) .equal values header (by decide) (by decide) htools hzero hbase guardFetch
    simpa only [HeaderBlockRun,Comparison.nat,beq_iff_eq,decide_eq_true_eq] using run
  have firstRun : ∀ state : State, decide (tools=0)=true → state.pc=choiceFirstPC origin →
      Header state base values → state.register .fresh=.natural base → HeaderMemory before state base →
      FetchesCode program state.pc (first (choiceFirstPC origin)) →
      HeaderBlockRun program input state base n k (zeroBadValues values penalty)
        (choiceFirstPC origin+(first (choiceFirstPC origin)).length) 990 := by
    intro state _ statePC stateHeader stateBase _ stateFetch
    obtain ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,afterPC,frame,output,memory⟩:=
      zeroBad_trace_memory program input state base n k values penalty stateHeader stateBase hpenalty stateFetch
    exact ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,by simpa only [statePC] using afterPC,frame,output,memory⟩
  have secondRun : ∀ state : State, decide (tools=0)=false → state.pc=choiceSecondPC first origin →
      Header state base values → state.register .fresh=.natural base → HeaderMemory before state base →
      FetchesCode program state.pc (second (choiceSecondPC first origin)) →
      HeaderBlockRun program input state base n k
        (loadedBadValues values fee penalty (previous.getD (tools-1) abandonEntry))
        (choiceEndPC first second origin) 4305 := by
    intro state falseGuard statePC stateHeader stateBase memory stateFetch
    have positive : tools ≠ 0 := of_decide_eq_false falseGuard
    have actualSource:=memory.heapList (source positive) (by
      intro offset bound
      exact outside positive offset (by simpa only [denseEncodeEntry_length,entryWords] using bound))
    have actualFetch : FetchesCode program (choiceSecondPC first origin) (loadedBadCode (choiceSecondPC first origin)) := by
      simpa only [statePC,second] using stateFetch
    obtain ⟨trace,after,head,last,chain,bound,afterHeader,_,_,_,_,_,afterBase,afterPC,frame,output,allMemory⟩:=
      loadedBad_trace_memory program input (choiceSecondPC first origin) P fee penalty previous (tools-1) pointer
        state base n k values statePC stateHeader stateBase hpointer hfee hpenalty actualSource (outside positive) actualFetch
    exact ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,afterPC,frame,output,allMemory⟩
  have run:=choice_compose_memory guard first second size program input before base n k origin 990 4305
    values (zeroBadValues values penalty) (loadedBadValues values fee penalty (previous.getD (tools-1) abandonEntry))
    (decide (tools=0)) codeFetch guarded firstRun secondRun
  have endPC:=choiceCode_end guard first second size origin
  simpa only [badChoiceValues,badChoiceCode,guard,first,second,decide_eq_true_eq,← endPC] using run

theorem badChoiceValues_original (P : Parameters) (values : ℕ → Cell) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) :
    badChoiceValues values fee penalty previous tools 31=.rational (P.menuBadBranch fee penalty previous tools).2.observation ∧
    badChoiceValues values fee penalty previous tools 32=.rational (P.menuBadBranch fee penalty previous tools).2.repairs ∧
    badChoiceValues values fee penalty previous tools 33=.rational (P.menuBadBranch fee penalty previous tools).2.failure ∧
    badChoiceValues values fee penalty previous tools 34=.natural (if (P.menuBadBranch fee penalty previous tools).1=.repair then 1 else 0) ∧
    badChoiceValues values fee penalty previous tools 22=.rational ((P.menuBadBranch fee penalty previous tools).2.objective fee penalty) := by
  cases tools with
  | zero => simp [badChoiceValues,zeroBadValues,Parameters.menuBadBranch,abandonEntry,MenuEntry.objective]
  | succ tools =>
    simpa only [badChoiceValues,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,Nat.add_sub_cancel,
      loadedBadValues,positiveBadValues] using
      badChoice_original P (denseReadHeaderValues (denseEncodeEntry (previous.getD tools abandonEntry)) 13 values)
        fee penalty previous tools

end PDCompute.Solver
