module

public import Paid.PDCompute_SolverChoiceBits_176
public import Paid.PDCompute_SolverLoadedBadBits_169
public import Paid.PDCompute_SolverBadChoice_108
public import Paid.PDCompute_Nat_NaturalBranchBits_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- Real tools-zero dispatch and actual positive-tools read/repair
branch. The previous dense cell is required ONLY when really read;
arbitrary old live Header42 at tools zero adds no source assumption. -/
theorem badChoice_trace_bits (program : Program) (input : List Cell) (origin : ℕ)
    (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (tools pointer : ℕ)
    (before : State) (base n k budget S L T : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (htools : values 20=.natural tools) (hzero : values 46=.natural 0) (hpointer : values 36=.natural pointer)
    (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (source : tools≠0 → PDLower.CalibrationCompute.HeapList before pointer (denseEncodeEntry (previous.getD (tools-1) abandonEntry)))
    (outside : tools≠0 → ∀ offset<6,pointer+offset<base ∨ base+headerWords≤pointer+offset)
    (safe : RootD27.Bits.SafeBits before budget)
    (observation : tools≠0 → ratEncodingBits (previous.getD (tools-1) abandonEntry).observation≤S)
    (repairs : tools≠0 → ratEncodingBits (previous.getD (tools-1) abandonEntry).repairs≤S)
    (failure : tools≠0 → ratEncodingBits (previous.getD (tools-1) abandonEntry).failure≤S)
    (feeBits : ratEncodingBits fee≤L) (penaltyBits : ratEncodingBits penalty≤T) (room : 1+16*(2*(S+3)+L+T+1)≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pointerBits : tools≠0 → 1+natBits (pointer+6)≤budget)
    (counter : natBits (origin+(badChoiceCode origin).length)≤budget) (fetch : FetchesCode program origin (badChoiceCode origin)) :
    HeaderBlockBits program input before base n k budget (badChoiceValues values fee penalty previous tools)
      (origin+(badChoiceCode origin).length) 5460 := by
  let guard:=naturalBranchCode .equal 20 46
  let first : ℕ → List Instruction:=fun _=>headerCode zeroBadCommands
  let second:=loadedBadCode
  have size : ∀ a b,(guard a b).length=8 := by intro a b; rfl
  have codeFetch : FetchesCode program origin (choiceCode guard first second origin) := fetch
  have codeEnd:=choiceCode_end guard first second size origin
  have endBits : natBits (choiceEndPC first second origin)≤budget := by
    simpa only [←codeEnd,badChoiceCode,guard,first,second] using counter
  have firstBits : natBits (choiceFirstPC origin)≤budget :=
    (natBits_mono (by simp only [choiceEndPC,choiceSecondPC,choiceFirstPC]; omega : choiceFirstPC origin≤choiceEndPC first second origin)).trans endBits
  have secondBits : natBits (choiceSecondPC first origin)≤budget :=
    (natBits_mono (by unfold choiceEndPC; omega : choiceSecondPC first origin≤choiceEndPC first second origin)).trans endBits
  have small : 4≤budget := by omega
  have oneBits : (.natural 1 : Cell).bits≤budget := by norm_num [Cell.bits,natBits]; omega
  have guarded : HeaderBlockBits program input before base n k budget values
      (if decide (tools=0) then choiceFirstPC origin else choiceSecondPC first origin) 135 := by
    have guardFetch : FetchesCode program before.pc (guard (choiceSecondPC first origin) (choiceFirstPC origin)) := by
      rw [hpc]
      exact choice_guard_fetch guard first second program origin codeFetch
    obtain ⟨trace,after,head,last,chain,cost,afterHeader,afterBase,afterPC,frame,output,resources⟩:=
      PDCompute.NatControl.naturalBranch_trace_bits program input before base n k 20 46 tools 0 (choiceSecondPC first origin) (choiceFirstPC origin) budget .equal values
        header (by decide) (by decide) htools hzero fresh safe oneBits addressBits
        ((natBits_mono (by rw [hpc]; unfold choiceFirstPC; omega : before.pc+7≤choiceFirstPC origin)).trans firstBits)
        secondBits firstBits guardFetch
    refine ⟨trace,after,head,last,chain,cost,afterHeader,afterBase,?_,frame,output,
      (fun state member=>(resources state member).1),(fun state member=>(resources state member).2)⟩
    simpa only [Comparison.nat,beq_iff_eq,decide_eq_true_eq] using afterPC
  have firstRun : ∀ state : State,decide (tools=0)=true → state.pc=choiceFirstPC origin → Header state base values →
      state.register .fresh=.natural base → HeaderMemory before state base → RootD27.Bits.SafeBits state budget →
      FetchesCode program state.pc (first (choiceFirstPC origin)) →
      HeaderBlockBits program input state base n k budget (zeroBadValues values penalty)
        (choiceFirstPC origin+(first (choiceFirstPC origin)).length) 990 := by
    intro state _ statePC stateHeader stateBase _ stateSafe stateFetch
    have bodyCounter : natBits (state.pc+(headerCode zeroBadCommands).length)≤budget :=
      (natBits_mono (by rw [statePC]; simp only [choiceEndPC,choiceSecondPC,first]; omega : state.pc+(headerCode zeroBadCommands).length≤choiceEndPC first second origin)).trans endBits
    obtain ⟨trace,after,head,last,chain,cost,afterHeader,afterBase,afterPC,frame,output,resources⟩:=
      zeroBad_trace_bits program input state base n k budget values penalty stateHeader stateBase hpenalty stateSafe small addressBits bodyCounter stateFetch
    exact ⟨trace,after,head,last,chain,cost,afterHeader,afterBase,by simpa only [statePC] using afterPC,frame,output,
      (fun later member=>(resources later member).1),(fun later member=>(resources later member).2)⟩
  have secondRun : ∀ state : State,decide (tools=0)=false → state.pc=choiceSecondPC first origin → Header state base values →
      state.register .fresh=.natural base → HeaderMemory before state base → RootD27.Bits.SafeBits state budget →
      FetchesCode program state.pc (second (choiceSecondPC first origin)) →
      HeaderBlockBits program input state base n k budget (loadedBadValues values fee penalty (previous.getD (tools-1) abandonEntry))
        (choiceEndPC first second origin) 4305 := by
    intro state falseGuard statePC stateHeader stateBase memory stateSafe stateFetch
    have positive : tools≠0 := of_decide_eq_false falseGuard
    have actualSource:=memory.heapList (source positive) (by
      intro offset bound
      exact outside positive offset (by simpa only [denseEncodeEntry_length,entryWords] using bound))
    have actualFetch : FetchesCode program (choiceSecondPC first origin) (loadedBadCode (choiceSecondPC first origin)) := by simpa only [statePC,second] using stateFetch
    obtain ⟨trace,after,head,last,chain,cost,afterHeader,_,_,_,_,_,afterBase,afterPC,frame,output,allMemory,allSafe⟩:=
      loadedBad_trace_bits program input (choiceSecondPC first origin) P fee penalty previous (tools-1) pointer state base n k budget S L T values
        statePC stateHeader stateBase hpointer hfee hpenalty actualSource (outside positive) stateSafe (observation positive) (repairs positive) (failure positive)
        feeBits penaltyBits room addressBits (pointerBits positive) endBits actualFetch
    exact ⟨trace,after,head,last,chain,cost,afterHeader,afterBase,afterPC,frame,output,allMemory,allSafe⟩
  have run:=choice_compose_bits guard first second size program input before base n k origin budget 990 4305 values
    (zeroBadValues values penalty) (loadedBadValues values fee penalty (previous.getD (tools-1) abandonEntry)) (decide (tools=0))
    codeFetch endBits guarded firstRun secondRun
  simpa only [badChoiceValues,badChoiceCode,guard,first,second,decide_eq_true_eq,←codeEnd] using run

end PDCompute.Solver
