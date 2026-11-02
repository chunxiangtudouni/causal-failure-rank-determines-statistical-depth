module

public import Paid.PDCompute_SolverSelectedTestingBits_194
public import Paid.PDCompute_SolverRationalBranchBits_177
public import Paid.PDCompute_SolverChoiceBits_176
public import Paid.PDCompute_SolverSelectedChoice_103

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

theorem HeaderBlockBits.empty (program : Program) (input : List Cell) (before : State) (base n k budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget) :
    HeaderBlockBits program input before base n k budget values before.pc 15 := by
  refine ⟨[before],before,rfl,rfl,.singleton before,time_singleton_le program before,header,fresh,rfl,
    ⟨fun _ _=>rfl,fun _ _=>Iff.rfl⟩,rfl,?_,?_⟩
  · intro state member
    have same:=List.mem_singleton.mp member
    subst state
    exact HeaderMemory.refl before base
  · intro state member
    have same:=List.mem_singleton.mp member
    subst state
    exact safe

/-- Real outer STRICT score/penalty comparison and actual selected
reconstruction. Equal score really keeps abandonment; no selected
answer or fictitious branch is supplied to the machine. -/
theorem selectedChoice_trace_bits (mode : ReaderMode) (program : Program) (input : List Cell)
    (P : Parameters) (fee penalty score : ℚ) (previous : MenuRow) (tools source level : ℕ)
    (before : State) (base n k budget S : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (hlevel : values 23=.natural level) (bound : level≤P.certificate.M)
    (hscore : values 28=.rational score) (hpenalty : values 24=.rational penalty)
    (hgo : values 10=.rational (previous.getD tools abandonEntry).observation)
    (hgr : values 11=.rational (previous.getD tools abandonEntry).repairs) (hgf : values 12=.rational (previous.getD tools abandonEntry).failure)
    (hbo : values 31=.rational (P.menuBadBranch fee penalty previous tools).2.observation)
    (hbr : values 32=.rational (P.menuBadBranch fee penalty previous tools).2.repairs) (hbf : values 33=.rational (P.menuBadBranch fee penalty previous tools).2.failure)
    (hb : values 34=.natural (if (P.menuBadBranch fee penalty previous tools).1=.repair then 1 else 0))
    (safe : RootD27.Bits.SafeBits before budget)
    (goBits : ratEncodingBits (previous.getD tools abandonEntry).observation≤S)
    (grBits : ratEncodingBits (previous.getD tools abandonEntry).repairs≤S) (gfBits : ratEncodingBits (previous.getD tools abandonEntry).failure≤S)
    (boBits : ratEncodingBits (P.menuBadBranch fee penalty previous tools).2.observation≤S)
    (brBits : ratEncodingBits (P.menuBadBranch fee penalty previous tools).2.repairs≤S) (bfBits : ratEncodingBits (P.menuBadBranch fee penalty previous tools).2.failure≤S)
    (room : 1+64*(maximumMenuBits P fee+S+1)≤budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget)
    (counter : natBits (before.pc+(selectedChoiceCode mode before.pc).length)≤budget)
    (fetch : FetchesCode program before.pc (selectedChoiceCode mode before.pc)) :
    HeaderBlockBits program input before base n k budget (selectedChoiceValues mode P values fee penalty score previous tools source level)
      (before.pc+(selectedChoiceCode mode before.pc).length) 3300 := by
  let guard:=rationalBranchCode .less 28 24
  let first : ℕ → List Instruction:=fun _=>selectedTestingCode mode
  let second : ℕ → List Instruction:=fun _=>[]
  have size : ∀ a b,(guard a b).length=8 := by intro a b; rfl
  have codeFetch : FetchesCode program before.pc (choiceCode guard first second before.pc) := fetch
  have codeEnd:=choiceCode_end guard first second size before.pc
  have endBits : natBits (choiceEndPC first second before.pc)≤budget := by simpa only [←codeEnd,selectedChoiceCode,guard,first,second] using counter
  have firstBits : natBits (choiceFirstPC before.pc)≤budget :=
    (natBits_mono (by simp only [choiceEndPC,choiceSecondPC,choiceFirstPC]; omega : choiceFirstPC before.pc≤choiceEndPC first second before.pc)).trans endBits
  have secondBits : natBits (choiceSecondPC first before.pc)≤budget :=
    (natBits_mono (by unfold choiceEndPC; omega : choiceSecondPC first before.pc≤choiceEndPC first second before.pc)).trans endBits
  have small : 4≤budget := by omega
  have guarded : HeaderBlockBits program input before base n k budget values
      (if decide (score<penalty) then choiceFirstPC before.pc else choiceSecondPC first before.pc) 135 :=
    rationalBranch_trace_bits program input before base n k 28 24 (choiceSecondPC first before.pc) (choiceFirstPC before.pc) budget score penalty .less values
      header (by decide) (by decide) hscore hpenalty fresh safe small addressBits
      ((natBits_mono (by unfold choiceFirstPC; omega : before.pc+7≤choiceFirstPC before.pc)).trans firstBits) secondBits firstBits
      (choice_guard_fetch guard first second program before.pc codeFetch)
  have firstRun : ∀ state : State,decide (score<penalty)=true → state.pc=choiceFirstPC before.pc → Header state base values →
      state.register .fresh=.natural base → HeaderMemory before state base → RootD27.Bits.SafeBits state budget →
      FetchesCode program state.pc (first (choiceFirstPC before.pc)) →
      HeaderBlockBits program input state base n k budget (selectedTestingValues P values fee penalty previous tools source level)
        (choiceFirstPC before.pc+(first (choiceFirstPC before.pc)).length) 3120 := by
    intro state _ statePC stateHeader stateBase memory stateSafe stateFetch
    have stateSource:=EndpointSource.frame_of_avoids mode input P source base n k before state hsource avoids (memory.frame n k)
    have bodyCounter : natBits (state.pc+(selectedTestingCode mode).length)≤budget :=
      (natBits_mono (by rw [statePC]; unfold choiceEndPC choiceSecondPC; simp only [first,second,List.length_nil,Nat.add_zero]; omega :
        state.pc+(selectedTestingCode mode).length≤choiceEndPC first second before.pc)).trans endBits
    obtain ⟨trace,after,head,last,chain,cost,afterHeader,_,afterBase,afterPC,frame,output,allMemory,allSafe⟩:=
      selectedTesting_trace_bits mode program input P fee penalty previous tools source level state base n k budget S values stateHeader stateBase stateSource avoids
        hsourceValue hlevel bound hgo hgr hgf hbo hbr hbf hb stateSafe goBits grBits gfBits boBits brBits bfBits room addressBits sourceBits bodyCounter stateFetch
    exact ⟨trace,after,head,last,chain,cost,afterHeader,afterBase,by simpa only [statePC] using afterPC,frame,output,allMemory,allSafe⟩
  have secondRun : ∀ state : State,decide (score<penalty)=false → state.pc=choiceSecondPC first before.pc → Header state base values →
      state.register .fresh=.natural base → HeaderMemory before state base → RootD27.Bits.SafeBits state budget →
      FetchesCode program state.pc (second (choiceSecondPC first before.pc)) →
      HeaderBlockBits program input state base n k budget values (choiceEndPC first second before.pc) 15 := by
    intro state _ statePC stateHeader stateBase _ stateSafe _
    simpa only [choiceEndPC,second,List.length_nil,Nat.add_zero,statePC] using HeaderBlockBits.empty program input state base n k budget values stateHeader stateBase stateSafe
  have run:=choice_compose_bits guard first second size program input before base n k before.pc budget 3120 15 values
    (selectedTestingValues P values fee penalty previous tools source level) values (decide (score<penalty)) codeFetch endBits guarded firstRun secondRun
  simpa only [selectedChoiceValues,selectedChoiceCode,guard,first,second,decide_eq_true_eq,←codeEnd] using run

end PDCompute.Solver
