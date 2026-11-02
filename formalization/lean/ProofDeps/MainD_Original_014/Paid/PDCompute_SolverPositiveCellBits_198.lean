module

public import Paid.PDCompute_SolverNonzeroCellBits_197
public import Paid.PDCompute_SolverChoicePostBits_186
public import Paid.PDCompute_SolverRationalBranchBits_177
public import Paid.PDCompute_SolverPositiveCell_117

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace PDCompute.Solver
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
attribute [local irreducible] positiveCellFieldsCode nonzeroCellFieldsCode

/-- Original actual zero/nonzero rational penalty dispatch, SAME-B
including both true branches and actual selected original fields. -/
theorem positiveCellFields_trace_bits (mode : ReaderMode) (program : Program) (input : List Cell)
    (origin : ℕ) (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (tools : ℕ)
    (before : State) (base n k source goodPointer badPointer budget S : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (hpenalty : values 2=.rational penalty)
    (hfee : values 5=.rational fee) (last : values 6=.natural P.certificate.M) (htools : values 20=.natural tools)
    (hgood : values 35=.natural goodPointer) (hbad : values 36=.natural badPointer)
    (goodSource : PDLower.CalibrationCompute.HeapList before goodPointer (denseEncodeEntry (previous.getD tools abandonEntry)))
    (badSource : tools ≠ 0 → PDLower.CalibrationCompute.HeapList before badPointer (denseEncodeEntry (previous.getD (tools-1) abandonEntry)))
    (goodOutside : ∀ offset < 6,goodPointer+offset < base ∨ base+headerWords ≤ goodPointer+offset)
    (badOutside : tools ≠ 0 → ∀ offset < 6,badPointer+offset < base ∨ base+headerWords ≤ badPointer+offset)
    (safe : RootD27.Bits.SafeBits before budget)
    (bounds : ∀ column,ratEncodingBits (previous.getD column abandonEntry).observation≤S ∧
      ratEncodingBits (previous.getD column abandonEntry).repairs≤S ∧ ratEncodingBits (previous.getD column abandonEntry).failure≤S)
    (room : 1+64*(maximumMenuBits P fee+16*(2*(S+3)+maximumMenuBits P fee+ratEncodingBits penalty+1)+1)≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (goodPointerBits : 1+natBits (goodPointer+6)≤budget)
    (badPointerBits : tools≠0 → 1+natBits (badPointer+6)≤budget) (indexBits : 1+natBits (P.certificate.M+1)≤budget)
    (sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget)
    (counter : natBits (origin+(positiveCellFieldsCode mode origin).length)≤budget)
    (fetch : FetchesCode program origin (positiveCellFieldsCode mode origin)) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 2500*(P.certificate.M+1)+15870 ∧ Header after base afterValues ∧
      DenseFields afterValues (P.cachedNextMenuEntry P.endpointCache fee penalty previous tools) ∧
      (∀ slot,SolverControlSlot slot → afterValues slot=values slot) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(positiveCellFieldsCode mode origin).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state ∈ trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let zeroValues:=Function.update values 46 (.rational 0)
  let zeroCode:=headerCode [.constant 46 (.rational 0)]
  let guardOrigin:=origin+zeroCode.length
  let guard:=rationalBranchCode .equal 2 46
  let first : ℕ → List Instruction:=fun _ => headerCode (terminalFieldsCommands true)
  let second:=nonzeroCellFieldsCode mode
  have small : 4≤budget := (solverCell_guard_rooms S (maximumMenuBits P fee) (ratEncodingBits penalty) budget room).1
  have wholeCode : positiveCellFieldsCode mode origin=zeroCode++choiceCode guard first second guardOrigin := by
    unfold positiveCellFieldsCode
    rfl
  rw [wholeCode] at fetch
  have size : ∀ a b,(guard a b).length=8 := by intro a b; rfl
  have codeEnd:=choiceCode_end guard first second size guardOrigin
  have wholeEnd : origin+(positiveCellFieldsCode mode origin).length=choiceEndPC first second guardOrigin := by
    rw [wholeCode,List.length_append,←codeEnd]
    exact (Nat.add_assoc _ _ _).symm
  have endBits : natBits (choiceEndPC first second guardOrigin)≤budget := by rw [←wholeEnd];exact counter
  have firstBits : natBits (choiceFirstPC guardOrigin)≤budget :=
    (natBits_mono (by simp only [choiceEndPC,choiceSecondPC,choiceFirstPC];omega : choiceFirstPC guardOrigin≤choiceEndPC first second guardOrigin)).trans endBits
  have secondBits : natBits (choiceSecondPC first guardOrigin)≤budget :=
    (natBits_mono (by unfold choiceEndPC;omega : choiceSecondPC first guardOrigin≤choiceEndPC first second guardOrigin)).trans endBits
  have zeroCounter : natBits (before.pc+zeroCode.length)≤budget :=
    (natBits_mono (by rw [hpc,wholeCode,List.length_append];omega : before.pc+zeroCode.length≤origin+(positiveCellFieldsCode mode origin).length)).trans counter
  let post := fun next : ℕ → Cell =>
    DenseFields next (P.cachedNextMenuEntry P.endpointCache fee penalty previous tools) ∧
      ∀ slot,SolverControlSlot slot → next slot=zeroValues slot
  have zeroFetch : FetchesCode program before.pc zeroCode := by rw [hpc]; exact fetch.append_left
  obtain ⟨zeroTrace,cleared,zeroHead,zeroLast,zeroChain,zeroTime,clearedHeader,clearedBase,clearedPC,
    zeroFrame,zeroOutput,zeroResources⟩:=
    headerCode_trace_bits [.constant 46 (.rational 0)] program input before base n k budget values zeroValues
      (by intro command member; have same:=List.mem_singleton.mp member; subst command; dsimp only [HeaderCommand.Valid,headerWords]; decide) header hbase rfl safe
        ⟨zeroValues,rfl,(HeaderValueBits.of_safe header safe).update (by norm_num [Cell.bits,ratEncodingBits,ratNumBits,ratDenBits,natBits];omega),True.intro⟩
        addressBits zeroCounter zeroFetch
  have zeroMemory : ∀ state∈zeroTrace,HeaderMemory before state base := fun state member=>(zeroResources state member).1
  have zeroSafe : ∀ state∈zeroTrace,RootD27.Bits.SafeBits state budget := fun state member=>(zeroResources state member).2
  have zeroBound : time program zeroTrace ≤ 330 := zeroTime
  have clearedAt : cleared.pc=guardOrigin := by rw [clearedPC,hpc]
  have zeroKeep (slot : ℕ) (different : slot ≠ 46) : zeroValues slot=values slot := Function.update_of_ne different _ _
  have choiceFetch : FetchesCode program guardOrigin (choiceCode guard first second guardOrigin) := fetch.append_right
  have guarded : HeaderBlockBits program input cleared base n k budget zeroValues
      (if decide (penalty=0) then choiceFirstPC guardOrigin else choiceSecondPC first guardOrigin) 135 := by
    have guardFetch : FetchesCode program cleared.pc (guard (choiceSecondPC first guardOrigin) (choiceFirstPC guardOrigin)) := by
      rw [clearedAt]
      exact choice_guard_fetch guard first second program guardOrigin choiceFetch
    have compareCounter : natBits (cleared.pc+7)≤budget :=
      (natBits_mono (by rw [clearedAt];unfold choiceFirstPC;omega : cleared.pc+7≤choiceFirstPC guardOrigin)).trans firstBits
    obtain ⟨trace,after,head,last,chain,cost,afterHeader,afterBase,afterPC,frame,output,memory,bounded⟩:=
      rationalBranch_trace_bits program input cleared base n k 2 46 (choiceSecondPC first guardOrigin) (choiceFirstPC guardOrigin) budget penalty 0 .equal zeroValues
        clearedHeader (by decide) (by decide) ((zeroKeep 2 (by decide)).trans hpenalty) rfl clearedBase
        (zeroSafe cleared (List.mem_of_getLast? zeroLast)) small addressBits compareCounter secondBits firstBits guardFetch
    refine ⟨trace,after,head,last,chain,cost,afterHeader,afterBase,?_,frame,output,memory,bounded⟩
    simpa only [Comparison.rat,beq_iff_eq,decide_eq_true_eq] using afterPC
  have firstRun : ∀ state : State,decide (penalty=0)=true → state.pc=choiceFirstPC guardOrigin →
      Header state base zeroValues → state.register .fresh=.natural base → HeaderMemory cleared state base → RootD27.Bits.SafeBits state budget →
      FetchesCode program state.pc (first (choiceFirstPC guardOrigin)) →
      ∃ next,HeaderBlockBits program input state base n k budget next
        (choiceFirstPC guardOrigin+(first (choiceFirstPC guardOrigin)).length) 1155 ∧ post next := by
    intro state zero statePC stateHeader stateBase _ stateSafe stateFetch
    have penaltyZero : penalty=0 := of_decide_eq_true zero
    have bodyCounter : natBits (state.pc+(headerCode (terminalFieldsCommands true)).length)≤budget :=
      (natBits_mono (by rw [statePC];simp only [choiceEndPC,choiceSecondPC,first];omega :
        state.pc+(headerCode (terminalFieldsCommands true)).length≤choiceEndPC first second guardOrigin)).trans endBits
    obtain ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,afterPC,frame,output,resources⟩:=
      terminalFields_trace_bits true program input state base n k budget zeroValues stateHeader stateBase stateSafe small addressBits bodyCounter stateFetch
    refine ⟨terminalFieldsValues zeroValues true,?_,?_,?_⟩
    · exact ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,by simpa only [statePC] using afterPC,frame,output,(fun later member=>(resources later member).1),(fun later member=>(resources later member).2)⟩
    · simpa only [Parameters.cachedNextMenuEntry,penaltyZero,ite_true] using terminalFieldsValues_dense true zeroValues
    · exact fun slot control => terminalFieldsValues_controls zeroValues true slot control
  have secondRun : ∀ state : State,decide (penalty=0)=false → state.pc=choiceSecondPC first guardOrigin →
      Header state base zeroValues → state.register .fresh=.natural base → HeaderMemory cleared state base → RootD27.Bits.SafeBits state budget →
      FetchesCode program state.pc (second (choiceSecondPC first guardOrigin)) →
      ∃ next,HeaderBlockBits program input state base n k budget next
        (choiceEndPC first second guardOrigin) (2500*(P.certificate.M+1)+14220) ∧ post next := by
    intro state nonzero statePC stateHeader stateBase memory stateSafe stateFetch
    have penaltyNonzero : penalty ≠ 0 := of_decide_eq_false nonzero
    have fromBefore : HeaderMemory before state base := (HeaderMemory.trace_last zeroMemory zeroLast).trans memory
    have actualSource:=EndpointSource.frame_of_avoids mode input P source base n k before state hsource avoids (fromBefore.frame n k)
    have actualGood:=fromBefore.heapList goodSource (by
      intro offset bound
      exact goodOutside offset (by simpa only [denseEncodeEntry_length,entryWords] using bound))
    have actualBad : tools ≠ 0 → PDLower.CalibrationCompute.HeapList state badPointer
        (denseEncodeEntry (previous.getD (tools-1) abandonEntry)) := by
      intro positive
      apply fromBefore.heapList (badSource positive)
      intro offset bound
      exact badOutside positive offset (by simpa only [denseEncodeEntry_length,entryWords] using bound)
    have actualFetch : FetchesCode program (choiceSecondPC first guardOrigin) (nonzeroCellFieldsCode mode (choiceSecondPC first guardOrigin)) := by
      simpa only [statePC,second] using stateFetch
    obtain ⟨trace,after,next,head,last,chain,bound,afterHeader,fields,controls,afterBase,afterPC,frame,output,allMemory,allSafe⟩:=
      nonzeroCellFields_trace_bits mode program input (choiceSecondPC first guardOrigin) P fee penalty previous tools state
        base n k source goodPointer badPointer budget S zeroValues statePC stateHeader stateBase actualSource avoids
        ((zeroKeep 0 (by decide)).trans hsourceValue) ((zeroKeep 2 (by decide)).trans hpenalty)
        ((zeroKeep 5 (by decide)).trans hfee) ((zeroKeep 6 (by decide)).trans last) ((zeroKeep 20 (by decide)).trans htools)
        ((zeroKeep 35 (by decide)).trans hgood) ((zeroKeep 36 (by decide)).trans hbad)
        actualGood actualBad goodOutside badOutside penaltyNonzero stateSafe bounds room addressBits goodPointerBits badPointerBits indexBits sourceBits
        (by simpa only [choiceEndPC,second] using endBits) actualFetch
    exact ⟨next,⟨trace,after,head,last,chain,bound,afterHeader,afterBase,afterPC,frame,output,allMemory,allSafe⟩,fields,controls⟩
  obtain ⟨next,choiceRun,fields,controls⟩:=choice_compose_post_bits guard first second size program input cleared base n k
    guardOrigin budget 1155 (2500*(P.certificate.M+1)+14220) zeroValues (decide (penalty=0)) post choiceFetch endBits guarded firstRun secondRun
  obtain ⟨choiceTrace,after,choiceHead,choiceLast,choiceChain,choiceTime,afterHeader,afterBase,afterPC,choiceFrame,choiceOutput,choiceMemory,choiceSafe⟩:=choiceRun
  have choiceBound : time program choiceTrace ≤ 2500*(P.certificate.M+1)+15540 := by
    calc
      _ ≤ 165+1155+(2500*(P.certificate.M+1)+14220) := choiceTime
      _ = _ := by ring
  have joined:=joinTrace_spec program input zeroTrace choiceTrace before cleared after 330 (2500*(P.certificate.M+1)+15540)
    zeroHead zeroLast choiceHead choiceLast zeroChain choiceChain zeroBound choiceBound
  refine ⟨joinTrace zeroTrace choiceTrace,after,next,joined.1,joined.2.1,joined.2.2.1,?_,afterHeader,fields,?_,afterBase,?_,
    zeroFrame.trans choiceFrame,choiceOutput.trans zeroOutput,
    joinTrace_memory zeroTrace choiceTrace before cleared base zeroLast zeroMemory choiceMemory,
    PDCompute.Pack.joinTrace_invariant zeroTrace choiceTrace (fun state=>RootD27.Bits.SafeBits state budget) zeroSafe choiceSafe⟩
  · calc
      _ ≤ 330+(2500*(P.certificate.M+1)+15540) := joined.2.2.2
      _ = _ := by ring
  · intro slot control
    have different : slot ≠ 46 := by unfold SolverControlSlot at control; omega
    exact (controls slot control).trans (zeroKeep slot different)
  · rw [afterPC,←codeEnd,positiveCellFieldsCode,List.length_append]
    change guardOrigin+(choiceCode guard first second guardOrigin).length=
      origin+(zeroCode.length+(choiceCode guard first second guardOrigin).length)
    exact Nat.add_assoc _ _ _


end PDCompute.Solver
