module

public import Paid.PDCompute_SolverNonzeroCell_115
public import Paid.PDCompute_SolverChoicePost_116

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

attribute [local irreducible] nonzeroCellFieldsCode

theorem terminalFieldsValues_controls (values : ℕ → Cell) (abandon : Bool) (slot : ℕ)
    (control : SolverControlSlot slot) : terminalFieldsValues values abandon slot=values slot := by
  have h40 : slot ≠ 40 := by unfold SolverControlSlot at control; omega
  have h41 : slot ≠ 41 := by unfold SolverControlSlot at control; omega
  have h42 : slot ≠ 42 := by unfold SolverControlSlot at control; omega
  have h43 : slot ≠ 43 := by unfold SolverControlSlot at control; omega
  have h44 : slot ≠ 44 := by unfold SolverControlSlot at control; omega
  have h45 : slot ≠ 45 := by unfold SolverControlSlot at control; omega
  simp only [terminalFieldsValues,Function.update_of_ne h40,Function.update_of_ne h41,Function.update_of_ne h42,
    Function.update_of_ne h43,Function.update_of_ne h44,Function.update_of_ne h45]

/-- ALL rational penalties, with the original zero-penalty branch
performed by a real rational equality guard in the same fixed program. -/
theorem positiveCellFields_trace_memory (mode : ReaderMode) (program : Program) (input : List Cell)
    (origin : ℕ) (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (tools : ℕ)
    (before : State) (base n k source goodPointer badPointer : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (hpenalty : values 2=.rational penalty)
    (hfee : values 5=.rational fee) (last : values 6=.natural P.certificate.M) (htools : values 20=.natural tools)
    (hgood : values 35=.natural goodPointer) (hbad : values 36=.natural badPointer)
    (goodSource : PDLower.CalibrationCompute.HeapList before goodPointer (denseEncodeEntry (previous.getD tools abandonEntry)))
    (badSource : tools ≠ 0 → PDLower.CalibrationCompute.HeapList before badPointer (denseEncodeEntry (previous.getD (tools-1) abandonEntry)))
    (goodOutside : ∀ offset < 6,goodPointer+offset < base ∨ base+headerWords ≤ goodPointer+offset)
    (badOutside : tools ≠ 0 → ∀ offset < 6,badPointer+offset < base ∨ base+headerWords ≤ badPointer+offset)
    (fetch : FetchesCode program origin (positiveCellFieldsCode mode origin)) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 2500*(P.certificate.M+1)+15870 ∧ Header after base afterValues ∧
      DenseFields afterValues (P.cachedNextMenuEntry P.endpointCache fee penalty previous tools) ∧
      (∀ slot,SolverControlSlot slot → afterValues slot=values slot) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(positiveCellFieldsCode mode origin).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace,HeaderMemory before state base := by
  let zeroValues:=Function.update values 46 (.rational 0)
  let zeroCode:=headerCode [.constant 46 (.rational 0)]
  let guardOrigin:=origin+zeroCode.length
  let guard:=rationalBranchCode .equal 2 46
  let first : ℕ → List Instruction:=fun _ => headerCode (terminalFieldsCommands true)
  let second:=nonzeroCellFieldsCode mode
  let post := fun next : ℕ → Cell =>
    DenseFields next (P.cachedNextMenuEntry P.endpointCache fee penalty previous tools) ∧
      ∀ slot,SolverControlSlot slot → next slot=zeroValues slot
  have zeroFetch : FetchesCode program before.pc zeroCode := by rw [hpc]; exact fetch.append_left
  obtain ⟨zeroTrace,cleared,zeroHead,zeroLast,zeroChain,zeroTime,clearedHeader,clearedBase,clearedPC,
    zeroFrame,zeroOutput,zeroMemory⟩:=
    headerCode_trace_memory [.constant 46 (.rational 0)] program input before base n k values zeroValues
      (by intro command member; have same:=List.mem_singleton.mp member; subst command; dsimp only [HeaderCommand.Valid,headerWords]; decide) header hbase rfl zeroFetch
  have zeroBound : time program zeroTrace ≤ 330 := zeroTime
  have clearedAt : cleared.pc=guardOrigin := by rw [clearedPC,hpc]
  have zeroKeep (slot : ℕ) (different : slot ≠ 46) : zeroValues slot=values slot := Function.update_of_ne different _ _
  have choiceFetch : FetchesCode program guardOrigin (choiceCode guard first second guardOrigin) := fetch.append_right
  have size : ∀ a b,(guard a b).length=8 := by intro a b; rfl
  have guarded : HeaderBlockRun program input cleared base n k zeroValues
      (if decide (penalty=0) then choiceFirstPC guardOrigin else choiceSecondPC first guardOrigin) 135 := by
    have guardFetch : FetchesCode program cleared.pc (guard (choiceSecondPC first guardOrigin) (choiceFirstPC guardOrigin)) := by
      rw [clearedAt]
      exact choice_guard_fetch guard first second program guardOrigin choiceFetch
    have run:=rationalBranch_trace_memory program input cleared base n k 2 46
      (choiceSecondPC first guardOrigin) (choiceFirstPC guardOrigin) penalty 0 .equal zeroValues clearedHeader
      (by decide) (by decide) ((zeroKeep 2 (by decide)).trans hpenalty) rfl clearedBase guardFetch
    simpa only [HeaderBlockRun,Comparison.rat,beq_iff_eq,decide_eq_true_eq] using run
  have firstRun : ∀ state : State,decide (penalty=0)=true → state.pc=choiceFirstPC guardOrigin →
      Header state base zeroValues → state.register .fresh=.natural base → HeaderMemory cleared state base →
      FetchesCode program state.pc (first (choiceFirstPC guardOrigin)) →
      ∃ next,HeaderBlockRun program input state base n k next
        (choiceFirstPC guardOrigin+(first (choiceFirstPC guardOrigin)).length) 1155 ∧ post next := by
    intro state zero statePC stateHeader stateBase _ stateFetch
    have penaltyZero : penalty=0 := of_decide_eq_true zero
    obtain ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,afterPC,frame,output,memory⟩:=
      terminalFields_trace_memory true program input state base n k zeroValues stateHeader stateBase stateFetch
    refine ⟨terminalFieldsValues zeroValues true,?_,?_,?_⟩
    · exact ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,by simpa only [statePC] using afterPC,frame,output,memory⟩
    · simpa only [Parameters.cachedNextMenuEntry,penaltyZero,ite_true] using terminalFieldsValues_dense true zeroValues
    · exact fun slot control => terminalFieldsValues_controls zeroValues true slot control
  have secondRun : ∀ state : State,decide (penalty=0)=false → state.pc=choiceSecondPC first guardOrigin →
      Header state base zeroValues → state.register .fresh=.natural base → HeaderMemory cleared state base →
      FetchesCode program state.pc (second (choiceSecondPC first guardOrigin)) →
      ∃ next,HeaderBlockRun program input state base n k next
        (choiceEndPC first second guardOrigin) (2500*(P.certificate.M+1)+14220) ∧ post next := by
    intro state nonzero statePC stateHeader stateBase memory stateFetch
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
    obtain ⟨trace,after,next,head,last,chain,bound,afterHeader,fields,controls,afterBase,afterPC,frame,output,allMemory⟩:=
      nonzeroCellFields_trace_memory mode program input (choiceSecondPC first guardOrigin) P fee penalty previous tools state
        base n k source goodPointer badPointer zeroValues statePC stateHeader stateBase actualSource avoids
        ((zeroKeep 0 (by decide)).trans hsourceValue) ((zeroKeep 2 (by decide)).trans hpenalty)
        ((zeroKeep 5 (by decide)).trans hfee) ((zeroKeep 6 (by decide)).trans last) ((zeroKeep 20 (by decide)).trans htools)
        ((zeroKeep 35 (by decide)).trans hgood) ((zeroKeep 36 (by decide)).trans hbad)
        actualGood actualBad goodOutside badOutside penaltyNonzero actualFetch
    exact ⟨next,⟨trace,after,head,last,chain,bound,afterHeader,afterBase,afterPC,frame,output,allMemory⟩,fields,controls⟩
  obtain ⟨next,choiceRun,fields,controls⟩:=choice_compose_post_memory guard first second size program input cleared base n k
    guardOrigin 1155 (2500*(P.certificate.M+1)+14220) zeroValues (decide (penalty=0)) post choiceFetch guarded firstRun secondRun
  obtain ⟨choiceTrace,after,choiceHead,choiceLast,choiceChain,choiceTime,afterHeader,afterBase,afterPC,choiceFrame,choiceOutput,choiceMemory⟩:=choiceRun
  have choiceBound : time program choiceTrace ≤ 2500*(P.certificate.M+1)+15540 := by
    calc
      _ ≤ 165+1155+(2500*(P.certificate.M+1)+14220) := choiceTime
      _ = _ := by ring
  have joined:=joinTrace_spec program input zeroTrace choiceTrace before cleared after 330 (2500*(P.certificate.M+1)+15540)
    zeroHead zeroLast choiceHead choiceLast zeroChain choiceChain zeroBound choiceBound
  refine ⟨joinTrace zeroTrace choiceTrace,after,next,joined.1,joined.2.1,joined.2.2.1,?_,afterHeader,fields,?_,afterBase,?_,
    zeroFrame.trans choiceFrame,choiceOutput.trans zeroOutput,
    joinTrace_memory zeroTrace choiceTrace before cleared base zeroLast zeroMemory choiceMemory⟩
  · calc
      _ ≤ 330+(2500*(P.certificate.M+1)+15540) := joined.2.2.2
      _ = _ := by ring
  · intro slot control
    have different : slot ≠ 46 := by unfold SolverControlSlot at control; omega
    exact (controls slot control).trans (zeroKeep slot different)
  · have choiceEnd:=choiceCode_end guard first second size guardOrigin
    rw [afterPC,← choiceEnd,positiveCellFieldsCode,List.length_append]
    change guardOrigin+(choiceCode guard first second guardOrigin).length=
      origin+(zeroCode.length+(choiceCode guard first second guardOrigin).length)
    exact Nat.add_assoc _ _ _

end PDCompute.Solver
