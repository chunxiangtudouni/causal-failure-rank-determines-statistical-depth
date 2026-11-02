module

public import Paid.PDCompute_SolverPositiveCell_117
public import Paid.PDCompute_SolverOriginalGrid_111

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

attribute [local irreducible] positiveCellFieldsCode

def SolverPersistentSlot (slot : ℕ) : Prop := SolverControlSlot slot ∧ slot ≠ 37

/-- Every row and column, including row zero and penalty zero. Previous
entries are obtained from the REAL completed dense prefix, not offered
as a precomputed whole row or a cell-computation oracle. -/
theorem cellFields_trace_memory (mode : ReaderMode) (program : Program) (input : List Cell)
    (origin : ℕ) (P : Parameters) (fee penalty : ℚ) (row column : ℕ)
    (before : State) (base n k source : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (hpenalty : values 2=.rational penalty)
    (hfee : values 5=.rational fee) (last : values 6=.natural P.certificate.M)
    (hrow : values 19=.natural row) (hcolumn : values 20=.natural column) (columnBound : column ≤ k)
    (hgood : values 35=.natural (cellBase base k (row-1) column))
    (hbad : values 36=.natural (cellBase base k (row-1) column-6))
    (hwrite : values 37=.natural (cellBase base k (row-1) column+6*(k+1)))
    (prior : DensePrefix before base k (solverEntry P fee penalty k) (row*(k+1)+column))
    (fetch : FetchesCode program origin (cellFieldsCode mode origin)) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 2500*(P.certificate.M+1)+17685 ∧ Header after base afterValues ∧
      DenseFields afterValues (solverEntry P fee penalty k row column) ∧
      afterValues 37=.natural (cellBase base k row column) ∧
      (∀ slot,SolverPersistentSlot slot → afterValues slot=values slot) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(cellFieldsCode mode origin).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace,HeaderMemory before state base := by
  let zeroValues:=Function.update values 46 (.natural 0)
  let zeroCode:=headerCode [.constant 46 (.natural 0)]
  let guardOrigin:=origin+zeroCode.length
  let guard:=naturalBranchCode .equal 19 46
  let first : ℕ → List Instruction:=fun _ => headerCode finishRowFieldsCommands
  let second:=positiveCellFieldsCode mode
  let post := fun next : ℕ → Cell => DenseFields next (solverEntry P fee penalty k row column) ∧
    next 37=.natural (cellBase base k row column) ∧ ∀ slot,SolverPersistentSlot slot → next slot=zeroValues slot
  have zeroFetch : FetchesCode program before.pc zeroCode := by rw [hpc]; exact fetch.append_left
  obtain ⟨zeroTrace,cleared,zeroHead,zeroLast,zeroChain,zeroTime,clearedHeader,clearedBase,clearedPC,
    zeroFrame,zeroOutput,zeroMemory⟩:=
    headerCode_trace_memory [.constant 46 (.natural 0)] program input before base n k values zeroValues
      (by intro command member; have same:=List.mem_singleton.mp member; subst command; dsimp only [HeaderCommand.Valid,headerWords]; decide) header hbase rfl zeroFetch
  have zeroBound : time program zeroTrace ≤ 330 := zeroTime
  have clearedAt : cleared.pc=guardOrigin := by rw [clearedPC,hpc]
  have zeroKeep (slot : ℕ) (different : slot ≠ 46) : zeroValues slot=values slot := Function.update_of_ne different _ _
  have choiceFetch : FetchesCode program guardOrigin (choiceCode guard first second guardOrigin) := fetch.append_right
  have size : ∀ a b,(guard a b).length=8 := by intro a b; rfl
  have guarded : HeaderBlockRun program input cleared base n k zeroValues
      (if decide (row=0) then choiceFirstPC guardOrigin else choiceSecondPC first guardOrigin) 135 := by
    have guardFetch : FetchesCode program cleared.pc (guard (choiceSecondPC first guardOrigin) (choiceFirstPC guardOrigin)) := by
      rw [clearedAt]
      exact choice_guard_fetch guard first second program guardOrigin choiceFetch
    have run:=naturalBranch_trace_memory program input cleared base n k 19 46 row 0
      (choiceSecondPC first guardOrigin) (choiceFirstPC guardOrigin) .equal zeroValues clearedHeader
      (by decide) (by decide) ((zeroKeep 19 (by decide)).trans hrow) rfl clearedBase guardFetch
    simpa only [HeaderBlockRun,Comparison.nat,beq_iff_eq,decide_eq_true_eq] using run
  have firstRun : ∀ state : State,decide (row=0)=true → state.pc=choiceFirstPC guardOrigin →
      Header state base zeroValues → state.register .fresh=.natural base → HeaderMemory cleared state base →
      FetchesCode program state.pc (first (choiceFirstPC guardOrigin)) →
      ∃ next,HeaderBlockRun program input state base n k next
        (choiceFirstPC guardOrigin+(first (choiceFirstPC guardOrigin)).length) 1320 ∧ post next := by
    intro state zero statePC stateHeader stateBase _ stateFetch
    have rowZero : row=0 := of_decide_eq_true zero
    obtain ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,afterPC,frame,output,memory⟩:=
      headerCode_trace_memory finishRowFieldsCommands program input state base n k zeroValues (finishRowFieldsValues zeroValues)
        finishRowFieldsCommands_valid stateHeader stateBase (finishRowFieldsCommands_eval zeroValues) stateFetch
    refine ⟨finishRowFieldsValues zeroValues,?_,?_,?_,?_⟩
    · exact ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,by simpa only [statePC] using afterPC,frame,output,memory⟩
    · rw [rowZero,solverEntry_zero P fee penalty k column columnBound]
      exact terminalFieldsValues_dense false _
    · have pointer : finishRowFieldsValues zeroValues 37=zeroValues 35 := by simp [finishRowFieldsValues,terminalFieldsValues]
      have baseRow : row-1=row := by omega
      exact pointer.trans ((zeroKeep 35 (by decide)).trans (hgood.trans (congrArg Cell.natural (by rw [baseRow]))))
    · intro slot persistent
      exact (terminalFieldsValues_controls (Function.update zeroValues 37 (zeroValues 35)) false slot persistent.1).trans
        (Function.update_of_ne persistent.2 _ _)
  have secondRun : ∀ state : State,decide (row=0)=false → state.pc=choiceSecondPC first guardOrigin →
      Header state base zeroValues → state.register .fresh=.natural base → HeaderMemory cleared state base →
      FetchesCode program state.pc (second (choiceSecondPC first guardOrigin)) →
      ∃ next,HeaderBlockRun program input state base n k next
        (choiceEndPC first second guardOrigin) (2500*(P.certificate.M+1)+15870) ∧ post next := by
    intro state nonzero statePC stateHeader stateBase memory stateFetch
    have rowPositive : 0 < row := Nat.pos_of_ne_zero (of_decide_eq_false nonzero)
    have fromBefore : HeaderMemory before state base := (HeaderMemory.trace_last zeroMemory zeroLast).trans memory
    have actualPrior:=prior.header fromBefore
    have actualSource:=EndpointSource.frame_of_avoids mode input P source base n k before state hsource avoids (fromBefore.frame n k)
    have actualGood:=actualPrior.previous_row rowPositive columnBound
    have actualBad : column ≠ 0 → PDLower.CalibrationCompute.HeapList state (cellBase base k (row-1) column-6)
        (denseEncodeEntry ((solverRow P fee penalty k (row-1)).getD (column-1) abandonEntry)) := by
      intro positive
      rw [previousTool_cellBase base k (row-1) column (Nat.pos_of_ne_zero positive)]
      exact actualPrior.previous_tools rowPositive (Nat.pos_of_ne_zero positive) columnBound
    have goodOutside : ∀ offset < 6,cellBase base k (row-1) column+offset < base ∨
        base+headerWords ≤ cellBase base k (row-1) column+offset := by
      intro offset _
      right
      unfold cellBase tableBase
      omega
    have badOutside : column ≠ 0 → ∀ offset < 6,cellBase base k (row-1) column-6+offset < base ∨
        base+headerWords ≤ cellBase base k (row-1) column-6+offset := by
      intro positive offset _
      rw [previousTool_cellBase base k (row-1) column (Nat.pos_of_ne_zero positive)]
      right
      unfold cellBase tableBase
      omega
    have actualFetch : FetchesCode program (choiceSecondPC first guardOrigin) (positiveCellFieldsCode mode (choiceSecondPC first guardOrigin)) := by
      simpa only [statePC,second] using stateFetch
    obtain ⟨trace,after,next,head,last,chain,bound,afterHeader,fields,controls,afterBase,afterPC,frame,output,allMemory⟩:=
      positiveCellFields_trace_memory mode program input (choiceSecondPC first guardOrigin) P fee penalty
        (solverRow P fee penalty k (row-1)) column state base n k source
        (cellBase base k (row-1) column) (cellBase base k (row-1) column-6) zeroValues statePC stateHeader stateBase actualSource avoids
        ((zeroKeep 0 (by decide)).trans hsourceValue) ((zeroKeep 2 (by decide)).trans hpenalty)
        ((zeroKeep 5 (by decide)).trans hfee) ((zeroKeep 6 (by decide)).trans last) ((zeroKeep 20 (by decide)).trans hcolumn)
        ((zeroKeep 35 (by decide)).trans hgood) ((zeroKeep 36 (by decide)).trans hbad)
        actualGood actualBad goodOutside badOutside actualFetch
    have rowEq : row-1+1=row := Nat.sub_add_cancel rowPositive
    have original : solverEntry P fee penalty k row column=
        P.cachedNextMenuEntry P.endpointCache fee penalty (solverRow P fee penalty k (row-1)) column := by
      simpa only [rowEq] using solverEntry_succ P fee penalty k (row-1) column columnBound
    refine ⟨next,⟨trace,after,head,last,chain,bound,afterHeader,afterBase,afterPC,frame,output,allMemory⟩,?_,?_,?_⟩
    · simpa only [original] using fields
    · exact (controls 37 (by decide)).trans ((zeroKeep 37 (by decide)).trans
        (hwrite.trans (congrArg Cell.natural (nextRow_cellBase base k row column rowPositive))))
    · exact fun slot persistent => controls slot persistent.1
  obtain ⟨next,choiceRun,fields,pointer,controls⟩:=choice_compose_post_memory guard first second size program input cleared base n k
    guardOrigin 1320 (2500*(P.certificate.M+1)+15870) zeroValues (decide (row=0)) post choiceFetch guarded firstRun secondRun
  obtain ⟨choiceTrace,after,choiceHead,choiceLast,choiceChain,choiceTime,afterHeader,afterBase,afterPC,choiceFrame,choiceOutput,choiceMemory⟩:=choiceRun
  have choiceBound : time program choiceTrace ≤ 2500*(P.certificate.M+1)+17355 := by
    calc
      _ ≤ 165+1320+(2500*(P.certificate.M+1)+15870) := choiceTime
      _ = _ := by ring
  have joined:=joinTrace_spec program input zeroTrace choiceTrace before cleared after 330 (2500*(P.certificate.M+1)+17355)
    zeroHead zeroLast choiceHead choiceLast zeroChain choiceChain zeroBound choiceBound
  refine ⟨joinTrace zeroTrace choiceTrace,after,next,joined.1,joined.2.1,joined.2.2.1,?_,afterHeader,fields,pointer,?_,afterBase,?_,
    zeroFrame.trans choiceFrame,choiceOutput.trans zeroOutput,
    joinTrace_memory zeroTrace choiceTrace before cleared base zeroLast zeroMemory choiceMemory⟩
  · calc
      _ ≤ 330+(2500*(P.certificate.M+1)+17355) := joined.2.2.2
      _ = _ := by ring
  · intro slot persistent
    have different : slot ≠ 46 := by have control:=persistent.1; unfold SolverControlSlot at control; omega
    exact (controls slot persistent).trans (zeroKeep slot different)
  · have choiceEnd:=choiceCode_end guard first second size guardOrigin
    rw [afterPC,← choiceEnd,cellFieldsCode,List.length_append]
    change guardOrigin+(choiceCode guard first second guardOrigin).length=
      origin+(zeroCode.length+(choiceCode guard first second guardOrigin).length)
    exact Nat.add_assoc _ _ _

end PDCompute.Solver
