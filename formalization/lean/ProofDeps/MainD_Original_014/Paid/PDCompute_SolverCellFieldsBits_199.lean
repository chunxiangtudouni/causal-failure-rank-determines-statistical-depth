module

public import Paid.PDCompute_SolverPositiveCellBits_198
public import Paid.PDCompute_SolverLiteralFieldsBits_165
public import Paid.PDCompute_SolverCellFields_118
public import Paid.PDCompute_Nat_RowPointerBounds_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace PDCompute.Solver
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
attribute [local irreducible] cellFieldsCode positiveCellFieldsCode

/-- ALL original row/column cases, all rational penalties, actual
previous cells from true completed dense prefix, original fields and
actual row0 pointer correction, EVERY-prefix SAME scalar budget. -/
theorem cellFields_trace_bits (mode : ReaderMode) (program : Program) (input : List Cell)
    (origin : ℕ) (P : Parameters) (fee penalty : ℚ) (row column : ℕ)
    (before : State) (base n k source budget : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (hpenalty : values 2=.rational penalty)
    (hfee : values 5=.rational fee) (last : values 6=.natural P.certificate.M)
    (hrow : values 19=.natural row) (hcolumn : values 20=.natural column) (rowBound : row≤n) (columnBound : column ≤ k)
    (hgood : values 35=.natural (cellBase base k (row-1) column))
    (hbad : values 36=.natural (cellBase base k (row-1) column-6))
    (hwrite : values 37=.natural (cellBase base k (row-1) column+6*(k+1)))
    (prior : DensePrefix before base k (solverEntry P fee penalty k) (row*(k+1)+column))
    (safe : RootD27.Bits.SafeBits before budget)
    (scalarRoom : 4194304*solverBitScale P fee penalty n k≤budget)
    (natural : ∀ value≤PDCompute.Pack.naturalCap base n k,(.natural value : Cell).bits≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (indexBits : 1+natBits (P.certificate.M+1)≤budget)
    (sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget)
    (counter : natBits (origin+(cellFieldsCode mode origin).length)≤budget)
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
      (∀ state ∈ trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let zeroValues:=Function.update values 46 (.natural 0)
  let zeroCode:=headerCode [.constant 46 (.natural 0)]
  let guardOrigin:=origin+zeroCode.length
  let guard:=naturalBranchCode .equal 19 46
  let first : ℕ → List Instruction:=fun _ => headerCode finishRowFieldsCommands
  let second:=positiveCellFieldsCode mode
  let S:=solverStatsBits P fee n
  have numericRoom : 1+64*(maximumMenuBits P fee+16*(2*(S+3)+maximumMenuBits P fee+ratEncodingBits penalty+1)+1)≤budget :=
    (solverNumericGuard_original P fee penalty n k).2.2.1.trans scalarRoom
  have small : 4≤budget := (solverCell_guard_rooms S (maximumMenuBits P fee) (ratEncodingBits penalty) budget numericRoom).1
  have oneBits : (.natural 1 : Cell).bits≤budget := by norm_num [Cell.bits,natBits];omega
  have pointers:=PDCompute.NatControl.rowPointerBounds base n k row column rowBound columnBound
  have goodPlus : cellBase base k (row-1) column+6≤PDCompute.Pack.naturalCap base n k := by
    have destination:=pointers.destination
    omega
  have badPlus : cellBase base k (row-1) column-6+6≤PDCompute.Pack.naturalCap base n k := by
    have lower:=Nat.sub_le (cellBase base k (row-1) column) 6
    omega
  have goodPointerBits : 1+natBits (cellBase base k (row-1) column+6)≤budget := natural _ goodPlus
  have badPointerBits : 1+natBits (cellBase base k (row-1) column-6+6)≤budget := natural _ badPlus
  have wholeCode : cellFieldsCode mode origin=zeroCode++choiceCode guard first second guardOrigin := by unfold cellFieldsCode;rfl
  rw [wholeCode] at fetch
  have size : ∀ a b,(guard a b).length=8 := by intro a b;rfl
  have codeEnd:=choiceCode_end guard first second size guardOrigin
  have wholeEnd : origin+(cellFieldsCode mode origin).length=choiceEndPC first second guardOrigin := by
    rw [wholeCode,List.length_append,←codeEnd]
    exact (Nat.add_assoc _ _ _).symm
  have endBits : natBits (choiceEndPC first second guardOrigin)≤budget := by rw [←wholeEnd];exact counter
  have firstBits : natBits (choiceFirstPC guardOrigin)≤budget :=
    (natBits_mono (by simp only [choiceEndPC,choiceSecondPC,choiceFirstPC];omega : choiceFirstPC guardOrigin≤choiceEndPC first second guardOrigin)).trans endBits
  have secondBits : natBits (choiceSecondPC first guardOrigin)≤budget :=
    (natBits_mono (by unfold choiceEndPC;omega : choiceSecondPC first guardOrigin≤choiceEndPC first second guardOrigin)).trans endBits
  have zeroCounter : natBits (before.pc+zeroCode.length)≤budget :=
    (natBits_mono (by rw [hpc,wholeCode,List.length_append];omega : before.pc+zeroCode.length≤origin+(cellFieldsCode mode origin).length)).trans counter
  let post := fun next : ℕ → Cell => DenseFields next (solverEntry P fee penalty k row column) ∧
    next 37=.natural (cellBase base k row column) ∧ ∀ slot,SolverPersistentSlot slot → next slot=zeroValues slot
  have zeroFetch : FetchesCode program before.pc zeroCode := by rw [hpc]; exact fetch.append_left
  obtain ⟨zeroTrace,cleared,zeroHead,zeroLast,zeroChain,zeroTime,clearedHeader,clearedBase,clearedPC,
    zeroFrame,zeroOutput,zeroResources⟩:=
    headerCode_trace_bits [.constant 46 (.natural 0)] program input before base n k budget values zeroValues
      (by intro command member; have same:=List.mem_singleton.mp member; subst command; dsimp only [HeaderCommand.Valid,headerWords]; decide) header hbase rfl safe
        ⟨zeroValues,rfl,(HeaderValueBits.of_safe header safe).update (by norm_num [Cell.bits,natBits];omega),True.intro⟩ addressBits zeroCounter zeroFetch
  have zeroMemory : ∀ state∈zeroTrace,HeaderMemory before state base := fun state member=>(zeroResources state member).1
  have zeroSafe : ∀ state∈zeroTrace,RootD27.Bits.SafeBits state budget := fun state member=>(zeroResources state member).2
  have zeroBound : time program zeroTrace ≤ 330 := zeroTime
  have clearedAt : cleared.pc=guardOrigin := by rw [clearedPC,hpc]
  have zeroKeep (slot : ℕ) (different : slot ≠ 46) : zeroValues slot=values slot := Function.update_of_ne different _ _
  have choiceFetch : FetchesCode program guardOrigin (choiceCode guard first second guardOrigin) := fetch.append_right
  have guarded : HeaderBlockBits program input cleared base n k budget zeroValues
      (if decide (row=0) then choiceFirstPC guardOrigin else choiceSecondPC first guardOrigin) 135 := by
    have guardFetch : FetchesCode program cleared.pc (guard (choiceSecondPC first guardOrigin) (choiceFirstPC guardOrigin)) := by
      rw [clearedAt]
      exact choice_guard_fetch guard first second program guardOrigin choiceFetch
    have compareCounter : natBits (cleared.pc+7)≤budget :=
      (natBits_mono (by rw [clearedAt];unfold choiceFirstPC;omega : cleared.pc+7≤choiceFirstPC guardOrigin)).trans firstBits
    obtain ⟨trace,after,head,last,chain,cost,afterHeader,afterBase,afterPC,frame,output,resources⟩:=
      PDCompute.NatControl.naturalBranch_trace_bits program input cleared base n k 19 46 row 0 (choiceSecondPC first guardOrigin) (choiceFirstPC guardOrigin) budget .equal zeroValues
        clearedHeader (by decide) (by decide) ((zeroKeep 19 (by decide)).trans hrow) rfl clearedBase (zeroSafe cleared (List.mem_of_getLast? zeroLast))
        oneBits addressBits compareCounter secondBits firstBits guardFetch
    refine ⟨trace,after,head,last,chain,cost,afterHeader,afterBase,?_,frame,output,(fun later member=>(resources later member).1),(fun later member=>(resources later member).2)⟩
    simpa only [Comparison.nat,beq_iff_eq,decide_eq_true_eq] using afterPC
  have firstRun : ∀ state : State,decide (row=0)=true → state.pc=choiceFirstPC guardOrigin →
      Header state base zeroValues → state.register .fresh=.natural base → HeaderMemory cleared state base → RootD27.Bits.SafeBits state budget →
      FetchesCode program state.pc (first (choiceFirstPC guardOrigin)) →
      ∃ next,HeaderBlockBits program input state base n k budget next
        (choiceFirstPC guardOrigin+(first (choiceFirstPC guardOrigin)).length) 1320 ∧ post next := by
    intro state zero statePC stateHeader stateBase _ stateSafe stateFetch
    have rowZero : row=0 := of_decide_eq_true zero
    have bodyCounter : natBits (state.pc+(headerCode finishRowFieldsCommands).length)≤budget :=
      (natBits_mono (by rw [statePC];simp only [choiceEndPC,choiceSecondPC,first];omega : state.pc+(headerCode finishRowFieldsCommands).length≤choiceEndPC first second guardOrigin)).trans endBits
    obtain ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,afterPC,frame,output,resources⟩:=
      finishRowFields_trace_bits program input state base n k budget zeroValues stateHeader stateBase stateSafe small addressBits bodyCounter stateFetch
    refine ⟨finishRowFieldsValues zeroValues,?_,?_,?_,?_⟩
    · exact ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,by simpa only [statePC] using afterPC,frame,output,(fun later member=>(resources later member).1),(fun later member=>(resources later member).2)⟩
    · rw [rowZero,solverEntry_zero P fee penalty k column columnBound]
      exact terminalFieldsValues_dense false _
    · have pointer : finishRowFieldsValues zeroValues 37=zeroValues 35 := by simp [finishRowFieldsValues,terminalFieldsValues]
      have baseRow : row-1=row := by omega
      exact pointer.trans ((zeroKeep 35 (by decide)).trans (hgood.trans (congrArg Cell.natural (by rw [baseRow]))))
    · intro slot persistent
      exact (terminalFieldsValues_controls (Function.update zeroValues 37 (zeroValues 35)) false slot persistent.1).trans
        (Function.update_of_ne persistent.2 _ _)
  have secondRun : ∀ state : State,decide (row=0)=false → state.pc=choiceSecondPC first guardOrigin →
      Header state base zeroValues → state.register .fresh=.natural base → HeaderMemory cleared state base → RootD27.Bits.SafeBits state budget →
      FetchesCode program state.pc (second (choiceSecondPC first guardOrigin)) →
      ∃ next,HeaderBlockBits program input state base n k budget next
        (choiceEndPC first second guardOrigin) (2500*(P.certificate.M+1)+15870) ∧ post next := by
    intro state nonzero statePC stateHeader stateBase memory stateSafe stateFetch
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
    obtain ⟨trace,after,next,head,last,chain,bound,afterHeader,fields,controls,afterBase,afterPC,frame,output,allMemory,allSafe⟩:=
      positiveCellFields_trace_bits mode program input (choiceSecondPC first guardOrigin) P fee penalty
        (solverRow P fee penalty k (row-1)) column state base n k source
        (cellBase base k (row-1) column) (cellBase base k (row-1) column-6) budget S zeroValues statePC stateHeader stateBase actualSource avoids
        ((zeroKeep 0 (by decide)).trans hsourceValue) ((zeroKeep 2 (by decide)).trans hpenalty)
        ((zeroKeep 5 (by decide)).trans hfee) ((zeroKeep 6 (by decide)).trans last) ((zeroKeep 20 (by decide)).trans hcolumn)
        ((zeroKeep 35 (by decide)).trans hgood) ((zeroKeep 36 (by decide)).trans hbad)
        actualGood actualBad goodOutside badOutside stateSafe
        (fun tool=>solverEntry_fieldBits P fee penalty n k (row-1) tool ((Nat.sub_le _ _).trans rowBound)) numericRoom
        addressBits goodPointerBits (fun _=>badPointerBits) indexBits sourceBits (by simpa only [choiceEndPC,second] using endBits) actualFetch
    have rowEq : row-1+1=row := Nat.sub_add_cancel rowPositive
    have original : solverEntry P fee penalty k row column=
        P.cachedNextMenuEntry P.endpointCache fee penalty (solverRow P fee penalty k (row-1)) column := by
      simpa only [rowEq] using solverEntry_succ P fee penalty k (row-1) column columnBound
    refine ⟨next,⟨trace,after,head,last,chain,bound,afterHeader,afterBase,afterPC,frame,output,allMemory,allSafe⟩,?_,?_,?_⟩
    · simpa only [original] using fields
    · exact (controls 37 (by decide)).trans ((zeroKeep 37 (by decide)).trans
        (hwrite.trans (congrArg Cell.natural (nextRow_cellBase base k row column rowPositive))))
    · exact fun slot persistent => controls slot persistent.1
  obtain ⟨next,choiceRun,fields,pointer,controls⟩:=choice_compose_post_bits guard first second size program input cleared base n k
    guardOrigin budget 1320 (2500*(P.certificate.M+1)+15870) zeroValues (decide (row=0)) post choiceFetch endBits guarded firstRun secondRun
  obtain ⟨choiceTrace,after,choiceHead,choiceLast,choiceChain,choiceTime,afterHeader,afterBase,afterPC,choiceFrame,choiceOutput,choiceMemory,choiceSafe⟩:=choiceRun
  have choiceBound : time program choiceTrace ≤ 2500*(P.certificate.M+1)+17355 := by
    calc
      _ ≤ 165+1320+(2500*(P.certificate.M+1)+15870) := choiceTime
      _ = _ := by ring
  have joined:=joinTrace_spec program input zeroTrace choiceTrace before cleared after 330 (2500*(P.certificate.M+1)+17355)
    zeroHead zeroLast choiceHead choiceLast zeroChain choiceChain zeroBound choiceBound
  refine ⟨joinTrace zeroTrace choiceTrace,after,next,joined.1,joined.2.1,joined.2.2.1,?_,afterHeader,fields,pointer,?_,afterBase,?_,
    zeroFrame.trans choiceFrame,choiceOutput.trans zeroOutput,
    joinTrace_memory zeroTrace choiceTrace before cleared base zeroLast zeroMemory choiceMemory,
    PDCompute.Pack.joinTrace_invariant zeroTrace choiceTrace (fun state=>RootD27.Bits.SafeBits state budget) zeroSafe choiceSafe⟩
  · calc
      _ ≤ 330+(2500*(P.certificate.M+1)+17355) := joined.2.2.2
      _ = _ := by ring
  · intro slot persistent
    have different : slot ≠ 46 := by have control:=persistent.1; unfold SolverControlSlot at control; omega
    exact (controls slot persistent).trans (zeroKeep slot different)
  · rw [afterPC,←codeEnd,cellFieldsCode,List.length_append]
    change guardOrigin+(choiceCode guard first second guardOrigin).length=
      origin+(zeroCode.length+(choiceCode guard first second guardOrigin).length)
    exact Nat.add_assoc _ _ _


end PDCompute.Solver
