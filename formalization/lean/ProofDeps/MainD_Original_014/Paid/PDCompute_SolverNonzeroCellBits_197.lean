module

public import Paid.PDCompute_SolverGoodEntryBits_160
public import Paid.PDCompute_SolverBadDispatchBits_185
public import Paid.PDCompute_SolverScanChoiceBits_196
public import Paid.PDCompute_SolverOriginalValueCaps_187
public import Paid.PDCompute_SolverNonzeroCell_115

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace PDCompute.Solver
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
attribute [local irreducible] nonzeroCellFieldsCode goodEntryObjectiveCode badChoiceCode scanChoiceCode

theorem solverCell_guard_rooms (S L T budget : ℕ)
    (room : 1+64*(L+16*(2*(S+3)+L+T+1)+1)≤budget) :
    4≤budget ∧ 1+16*(S+L+T+1)≤budget ∧
    1+16*(2*(S+3)+L+T+1)≤budget ∧ 1+64*(L+2*(S+3)+1)≤budget := by omega

/-- COMPLETE positive-row nonzero-penalty actual cell fields at SAME B.
Every source entry, bad branch, M+1 endpoint and selected reconstruction
is genuinely executed; fine original entry bounds are reset per cell. -/
theorem nonzeroCellFields_trace_bits (mode : ReaderMode) (program : Program) (input : List Cell)
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
    (nonzero : penalty ≠ 0) (safe : RootD27.Bits.SafeBits before budget)
    (bounds : ∀ column,ratEncodingBits (previous.getD column abandonEntry).observation≤S ∧
      ratEncodingBits (previous.getD column abandonEntry).repairs≤S ∧ ratEncodingBits (previous.getD column abandonEntry).failure≤S)
    (room : 1+64*(maximumMenuBits P fee+16*(2*(S+3)+maximumMenuBits P fee+ratEncodingBits penalty+1)+1)≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (goodPointerBits : 1+natBits (goodPointer+6)≤budget)
    (badPointerBits : tools≠0 → 1+natBits (badPointer+6)≤budget) (indexBits : 1+natBits (P.certificate.M+1)≤budget)
    (sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget)
    (counter : natBits (origin+(nonzeroCellFieldsCode mode origin).length)≤budget)
    (fetch : FetchesCode program origin (nonzeroCellFieldsCode mode origin)) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 2500*(P.certificate.M+1)+14220 ∧ Header after base afterValues ∧
      DenseFields afterValues (P.cachedNextMenuEntry P.endpointCache fee penalty previous tools) ∧
      (∀ slot,SolverControlSlot slot → afterValues slot=values slot) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(nonzeroCellFieldsCode mode origin).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state ∈ trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let entry:=previous.getD tools abandonEntry
  let goodValues:=goodObjectiveValues (denseReadHeaderValues (denseEncodeEntry entry) 7 values)
    fee penalty entry.observation entry.repairs entry.failure
  let zeroValues:=Function.update goodValues 46 (.natural 0)
  let badValues:=badChoiceValues zeroValues fee penalty previous tools
  let resetValues:=scanResetValues badValues source penalty
  let zeroCode:=headerCode [.constant 46 (.natural 0)]
  let badOrigin:=origin+goodEntryObjectiveCode.length+zeroCode.length
  let resetOrigin:=badOrigin+(badChoiceCode badOrigin).length
  let scanOrigin:=resetOrigin+(runtimeCode scanResetCommands).length
  have literalCode : nonzeroCellFieldsCode mode origin=goodEntryObjectiveCode++zeroCode++badChoiceCode badOrigin++runtimeCode scanResetCommands++scanChoiceCode mode scanOrigin := by
    unfold nonzeroCellFieldsCode
    rfl
  rw [literalCode] at fetch
  let L:=maximumMenuBits P fee
  let T:=ratEncodingBits penalty
  let R:=2*(S+3)
  let G:=16*(R+L+T+1)
  have guardRooms:=solverCell_guard_rooms S L T budget room
  have fieldsRoom : 1+64*(L+R+1)≤budget := guardRooms.2.2.2
  have small : 4≤budget := guardRooms.1
  have goodLength : goodEntryObjectiveCode.length=79 := by
    simp only [goodEntryObjectiveCode,List.length_append,loadDenseEntryCode_length,
      show (headerCode goodObjectiveCommands).length=40 from rfl]
  have feeBound : ratEncodingBits fee≤L := (maximumMenuBits_bound P fee).2 fee (by simp [menuScalars])
  have goodBounds:=bounds tools
  have badBounds:=badBranch_fieldBits P fee penalty previous tools S bounds
  have statsWiden : S≤R := by dsimp only [R];omega
  have goodObjectiveBits : ratEncodingBits (entry.objective fee penalty)≤G :=
    (solverObjective_intermediate_bits entry fee penalty R L T (goodBounds.1.trans statsWiden) (goodBounds.2.1.trans statsWiden)
      (goodBounds.2.2.trans statsWiden) feeBound (le_refl _)).2.2.2
  have badObjectiveBits : ratEncodingBits ((P.menuBadBranch fee penalty previous tools).2.objective fee penalty)≤G :=
    (solverObjective_intermediate_bits _ fee penalty R L T badBounds.1 badBounds.2.1 badBounds.2.2 feeBound (le_refl _)).2.2.2
  have originalEnd : origin+(nonzeroCellFieldsCode mode origin).length=scanOrigin+(scanChoiceCode mode scanOrigin).length := by
    simp only [nonzeroCellFieldsCode,List.length_append,scanOrigin,resetOrigin,badOrigin,zeroCode,Nat.add_assoc]
  have endBits : natBits (scanOrigin+(scanChoiceCode mode scanOrigin).length)≤budget := by rw [←originalEnd];exact counter
  have phaseBits (pc : ℕ) (earlier : pc≤scanOrigin) : natBits pc≤budget :=
    (natBits_mono (earlier.trans (Nat.le_add_right _ _))).trans endBits
  have goodCounter : natBits (before.pc+79)≤budget := phaseBits _ (by
    rw [hpc,←goodLength]
    dsimp only [scanOrigin,resetOrigin,badOrigin]
    omega)
  have goodFetch : FetchesCode program before.pc goodEntryObjectiveCode := by
    rw [hpc]
    exact fetch.append_left.append_left.append_left.append_left
  obtain ⟨goodTrace,loaded,goodHead,goodLast,goodChain,goodTime,loadedHeader,_,loadedBase,loadedPC79,
    goodFrame,goodOutput,goodMemory,goodSafe⟩:=goodEntryObjective_trace_bits program input before base goodPointer n k budget S L T values entry fee penalty
      header hbase hgood hfee hpenalty goodSource goodOutside safe addressBits goodPointerBits goodCounter goodBounds.1 goodBounds.2.1 goodBounds.2.2
      feeBound (le_refl _) guardRooms.2.1 goodFetch
  have loadedPC : loaded.pc=before.pc+goodEntryObjectiveCode.length := by simpa only [goodLength] using loadedPC79
  have goodKeep (slot : ℕ) (outside : slot < 7 ∨ 13 ≤ slot) (h21 : slot ≠ 21) (h29 : slot ≠ 29) (h30 : slot ≠ 30) :
      goodValues slot=values slot := by
    simp only [goodValues,goodObjectiveValues,Function.update_of_ne h21,Function.update_of_ne h29,Function.update_of_ne h30]
    apply denseReadHeaderValues_preserves
    simpa only [denseEncodeEntry_length,entryWords] using outside
  have goodStats:=denseReadHeaderValues_good_stats entry values
  have good10 : goodValues 10=.rational entry.observation := by simpa [goodValues,goodObjectiveValues] using goodStats.1
  have good11 : goodValues 11=.rational entry.repairs := by simpa [goodValues,goodObjectiveValues] using goodStats.2.1
  have good12 : goodValues 12=.rational entry.failure := by simpa [goodValues,goodObjectiveValues] using goodStats.2.2
  have zeroFetch : FetchesCode program loaded.pc zeroCode := by
    rw [loadedPC,hpc]
    exact fetch.append_left.append_left.append_left.append_right
  have loadedSafe:=goodSafe loaded (List.mem_of_getLast? goodLast)
  have zeroBits : (.natural 0 : Cell).bits≤budget := by norm_num [Cell.bits,natBits];omega
  have zeroEvaluated : HeaderEvaluatedBits budget [.constant 46 (.natural 0)] goodValues :=
    ⟨zeroValues,rfl,(HeaderValueBits.of_safe loadedHeader loadedSafe).update zeroBits,True.intro⟩
  have zeroCounter : natBits (loaded.pc+zeroCode.length)≤budget := phaseBits _ (by rw [loadedPC,hpc];dsimp only [scanOrigin,resetOrigin,badOrigin];omega)
  obtain ⟨zeroTrace,cleared,zeroHead,zeroLast,zeroChain,zeroTime,clearedHeader,clearedBase,clearedPC,zeroFrame,zeroOutput,zeroResources⟩:=
    headerCode_trace_bits [.constant 46 (.natural 0)] program input loaded base n k budget goodValues zeroValues
      (by intro command member; have same:=List.mem_singleton.mp member; subst command; dsimp only [HeaderCommand.Valid,headerWords]; decide) loadedHeader loadedBase rfl loadedSafe zeroEvaluated addressBits zeroCounter zeroFetch
  have zeroMemory : ∀ state∈zeroTrace,HeaderMemory loaded state base := fun state member=>(zeroResources state member).1
  have zeroSafe : ∀ state∈zeroTrace,RootD27.Bits.SafeBits state budget := fun state member=>(zeroResources state member).2
  have zeroBound : time program zeroTrace ≤ 330 := zeroTime
  have clearedAt : cleared.pc=badOrigin := by rw [clearedPC,loadedPC,hpc]
  have zeroKeep (slot : ℕ) (different : slot ≠ 46) : zeroValues slot=goodValues slot := Function.update_of_ne different _ _
  have clearedMemory : HeaderMemory before cleared base :=
    (HeaderMemory.trace_last goodMemory goodLast).trans (HeaderMemory.trace_last zeroMemory zeroLast)
  have badSource' : tools ≠ 0 → PDLower.CalibrationCompute.HeapList cleared badPointer
      (denseEncodeEntry (previous.getD (tools-1) abandonEntry)) := by
    intro positive
    apply clearedMemory.heapList (badSource positive)
    intro offset bound
    exact badOutside positive offset (by simpa only [denseEncodeEntry_length,entryWords] using bound)
  have badFetch : FetchesCode program badOrigin (badChoiceCode badOrigin) := by
    have raw:=fetch.append_left.append_left.append_right
    simpa only [List.length_append,badOrigin,zeroCode,Nat.add_assoc] using raw
  obtain ⟨badTrace,chosen,badHead,badLast,badChain,badTime,chosenHeader,chosenBase,chosenPC,badFrame,badOutput,badMemory,badSafe⟩:=
    badChoice_trace_bits program input badOrigin P fee penalty previous tools badPointer cleared base n k budget S L T zeroValues
      clearedAt clearedHeader clearedBase
      ((zeroKeep 20 (by decide)).trans ((goodKeep 20 (Or.inr (by decide)) (by decide) (by decide) (by decide)).trans htools)) rfl
      ((zeroKeep 36 (by decide)).trans ((goodKeep 36 (Or.inr (by decide)) (by decide) (by decide) (by decide)).trans hbad))
      ((zeroKeep 5 (by decide)).trans ((goodKeep 5 (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans hfee))
      ((zeroKeep 2 (by decide)).trans ((goodKeep 2 (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans hpenalty))
      badSource' badOutside (zeroSafe cleared (List.mem_of_getLast? zeroLast))
      (fun _=>(bounds (tools-1)).1) (fun _=>(bounds (tools-1)).2.1) (fun _=>(bounds (tools-1)).2.2)
      feeBound (le_refl _) guardRooms.2.2.1 addressBits badPointerBits
      (phaseBits _ (by dsimp only [scanOrigin,resetOrigin];omega)) badFetch
  have badKeep (slot : ℕ) (outside : BadUntouched slot) : badValues slot=zeroValues slot :=
    badChoiceValues_preserves zeroValues fee penalty previous tools slot outside
  have beforeKeep (slot : ℕ) (badOutside : BadUntouched slot) (different : slot ≠ 46)
      (outside : slot < 7 ∨ 13 ≤ slot) (h21 : slot ≠ 21) (h29 : slot ≠ 29) (h30 : slot ≠ 30) :
      badValues slot=values slot := (badKeep slot badOutside).trans ((zeroKeep slot different).trans (goodKeep slot outside h21 h29 h30))
  have original:=badChoiceValues_original P zeroValues fee penalty previous tools
  have resetFetch : FetchesCode program chosen.pc (runtimeCode scanResetCommands) := by
    rw [chosenPC]
    have raw:=fetch.append_left.append_right
    simpa only [List.length_append,badOrigin,zeroCode,Nat.add_assoc] using raw
  have sourceValue : badValues 0=.natural source :=
    (beforeKeep 0 (Or.inl (by decide)) (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans hsourceValue
  have penaltyValue : badValues 2=.rational penalty :=
    (beforeKeep 2 (Or.inl (by decide)) (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans hpenalty
  have resetCounter : natBits (chosen.pc+(runtimeCode scanResetCommands).length)≤budget := phaseBits _ (by rw [chosenPC])
  obtain ⟨resetTrace,reset,resetHead,resetLast,resetChain,resetTime,resetHeader,resetBase,resetPC,resetFrame,resetOutput,resetResources⟩:=
    scanReset_trace_bits program input chosen base source n k budget badValues penalty chosenHeader chosenBase sourceValue penaltyValue
      (badSafe chosen (List.mem_of_getLast? badLast)) small
      ((Nat.add_le_add_left (natBits_mono (by omega : source+1≤source+(1+2*(P.certificate.M+1)))) 1).trans sourceBits)
      addressBits resetCounter resetFetch
  have resetMemory : ∀ state∈resetTrace,HeaderMemory chosen state base := fun state member=>(resetResources state member).1
  have resetSafe : ∀ state∈resetTrace,RootD27.Bits.SafeBits state budget := fun state member=>(resetResources state member).2
  have resetBound : time program resetTrace ≤ 1980 := resetTime.trans (by decide : 990≤1980)
  have resetKeep (slot : ℕ) (h23 : slot ≠ 23) (h24 : slot ≠ 24) (h25 : slot ≠ 25) (h39 : slot ≠ 39) (h46 : slot ≠ 46) :
      resetValues slot=badValues slot := scanResetValues_preserves badValues source slot penalty h23 h24 h25 h39 h46
  have scanAt : reset.pc=scanOrigin := by rw [resetPC,chosenPC]
  have scanFetch : FetchesCode program scanOrigin (scanChoiceCode mode scanOrigin) := by
    have raw:=fetch.append_right
    simpa only [List.length_append,scanOrigin,resetOrigin,badOrigin,zeroCode,Nat.add_assoc] using raw
  have actualSource:=EndpointSource.frame_of_avoids mode input P source base n k before reset hsource avoids
    (goodFrame.trans (zeroFrame.trans (badFrame.trans resetFrame)))
  have goodValue : goodValues 21=.rational (entry.objective fee penalty) := goodObjectiveValues_objective _ fee penalty entry
  have scanGood : resetValues 21=.rational (entry.objective fee penalty) :=
    (resetKeep 21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((badKeep 21 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans ((zeroKeep 21 (by decide)).trans goodValue))
  have scanStat (slot : ℕ) (small : slot < 13) (different : slot ≠ 46) : resetValues slot=goodValues slot :=
    (resetKeep slot (by omega) (by omega) (by omega) (by omega) different).trans
      ((badKeep slot (Or.inl small)).trans (zeroKeep slot different))
  obtain ⟨scanTrace,after,afterValues,scanHead,scanLast,scanChain,scanTime,afterHeader,fields,controls,afterBase,afterPC,
    scanFrame,scanOutput,scanMemory,scanSafe⟩:=
    scanChoice_trace_bits mode program input scanOrigin scanFetch P base source n k budget R G fee penalty previous tools nonzero avoids
      reset resetValues scanAt resetHeader resetBase actualSource
      ((resetKeep 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans sourceValue)
      ((resetKeep 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans penaltyValue)
      ((scanStat 6 (by decide) (by decide)).trans ((goodKeep 6 (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans last))
      scanGood ((resetKeep 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans original.2.2.2.2)
      rfl rfl rfl rfl
      ((scanStat 10 (by decide) (by decide)).trans good10) ((scanStat 11 (by decide) (by decide)).trans good11)
      ((scanStat 12 (by decide) (by decide)).trans good12)
      ((resetKeep 31 (by decide) (by decide) (by decide) (by decide) (by decide)).trans original.1)
      ((resetKeep 32 (by decide) (by decide) (by decide) (by decide) (by decide)).trans original.2.1)
      ((resetKeep 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans original.2.2.1)
      ((resetKeep 34 (by decide) (by decide) (by decide) (by decide) (by decide)).trans original.2.2.2.1)
      (resetSafe reset (List.mem_of_getLast? resetLast)) goodObjectiveBits badObjectiveBits
      (goodBounds.1.trans statsWiden) (goodBounds.2.1.trans statsWiden) (goodBounds.2.2.trans statsWiden)
      badBounds.1 badBounds.2.1 badBounds.2.2 room fieldsRoom
      addressBits indexBits sourceBits endBits
  have join1:=joinTrace_spec program input goodTrace zeroTrace before loaded cleared 1530 330
    goodHead goodLast zeroHead zeroLast goodChain zeroChain goodTime zeroBound
  have memory1:=joinTrace_memory goodTrace zeroTrace before loaded base goodLast goodMemory zeroMemory
  have join2:=joinTrace_spec program input (joinTrace goodTrace zeroTrace) badTrace before cleared chosen 1860 5460
    join1.1 join1.2.1 badHead badLast join1.2.2.1 badChain join1.2.2.2 badTime
  have memory2:=joinTrace_memory (joinTrace goodTrace zeroTrace) badTrace before cleared base join1.2.1 memory1 badMemory
  have join3:=joinTrace_spec program input (joinTrace (joinTrace goodTrace zeroTrace) badTrace) resetTrace before chosen reset 7320 1980
    join2.1 join2.2.1 resetHead resetLast join2.2.2.1 resetChain join2.2.2.2 resetBound
  have memory3:=joinTrace_memory (joinTrace (joinTrace goodTrace zeroTrace) badTrace) resetTrace before chosen base join2.2.1 memory2 resetMemory
  have join4:=joinTrace_spec program input (joinTrace (joinTrace (joinTrace goodTrace zeroTrace) badTrace) resetTrace) scanTrace
    before reset after 9300 (2500*(P.certificate.M+1)+4920) join3.1 join3.2.1 scanHead scanLast join3.2.2.1 scanChain join3.2.2.2 scanTime
  refine ⟨joinTrace (joinTrace (joinTrace (joinTrace goodTrace zeroTrace) badTrace) resetTrace) scanTrace,after,afterValues,
    join4.1,join4.2.1,join4.2.2.1,?_,afterHeader,fields,?_,afterBase,?_,
    goodFrame.trans (zeroFrame.trans (badFrame.trans (resetFrame.trans scanFrame))),
    scanOutput.trans (resetOutput.trans (badOutput.trans (zeroOutput.trans goodOutput))),
    joinTrace_memory _ scanTrace before reset base join3.2.1 memory3 scanMemory,
    PDCompute.Pack.joinTrace_invariant _ scanTrace (fun state=>RootD27.Bits.SafeBits state budget)
      (PDCompute.Pack.joinTrace_invariant _ resetTrace (fun state=>RootD27.Bits.SafeBits state budget)
        (PDCompute.Pack.joinTrace_invariant _ badTrace (fun state=>RootD27.Bits.SafeBits state budget)
          (PDCompute.Pack.joinTrace_invariant goodTrace zeroTrace (fun state=>RootD27.Bits.SafeBits state budget) goodSafe zeroSafe) badSafe) resetSafe) scanSafe⟩
  · calc
      _ ≤ 9300+(2500*(P.certificate.M+1)+4920) := join4.2.2.2
      _ = _ := by ring
  · intro slot control
    have controlRange : slot < 7 ∨ 13 ≤ slot := by unfold SolverControlSlot at control; omega
    have untouched : BadUntouched slot := by unfold SolverControlSlot at control; unfold BadUntouched; omega
    have h21 : slot ≠ 21 := by unfold SolverControlSlot at control; omega
    have h23 : slot ≠ 23 := by unfold SolverControlSlot at control; omega
    have h24 : slot ≠ 24 := by unfold SolverControlSlot at control; omega
    have h25 : slot ≠ 25 := by unfold SolverControlSlot at control; omega
    have h29 : slot ≠ 29 := by unfold SolverControlSlot at control; omega
    have h30 : slot ≠ 30 := by unfold SolverControlSlot at control; omega
    have h39 : slot ≠ 39 := by unfold SolverControlSlot at control; omega
    have h46 : slot ≠ 46 := by unfold SolverControlSlot at control; omega
    exact (controls slot control).trans ((resetKeep slot h23 h24 h25 h39 h46).trans
      (beforeKeep slot untouched h46 controlRange h21 h29 h30))
  · simpa only [nonzeroCellFieldsCode,List.length_append,scanOrigin,resetOrigin,badOrigin,zeroCode,Nat.add_assoc] using afterPC


end PDCompute.Solver
