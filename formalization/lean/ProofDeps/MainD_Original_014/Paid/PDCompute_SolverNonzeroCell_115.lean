module

public import Paid.PDCompute_SolverCellProgram_112
public import Paid.PDCompute_SolverBadPreserves_114

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

attribute [local irreducible] goodEntryObjectiveCode badChoiceCode scanChoiceCode

/-- Complete positive-row, NONZERO-penalty original cell computation:
real good/prior-tools reads, actual bad branch, all M+1 endpoint tests,
strict abandonment guard, and actual selected entry reconstruction. -/
theorem nonzeroCellFields_trace_memory (mode : ReaderMode) (program : Program) (input : List Cell)
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
    (nonzero : penalty ≠ 0) (fetch : FetchesCode program origin (nonzeroCellFieldsCode mode origin)) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 2500*(P.certificate.M+1)+14220 ∧ Header after base afterValues ∧
      DenseFields afterValues (P.cachedNextMenuEntry P.endpointCache fee penalty previous tools) ∧
      (∀ slot,SolverControlSlot slot → afterValues slot=values slot) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(nonzeroCellFieldsCode mode origin).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace,HeaderMemory before state base := by
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
  have goodFetch : FetchesCode program before.pc goodEntryObjectiveCode := by
    rw [hpc]
    exact fetch.append_left.append_left.append_left.append_left
  obtain ⟨goodTrace,loaded,goodHead,goodLast,goodChain,goodTime,loadedHeader,_,loadedBase,loadedPC,
    goodFrame,goodOutput,goodMemory⟩:=goodEntryObjective_trace_memory program input before base goodPointer n k values entry fee penalty
      header hbase hgood hfee hpenalty goodSource goodOutside goodFetch
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
  obtain ⟨zeroTrace,cleared,zeroHead,zeroLast,zeroChain,zeroTime,clearedHeader,clearedBase,clearedPC,zeroFrame,zeroOutput,zeroMemory⟩:=
    headerCode_trace_memory [.constant 46 (.natural 0)] program input loaded base n k goodValues zeroValues
      (by intro command member; have same:=List.mem_singleton.mp member; subst command; dsimp only [HeaderCommand.Valid,headerWords]; decide) loadedHeader loadedBase rfl zeroFetch
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
  obtain ⟨badTrace,chosen,badHead,badLast,badChain,badTime,chosenHeader,chosenBase,chosenPC,badFrame,badOutput,badMemory⟩:=
    badChoice_trace_memory program input badOrigin P fee penalty previous tools badPointer cleared base n k zeroValues
      clearedAt clearedHeader clearedBase
      ((zeroKeep 20 (by decide)).trans ((goodKeep 20 (Or.inr (by decide)) (by decide) (by decide) (by decide)).trans htools)) rfl
      ((zeroKeep 36 (by decide)).trans ((goodKeep 36 (Or.inr (by decide)) (by decide) (by decide) (by decide)).trans hbad))
      ((zeroKeep 5 (by decide)).trans ((goodKeep 5 (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans hfee))
      ((zeroKeep 2 (by decide)).trans ((goodKeep 2 (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans hpenalty))
      badSource' badOutside badFetch
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
  obtain ⟨resetTrace,reset,resetHead,resetLast,resetChain,resetTime,resetHeader,resetBase,resetPC,resetFrame,resetOutput,resetMemory⟩:=
    runtimeCode_trace_memory scanResetCommands program input chosen base n k badValues resetValues scanResetCommands_valid
      chosenHeader chosenBase (scanResetCommands_eval badValues source penalty sourceValue penaltyValue) resetFetch
  have resetBound : time program resetTrace ≤ 1980 := resetTime
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
    scanFrame,scanOutput,scanMemory⟩:=
    scanChoice_trace_memory mode program input scanOrigin scanFetch P base source n k fee penalty previous tools nonzero avoids
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
    joinTrace_memory _ scanTrace before reset base join3.2.1 memory3 scanMemory⟩
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
