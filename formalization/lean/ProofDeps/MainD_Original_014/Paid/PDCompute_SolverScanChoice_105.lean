module

public import Paid.PDCompute_SolverFinalChoiceSetup_104
public import Paid.PDCompute_SolverScanCallerMemory_070

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

instance instDecidableScanUntouched (slot : ℕ) : Decidable (ScanUntouched slot) := by
  unfold ScanUntouched
  infer_instance

abbrev SolverControlSlot (slot : ℕ) : Prop :=
  slot < 7 ∨ slot=19 ∨ slot=20 ∨ slot=35 ∨ slot=36 ∨ slot=37 ∨ slot=38 ∨ slot=47

theorem selectedChoiceValues_controls (mode : ReaderMode) (P : Parameters) (values : ℕ → Cell)
    (fee penalty score : ℚ) (previous : MenuRow) (tools source level slot : ℕ)
    (control : SolverControlSlot slot) :
    selectedChoiceValues mode P values fee penalty score previous tools source level slot=values slot := by
  have h26 : slot ≠ 26 := by unfold SolverControlSlot at control; omega
  have h27 : slot ≠ 27 := by unfold SolverControlSlot at control; omega
  have h29 : slot ≠ 29 := by unfold SolverControlSlot at control; omega
  have h30 : slot ≠ 30 := by unfold SolverControlSlot at control; omega
  have h39 : slot ≠ 39 := by unfold SolverControlSlot at control; omega
  have h40 : slot ≠ 40 := by unfold SolverControlSlot at control; omega
  have h41 : slot ≠ 41 := by unfold SolverControlSlot at control; omega
  have h42 : slot ≠ 42 := by unfold SolverControlSlot at control; omega
  have h43 : slot ≠ 43 := by unfold SolverControlSlot at control; omega
  have h44 : slot ≠ 44 := by unfold SolverControlSlot at control; omega
  have h45 : slot ≠ 45 := by unfold SolverControlSlot at control; omega
  unfold selectedChoiceValues
  split_ifs
  · simp only [selectedTestingValues,scanEndpointValues,testingFieldsValues,Function.update_of_ne h26,
      Function.update_of_ne h27,Function.update_of_ne h29,Function.update_of_ne h30,Function.update_of_ne h39,
      Function.update_of_ne h40,Function.update_of_ne h41,Function.update_of_ne h42,Function.update_of_ne h43,
      Function.update_of_ne h44,Function.update_of_ne h45]
  · rfl

def scanChoiceCode (mode : ReaderMode) (origin : ℕ) : List Instruction :=
  scanKernel mode origin++headerCode finalChoiceCommands++
    selectedChoiceCode mode (origin+112+(headerCode finalChoiceCommands).length)

/-- COMPLETE original M+1 endpoint scan followed by the ACTUAL strict
outer comparison and actual selected-entry reconstruction. No selected
answer, argmin or optimum is supplied to this fixed program. -/
theorem scanChoice_trace_memory (mode : ReaderMode) (program : Program) (input : List Cell)
    (origin : ℕ) (fetch : FetchesCode program origin (scanChoiceCode mode origin))
    (P : Parameters) (base source n k : ℕ) (fee penalty : ℚ) (previous : MenuRow) (tools : ℕ)
    (nonzero : penalty ≠ 0) (avoids : EndpointAvoids mode P source base n k)
    (before : State) (values : ℕ → Cell) (hpc : before.pc=origin) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hsource : EndpointSource mode input P source before)
    (hsourceValue : values 0=.natural source) (hpenalty : values 2=.rational penalty)
    (last : values 6=.natural P.certificate.M)
    (good : values 21=.rational ((previous.getD tools abandonEntry).objective fee penalty))
    (bad : values 22=.rational ((P.menuBadBranch fee penalty previous tools).2.objective fee penalty))
    (bestLevel : values 23=.natural 0) (best : values 24=.rational penalty)
    (index : values 25=.natural 0) (pointer : values 39=.natural (source+1))
    (hgo : values 10=.rational (previous.getD tools abandonEntry).observation)
    (hgr : values 11=.rational (previous.getD tools abandonEntry).repairs)
    (hgf : values 12=.rational (previous.getD tools abandonEntry).failure)
    (hbo : values 31=.rational (P.menuBadBranch fee penalty previous tools).2.observation)
    (hbr : values 32=.rational (P.menuBadBranch fee penalty previous tools).2.repairs)
    (hbf : values 33=.rational (P.menuBadBranch fee penalty previous tools).2.failure)
    (hb : values 34=.natural (if (P.menuBadBranch fee penalty previous tools).1=.repair then 1 else 0)) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 2500*(P.certificate.M+1)+4920 ∧ Header after base afterValues ∧
      DenseFields afterValues (P.cachedNextMenuEntry P.endpointCache fee penalty previous tools) ∧
      (∀ slot,SolverControlSlot slot → afterValues slot=values slot) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(scanChoiceCode mode origin).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace,HeaderMemory before state base := by
  let selected:=cutoffScan
    (fun level => (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level).objective fee penalty)
    penalty P.certificate.M
  have scanFetch : FetchesCode program origin (scanKernel mode origin) := fetch.append_left.append_left
  obtain ⟨scanTrace,scanned,scannedValues,scanHead,scanLast,scanChain,scanTime,scannedHeader,selectedLevel,selectedScore,
    scannedBase,scannedPC,scanFrame,scanOutput,scanMemory,preserved,_⟩ :=
    scanKernel_caller_memory mode program input origin scanFetch P base source n k fee penalty previous tools nonzero avoids
      before values hpc header hbase hsource last good bad bestLevel best index pointer
  have scanLevel : scannedValues 23=.natural selected.1 := (scannedHeader.value 23 (by decide)).symm.trans selectedLevel
  have scanScore : scannedValues 24=.rational selected.2 := (scannedHeader.value 24 (by decide)).symm.trans selectedScore
  have prepFetch : FetchesCode program scanned.pc (headerCode finalChoiceCommands) := by
    rw [scannedPC]
    exact fetch.append_left.append_right
  obtain ⟨prepTrace,prepared,prepHead,prepLast,prepChain,prepTime,preparedHeader,preparedBase,preparedPC,prepFrame,prepOutput,prepMemory⟩:=
    headerCode_trace_memory finalChoiceCommands program input scanned base n k scannedValues (finalChoiceValues scannedValues)
      finalChoiceCommands_valid scannedHeader scannedBase (finalChoiceCommands_eval scannedValues) prepFetch
  have prepBound : time program prepTrace ≤ 1485 := prepTime
  have keep (slot : ℕ) (untouched : ScanUntouched slot) (h24 : slot ≠ 24) (h28 : slot ≠ 28)
      (outside : slot < 40 ∨ 46 ≤ slot) : finalChoiceValues scannedValues slot=values slot :=
    (finalChoiceValues_preserves scannedValues slot h24 h28 outside).trans (preserved slot untouched)
  have choiceFetch : FetchesCode program prepared.pc (selectedChoiceCode mode prepared.pc) := by
    have actualPC : prepared.pc=origin+112+(headerCode finalChoiceCommands).length := by rw [preparedPC,scannedPC]
    rw [actualPC]
    have raw:=fetch.append_right
    simpa only [List.length_append,scanKernel_length,Nat.add_assoc] using raw
  have preparedSource:=EndpointSource.frame_of_avoids mode input P source base n k before prepared hsource avoids
    (scanFrame.trans prepFrame)
  have preparedPenalty : finalChoiceValues scannedValues 24=.rational penalty :=
    (finalChoiceValues_cutoff scannedValues).trans ((preserved 2 (by decide)).trans hpenalty)
  have run:=selectedChoice_trace_memory mode program input P fee penalty selected.2 previous tools source selected.1
    prepared base n k (finalChoiceValues scannedValues) preparedHeader preparedBase preparedSource avoids
    ((keep 0 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hsourceValue)
    ((finalChoiceValues_preserves scannedValues 23 (by decide) (by decide) (Or.inl (by decide))).trans scanLevel)
    (cutoffScan_index_le _ _ _) ((finalChoiceValues_score scannedValues).trans scanScore) preparedPenalty
    ((keep 10 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hgo)
    ((keep 11 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hgr)
    ((keep 12 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hgf)
    ((keep 31 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hbo)
    ((keep 32 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hbr)
    ((keep 33 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hbf)
    ((keep 34 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hb) choiceFetch
  obtain ⟨choiceTrace,after,choiceHead,choiceLast,choiceChain,choiceTime,afterHeader,afterBase,afterPC,choiceFrame,choiceOutput,choiceMemory⟩:=run
  have firstJoin:=joinTrace_spec program input scanTrace prepTrace before scanned prepared
    (2500*(P.certificate.M+1)+135) 1485 scanHead scanLast prepHead prepLast scanChain prepChain scanTime prepBound
  have firstMemory:=joinTrace_memory scanTrace prepTrace before scanned base scanLast scanMemory prepMemory
  have finalJoin:=joinTrace_spec program input (joinTrace scanTrace prepTrace) choiceTrace before prepared after
    (2500*(P.certificate.M+1)+135+1485) 3300 firstJoin.1 firstJoin.2.1 choiceHead choiceLast firstJoin.2.2.1
    choiceChain firstJoin.2.2.2 choiceTime
  refine ⟨joinTrace (joinTrace scanTrace prepTrace) choiceTrace,after,_,finalJoin.1,finalJoin.2.1,finalJoin.2.2.1,?_,
    afterHeader,?_,?_,afterBase,?_,scanFrame.trans (prepFrame.trans choiceFrame),choiceOutput.trans (prepOutput.trans scanOutput),
    joinTrace_memory (joinTrace scanTrace prepTrace) choiceTrace before prepared base firstJoin.2.1 firstMemory choiceMemory⟩
  · have bound:=finalJoin.2.2.2
    omega
  · rw [cachedNextMenuEntry_cutoff_strict P fee penalty previous tools nonzero]
    exact selectedChoiceValues_dense mode P (finalChoiceValues scannedValues) fee penalty selected.2 previous tools source selected.1
      (finalChoiceValues_dense scannedValues)
  · intro slot control
    have h24 : slot ≠ 24 := by unfold SolverControlSlot at control; omega
    have h28 : slot ≠ 28 := by unfold SolverControlSlot at control; omega
    have outside : slot < 40 ∨ 46 ≤ slot := by unfold SolverControlSlot at control; omega
    have untouched : ScanUntouched slot := by
      unfold ScanUntouched
      unfold SolverControlSlot at control
      omega
    exact (selectedChoiceValues_controls mode P _ fee penalty selected.2 previous tools source selected.1 slot control).trans
      ((finalChoiceValues_preserves scannedValues slot h24 h28 outside).trans (preserved slot untouched))
  · rw [afterPC,preparedPC,scannedPC,scanChoiceCode,List.length_append,List.length_append,scanKernel_length]
    omega

end PDCompute.Solver
