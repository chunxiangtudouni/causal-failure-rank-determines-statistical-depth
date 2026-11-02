module

public import Paid.PDCompute_SolverScanCallerBits_188
public import Paid.PDCompute_SolverScanSetupBits_183
public import Paid.PDCompute_SolverSelectedChoiceBits_195
public import Paid.PDCompute_SolverScanChoice_105

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.Solver
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- COMPLETE original M+1 scan and actual strict selected reconstruction,
with all original output fields and EVERY-prefix memory/bits on ONE run. -/
theorem scanChoice_trace_bits (mode : ReaderMode) (program : Program) (input : List Cell)
    (origin : ℕ) (fetch : FetchesCode program origin (scanChoiceCode mode origin))
    (P : Parameters) (base source n k budget S G : ℕ) (fee penalty : ℚ) (previous : MenuRow) (tools : ℕ)
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
    (hb : values 34=.natural (if (P.menuBadBranch fee penalty previous tools).1=.repair then 1 else 0))
    (safe : RootD27.Bits.SafeBits before budget)
    (goodBits : ratEncodingBits ((previous.getD tools abandonEntry).objective fee penalty)≤G)
    (badBits : ratEncodingBits ((P.menuBadBranch fee penalty previous tools).2.objective fee penalty)≤G)
    (goBits : ratEncodingBits (previous.getD tools abandonEntry).observation≤S)
    (grBits : ratEncodingBits (previous.getD tools abandonEntry).repairs≤S) (gfBits : ratEncodingBits (previous.getD tools abandonEntry).failure≤S)
    (boBits : ratEncodingBits (P.menuBadBranch fee penalty previous tools).2.observation≤S)
    (brBits : ratEncodingBits (P.menuBadBranch fee penalty previous tools).2.repairs≤S) (bfBits : ratEncodingBits (P.menuBadBranch fee penalty previous tools).2.failure≤S)
    (scanRoom : 1+64*(maximumMenuBits P fee+G+1)≤budget) (fieldsRoom : 1+64*(maximumMenuBits P fee+S+1)≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (indexBits : 1+natBits (P.certificate.M+1)≤budget)
    (sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget)
    (counter : natBits (origin+(scanChoiceCode mode origin).length)≤budget) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 2500*(P.certificate.M+1)+4920 ∧ Header after base afterValues ∧
      DenseFields afterValues (P.cachedNextMenuEntry P.endpointCache fee penalty previous tools) ∧
      (∀ slot,SolverControlSlot slot → afterValues slot=values slot) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(scanChoiceCode mode origin).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state ∈ trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let selected:=cutoffScan
    (fun level => (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level).objective fee penalty)
    penalty P.certificate.M
  have scanFetch : FetchesCode program origin (scanKernel mode origin) := fetch.append_left.append_left
  obtain ⟨scanTrace,scanned,scannedValues,scanHead,scanLast,scanChain,scanTime,scannedHeader,selectedLevel,selectedScore,
    scannedBase,scannedPC,scanFrame,scanOutput,scanMemory,preserved,scanSafe,_⟩ :=
    scanKernel_caller_bits mode program input origin scanFetch P base source n k budget G fee penalty previous tools nonzero avoids
      before values hpc header hbase hsource last good bad bestLevel best index pointer safe goodBits badBits scanRoom addressBits indexBits sourceBits
      ((natBits_mono (by unfold scanChoiceCode; simp only [List.length_append,scanKernel_length]; omega : origin+112≤origin+(scanChoiceCode mode origin).length)).trans counter)
  have scanLevel : scannedValues 23=.natural selected.1 := (scannedHeader.value 23 (by decide)).symm.trans selectedLevel
  have scanScore : scannedValues 24=.rational selected.2 := (scannedHeader.value 24 (by decide)).symm.trans selectedScore
  have prepFetch : FetchesCode program scanned.pc (headerCode finalChoiceCommands) := by
    rw [scannedPC]
    exact fetch.append_left.append_right
  have prepCounter : natBits (scanned.pc+(headerCode finalChoiceCommands).length)≤budget :=
    (natBits_mono (by rw [scannedPC]; unfold scanChoiceCode; simp only [List.length_append,scanKernel_length]; omega :
      scanned.pc+(headerCode finalChoiceCommands).length≤origin+(scanChoiceCode mode origin).length)).trans counter
  obtain ⟨prepTrace,prepared,prepHead,prepLast,prepChain,prepTime,preparedHeader,preparedBase,preparedPC,prepFrame,prepOutput,prepResources⟩:=
    finalChoice_trace_bits program input scanned base n k budget scannedValues scannedHeader scannedBase (scanSafe scanned (List.mem_of_getLast? scanLast))
      (by omega) addressBits prepCounter prepFetch
  have prepMemory : ∀ state∈prepTrace,HeaderMemory scanned state base := fun state member=>(prepResources state member).1
  have prepSafe : ∀ state∈prepTrace,RootD27.Bits.SafeBits state budget := fun state member=>(prepResources state member).2
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
  have choiceCounter : natBits (prepared.pc+(selectedChoiceCode mode prepared.pc).length)≤budget := by
    have actualPC : prepared.pc=origin+112+(headerCode finalChoiceCommands).length := by rw [preparedPC,scannedPC]
    rw [actualPC]
    simpa only [scanChoiceCode,List.length_append,scanKernel_length,Nat.add_assoc] using counter
  have run:=selectedChoice_trace_bits mode program input P fee penalty selected.2 previous tools source selected.1
    prepared base n k budget S (finalChoiceValues scannedValues) preparedHeader preparedBase preparedSource avoids
    ((keep 0 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hsourceValue)
    ((finalChoiceValues_preserves scannedValues 23 (by decide) (by decide) (Or.inl (by decide))).trans scanLevel)
    (cutoffScan_index_le _ _ _) ((finalChoiceValues_score scannedValues).trans scanScore) preparedPenalty
    ((keep 10 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hgo)
    ((keep 11 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hgr)
    ((keep 12 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hgf)
    ((keep 31 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hbo)
    ((keep 32 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hbr)
    ((keep 33 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hbf)
    ((keep 34 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hb)
    (prepSafe prepared (List.mem_of_getLast? prepLast)) goBits grBits gfBits boBits brBits bfBits fieldsRoom addressBits sourceBits choiceCounter choiceFetch
  obtain ⟨choiceTrace,after,choiceHead,choiceLast,choiceChain,choiceTime,afterHeader,afterBase,afterPC,choiceFrame,choiceOutput,choiceMemory,choiceSafe⟩:=run
  have firstJoin:=joinTrace_spec program input scanTrace prepTrace before scanned prepared
    (2500*(P.certificate.M+1)+135) 1485 scanHead scanLast prepHead prepLast scanChain prepChain scanTime prepBound
  have firstMemory:=joinTrace_memory scanTrace prepTrace before scanned base scanLast scanMemory prepMemory
  have finalJoin:=joinTrace_spec program input (joinTrace scanTrace prepTrace) choiceTrace before prepared after
    (2500*(P.certificate.M+1)+135+1485) 3300 firstJoin.1 firstJoin.2.1 choiceHead choiceLast firstJoin.2.2.1
    choiceChain firstJoin.2.2.2 choiceTime
  refine ⟨joinTrace (joinTrace scanTrace prepTrace) choiceTrace,after,_,finalJoin.1,finalJoin.2.1,finalJoin.2.2.1,?_,
    afterHeader,?_,?_,afterBase,?_,scanFrame.trans (prepFrame.trans choiceFrame),choiceOutput.trans (prepOutput.trans scanOutput),
    joinTrace_memory (joinTrace scanTrace prepTrace) choiceTrace before prepared base firstJoin.2.1 firstMemory choiceMemory,
    PDCompute.Pack.joinTrace_invariant (joinTrace scanTrace prepTrace) choiceTrace (fun state=>RootD27.Bits.SafeBits state budget)
      (PDCompute.Pack.joinTrace_invariant scanTrace prepTrace (fun state=>RootD27.Bits.SafeBits state budget) scanSafe prepSafe) choiceSafe⟩
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
