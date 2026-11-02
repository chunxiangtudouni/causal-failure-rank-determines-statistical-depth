module
public import Paid.PDCompute_Nat_OriginalResources_014
public import Paid.PDCompute_SolverCalleeCode_145
public import Paid.PDCompute_Nat_IncrementResources_016

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
attribute [local irreducible] fullCellCode matrixCode matrixPackCode

/-- M+1 comes from the ORIGINAL actual cache length. It is paid by162's
original scale, never incorrectly bounded by the n/k workspace capacity. -/
theorem originalControlBudget_count (incoming : ℕ) (P : Parameters) (fee penalty : ℚ) (n k origin span : ℕ) :
    1+natBits (P.certificate.M+1)≤originalControlBudget incoming P fee penalty n k origin span := by
  have first:=Nat.mul_le_mul_right (2*(P.certificate.M+1)+2) (by omega : 1≤n+1)
  simp only [one_mul] at first
  have second:=Nat.mul_le_mul_left ((n+1)*(2*(P.certificate.M+1)+2)) (by omega : 1≤maximumMenuBits P fee+1)
  simp only [mul_one] at second
  have weight : P.certificate.M+1≤solverBitScale P fee penalty n k:=by unfold solverBitScale;omega
  have countBits : natBits (P.certificate.M+1)≤(P.certificate.M+1)+1:=Nat.add_le_add_right (Nat.log2_le_self _) 1
  unfold originalControlBudget
  omega

/-- TRUE seven-register original solver entry, without initialized Header,
precomputed table, resource/run oracle or world-live-disjointness. Frozen
140/144 execute the real37+9 producer on ONE caller-carried global budget;
all actual subsequent natural nodes use this same ControlContext. -/
theorem solver_natural_entry_resources (mode : ReaderMode) (origin : ℕ) (input : List Cell)
    (P : Parameters) (fee penalty : ℚ) (before : State) (base n k source returnPC : ℕ)
    (hpc : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (old : before.register .old=.natural returnPC) (address : before.register .address=.natural source)
    (total : before.register .total=.rational penalty) (index : before.register .index=.natural n)
    (value : before.register .value=.natural k) (flag : before.register .flag=.rational fee)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k) :
    ∃ trace : List State,∃ ready : State,∃ values : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some ready ∧
      trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧ time (solverLocatedProgram mode origin) trace≤2610 ∧
      Header ready base values ∧ values 0=.natural source ∧ values 1=.natural returnPC ∧ values 2=.rational penalty ∧
      values 3=.natural n ∧ values 4=.natural k ∧ values 5=.rational fee ∧ values 6=.natural P.certificate.M ∧
      ready.register .fresh=.natural base ∧ ready.pc=origin+46 ∧ EndpointSource mode input P source ready ∧
      Frame before ready base n k ∧ ready.output=before.output ∧
      peakCells trace≤workingCells before+62*entryCount n k ∧
      natBits returnPC≤originalControlBudget (PDCompute.Pack.initialBits before) P fee penalty n k origin (solverCalleeCode mode origin).length ∧
      SolverControlContext before (PDCompute.Pack.initialBits before) base n k mode origin
        (originalControlBudget (PDCompute.Pack.initialBits before) P fee penalty n k origin (solverCalleeCode mode origin).length) ∧
      ∀ state∈trace,RegionMemory before state (workspace base n k) ∧ RootD27.Bits.SafeBits state
        (originalControlBudget (PDCompute.Pack.initialBits before) P fee penalty n k origin (solverCalleeCode mode origin).length) := by
  let program:=solverLocatedProgram mode origin
  have fetch:=solverLocated_fetch mode origin
  let budget:=originalControlBudget (PDCompute.Pack.initialBits before) P fee penalty n k origin (solverCalleeCode mode origin).length
  have context:=controlContext_originalScale before (PDCompute.Pack.initialBits before) base n k origin (solverCalleeCode mode origin).length P fee penalty
    (PDCompute.Pack.initialBits_safe before) fresh
  have initialSafe : RootD27.Bits.SafeBits before budget:=context.initial_safe
  have addressBits : 1+natBits (base+headerWords)≤budget:=context.header
  have zeroSmall : (.rational 0 : Cell).bits≤(.natural 48 : Cell).bits:=by decide
  have zeroBits : (.rational 0 : Cell).bits≤budget:=zeroSmall.trans (context.small 48 (le_refl _))
  have lengthBits : 1+natBits (P.certificate.M+1)≤budget:=originalControlBudget_count _ P fee penalty n k origin _
  have spanBound : 46≤(solverCalleeCode mode origin).length:=by
    simp only [solverCalleeCode,List.length_append,solverHeaderCode_length,endpointCountHeaderCode_length]
    omega
  have pcBits : natBits (origin+46)≤budget:=context.pc _ (by omega)
  have headerPC : natBits (origin+37)≤budget:=(natBits_mono (by omega : origin+37≤origin+46)).trans pcBits
  have prologueFetch : FetchesCode program before.pc solverPrologue := by rw [hpc]; exact solverCallee_prologue_fetch mode program origin fetch
  obtain ⟨initial,initialized,initialHead,initialLast,initialChain,initialTime,initialHeader,initialBase,initialPC,initialFrame,_,initialResources,_⟩:=
    solver_header_initialization_resources program input origin before base n k budget hpc fresh initialSafe addressBits zeroBits headerPC
      prologueFetch (solverCallee_lead_fetch mode program origin fetch) (solverCallee_loop_fetch mode program origin fetch)
  let values:=initializedHeaderValues (solverPrologueResult before base) base
  have saved0 : values 0=.natural source := by simpa only [savedArguments,List.getElem_cons_zero,address] using initializedHeaderValue_saved before base 0 (by decide)
  have saved1 : values 1=.natural returnPC := by simpa only [savedArguments,List.getElem_cons_succ,List.getElem_cons_zero,old] using initializedHeaderValue_saved before base 1 (by decide)
  have saved2 : values 2=.rational penalty := by simpa only [savedArguments,List.getElem_cons_succ,List.getElem_cons_zero,total] using initializedHeaderValue_saved before base 2 (by decide)
  have saved3 : values 3=.natural n := by simpa only [savedArguments,List.getElem_cons_succ,List.getElem_cons_zero,index] using initializedHeaderValue_saved before base 3 (by decide)
  have saved4 : values 4=.natural k := by simpa only [savedArguments,List.getElem_cons_succ,List.getElem_cons_zero,value] using initializedHeaderValue_saved before base 4 (by decide)
  have saved5 : values 5=.rational fee := by simpa only [savedArguments,List.getElem_cons_succ,List.getElem_cons_zero,flag] using initializedHeaderValue_saved before base 5 (by decide)
  have initializedSource:=EndpointSource.frame_of_avoids mode input P source base n k before initialized hsource avoids initialFrame
  have initializedSafe:=(initialResources initialized (List.mem_of_getLast? initialLast)).2.1
  have countPC : natBits (initialized.pc+9) ≤ budget := by simpa only [initialPC,Nat.add_assoc] using pcBits
  have countFetch : FetchesCode program initialized.pc (endpointCountHeaderCode mode) := by rw [initialPC]; exact solverCallee_count_fetch mode program origin fetch
  obtain ⟨count,middle,countHead,countLast,countChain,countTime,middleHeader,middleBase,middlePC,countResources⟩:=
    endpointCountHeader_trace_resources mode program input P initialized base source budget values initialHeader initialBase initializedSource saved0
      initializedSafe addressBits lengthBits countPC countFetch
  let middleValues:=Function.update values 6 (.natural P.certificate.M)
  have countMemory : ∀ state∈count,RegionMemory initialized state (workspace base n k) :=
    fun state member=>(countResources state member).1.enlarge (headerRegion_subset_workspace base n k)
  have middleFrame:=(RegionMemory.trace_last countMemory countLast).frame (Finset.Subset.refl _)
  have middleSource:=EndpointSource.frame_of_avoids mode input P source base n k initialized middle initializedSource avoids middleFrame
  have atMatrix : middle.pc=origin+46 := by rw [middlePC,initialPC]
  have middle0 : middleValues 0=.natural source := by simpa only [middleValues,Function.update_of_ne (by decide : (0 : ℕ) ≠ 6)] using saved0
  have middle1 : middleValues 1=.natural returnPC := by simpa only [middleValues,Function.update_of_ne (by decide : (1 : ℕ) ≠ 6)] using saved1
  have middle2 : middleValues 2=.rational penalty := by simpa only [middleValues,Function.update_of_ne (by decide : (2 : ℕ) ≠ 6)] using saved2
  have middle3 : middleValues 3=.natural n := by simpa only [middleValues,Function.update_of_ne (by decide : (3 : ℕ) ≠ 6)] using saved3
  have middle4 : middleValues 4=.natural k := by simpa only [middleValues,Function.update_of_ne (by decide : (4 : ℕ) ≠ 6)] using saved4
  have middle5 : middleValues 5=.rational fee := by simpa only [middleValues,Function.update_of_ne (by decide : (5 : ℕ) ≠ 6)] using saved5
  have initialMemory : ∀ state∈initial,RegionMemory before state (workspace base n k):=
    fun state member=>(initialResources state member).1.enlarge (headerRegion_subset_workspace base n k)
  have joined:=joinTrace_spec program input initial count before initialized middle 2460 150
    initialHead initialLast countHead countLast initialChain countChain initialTime countTime
  have allMemory:=RegionMemory.join_trace initial count before initialized _ initialLast initialMemory countMemory
  have allBits : ∀ state∈joinTrace initial count,RootD27.Bits.SafeBits state budget:=PDCompute.Pack.joinTrace_invariant initial count
    (fun state=>RootD27.Bits.SafeBits state budget) (fun state member=>(initialResources state member).2.1)
    (fun state member=>(countResources state member).2.1)
  have finalMemory:=RegionMemory.trace_last allMemory joined.2.1
  refine ⟨joinTrace initial count,middle,middleValues,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,middleHeader,
    middle0,middle1,middle2,middle3,middle4,middle5,Function.update_self _ _ _,middleBase,atMatrix,middleSource,
    finalMemory.frame (Finset.Subset.refl _),finalMemory.2.2.2,?_,context.returnPC returnPC old,context,
    fun state member=>⟨allMemory state member,allBits state member⟩⟩
  exact PDLower.CalibrationCompute.peakCells_le_of_forall _ _ (fun state member=>(allMemory state member).workspace_workingCells)

end PDCompute.NatControl
