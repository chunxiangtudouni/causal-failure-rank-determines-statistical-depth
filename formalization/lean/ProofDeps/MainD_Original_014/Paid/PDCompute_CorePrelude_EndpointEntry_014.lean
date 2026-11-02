module
public import Paid.PDCompute_CorePrelude_EndpointAdvance_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
@[expose] public section
namespace PDCompute.CorePrelude
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver RootD27.Endpoint RootD27.Bits PDMenu.ComputeFrame PDROC.EndpointOperands

/-- Literal initialization105 contains every original fetch, including
its shared padding flag instruction. -/
theorem initialization_fetch_parts (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (initializationCode origin)) :
    FetchesCode program origin solverPrologue ∧
    FetchesCode program (origin+16) paddingLeadCode ∧
    FetchesCode program (origin+19) (baseRowCode (origin+19)) ∧
    FetchesCode program (origin+37) (PDCompute.Solver.headerCode initialCommands) ∧
    FetchesCode program (origin+93) cacheHeaderCode := by
  simp only [initializationCode,List.append_assoc] at fetch
  refine ⟨fetch.append_left,?_,?_,?_,?_⟩
  · have rest : FetchesCode program (origin+16)
        (paddingSetup++(baseRowCode (origin+19)++(PDCompute.Solver.headerCode initialCommands++cacheHeaderCode))):=by
      simpa only [solverPrologue_length] using fetch.append_right
    intro offset inside
    have bounded : offset<4:=inside
    have actualBound : offset<(paddingSetup++(baseRowCode (origin+19)++
        (PDCompute.Solver.headerCode initialCommands++cacheHeaderCode))).length:=by
      simp only [List.length_append,paddingSetup_length,baseRowCode_length,initialScalar_length,cacheHeaderCode_length]
      omega
    have same : (paddingSetup++(baseRowCode (origin+19)++
        (PDCompute.Solver.headerCode initialCommands++cacheHeaderCode)))[offset]?=paddingLeadCode[offset]?:=by
      interval_cases offset <;> rfl
    exact (rest offset actualBound).trans same
  · simpa only [solverPrologue_length,paddingSetup_length,Nat.add_assoc] using fetch.append_right.append_right.append_left
  · simpa only [solverPrologue_length,paddingSetup_length,baseRowCode_length,Nat.add_assoc] using fetch.append_right.append_right.append_right.append_left
  · simpa only [solverPrologue_length,paddingSetup_length,baseRowCode_length,initialScalar_length,Nat.add_assoc] using
      fetch.append_right.append_right.append_right.append_right

/-- The same original105 initializer and its actual chosen numeric trace,
now retaining a real located scope and exactly one entrance. -/
theorem endpoint_entry_scoped (P : Parameters) (input : List Cell)
    (origin : ℕ) (before : State) (base E returnPC budget : ℕ)
    (position : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (hE : before.register .address=.natural E) (hret : before.register .old=.natural returnPC)
    (hgamma : before.register .total=.rational P.certificate.gamma)
    (hM : before.register .index=.natural P.certificate.M)
    (hfee : before.register .value=.rational P.reviewFee)
    (separated : base+48≤E)
    (callerSafe : SafeBits before budget) (control : ControlBudget P origin base E returnPC budget)
    (rational : rationalBudget P≤budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step (locatedBlock origin (initializationCode origin).toArray) input first=some later) ∧
      time (locatedBlock origin (initializationCode origin).toArray) trace≤4140 ∧ after.pc=origin+105 ∧ after.register .fresh=.natural base ∧
      Header after base (loopEntryValues P before base) ∧
      EndpointValues P E returnPC 0 (loopEntryValues P before base) ∧
      StoredCache P E 0 after ∧ after.output=before.output ∧ BelowBase before after base ∧
      (∀ state∈trace,RegionMemory before state (endpointLoopRegion base E P.certificate.M) ∧
        SafeBits state budget) ∧
      PaperProofs.Paid.Computation.entryCount origin trace=1 ∧
      (∀ state∈trace.dropLast,origin≤state.pc ∧ state.pc<origin+105) := by
  let program:=locatedBlock origin (initializationCode origin).toArray
  have fetched : FetchesCode program origin (initializationCode origin):=by
    intro offset inside
    rw [locatedBlock_fetch,List.getElem?_toArray]
  have parts:=initialization_fetch_parts program origin fetched
  let values := entryHeaderValues before base
  have vE : values 0=.natural E := by
    dsimp only [values]
    rw [entryHeaderValues_saved before base 0 (by decide)]
    simpa only [savedArguments,List.getElem_cons_zero] using hE
  have vr : values 1=.natural returnPC := by
    dsimp only [values]
    rw [entryHeaderValues_saved before base 1 (by decide)]
    simpa only [savedArguments,List.getElem_cons_succ,List.getElem_cons_zero] using hret
  have vg : values 2=.rational P.certificate.gamma := by
    dsimp only [values]
    rw [entryHeaderValues_saved before base 2 (by decide)]
    simpa only [savedArguments,List.getElem_cons_succ,List.getElem_cons_zero] using hgamma
  have vM : values 3=.natural P.certificate.M := by
    dsimp only [values]
    rw [entryHeaderValues_saved before base 3 (by decide)]
    simpa only [savedArguments,List.getElem_cons_succ,List.getElem_cons_zero] using hM
  have vf : values 4=.rational P.reviewFee := by
    dsimp only [values]
    rw [entryHeaderValues_saved before base 4 (by decide)]
    simpa only [savedArguments,List.getElem_cons_succ,List.getElem_cons_zero] using hfee
  obtain ⟨bootTrace,boot,bh,bl,bc,bt,bootHeader,bootFresh,bootPC,bootFrame,bootOutput,bootPrefixes,_proper⟩ :=
    header_initialization_sameBudget program input P origin base E returnPC budget before position fresh callerSafe control
      (by rw [position];exact parts.1)
      (parts.2.1) (parts.2.2.1)
  have bootSafe := (bootPrefixes boot (List.mem_of_getLast? bl)).2.1
  have scalarFetch : FetchesCode program boot.pc (PDCompute.Solver.headerCode initialCommands) := by
    rw [bootPC]
    exact parts.2.2.2.1
  obtain ⟨scalarTrace,scalar,sh,sl,sc,st,scalarHeader,scalarFresh,scalarPC,scalarFrame,scalarOutput,scalarPrefixes⟩ :=
    initial_scalar_actual_sameBudget P program input origin base E returnPC budget boot values bootHeader bootFresh vg
      bootSafe control rational (by rw [bootPC];unfold pcCap;omega) scalarFetch
  have scalarSafe := (scalarPrefixes scalar (List.mem_of_getLast? sl)).2
  have cacheFetch : FetchesCode program scalar.pc cacheHeaderCode := by
    rw [scalarPC,bootPC]
    simpa only [Nat.add_assoc] using parts.2.2.2.2
  have initialInvariant := EndpointValues.initialized P E returnPC values vE vr vg vM vf
  obtain ⟨cacheTrace,ch,cl,cc,ct,cacheHeader,cacheLive,cacheValue,cachePrefixes⟩ :=
    cache_header_actual_sameBudget P program input origin base E returnPC budget scalar
      (initializedValues values P.certificate.gamma) scalarHeader scalarFresh initialInvariant.stop initialInvariant.cache
      scalarSafe control separated (by rw [scalarPC,bootPC];unfold pcCap;omega) cacheFetch
  let after := cacheHeaderResult scalar base P.certificate.M E
  have joined1 := joinTrace_spec program input bootTrace scalarTrace before boot scalar 2460 1485
    bh bl sh sl bc sc bt st
  have joined := joinTrace_spec program input (joinTrace bootTrace scalarTrace) cacheTrace before scalar after 3945 195
    joined1.1 joined1.2.1 ch cl joined1.2.2.1 cc joined1.2.2.2 ct
  have firstMemory : ∀ state∈joinTrace bootTrace scalarTrace,
      RegionMemory before state (endpointLoopRegion base E P.certificate.M) :=
    RegionMemory.join_trace bootTrace scalarTrace before boot _ bl
      (fun state member=>(bootPrefixes state member).1.enlarge Finset.subset_union_left)
      (fun state member=>(scalarPrefixes state member).1.region _ Finset.subset_union_left)
  have allMemory := RegionMemory.join_trace (joinTrace bootTrace scalarTrace) cacheTrace before scalar _
    joined1.2.1 firstMemory (fun state member=>(cachePrefixes state member).1)
  have firstSafe := PDCompute.Pack.joinTrace_invariant bootTrace scalarTrace (fun state=>SafeBits state budget)
    (fun state member=>(bootPrefixes state member).2.1) (fun state member=>(scalarPrefixes state member).2)
  have allSafe := PDCompute.Pack.joinTrace_invariant (joinTrace bootTrace scalarTrace) cacheTrace
    (fun state=>SafeBits state budget) firstSafe (fun state member=>(cachePrefixes state member).2)
  refine ⟨joinTrace (joinTrace bootTrace scalarTrace) cacheTrace,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2,?_,?_,cacheHeader,initialInvariant.cache_header,StoredCache.initial P E after cacheLive cacheValue,?_,?_,?_,?_,?_⟩
  · rw [cacheHeader_pc,scalarPC,bootPC]
  · exact (cacheHeader_fresh scalar base P.certificate.M E).trans scalarFresh
  · exact (cacheHeader_output scalar base P.certificate.M E).trans (scalarOutput.trans bootOutput)
  · exact (belowBase_of_solverFrame bootFrame).trans
      ((belowBase_of_solverFrame scalarFrame).trans (cacheHeader_below scalar base P.certificate.M E separated))
  · exact fun state member=>⟨allMemory state member,allSafe state member⟩

  · exact initialization_trace_entry_count origin input before _ joined.1 position joined.2.2.1
  · simpa only [List.size_toArray,initializationCode_length] using
      PDLower.CalibrationCompute.located_chain_scope origin (initializationCode origin).toArray input
        (joinTrace (joinTrace bootTrace scalarTrace) cacheTrace) joined.2.2.1

end PDCompute.CorePrelude
