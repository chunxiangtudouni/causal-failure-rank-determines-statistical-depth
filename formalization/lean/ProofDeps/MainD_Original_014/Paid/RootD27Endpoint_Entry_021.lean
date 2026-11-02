module

public import Paid.RootD27Endpoint_CacheInvariant_016
public import Paid.RootD27Endpoint_Fetch_020
public import Paid.RootD27Endpoint_CacheHead_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

def entryHeaderValues (before : State) (base : ℕ) : ℕ → Cell :=
  initializedHeaderValues (solverPrologueResult before base) base

theorem entryHeaderValues_saved (before : State) (base slot : ℕ) (inside : slot<6) :
    entryHeaderValues before base slot=(savedArguments before)[slot]'(by change slot<6; exact inside) := by
  simp only [entryHeaderValues,initializedHeaderValues,ite_eq_left inside]
  exact PDLower.CalibrationCompute.HeapList.value (solverPrologue_arguments before base) slot
    (by change slot<6; exact inside)

def loopEntryValues (P : Parameters) (before : State) (base : ℕ) : ℕ → Cell :=
  Function.update (initializedValues (entryHeaderValues before base) P.certificate.gamma) 17 (.natural (P.certificate.M+1))

/-- The entire105-opcode entry actually builds its header and the one-cell
cache prefix from the real six register arguments. No initialized heap,
answer cache, successful run, fuel or workspace-disjointness is assumed. -/
theorem entry_actual (P : Parameters) (program : Program) (input : List Cell)
    (origin : ℕ) (before : State) (base E returnPC : ℕ)
    (position : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (hE : before.register .address=.natural E) (hret : before.register .old=.natural returnPC)
    (hgamma : before.register .total=.rational P.certificate.gamma)
    (hM : before.register .index=.natural P.certificate.M)
    (hfee : before.register .value=.rational P.reviewFee)
    (separated : base+48≤E) (fetched : FetchesCode program origin (endpointCode origin)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤4140 ∧ after.pc=origin+105 ∧ after.register .fresh=.natural base ∧
      Header after base (loopEntryValues P before base) ∧
      EndpointValues P E returnPC 0 (loopEntryValues P before base) ∧
      StoredCache P E 0 after ∧ after.output=before.output := by
  let values:=entryHeaderValues before base
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
  obtain ⟨bootTrace,boot,bh,bl,bc,bt,bootHeader,bootFresh,bootPC,_,bootOutput⟩:=
    header_initialization_actual program input origin before base position fresh
      (by rw [position]; exact endpoint_prologue_fetch program origin fetched)
      (endpoint_paddingLead_fetch program origin fetched) (endpoint_padding_fetch program origin fetched)
  have scalarFetch : FetchesCode program boot.pc (headerCode initialCommands) := by
    rw [bootPC]
    exact endpoint_scalar_fetch program origin fetched
  obtain ⟨scalarTrace,scalar,sh,sl,sc,st,scalarHeader,scalarFresh,scalarPC,_,scalarOutput,_⟩:=
    initialize_scalar_actual P program input boot base values bootHeader bootFresh vg scalarFetch
  have cacheFetch : FetchesCode program scalar.pc cacheHeaderCode := by
    rw [scalarPC,bootPC]
    simpa only [Nat.add_assoc] using endpoint_cacheHead_fetch program origin fetched
  have initialInvariant:=EndpointValues.initialized P E returnPC values vE vr vg vM vf
  obtain ⟨cacheTrace,ch,cl,cc,ct,cacheHeader,cacheLive,cacheValue⟩:=
    cacheHeader_actual program input scalar base P.certificate.M E (initializedValues values P.certificate.gamma)
      scalarHeader scalarFresh initialInvariant.stop initialInvariant.cache separated cacheFetch
  let after:=cacheHeaderResult scalar base P.certificate.M E
  have joined1:=joinTrace_spec program input bootTrace scalarTrace before boot scalar 2460 1485
    bh bl sh sl bc sc bt st
  have joined:=joinTrace_spec program input (joinTrace bootTrace scalarTrace) cacheTrace before scalar after 3945 195
    joined1.1 joined1.2.1 ch cl joined1.2.2.1 cc joined1.2.2.2 ct
  refine ⟨joinTrace (joinTrace bootTrace scalarTrace) cacheTrace,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2,?_,?_,cacheHeader,initialInvariant.cache_header,StoredCache.initial P E after cacheLive cacheValue,?_⟩
  · rw [cacheHeader_pc,scalarPC,bootPC]
  · exact (cacheHeader_fresh scalar base P.certificate.M E).trans scalarFresh
  · exact (cacheHeader_output scalar base P.certificate.M E).trans (scalarOutput.trans bootOutput)

end RootD27.Endpoint
