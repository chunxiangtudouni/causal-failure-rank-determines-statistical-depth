module
public import Paid.PDCompute_CoreFinalization_Boundary_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
@[expose] public section
namespace PDCompute.CoreFinalization
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open RootD27.Core PDLower.CoreSearch PDCompute.CoreSearchLoop

def emittedCells (P : Parameters) (fee : ℚ) (frontend : CachedFrontend) : List Cell :=
  encodeState frontend.state++[.rational (selectorWeightRat P fee frontend)]

structure Result (program : Program) (labels : RoutineLabels) (input : List Cell) (P : Parameters) (fee : ℚ)
    (frontend : CachedFrontend) (budget origin : ℕ) (before : State) where
  trace : List State
  selected : State
  after : State
  head : trace.head?=some before
  last : trace.getLast?=some after
  chain : trace.IsChain (fun first later=>step program input first=some later)
  timeBound : time program trace≤4000+1024*((encodeState frontend.state).length+2)
  selectedMember : selected∈trace
  selectedPC : selected.pc=origin+180
  selectedWeight : selected.heap 29=.rational (selectorWeightRat P fee frontend)
  heap : after.heap=selected.heap
  live : after.live=selected.live
  counter : after.heap 28=before.heap 28
  output : after.output=before.output++emittedCells P fee frontend
  pc : after.pc=origin+251
  halt : program[after.pc]?=some .halt
  stopped : step program input after=none
  frames : ∀ state∈trace,OutputRegion before (emittedCells P fee frontend) state
  safe : ∀ state∈trace,RootD27.Bits.SafeBits state budget
  space : peakCells trace≤workingCells before+(emittedCells P fee frontend).length
  bits : peakOperandBits trace≤budget
  scope : ∀ state∈trace,origin≤state.pc ∧ state.pc≤origin+251
  proper : ∀ state∈trace.dropLast,origin≤state.pc ∧ state.pc<origin+251
  below : ∀ state∈trace,origin≤state.pc ∧ state.pc<labels.solveEntry
  requests : actualSolveRequests labels trace=[]
  count : PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0
  refinement : SolverCallRefinement program labels P fee 40000 trace

/-- Original252 = actualSelector180 + actualTail72, with physical emit
facts DERIVED from true083 representation rather than supplied payload. -/
theorem given_budget (P : Parameters) (fee : ℚ) (frontend : CachedFrontend)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (origin : ℕ) (before : State)
    (scale budget : ℕ) (position : before.pc=origin) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before frontend.state) (safe : RootD27.Bits.SafeBits before budget)
    (small : 7≤budget)
    (bracketFields : ∀ lower upper,frontend.state=.bracket lower upper→ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (capBits : 1+natBits (PDLower.CoreRuntimeNumeric.runtimeAddressLimit P)≤budget)
    (endBits : natBits (origin+252)≤budget) (belowEntry : origin+252≤labels.solveEntry)
    (fetched : FetchesCode program origin (finalizationCode origin)) :
    Nonempty (Result program labels input P fee frontend budget origin before) := by
  have parts:=fetch_parts program origin fetched
  have selectorFetch : FetchesCode program before.pc (finalSelectorCode before.pc) := by rw [position];exact parts.1
  obtain ⟨selecting,selected,sh,sl,sc,st,selectedPC,selectedReady,selectedRep,weight,counter,output,properties,
    selectorScope,_selectorProper,_selectorSpace,_selectorRequests,_selectorCount,_selectorRefinement⟩:=
    PDCompute.CoreSelector.selector_actual P fee frontend frontend.state program labels input before scale budget 40000
      rfl ready represented safe small bracketFields room addressBits
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+180≤origin+252)).trans endBits) (by omega) selectorFetch
  have actualSelectedPC : selected.pc=origin+180 := by omega
  have selectedMemory:=(properties selected (List.mem_of_getLast? sl)).1
  have selectedSafe:=(properties selected (List.mem_of_getLast? sl)).2
  have dimensions:=prepared_emit_dimensions P fee selected selectedReady.prepared
  have payload:=selectedRep.emit_payload
  have ends : PDCompute.CoreEmit.StateEndBound P.certificate.stages P.tools P.certificate.M
      (PDLower.CoreRuntimeNumeric.runtimeAddressLimit P) frontend.state := selectedRep.emit_ends
  have selectorStored:=live_selector selected _ selectedReady.header weight
  obtain ⟨tail,after,th,tl,tc,tt,afterPC,halt,stopped,heap,live,afterOutput,emitted,_tailSpace,_tailBits,tailSafe,tailProper⟩:=
    PDCompute.CoreFinalTail.tail_trace_resources program input (origin+180) selected P.certificate.stages P.tools
      P.certificate.M (PDLower.CoreRuntimeNumeric.runtimeAddressLimit P) budget frontend.state
      (selectorWeightRat P fee frontend) actualSelectedPC dimensions payload selectorStored selectedSafe ends capBits
      (by simpa only [Nat.add_assoc] using endBits) parts.2
  have finalPC : after.pc=origin+251 := by omega
  have tailScope : ∀ state∈tail,origin+180≤state.pc ∧ state.pc≤origin+251 := by
    have split:=List.dropLast_append_getLast? after (by rw [tl];simp)
    intro state member
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · have bounds:=tailProper state proper
      omega
    · have same:=List.mem_singleton.mp terminal
      subst state
      omega
  have joined:=joinTrace_spec program input selecting tail before selected after 4000
    (1024*((encodeState frontend.state).length+2)) sh sl th tl sc tc st tt
  have allFrames : ∀ state∈joinTrace selecting tail,OutputRegion before (emittedCells P fee frontend) state := by
    intro state member
    rcases joinTrace_member member with prior|later
    · exact OutputRegion.of_scalar _ ready.header (properties state prior).1
    · exact OutputRegion.of_emitted ready.header selectedMemory output (emitted state later)
  have allSafe:=PDCompute.Pack.joinTrace_invariant selecting tail (fun state=>RootD27.Bits.SafeBits state budget)
    (fun state member=>(properties state member).2) tailSafe
  have allScope : ∀ state∈joinTrace selecting tail,origin≤state.pc ∧ state.pc≤origin+251 := by
    intro state member
    rcases joinTrace_member member with prior|later
    · have bounds:=selectorScope state prior
      omega
    · have bounds:=tailScope state later
      omega
  have tailNonempty : tail≠[]:=by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at th
  have allProper : ∀ state∈(joinTrace selecting tail).dropLast,origin≤state.pc ∧ state.pc<origin+251 := by
    intro state member
    change state∈(selecting.dropLast++tail).dropLast at member
    rw [List.dropLast_append_of_ne_nil tailNonempty] at member
    rcases List.mem_append.mp member with prior|later
    · have bounds:=selectorScope state (List.mem_of_mem_dropLast prior)
      omega
    · have bounds:=tailProper state later
      omega
  have allBelow : ∀ state∈joinTrace selecting tail,origin≤state.pc ∧ state.pc<labels.solveEntry := by
    intro state member
    have bounds:=allScope state member
    omega
  have excluded : ∀ state∈joinTrace selecting tail,state.pc≠labels.solveEntry :=
    fun state member=>Nat.ne_of_lt (allBelow state member).2
  have noCalls:=no_solve_entry labels (joinTrace selecting tail) excluded
  have refinement:=refinement_of_no_entry program labels P fee 40000 (joinTrace selecting tail) excluded
  have selectedMember : selected∈joinTrace selecting tail := by
    apply List.mem_append_right
    exact List.mem_of_head? th
  have allSpace : ∀ state∈joinTrace selecting tail,
      workingCells state≤workingCells before+(emittedCells P fee frontend).length :=
    fun state member=>(allFrames state member).space
  refine ⟨⟨joinTrace selecting tail,selected,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    selectedMember,actualSelectedPC,weight,heap,live,?_,?_,finalPC,halt,stopped,allFrames,allSafe,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,PDCompute.Pack.safeBits_peak _ budget allSafe,
    allScope,allProper,allBelow,noCalls.1,noCalls.2,refinement⟩⟩
  · rw [heap]
    exact counter
  · simpa only [output,emittedCells] using afterOutput

end PDCompute.CoreFinalization
