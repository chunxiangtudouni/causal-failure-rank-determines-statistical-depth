module
public import Paid.PDCompute_CoreSelector_Bracket_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace PDCompute.CoreSelector
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CoreSearch RootD27.Core PDCompute.CoreSearchLoop

/-- All three real paths of the fixed180 selector. The initial two heap
fields and all subsidiary fetches are derived from Ready and the whole
literal-code fetch, never supplied as original input qualifications. -/
theorem selector_piece (P : Parameters) (fee : ℚ) (frontend : CachedFrontend) (source : MultiplierState)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (scale budget : ℕ) (sourceEq : frontend.state=source) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before source) (safe : RootD27.Bits.SafeBits before budget)
    (small : 7≤budget)
    (bracketFields : ∀ lower upper,source=.bracket lower upper→ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+180)≤budget) (belowEntry : before.pc+180<labels.solveEntry)
    (fetched : FetchesCode program before.pc (finalSelectorCode before.pc)) :
    ∃ after,∃ _piece : Piece program input P fee source budget before.pc (before.pc+180) before after 4000,
      after.pc=before.pc+180 ∧ after.heap 29=.rational (selectorWeightRat P fee frontend) := by
  have parts:=finalSelector_fetch_parts program before.pc fetched
  obtain ⟨compared,risk,riskPC⟩:=risk_piece P fee source program labels input before budget ready represented safe
    small addressBits pcBits belowEntry parts.1
  have comparedSafe:=(risk.properties compared (List.mem_of_getLast? risk.last)).2
  by_cases zero : P.zeroChargeRisk fee≤P.certificate.risk
  · have comparedPC : compared.pc=before.pc+176 := by simpa only [ite_eq_left zero] using riskPC
    obtain ⟨after,written,pc,value⟩:=zero_piece P fee source program labels input before.pc compared budget comparedPC
      risk.ready risk.represented comparedSafe small addressBits pcBits belowEntry parts.2.2.2.2
    have selected:=selector_source_zero P fee frontend zero
    exact ⟨after,(risk.join written).bound (by decide),pc,by simpa only [selected] using value⟩
  · have comparedPC : compared.pc=before.pc+11 := by simpa only [ite_eq_right zero] using riskPC
    obtain ⟨tagged,tag,tagPC⟩:=tag_piece P fee source program labels input before.pc compared budget comparedPC
      risk.ready risk.represented comparedSafe small pcBits belowEntry parts.2.1
    have taggedSafe:=(tag.properties tagged (List.mem_of_getLast? tag.last)).2
    cases source with
    | exact solution =>
      have taggedPC : tagged.pc=before.pc+176:=tagPC
      obtain ⟨after,written,pc,value⟩:=zero_piece P fee (.exact solution) program labels input before.pc tagged budget
        taggedPC tag.ready tag.represented taggedSafe small addressBits pcBits belowEntry parts.2.2.2.2
      have selected:=selector_source_exact P fee frontend solution sourceEq
      exact ⟨after,((risk.join tag).join written).bound (by decide),pc,by simpa only [selected] using value⟩
    | bracket lower upper =>
      have taggedPC : tagged.pc=before.pc+15:=tagPC
      obtain ⟨after,written,pc,value⟩:=bracket_piece P fee lower upper program labels input before.pc tagged scale budget
        taggedPC tag.ready tag.represented taggedSafe (bracketFields lower upper rfl) room addressBits pcBits belowEntry
        parts.2.2.1 parts.2.2.2.1
      have selected:=selector_source_bracket P fee frontend lower upper zero sourceEq
      exact ⟨after,((risk.join tag).join written).bound (by decide),pc,by simpa only [selected] using value⟩

/-- Actual finalSelectorCode180 on ONE real trace: true source weight,
all-prefix SAME B/one scalar region, proper PC, no space increase, no
solver request and the original fixed-epilogue call-refinement predicate. -/
theorem selector_actual (P : Parameters) (fee : ℚ) (frontend : CachedFrontend) (source : MultiplierState)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (scale budget callConstant : ℕ) (sourceEq : frontend.state=source) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before source) (safe : RootD27.Bits.SafeBits before budget)
    (small : 7≤budget)
    (bracketFields : ∀ lower upper,source=.bracket lower upper→ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+180)≤budget) (belowEntry : before.pc+180<labels.solveEntry)
    (fetched : FetchesCode program before.pc (finalSelectorCode before.pc)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤4000 ∧
      after.pc=before.pc+180 ∧ Ready P fee after ∧ SearchStateRep P fee after source ∧
      after.heap 29=.rational (selectorWeightRat P fee frontend) ∧ after.heap 28=before.heap 28 ∧
      after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state scalarRegion ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+180) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+180) ∧ peakCells trace≤workingCells before ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 ∧
      SolverCallRefinement program labels P fee callConstant trace := by
  obtain ⟨after,piece,pc,value⟩:=selector_piece P fee frontend source program labels input before scale budget sourceEq
    ready represented safe small bracketFields room addressBits pcBits belowEntry fetched
  have scalarLive : scalarRegion⊆before.live := by
    intro address member
    have bound:=(Finset.mem_Icc.mp member).2
    have inside : address<headerWords:=by change address<48;omega
    simpa only [Nat.zero_add] using ready.header.live address inside
  have allSpace : ∀ state∈piece.trace,workingCells state≤workingCells before := by
    intro state member
    exact (existing_region_workingCells scalarLive (piece.properties state member).1).le
  have excluded : ∀ state∈piece.trace,state.pc≠labels.solveEntry := by
    intro state member
    have bound:=piece.scope state member
    omega
  have noCalls:=no_solve_entry labels piece.trace excluded
  have refinement:=refinement_of_no_entry program labels P fee callConstant piece.trace excluded
  exact ⟨piece.trace,after,piece.head,piece.last,piece.chain,piece.time,pc,piece.ready,piece.represented,value,
    piece.counter,piece.output,piece.properties,piece.scope,piece.proper,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,noCalls.1,noCalls.2,refinement⟩

end PDCompute.CoreSelector
