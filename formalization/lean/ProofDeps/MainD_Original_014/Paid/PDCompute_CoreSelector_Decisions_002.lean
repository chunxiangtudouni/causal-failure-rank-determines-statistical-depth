module
public import Paid.PDCompute_CoreSelector_Pieces_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
@[expose] public section
namespace PDCompute.CoreSelector
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CoreSearch RootD27.Core PDCompute.CoreSearchLoop

theorem risk_piece (P : Parameters) (fee : ℚ) (source : MultiplierState)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (budget : ℕ) (ready : Ready P fee before) (represented : SearchStateRep P fee before source)
    (safe : RootD27.Bits.SafeBits before budget) (small : 7≤budget)
    (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (before.pc+180)≤budget)
    (belowEntry : before.pc+180<labels.solveEntry)
    (fetched : FetchesCode program before.pc
      (comparisonDecisionCode .lessEqual 12 3 (before.pc+11) (before.pc+176))) :
    ∃ after,∃ _piece : Piece program input P fee source budget before.pc (before.pc+180) before after 180,
      after.pc=if P.zeroChargeRisk fee≤P.certificate.risk then before.pc+176 else before.pc+11 := by
  have fields:=prepared_selector_fields P fee before ready.prepared
  obtain ⟨trace,after,head,last,chain,cost,pc,fresh,header,rep,precise,properties,scope,proper,
    _space,_requests,_count,_refinement⟩:=
    represented_comparison_decision_actual P fee source .lessEqual 12 3 (P.zeroChargeRisk fee)
      P.certificate.risk program labels input before (before.pc+11) (before.pc+176) budget 1
      ready.header ready.fresh represented (by decide) (by decide) fields.1 fields.2 safe (by omega)
      addressBits ((PDROC.DataBits.natBits_mono (by omega : before.pc+11≤before.pc+180)).trans pcBits)
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+11≤before.pc+180)).trans pcBits)
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+176≤before.pc+180)).trans pcBits)
      (by omega) (by omega) (by omega) fetched
  have target : comparisonDecisionTarget .lessEqual (P.zeroChargeRisk fee) P.certificate.risk
      (before.pc+11) (before.pc+176)=
      if P.zeroChargeRisk fee≤P.certificate.risk then before.pc+176 else before.pc+11 := by
    simp only [comparisonDecisionTarget,Comparison.rat,decide_eq_true_eq]
  have locations : ∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+180 := by
    intro state member
    rcases scope state member with inline|terminal
    · omega
    · rw [target] at terminal
      split_ifs at terminal <;> omega
  let piece:=Piece.of_trace trace head last chain cost ready header fresh rep
    (precise.1 28 (by decide)) precise.2.2.2 properties locations
    (fun state member=>by have bounds:=proper state member;omega)
  exact ⟨after,piece,pc.trans target⟩

def selectorTagTarget (origin : ℕ) : MultiplierState→ℕ
  | .exact _=>origin+176
  | .bracket _ _=>origin+15

theorem selectorTagTarget_bounds (origin : ℕ) (source : MultiplierState) :
    origin≤selectorTagTarget origin source ∧ selectorTagTarget origin source≤origin+180 := by
  cases source <;> simp only [selectorTagTarget] <;> omega

theorem selector_tag_target (before : State) (source : MultiplierState) (origin : ℕ)
    (position : before.pc=origin+11) :
    (tagDecisionResult before source (origin+176)).pc=selectorTagTarget origin source := by
  cases source <;> simp [tagDecisionResult,tagDecisionTarget,sourceTag,selectorTagTarget,position,Nat.add_assoc]

theorem tag_piece (P : Parameters) (fee : ℚ) (source : MultiplierState)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (origin : ℕ) (before : State)
    (budget : ℕ) (position : before.pc=origin+11) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before source) (safe : RootD27.Bits.SafeBits before budget)
    (small : 7≤budget) (pcBits : natBits (origin+180)≤budget) (belowEntry : origin+180<labels.solveEntry)
    (fetched : FetchesCode program (origin+11) (tagDecisionCode (origin+11) (origin+176))) :
    ∃ after,∃ _piece : Piece program input P fee source budget origin (origin+180) before after 75,
      after.pc=selectorTagTarget origin source := by
  have fetch : FetchesCode program before.pc (tagDecisionCode before.pc (origin+176)) := by rw [position];exact fetched
  obtain ⟨trace,head,last,chain,cost,header,fresh,rep,properties,scope,proper,_space,_requests,_count⟩:=
    represented_tag_actual P fee source program labels input before (origin+176) budget ready.header ready.fresh
      represented safe small
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+4≤origin+180)).trans pcBits)
      ((PDROC.DataBits.natBits_mono (by omega : origin+176≤origin+180)).trans pcBits)
      (by omega) (by omega) fetch
  let after:=tagDecisionResult before source (origin+176)
  have target : after.pc=selectorTagTarget origin source := selector_tag_target before source origin position
  have targetBounds:=selectorTagTarget_bounds origin source
  have locations : ∀ state∈trace,origin≤state.pc ∧ state.pc≤origin+180 := by
    intro state member
    rcases scope state member with inline|terminal
    · omega
    · change state.pc=after.pc at terminal
      rw [target] at terminal
      omega
  let piece:=Piece.of_trace trace head last chain cost ready header fresh rep rfl rfl
    (fun state member=>⟨((properties state member).1).enlarge (Finset.empty_subset _),(properties state member).2⟩)
    locations (fun state member=>by have bounds:=proper state member;omega)
  exact ⟨after,piece,target⟩

theorem zero_piece (P : Parameters) (fee : ℚ) (source : MultiplierState)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (origin : ℕ) (before : State)
    (budget : ℕ) (position : before.pc=origin+176) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before source) (safe : RootD27.Bits.SafeBits before budget)
    (small : 7≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (origin+180)≤budget) (belowEntry : origin+180<labels.solveEntry)
    (fetched : FetchesCode program (origin+176) (headerCode selectorZeroCommands)) :
    ∃ after,∃ _piece : Piece program input P fee source budget origin (origin+180) before after 75,
      after.pc=origin+180 ∧ after.heap 29=.rational 0 := by
  have fetch : FetchesCode program before.pc (headerCode selectorZeroCommands) := by rw [position];exact fetched
  obtain ⟨trace,after,head,last,chain,cost,pc,afterReady,rep,value,counter,output,_precise,properties,
    scope,proper,_space,_requests,_count,_refinement⟩:=
    represented_selector_zero_actual P fee source program labels input before budget 1 ready represented safe (by omega)
      addressBits (by simpa only [position,Nat.add_assoc] using pcBits) (by omega) fetch
  let piece : Piece program input P fee source budget origin (origin+180) before after 75:=
    ⟨trace,head,last,chain,cost,afterReady,rep,counter,output,properties,
      (fun state member=>by have bounds:=scope state member;omega),
      (fun state member=>by have bounds:=proper state member;omega)⟩
  exact ⟨after,piece,by omega,value⟩

end PDCompute.CoreSelector
