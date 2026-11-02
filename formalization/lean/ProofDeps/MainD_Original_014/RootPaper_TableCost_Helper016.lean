module
public import RootPaper_TableCost_Naturals010
public import RootPaper_TableCost_Fees009
public import RootPaper_Reference_ChargedHistory009

/-! Thin concrete work-coverage bridges for the frozen TABLE helper sites.
Each result below is made from the values returned by the charged recursive
history traversals. The old TABLE body is implemented by substituting these
equal values. This does not change its cache, archive, action or information.
The factor 16 is a uniform visit allowance, not an assumed runtime oracle. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RootPaper.TableCost
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open RationalControllerComputation
variable {I : Instance}

theorem cursor_helper (history : List (VisibleEvent I)) :
    (RootPaper.Reference.Charged.lengthOf eventAdvance history).1=historyCursor history ∧
    (RootPaper.Reference.Charged.lengthOf eventAdvance history).2≤16*(HistoryRead.mk .cursor history.length).visits := by
  have actual:=RootPaper.Reference.Charged.lengthOf_spec eventAdvance history
  exact ⟨actual.1,actual.2.trans (by change 10*(history.length+1)≤16*(history.length+1);omega)⟩

theorem actions_helper (history : List (VisibleEvent I)) :
    (RootPaper.Reference.Charged.lengthOf eventAction history).1=(historyActions history).length ∧
    (RootPaper.Reference.Charged.lengthOf eventAction history).2≤16*(HistoryRead.mk .actions history.length).visits := by
  have actual:=RootPaper.Reference.Charged.lengthOf_spec eventAction history
  exact ⟨actual.1,actual.2.trans (by change 10*(history.length+1)≤16*(history.length+1);omega)⟩

theorem written_helper (history : List (VisibleEvent I)) (stage : I.Stage) :
    (RootPaper.Reference.Charged.lastOf (eventWrite stage) history).1=historyWrite history stage ∧
    (RootPaper.Reference.Charged.lastOf (eventWrite stage) history).2≤16*(HistoryRead.mk .written history.length).visits := by
  have actual:=RootPaper.Reference.Charged.lastOf_spec (eventWrite stage) history
  exact ⟨actual.1,actual.2.trans (by change 10*(history.length+1)≤16*(2*(history.length+1));omega)⟩

theorem reported_helper (history : List (VisibleEvent I)) (stage : I.Stage) :
    (RootPaper.Reference.Charged.lastOf (eventReport stage) history).1=historyReport history stage ∧
    (RootPaper.Reference.Charged.lastOf (eventReport stage) history).2≤16*(HistoryRead.mk .reported history.length).visits := by
  have actual:=RootPaper.Reference.Charged.lastOf_spec (eventReport stage) history
  exact ⟨actual.1,actual.2.trans (by change 10*(history.length+1)≤16*(2*(history.length+1));omega)⟩

def mismatchCalculation (cache : ReferenceReplayCache I) (stage : I.Stage) (handle : MismatchHandle I) : Bool×Nat :=
  let written:=RootPaper.Reference.Charged.lastOf (eventWrite stage) cache.seen
  let reported:=RootPaper.Reference.Charged.lastOf (eventReport stage) cache.seen
  let value:=match written.1,reported.1 with
    | some (bit,serial),some (truth,reportedSerial) =>
      decide (bit≠truth ∧ handle.stage=stage ∧ handle.writeSerial=serial ∧ reportedSerial=serial)
    | _,_ => false
  (value,written.2+reported.2+8)

theorem mismatch_helper (cache : ReferenceReplayCache I) (stage : I.Stage) (handle : MismatchHandle I) :
    (mismatchCalculation cache stage handle).1=referenceReplayMismatch cache stage handle ∧
    (mismatchCalculation cache stage handle).2≤16*(HistoryRead.mk .mismatch cache.seen.length).visits := by
  have w:=RootPaper.Reference.Charged.lastOf_spec (eventWrite stage) cache.seen
  have r:=RootPaper.Reference.Charged.lastOf_spec (eventReport stage) cache.seen
  refine ⟨?_,?_⟩
  · simp only [mismatchCalculation,w.1,r.1,referenceReplayMismatch,historyWrite,historyReport]
    rfl
  · change _+_+8≤16*(4*(cache.seen.length+1)+8)
    omega

def correctCalculation (cache : ReferenceReplayCache I) (stage : I.Stage) : Bool×Nat :=
  let written:=RootPaper.Reference.Charged.lastOf (eventWrite stage) cache.seen
  let reported:=RootPaper.Reference.Charged.lastOf (eventReport stage) cache.seen
  let value:=match written.1,reported.1 with
    | some (bit,serial),some (truth,reportedSerial) => decide (bit=truth ∧ reportedSerial=serial)
    | _,_ => false
  (value,written.2+reported.2+4)

theorem correct_helper (cache : ReferenceReplayCache I) (stage : I.Stage) :
    (correctCalculation cache stage).1=referenceReplayCorrect cache stage ∧
    (correctCalculation cache stage).2≤16*(HistoryRead.mk .correct cache.seen.length).visits := by
  have w:=RootPaper.Reference.Charged.lastOf_spec (eventWrite stage) cache.seen
  have r:=RootPaper.Reference.Charged.lastOf_spec (eventReport stage) cache.seen
  refine ⟨?_,?_⟩
  · simp only [correctCalculation,w.1,r.1,referenceReplayCorrect,historyWrite,historyReport]
    rfl
  · change _+_+4≤16*(4*(cache.seen.length+1)+8)
    omega

def handleCalculation (history : List (VisibleEvent I)) (stage : I.Stage) : Option (MismatchHandle I)×Nat :=
  let written:=RootPaper.Reference.Charged.lastOf (eventWrite stage) history
  (written.1.map (fun value=>⟨stage,value.2⟩),written.2+4)

theorem handle_helper (history : List (VisibleEvent I)) (stage : I.Stage) :
    (handleCalculation history stage).1=referenceVisibleHandle history stage ∧
    (handleCalculation history stage).2≤16*(HistoryRead.mk .handle history.length).visits := by
  have w:=RootPaper.Reference.Charged.lastOf_spec (eventWrite stage) history
  refine ⟨?_,?_⟩
  · simp only [handleCalculation,w.1,referenceVisibleHandle,historyWrite]
    cases (history.filterMap (eventWrite stage)).getLast? <;> rfl
  · change _+4≤16*(2*(history.length+1));omega

theorem used_card_history (history : List (VisibleEvent I)) :
    (RootPaper.Reference.Charged.used history).1.card≤history.length := by
  rw [RootPaper.Reference.Charged.used_value,historyUsed]
  exact (List.toFinset_card_le _).trans (by
    simp only [List.length_map,historyCommitments]
    exact List.length_filterMap_le _ _)

theorem used_work_history (history : List (VisibleEvent I)) :
    (RootPaper.Reference.Charged.used history).2≤8*(history.length+1)^2 := by
  induction history with
  | nil => change 1≤8*(0+1)^2;decide
  | cons event rest ih =>
    have card:=used_card_history rest
    dsimp only [RootPaper.Reference.Charged.used]
    cases entry:eventCommitment event with
    | none => simp only [List.length_cons];nlinarith
    | some pair =>
      dsimp only
      have probe:=(RootPaper.Reference.Charged.probe_spec pair.2 (RootPaper.Reference.Charged.used rest).1).2
      split_ifs <;> simp only [List.length_cons] <;> nlinarith

def usedCalculation (history : List (VisibleEvent I)) (tool : I.Tool) : Bool×Nat :=
  let selected:=RootPaper.Reference.Charged.used history
  let found:=RootPaper.Reference.Charged.probe tool selected.1
  (found.1,selected.2+found.2+2)

theorem used_helper (history : List (VisibleEvent I)) (tool : I.Tool) :
    (usedCalculation history tool).1=decide (tool∈historyUsed history) ∧
    (usedCalculation history tool).2≤16*(HistoryRead.mk .used history.length).visits := by
  have card:=used_card_history history
  have work:=used_work_history history
  have probe:=RootPaper.Reference.Charged.probe_spec tool (RootPaper.Reference.Charged.used history).1
  refine ⟨?_,?_⟩
  · simpa only [usedCalculation,RootPaper.Reference.Charged.used_value] using probe.1
  · change _+_+2≤16*(4*(history.length+1)^2)
    nlinarith [probe.2]

theorem available_helper (available : Finset I.Tool) (tool : I.Tool) :
    (RootPaper.Reference.Charged.probe tool available).1=decide (tool∈available) ∧
    (RootPaper.Reference.Charged.probe tool available).2≤16*(HistoryRead.mk .available I.toolCount).visits := by
  have actual:=RootPaper.Reference.Charged.probe_spec tool available
  have cardinal : available.card≤I.toolCount:=by simpa using Finset.card_le_univ available
  refine ⟨actual.1,?_⟩
  change _≤16*(I.toolCount+1)
  omega

def observationsCalculation (input : StatisticalInput I) (history : List (VisibleEvent I)) (stage : I.Stage) : (List Nat×Bool)×Nat :=
  let selected:=RootPaper.Reference.Charged.collect (eventObservation stage) history
  let checked:=RootPaper.Reference.Charged.validate (fun symbol=>decide (symbol<(input.experiment stage).alphabetSize)) selected.1
  let measured:=RootPaper.Reference.Charged.count selected.1
  let copied:=RootPaper.Reference.Charged.collect some selected.1
  ((copied.1,checked.1),selected.2+checked.2+measured.2+copied.2+4)

theorem observations_helper (input : StatisticalInput I) (history : List (VisibleEvent I)) (stage : I.Stage) :
    (observationsCalculation input history stage).1=(historyObservations history stage,
      decide (∀ symbol∈historyObservations history stage,symbol<(input.experiment stage).alphabetSize)) ∧
    (observationsCalculation input history stage).2≤16*(HistoryRead.mk .observations history.length).visits := by
  let selected:=RootPaper.Reference.Charged.collect (eventObservation stage) history
  have value: selected.1=historyObservations history stage:=RootPaper.Reference.Charged.collect_value _ _
  have collect:=RootPaper.Reference.Charged.collect_work (eventObservation stage) history
  have check:=RootPaper.Reference.Charged.validate_work (fun symbol=>decide (symbol<(input.experiment stage).alphabetSize)) selected.1
  have count:=(RootPaper.Reference.Charged.count_spec selected.1).2
  have copy:=RootPaper.Reference.Charged.collect_work (some : Nat→Option Nat) selected.1
  have length:selected.1.length≤history.length:=by rw [value];exact List.length_filterMap_le _ _
  refine ⟨?_,?_⟩
  · apply Prod.ext
    · simp only [observationsCalculation,RootPaper.Reference.Charged.collect_value,List.filterMap_some]
      rfl
    · simp only [observationsCalculation,RootPaper.Reference.Charged.validate_value]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true,decide_eq_true_eq,RootPaper.Reference.Charged.collect_value,historyObservations]
      exact ⟨fun proof=>_root_.decide_eq_true proof,fun proof=>_root_.of_decide_eq_true proof⟩
  · change selected.2+_+_+_+4≤16*(4*(history.length+1)^2)
    nlinarith

theorem append_helper {α : Type*} (items : List α) (value : α) :
    (RootPaper.Reference.Charged.appendOne items value).1=items++[value] ∧
    (RootPaper.Reference.Charged.appendOne items value).2≤4*(items.length+1) := by
  have actual:=RootPaper.Reference.Charged.appendOne_spec items value
  exact ⟨actual.1,by omega⟩

theorem count_helper {α : Type*} (items : List α) :
    (RootPaper.Reference.Charged.count items).1=items.length ∧
    (RootPaper.Reference.Charged.count items).2≤16*(HistoryRead.mk .events items.length).visits := by
  have actual:=RootPaper.Reference.Charged.count_spec items
  exact ⟨actual.1,by change _≤16*(items.length+1);omega⟩

def sameHistoryCalculation : List (VisibleEvent I)→List (VisibleEvent I)→Bool×Nat
  | [],[] => (true,1)
  | [],_::_ | _::_,[] => (false,2)
  | left::ls,right::rs =>
      if left=right then let tail:=sameHistoryCalculation ls rs;(tail.1,tail.2+4)
      else (false,3)

theorem sameHistory_value (left right : List (VisibleEvent I)) :
    (sameHistoryCalculation left right).1=decide (left=right) := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons first later ih =>
      cases right with
      | nil => rfl
      | cons second rest =>
          by_cases equal:first=second
          · subst second;simp [sameHistoryCalculation,ih]
          · simp [sameHistoryCalculation,equal]

theorem sameHistory_work (left right : List (VisibleEvent I)) :
    (sameHistoryCalculation left right).2≤16*(HistoryRead.mk .sameHistory (left.length+right.length)).visits := by
  induction left generalizing right with
  | nil => cases right <;> simp only [sameHistoryCalculation,HistoryRead.visits,List.length_nil,List.length_cons] <;> omega
  | cons first later ih =>
      cases right with
      | nil => simp only [sameHistoryCalculation,HistoryRead.visits,List.length_nil,List.length_cons];omega
      | cons second rest =>
          have tail:=ih rest
          dsimp only [sameHistoryCalculation]
          split_ifs <;> simp only [HistoryRead.visits,List.length_cons] at * <;> omega

/-- A charged traversal unit allows eight binary guards and a bounded
number of record-field/pointer copies. Final TABLE accounting uses the
fixed factor 256, covering the sixteen-unit helper allowance as well. -/
def helperUnitFee (B : Nat) : Nat:=(32840*9+4096)*(B+1)^2
def helperBitFee (B : Nat) (read : HistoryRead) : Nat:=256*65536*read.visits*(B+1)^2

theorem helper_fee_coverage (B ticks : Nat) (read : HistoryRead) (actual : ticks≤16*read.visits) :
    ticks*helperUnitFee B≤helperBitFee B read := by
  have coefficient : 16*(32840*9+4096)≤256*65536:=by decide
  calc
    _≤(16*read.visits)*((32840*9+4096)*(B+1)^2):=Nat.mul_le_mul_right _ actual
    _=(16*(32840*9+4096))*read.visits*(B+1)^2:=by ring
    _≤(256*65536)*read.visits*(B+1)^2:=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ coefficient)

theorem helper_binary_guard (B : Nat) (pair : Nat×Nat) (bound : NatPairBound B pair) :
    naturalFee pair≤helperUnitFee B := by
  have positive : 1≤natBits pair.1+natBits pair.2+1:=by omega
  have square : natBits pair.1+natBits pair.2+1≤(natBits pair.1+natBits pair.2+1)^2:=by nlinarith
  have first:naturalFee pair≤32840*(natBits pair.1+natBits pair.2+1)^2:=by unfold naturalFee;nlinarith
  have width:natBits pair.1+natBits pair.2+1≤3*(B+1):=by dsimp only [NatPairBound] at bound;omega
  have multiplied:=Nat.mul_le_mul_left 32840 (Nat.pow_le_pow_left width 2)
  have normalized : 32840*(3*(B+1))^2≤helperUnitFee B:=by unfold helperUnitFee;nlinarith
  exact first.trans (multiplied.trans normalized)

end RootPaper.TableCost
