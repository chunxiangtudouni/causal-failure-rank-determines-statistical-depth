module

public import Common.PSTR_L01_NativeRecordRule_009

/-! The final permission filter is nonbinding on REAL original TABLE
Prefixes, by the existing aligned-ledger theorem. Omitting it here removes
the hidden I.eligible queries in historyAllowsAction. This equality is not
asserted on arbitrary malformed histories; the original L01 cost target
calls its planner only on actual native histories. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTableRecordPlanner

open PaperProofs.Statistics PaperProofs.Structure PaperProofs.Structure.LaminarTree
open CompactPrice PSTRQueryRecords PSTRTML01RecordReplay253 PSTRStatistics.TableAlignment

variable {I : Instance}

def recordCandidatePlanner (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I)) (records : List Nat) : Action I :=
  match recordReplay input available budget records history with
  | none => .abandon
  | some cache => recordCandidateFromCache input budget limit history records cache

theorem actual_prefix_record_candidate (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {clock : Nat} {state : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes clock state) :
    recordCandidatePlanner input available budget limit state.history (nativeRecords available state.history) =
      tableRule input available budget limit () state.history := by
  obtain ⟨cache, replay, aligned, kind, tool⟩ := actual_record_cache input C laminar current accounting
    available budget positive small limit seed truth tapes hp
  unfold recordCandidatePlanner
  rw [replay]
  have candidate := record_candidate_eq input available budget limit state.history
    (nativeRecords available state.history) cache aligned.parsed kind tool
  have allowed := tableRule_eq_candidate_of_prefix laminar input C current.1 accounting
    available budget positive small limit seed truth tapes hp
  exact candidate.trans allowed.symm

end PaperProofs.Common.Native.PSTRTableRecordPlanner
