module

public import Common.PSTR_L01_RecordDecision_002

/-! The fourth physical word carries the TABLE's actual chosen tool.
Decode its original none0/some(val+1) convention, preserving that exact
tie. Eligibility and the unused-tool guarantee come from the proved
callback producer; no incidence matrix is read by this local decoder. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTableRecordDecision

open PaperProofs.Statistics PaperProofs.Structure PaperProofs.Structure.LaminarTree
open PSTRQueryRecords

def encodedTool (q word : Nat) : Option (Fin q) :=
  if word = 0 then none else
  if within : word - 1 < q then some ⟨word - 1, within⟩ else none

def recordTool (q : Nat) : List Nat → Option (Fin q)
  | _current :: _good :: _bad :: tool :: _later => encodedTool q tool
  | _ => none

theorem encoded_tool_none (q : Nat) : encodedTool q 0 = none := by simp [encodedTool]

theorem encoded_tool_some (q : Nat) (tool : Fin q) : encodedTool q (tool.val + 1) = some tool := by
  rcases tool with ⟨value, within⟩
  simp [encodedTool, within]

theorem record_tool_reply (q : Nat) (answer : IndexedQuery.Reply q) :
    recordTool q (replyWords q answer) = answer.tool := by
  change encodedTool q (match answer.tool with | none => 0 | some tool => tool.val + 1) = answer.tool
  cases present : answer.tool with
  | none => exact encoded_tool_none q
  | some tool => exact encoded_tool_some q tool

theorem actual_current_tool {I : Instance} (available : Finset I.Tool)
    (history : List (VisibleEvent I)) (active : historyCursor history < I.stageCount) :
    recordTool I.toolCount ((nativeRecords available history).drop (4 * historyCursor history)) =
      (CompactControllerClaims.callback I.toolCount I.compatibility
        ⟨historyCursor history, Nat.lt_succ_of_lt active⟩
        (PA17L01HistoryPrefixStrategy002.stageUsed available history (historyCursor history))).tool := by
  rw [nativeRecords_current available history active]
  exact record_tool_reply _ _

theorem callback_record_tool_spec (q : Nat) (full : List (Finset (Fin q)))
    (laminar : LaminarSchedule full) (stage : Fin full.length) (used : Finset (Fin q))
    (tool : Fin q)
    (selected : recordTool q (replyWords q
      (CompactControllerClaims.callback q full ⟨stage.val, by omega⟩ used)) = some tool) :
    tool ∈ full[stage.val] ∧ tool ∉ used ∧
      errorRank (full.drop (stage.val + 1)) ((Finset.univ \ used).erase tool) =
        (CompactControllerClaims.callback q full ⟨stage.val, by omega⟩ used).bad := by
  rw [record_tool_reply] at selected
  exact (PSTRCallback.callback_stage q full laminar stage used).2.2.2 tool selected

end PaperProofs.Common.Native.PSTRTableRecordDecision
