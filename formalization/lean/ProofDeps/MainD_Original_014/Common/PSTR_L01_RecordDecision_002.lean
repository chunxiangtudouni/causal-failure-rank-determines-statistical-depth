module

public import Common.PSTR_L01_PlannerStreams_001
public import Structure.PSTR_Callback_001

/-! Executable integer decisions from the SAME physical four-word record.
No structural rank recursion is performed by this local TABLE decision.
The q+2 sentinel is distinguished from every possible finite rank (<=q+1),
including the original zero-bad and infinite-bad branches. These are the
record-only semantics to implement after the real dual-stream parser. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTableRecordDecision

open PaperProofs.Statistics PaperProofs.Structure.LaminarTree
open PSTRQueryRecords

def encodedKind (q current bad : Nat) : Option ReferenceBudgetCase :=
  if current = q + 2 then some .infiniteRank else
  if bad = 0 then some .noTool else
  if bad = q + 2 then none else
  if positive : 0 < bad then some (.finiteBad ⟨bad, positive⟩) else none

def recordKind (q : Nat) : List Nat → Option ReferenceBudgetCase
  | current :: _good :: bad :: _tool :: _later => encodedKind q current bad
  | _ => none

theorem encoded_kind_correct (q : Nat) (current bad : ℕ∞)
    (currentBound : current ≠ ⊤ → current ≤ ((q + 1 : Nat) : ℕ∞))
    (badBound : bad ≠ ⊤ → bad ≤ ((q + 1 : Nat) : ℕ∞)) :
    encodedKind q (AlgorithmClaims.encodeRank q current) (AlgorithmClaims.encodeRank q bad) =
      referenceCaseOfRanks current bad := by
  cases current using ENat.recTopCoe with
  | top => simp [encodedKind, AlgorithmClaims.encodeRank, referenceCaseOfRanks]
  | coe current =>
    have limited : current ≤ q + 1 := ENat.natCast_le_natCast.mp (currentBound (by simp))
    have different : current ≠ q + 2 := by omega
    cases bad using ENat.recTopCoe with
    | top => simp [encodedKind, AlgorithmClaims.encodeRank, referenceCaseOfRanks, different]
    | coe bad =>
      have limitedBad : bad ≤ q + 1 := ENat.natCast_le_natCast.mp (badBound (by simp))
      have differentBad : bad ≠ q + 2 := by omega
      by_cases zero : bad = 0
      · subst bad
        simp [encodedKind, AlgorithmClaims.encodeRank, referenceCaseOfRanks, different]
      · have positive : 0 < bad := Nat.pos_of_ne_zero zero
        simp [encodedKind, AlgorithmClaims.encodeRank, referenceCaseOfRanks,
          different, differentBad, zero, positive]

theorem record_kind_reply (q : Nat) (answer : IndexedQuery.Reply q)
    (currentBound : answer.rank ≠ ⊤ → answer.rank ≤ ((q + 1 : Nat) : ℕ∞))
    (badBound : answer.bad ≠ ⊤ → answer.bad ≤ ((q + 1 : Nat) : ℕ∞)) :
    recordKind q (replyWords q answer) = referenceCaseOfRanks answer.rank answer.bad := by
  change encodedKind q (AlgorithmClaims.encodeRank q answer.rank) (AlgorithmClaims.encodeRank q answer.bad) = _
  exact encoded_kind_correct q answer.rank answer.bad currentBound badBound

theorem callback_record_kind (q : Nat) (full : List (Finset (Fin q)))
    (laminar : LaminarSchedule full) (stage : Fin full.length) (used : Finset (Fin q)) :
    let answer := CompactControllerClaims.callback q full ⟨stage.val, by omega⟩ used
    recordKind q (replyWords q answer) = referenceCaseOfRanks answer.rank answer.bad := by
  dsimp only
  apply record_kind_reply
  · intro finite
    rw [PSTRCallback.callback_rank q full laminar] at finite ⊢
    exact IndexedQuery.errorRank_finite_le_q_add_one q _ _ finite
  · intro finite
    have same := (PSTRCallback.callback_stage q full laminar stage used).2.1
    rw [same] at finite ⊢
    exact IndexedQuery.badChildRank_finite_le_q_add_one q _ _ _ finite

theorem actual_current_kind {I : Instance} (available : Finset I.Tool)
    (history : List (VisibleEvent I)) (laminar : LaminarSchedule I.compatibility)
    (active : historyCursor history < I.stageCount) :
    let answer := CompactControllerClaims.callback I.toolCount I.compatibility
      ⟨historyCursor history, Nat.lt_succ_of_lt active⟩
      (PA17L01HistoryPrefixStrategy002.stageUsed available history (historyCursor history))
    recordKind I.toolCount ((nativeRecords available history).drop (4 * historyCursor history)) =
      referenceCaseOfRanks answer.rank answer.bad := by
  dsimp only
  rw [nativeRecords_current available history active]
  exact callback_record_kind I.toolCount I.compatibility laminar ⟨historyCursor history, active⟩ _

end PaperProofs.Common.Native.PSTRTableRecordDecision
