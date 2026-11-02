module

public import Common.PSTR_SYM_NaturalExportOriginalRun_092
public import Common.PSTR_L01_PlannerStreams_001
public import Structure.PSTR_CurrentRecordSlice_147
public import Structure.PSTR_Callback_001
public import Structure.PA17_L01HistoryPrefix_Actual_004b

/-!
L01.3 -> L01.4 -> L01.5: first real consumer endpoint.

The fixed combined Bool/TM2 program is the existing 020 dual-stream parser
followed by the existing 086 natural getter.  This file only joins that
actual machine path to the existing physical four-word record navigation and
to an actual Native Prefix.  It does not use replay, a generic picker, a
pre-filled table, or a symbolic expression as a planner proof.
-/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000

namespace PaperProofs.Common.Native.L01_3_5_TABLE_Consumer001

open PaperProofs.Common
open PaperProofs.Common.Native
open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree
open CompactPrice
open PSTRQueryRecords
open PSTRTablePlannerStreams
open PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport
open PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport.Joined
open PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream
open PaperProofs.Common.Native.PSTRWordVM
open PaperProofs.Common.Native.PSTRWordBool
open Turing
open PaperProofs.Structure.LaminarTree.PSTRCallback

variable {I : Instance}

/- Exact frozen four-word record ABI, kept local so this endpoint consumes
   the physical record product directly and does not import the old planner
   replay modules. -/
def recordAt (records : List Nat) (index : Nat) : List Nat :=
  (records.drop (4 * index)).take 4

def encodedKind (q current bad : Nat) : Option ReferenceBudgetCase :=
  if current = q + 2 then some .infiniteRank else
  if bad = 0 then some .noTool else
  if bad = q + 2 then none else
  if positive : 0 < bad then some (.finiteBad ⟨bad, positive⟩) else none

def recordKind (q : Nat) : List Nat → Option ReferenceBudgetCase
  | current :: _good :: bad :: _tool :: _later => encodedKind q current bad
  | _ => none

def encodedTool (q word : Nat) : Option (Fin q) :=
  if word = 0 then none else
  if within : word - 1 < q then some ⟨word - 1, within⟩ else none

def recordTool (q : Nat) : List Nat → Option (Fin q)
  | _current :: _good :: _bad :: tool :: _later => encodedTool q tool
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

theorem record_tool_reply (q : Nat) (answer : IndexedQuery.Reply q) :
    recordTool q (replyWords q answer) = answer.tool := by
  change encodedTool q (match answer.tool with | none => 0 | some tool => tool.val + 1) = answer.tool
  cases present : answer.tool with
  | none => simp [encodedTool]
  | some tool =>
    rcases tool with ⟨value, within⟩
    simp [encodedTool, within]

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

theorem callback_record_tool (q : Nat) (full : List (Finset (Fin q)))
    (stage : Fin full.length) (used : Finset (Fin q)) :
    recordTool q (replyWords q (CompactControllerClaims.callback q full
      ⟨stage.val, by omega⟩ used)) =
      (CompactControllerClaims.callback q full ⟨stage.val, by omega⟩ used).tool := by
  exact record_tool_reply _ _

structure RecordStepView (q : Nat) where
  words : List Nat
  kind : Option ReferenceBudgetCase
  tool : Option (Fin q)

def recordStep (q : Nat) (records : List Nat) (index : Nat) : RecordStepView q :=
  { words := recordAt records index
    kind := recordKind q (recordAt records index)
    tool := recordTool q (recordAt records index) }

noncomputable def nativeRecordStep (available : Finset I.Tool) (history : List (VisibleEvent I)) :
    RecordStepView I.toolCount :=
  recordStep I.toolCount (nativeRecords available history) (historyCursor history)

theorem recordStep_words (q : Nat) (records : List Nat) (index : Nat) :
    (recordStep q records index).words = recordAt records index := rfl

theorem recordStep_current_active (available : Finset I.Tool)
    (history : List (VisibleEvent I)) (laminar : LaminarSchedule I.compatibility)
    (active : historyCursor history < I.stageCount) :
    (nativeRecordStep available history).kind =
        referenceCaseOfRanks
          (CompactControllerClaims.callback I.toolCount I.compatibility
            ⟨historyCursor history, Nat.lt_succ_of_lt active⟩
            (PA17L01HistoryPrefixStrategy002.stageUsed available history
              (historyCursor history))).rank
          (CompactControllerClaims.callback I.toolCount I.compatibility
            ⟨historyCursor history, Nat.lt_succ_of_lt active⟩
            (PA17L01HistoryPrefixStrategy002.stageUsed available history
              (historyCursor history))).bad ∧
      (nativeRecordStep available history).tool =
        (CompactControllerClaims.callback I.toolCount I.compatibility
          ⟨historyCursor history, Nat.lt_succ_of_lt active⟩
          (PA17L01HistoryPrefixStrategy002.stageUsed available history
            (historyCursor history))).tool := by
  let index := historyCursor history
  have currentWords :
      recordAt (nativeRecords available history) index =
        replyWords I.toolCount
          (CompactControllerClaims.callback I.toolCount I.compatibility
            ⟨index, Nat.lt_succ_of_lt active⟩
            (PA17L01HistoryPrefixStrategy002.stageUsed available history index)) := by
    unfold recordAt
    rw [nativeRecords_current available history active]
    simp [index, replyWords]
  have kind := callback_record_kind I.toolCount I.compatibility laminar
    ⟨index, active⟩ (PA17L01HistoryPrefixStrategy002.stageUsed available history index)
  have tool := callback_record_tool I.toolCount I.compatibility
    ⟨index, active⟩ (PA17L01HistoryPrefixStrategy002.stageUsed available history index)
  rw [nativeRecordStep, recordStep, currentWords]
  exact ⟨kind, tool⟩

/-- The actual parser/getter output contract, including its real parser EOF. -/
theorem actual_consumer_recordStep
    (context : Unit) (background : Slot → List Bool)
    (input : StatisticalInput I) (contract : Contract I)
    (available : Finset I.Tool) (budget : Rat)
    (history : List (VisibleEvent I)) :
    ∃ (firstDigits secondDigits : List Bool) (path : List (GlobalState Unit))
      (final parsed : GlobalState Unit),
      path.head? = some (Joined.initial context background
        (CompactPrice.plannerInput input contract available budget history
          (nativeRecords available history))) ∧
      path.IsChain (fun before after =>
        TM2.step Joined.combinedProgram before = some after) ∧
      path.getLast? = some final ∧
      parsed ∈ path ∧
      parsed.l = some 1 ∧
      (Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0))).head = true ∧
      (Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0))).right =
        ListBlank.mk [] ∧
      Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0)) =
        recordEndTape (PSTRTablePlannerStreams.firstData input contract available budget history)
          firstDigits (nativeRecords available history) secondDigits ∧
      final.l = some (if nativeRecords available history = [] then 4 else 5) ∧
      final.var.1.1 = context ∧
      final.stk = Function.update parsed.stk 15
        (selectedOutput (nativeRecords available history) ++
          false :: false :: background 15) ∧
      (∀ slot, slot ≠ 0 → slot ≠ 1 → parsed.stk slot = background slot) ∧
      path.length ≤
        16385 *
            ((CompactPrice.plannerInput input contract available budget history
              (nativeRecords available history)).length + 1)^3 +
          3 * (VirtualReturn.outside background +
            65536 *
              ((CompactPrice.plannerInput input contract available budget history
                (nativeRecords available history)).length + 1)^3) + 6 ∧
      (∀ current ∈ path,
        current.var.1.1 = context ∧
        VirtualReturn.occupiedSlots current.stk ≤
          3 * (VirtualReturn.outside background +
            65536 *
              ((CompactPrice.plannerInput input contract available budget history
                (nativeRecords available history)).length + 1)^3) + 9) ∧
      ∀ current ∈ path, ∀ label, current.l = some label →
        (∀ node ∈ AuxWorkspace.nodes (Joined.combinedProgram label) current.var current.stk,
          VirtualReturn.occupiedSlots node.2 ≤
            16 *
              (3 * (VirtualReturn.outside background +
                65536 *
                  ((CompactPrice.plannerInput input contract available budget history
                    (nativeRecords available history)).length + 1)^3) + 16)) ∧
        ScannerStatement.clock (Joined.combinedProgram label) current.var current.stk ≤
          18 *
            (3 * (VirtualReturn.outside background +
              65536 *
                ((CompactPrice.plannerInput input contract available budget history
                  (nativeRecords available history)).length + 1)^3) + 17) := by
  obtain ⟨firstDigits, secondDigits, path, final, parsed, head, chain, last,
    member, port, tape, finalPort, finalContext, output, frame, time, resources, nodes⟩ :=
    actual_original_getter context background input contract available budget history
  have eofHead :
      (Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0))).head = true := by
    rw [tape]
    exact record_end_head _ _ _ _
  have eofRight :
      (Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0))).right =
        ListBlank.mk [] := by
    rw [tape]
    exact record_end_right _ _ _ _
  refine ⟨firstDigits, secondDigits, path, final, parsed, ?_⟩
  exact
    (show
      path.head? = some (Joined.initial context background
          (CompactPrice.plannerInput input contract available budget history
            (nativeRecords available history))) ∧
        path.IsChain (fun before after =>
          TM2.step Joined.combinedProgram before = some after) ∧
        path.getLast? = some final ∧
        parsed ∈ path ∧
        parsed.l = some 1 ∧
        (Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0))).head = true ∧
        (Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0))).right =
          ListBlank.mk [] ∧
        Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0)) =
          recordEndTape (PSTRTablePlannerStreams.firstData input contract available budget history)
            firstDigits (nativeRecords available history) secondDigits ∧
        final.l = some (if nativeRecords available history = [] then 4 else 5) ∧
        final.var.1.1 = context ∧
        final.stk = Function.update parsed.stk 15
          (selectedOutput (nativeRecords available history) ++
            false :: false :: background 15) ∧
        (∀ slot, slot ≠ 0 → slot ≠ 1 → parsed.stk slot = background slot) ∧
        path.length ≤
          16385 *
              ((CompactPrice.plannerInput input contract available budget history
                (nativeRecords available history)).length + 1)^3 +
            3 * (VirtualReturn.outside background +
              65536 *
                ((CompactPrice.plannerInput input contract available budget history
                  (nativeRecords available history)).length + 1)^3) + 6 ∧
        (∀ current ∈ path,
          current.var.1.1 = context ∧
          VirtualReturn.occupiedSlots current.stk ≤
            3 * (VirtualReturn.outside background +
              65536 *
                ((CompactPrice.plannerInput input contract available budget history
                  (nativeRecords available history)).length + 1)^3) + 9) ∧
        ∀ current ∈ path, ∀ label, current.l = some label →
          (∀ node ∈ AuxWorkspace.nodes (Joined.combinedProgram label) current.var current.stk,
            VirtualReturn.occupiedSlots node.2 ≤
              16 *
                (3 * (VirtualReturn.outside background +
                  65536 *
                    ((CompactPrice.plannerInput input contract available budget history
                      (nativeRecords available history)).length + 1)^3) + 16)) ∧
          ScannerStatement.clock (Joined.combinedProgram label) current.var current.stk ≤
            18 *
              (3 * (VirtualReturn.outside background +
                65536 *
                  ((CompactPrice.plannerInput input contract available budget history
              (nativeRecords available history)).length + 1)^3) + 17) from
      ⟨head, chain, last, member, port, eofHead, eofRight, tape, finalPort,
        finalContext, output, frame, time, resources, nodes⟩)

/-- The same endpoint at an actual Native Prefix; records are the same
physical Native records, and the TABLE tie is read from that record. -/
theorem actual_native_prefix_recordStep
    (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility)
    (_current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : Rat)
    (limit : ReferenceObservationLimit I)
    (_positive : 0 < budget) (_small : budget ≤ 1 / 2)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {clock : Nat} {state : State I}
    (_hp : Prefix input C .uncapped accounting
      (tableRule input available budget limit) seed truth tapes clock state) :
    state.cursor = historyCursor state.history ∧
      (nativeRecordStep available state.history).words =
        recordAt (nativeRecords available state.history) (historyCursor state.history) ∧
      ((active : historyCursor state.history < I.stageCount) →
        (nativeRecordStep available state.history).kind =
            referenceCaseOfRanks
              (CompactControllerClaims.callback I.toolCount I.compatibility
                ⟨historyCursor state.history,
                  Nat.lt_succ_of_lt active⟩
                (PA17L01HistoryPrefixStrategy002.stageUsed available state.history
                  (historyCursor state.history))).rank
              (CompactControllerClaims.callback I.toolCount I.compatibility
                ⟨historyCursor state.history,
                  Nat.lt_succ_of_lt active⟩
                (PA17L01HistoryPrefixStrategy002.stageUsed available state.history
                  (historyCursor state.history))).bad ∧
        (nativeRecordStep available state.history).tool =
            (CompactControllerClaims.callback I.toolCount I.compatibility
              ⟨historyCursor state.history,
                Nat.lt_succ_of_lt active⟩
              (PA17L01HistoryPrefixStrategy002.stageUsed available state.history
                (historyCursor state.history))).tool) := by
  have cursor := prefix_historyCursor input C .uncapped accounting
    (tableRule input available budget limit) seed truth tapes _hp
  refine ⟨cursor.symm, rfl, ?_⟩
  intro active
  exact recordStep_current_active available state.history laminar active

end PaperProofs.Common.Native.L01_3_5_TABLE_Consumer001

