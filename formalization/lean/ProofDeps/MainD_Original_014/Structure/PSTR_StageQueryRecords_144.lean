module

public import Structure.PSTR_QueryRecordSemantics_143

/-! The semantic record stream for the ORIGINAL query/declaration grammar.
Completed-stage transitions are later discharged by the existing actual
Native history theorem. A current unpaired query remains in the stream. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRQueryRecords

open PaperProofs.Structure.LaminarTree
open CompactControllerClaims PA17L01HistoryPrefixCommands001

theorem semanticRecords_congr {q : Nat} (full : List (Finset (Fin q)))
    (leftConfiguration rightConfiguration : Configuration q) (left right : List Command)
    (configurationEq : leftConfiguration = rightConfiguration) (commandsEq : left = right)
    (leftAllowed : PSTRCommandPrefixes.AllowedSequence full leftConfiguration left)
    (rightAllowed : PSTRCommandPrefixes.AllowedSequence full rightConfiguration right) :
    semanticRecords full leftConfiguration left leftAllowed =
      semanticRecords full rightConfiguration right rightAllowed := by
  cases configurationEq
  cases commandsEq
  rfl

noncomputable def stageWords {q : Nat} (full : List (Finset (Fin q)))
    (used : Nat → Finset (Fin q)) (stage : Nat) : List Nat :=
  if bound : stage < full.length + 1 then
    replyWords q (callback q full ⟨stage, bound⟩ (used stage)) else []

noncomputable def stageRecords {q : Nat} (full : List (Finset (Fin q)))
    (used : Nat → Finset (Fin q)) (first count : Nat) : List Nat :=
  (List.range' first count).flatMap (stageWords full used)

theorem stageWords_spec {q : Nat} (full : List (Finset (Fin q)))
    (used : Nat → Finset (Fin q)) (stage : Nat) (bound : stage < full.length + 1) :
    stageWords full used stage = replyWords q (callback q full ⟨stage, bound⟩ (used stage)) := by
  simp only [stageWords, bound, ↓reduceDIte]

theorem query_step {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (later : List Command) (allowed : PSTRCommandPrefixes.AllowedSequence full configuration (.query :: later)) :
    semanticRecords full configuration (.query :: later) allowed =
      replyWords q (callback q full
        ⟨configuration.stage, allowed_stage_bound full configuration .query allowed.1⟩ configuration.used) ++
      semanticRecords full configuration later allowed.2 := rfl

theorem declaration_step {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (later : List Command) (notQuery : command ≠ .query)
    (allowed : PSTRCommandPrefixes.AllowedSequence full configuration (command :: later)) :
    semanticRecords full configuration (command :: later) allowed =
      semanticRecords full (nextConfiguration q full configuration command) later allowed.2 := by
  change (if command = .query then _ else []) ++
    semanticRecords full (nextConfiguration q full configuration command) later allowed.2 = _
  rw [ite_eq_right notQuery, List.nil_append]

theorem stageRecords_zero {q : Nat} (full : List (Finset (Fin q)))
    (used : Nat → Finset (Fin q)) (first : Nat) : stageRecords full used first 0 = [] := rfl

theorem stageRecords_succ {q : Nat} (full : List (Finset (Fin q)))
    (used : Nat → Finset (Fin q)) (first count : Nat) :
    stageRecords full used first (count + 1) =
      stageWords full used first ++ stageRecords full used (first + 1) count := by
  simp only [stageRecords, List.range'_succ, List.flatMap_cons]

theorem pair_extra_records {q : Nat} (full : List (Finset (Fin q)))
    (declaration : Nat → Command) (used : Nat → Finset (Fin q)) (limit : Nat)
    (hlimit : limit ≤ full.length) (transitions : StageTransitions full declaration used limit)
    (first count : Nat) (bound : first + count ≤ limit) (extra : Bool)
    (allowed : PSTRCommandPrefixes.AllowedSequence full (stageConfiguration used first)
      (pairCommands declaration first count ++ if extra then [.query] else [])) :
    semanticRecords full (stageConfiguration used first)
        (pairCommands declaration first count ++ if extra then [.query] else []) allowed =
      stageRecords full used first count ++ if extra then stageWords full used (first + count) else [] := by
  induction count generalizing first with
  | zero =>
    have hs : first < full.length + 1 := by omega
    cases extra with
    | false =>
      change semanticRecords full (stageConfiguration used first) [] _ = []
      rfl
    | true =>
      have head := (stageWords_spec full used first hs).symm
      have actual := query_step full (stageConfiguration used first) [] allowed
      exact actual.trans ((congrArg₂ List.append head rfl).trans (List.append_nil _))
  | succ count ih =>
    have hs : first < full.length := by omega
    have facts := stageTransition_facts full declaration used ⟨first, hs⟩
      (transitions ⟨first, hs⟩ (by change first < limit; omega))
    have notQuery : declaration first ≠ .query := by
      rcases facts.1 with correct | failed
      · rw [correct]; decide
      · rw [failed]; decide
    have commandsEq : pairCommands declaration first (count + 1) ++ (if extra then [.query] else []) =
        .query :: declaration first :: (pairCommands declaration (first + 1) count ++ if extra then [.query] else []) := by
      rw [pairCommands_cons]
      simp only [List.cons_append, List.nil_append]
    have allowedNew : PSTRCommandPrefixes.AllowedSequence full (stageConfiguration used first)
        (.query :: declaration first :: (pairCommands declaration (first + 1) count ++ if extra then [.query] else [])) :=
      commandsEq ▸ allowed
    refine (semanticRecords_congr full _ _ _ _ rfl commandsEq allowed allowedNew).trans ?_
    have afterQueryAllowed : PSTRCommandPrefixes.AllowedSequence full (stageConfiguration used first)
        (declaration first :: (pairCommands declaration (first + 1) count ++ if extra then [.query] else [])) := by
      exact allowedNew.2
    have beforeAllowed : PSTRCommandPrefixes.AllowedSequence full
        (nextConfiguration q full (stageConfiguration used first) (declaration first))
        (pairCommands declaration (first + 1) count ++ if extra then [.query] else []) :=
      afterQueryAllowed.2
    have restAllowed : PSTRCommandPrefixes.AllowedSequence full (stageConfiguration used (first + 1))
        (pairCommands declaration (first + 1) count ++ if extra then [.query] else []) := by
      have tail := beforeAllowed
      rw [facts.2.2] at tail
      exact tail
    have tail := ih (first + 1) (by omega) restAllowed
    have tailSemantic : semanticRecords full
        (nextConfiguration q full (stageConfiguration used first) (declaration first))
        (pairCommands declaration (first + 1) count ++ if extra then [.query] else []) beforeAllowed =
      stageRecords full used (first + 1) count ++
        if extra then stageWords full used ((first + 1) + count) else [] := by
      simpa only [facts.2.2] using tail
    have hs' : first < full.length + 1 := Nat.lt_succ_of_lt hs
    have head := (stageWords_spec full used first hs').symm
    have query := query_step full (stageConfiguration used first) _ allowedNew
    have declarationRun := declaration_step full (stageConfiguration used first) (declaration first) _ notQuery afterQueryAllowed
    have heq : (first + 1) + count = first + (count + 1) := by omega
    calc
      semanticRecords full (stageConfiguration used first)
          (.query :: declaration first :: (pairCommands declaration (first + 1) count ++ if extra then [.query] else [])) allowedNew = _ := query
      _ = stageWords full used first ++
          semanticRecords full (nextConfiguration q full (stageConfiguration used first) (declaration first))
            (pairCommands declaration (first + 1) count ++ if extra then [.query] else []) beforeAllowed :=
        congrArg₂ List.append head declarationRun
      _ = stageWords full used first ++ (stageRecords full used (first + 1) count ++
          if extra then stageWords full used ((first + 1) + count) else []) :=
        congrArg (stageWords full used first ++ ·) tailSemantic
      _ = _ := by rw [stageRecords_succ, List.append_assoc, heq]

end PaperProofs.Common.Native.PSTRQueryRecords
