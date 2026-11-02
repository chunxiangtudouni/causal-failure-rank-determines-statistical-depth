module

public import Common.PSTR_ST_CommandBounds_044
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Range

/-! Pure structure of the ORIGINAL commandsAt. Completed stages contribute
query/declaration pairs; an unadvanced current stage contributes one query,
including an abandoned current stage. No claim of native-history legality. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17L01HistoryPrefixCommands001

open CompactControllerClaims
open PaperProofs.Common PaperProofs.Common.Native

variable {I : Instance}

theorem declaration_cases (history : List (VisibleEvent I)) (stage : I.Stage) :
    CompactPrice.declaration history stage = .correct ∨ CompactPrice.declaration history stage = .error := by
  cases hw : historyWrite history stage with
  | none => simp only [CompactPrice.declaration, hw, true_or]
  | some written =>
    cases hr : historyReport history stage with
    | none => simp only [CompactPrice.declaration, hw, hr, true_or]
    | some reported =>
      rcases written with ⟨bit, serial⟩
      rcases reported with ⟨truth, reportedSerial⟩
      by_cases heq : bit = truth <;> simp only [CompactPrice.declaration, hw, hr, heq, ite_true, ite_false, true_or, or_true]

def declarationAt (history : List (VisibleEvent I)) (stage : Nat) : Command :=
  if h : stage < I.stageCount then CompactPrice.declaration history ⟨stage, h⟩ else .correct

theorem declarationAt_lt (history : List (VisibleEvent I)) (stage : Nat) (hs : stage < I.stageCount) :
    declarationAt history stage = CompactPrice.declaration history ⟨stage, hs⟩ := by
  simp only [declarationAt, hs, ↓reduceDIte]

def pairCommands (declaration : Nat → Command) (first count : Nat) : List Command :=
  (List.range' first count).flatMap (fun stage => [.query, declaration stage])

theorem pairCommands_zero (declaration : Nat → Command) (first : Nat) :
    pairCommands declaration first 0 = [] := rfl

theorem pairCommands_cons (declaration : Nat → Command) (first count : Nat) :
    pairCommands declaration first (count + 1) =
      [.query, declaration first] ++ pairCommands declaration (first + 1) count := by
  simp only [pairCommands, List.range'_succ, List.flatMap_cons]

theorem pairCommands_append (declaration : Nat → Command) (first left right : Nat) :
    pairCommands declaration first (left + right) =
      pairCommands declaration first left ++ pairCommands declaration (first + left) right := by
  unfold pairCommands
  rw [← List.range'_append_1, List.flatMap_append]

theorem pairCommands_length (declaration : Nat → Command) (first count : Nat) :
    (pairCommands declaration first count).length = 2 * count := by
  simp [pairCommands, List.length_flatMap, Nat.mul_comm]

theorem pairCommands_congr (left right : Nat → Command) (first count : Nat)
    (heq : ∀ stage, first ≤ stage → stage < first + count → left stage = right stage) :
    pairCommands left first count = pairCommands right first count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
    rw [pairCommands_cons, pairCommands_cons, heq first (by omega) (by omega)]
    apply congrArg ([Command.query, right first] ++ ·)
    apply ih
    intro stage hl hr
    exact heq stage (by omega) (by omega)

private theorem map_val_finRange (count : Nat) :
    (List.finRange count).map Fin.val = List.range count := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp

theorem commandsAt_eq_pairs (history : List (VisibleEvent I)) :
    CompactPrice.commandsAt I history =
      pairCommands (declarationAt history) 0 (min (historyCursor history) I.stageCount) ++
        if historyCursor history < I.stageCount then [.query] else [] := by
  let count := min (historyCursor history) I.stageCount
  unfold CompactPrice.commandsAt
  apply congrArg (fun commands : List Command => commands ++ if historyCursor history < I.stageCount then [Command.query] else [])
  have hfunction : (fun stage : Fin count =>
      [Command.query, CompactPrice.declaration history
        ⟨stage.val, lt_of_lt_of_le stage.isLt (min_le_right _ _)⟩]) =
      (fun stage : Fin count => [Command.query, declarationAt history stage.val]) := by
    funext stage
    rw [declarationAt_lt history stage.val (stage.isLt.trans_le (Nat.min_le_right _ _))]
  rw [hfunction]
  have mapped := congrArg (fun stages : List Nat =>
    stages.flatMap (fun stage => [Command.query, declarationAt history stage])) (map_val_finRange count)
  simpa only [List.flatMap_map, Function.comp_def, List.range_eq_range', pairCommands] using mapped

theorem commandsAt_zero_stages (history : List (VisibleEvent I)) (hN : I.stageCount = 0) :
    CompactPrice.commandsAt I history = [] := by
  rw [commandsAt_eq_pairs]
  simp only [hN, Nat.min_zero, pairCommands_zero, Nat.not_lt_zero, ite_false, List.append_nil]

theorem commandsAt_prefix (earlier later : List (VisibleEvent I))
    (hbound : historyCursor later ≤ I.stageCount)
    (hmono : historyCursor earlier ≤ historyCursor later)
    (hdeclaration : ∀ stage : I.Stage, stage.val < historyCursor earlier →
      CompactPrice.declaration earlier stage = CompactPrice.declaration later stage) :
    (CompactPrice.commandsAt I earlier).IsPrefix (CompactPrice.commandsAt I later) := by
  let first := historyCursor earlier
  let last := historyCursor later
  let left := declarationAt earlier
  let right := declarationAt later
  have hfirst : historyCursor earlier ≤ I.stageCount := hmono.trans hbound
  rw [commandsAt_eq_pairs, commandsAt_eq_pairs, Nat.min_eq_left hfirst, Nat.min_eq_left hbound]
  have hpairs : pairCommands left 0 first = pairCommands right 0 first := by
    apply pairCommands_congr
    intro stage _ hs
    have hsN : stage < I.stageCount := lt_of_lt_of_le (by simpa only [Nat.zero_add] using hs) hfirst
    dsimp only [left, right]
    rw [declarationAt_lt earlier stage hsN, declarationAt_lt later stage hsN]
    exact hdeclaration ⟨stage, hsN⟩ (by simpa only [Nat.zero_add] using hs)
  change (pairCommands left 0 first ++ if first < I.stageCount then [Command.query] else []).IsPrefix
    (pairCommands right 0 last ++ if last < I.stageCount then [Command.query] else [])
  rw [hpairs]
  by_cases heq : first = last
  · refine ⟨[], ?_⟩
    simp only [heq, List.append_nil]
  · have hlt : first < last := by change first ≤ last at hmono; omega
    have hfirstN : first < I.stageCount := hlt.trans_le hbound
    let extra := last - first - 1
    have hlast : last = first + (extra + 1) := by dsimp only [extra]; omega
    have hsplit : pairCommands right 0 last = pairCommands right 0 first ++
        ([.query, right first] ++ pairCommands right (first + 1) extra) := by
      rw [hlast, pairCommands_append, Nat.zero_add, pairCommands_cons]
    rw [ite_eq_left hfirstN, hsplit]
    refine ⟨[right first] ++ pairCommands right (first + 1) extra ++
      (if last < I.stageCount then [.query] else []), ?_⟩
    simp only [List.append_assoc, List.cons_append, List.nil_append]

end PaperProofs.Structure.LaminarTree.PA17L01HistoryPrefixCommands001
