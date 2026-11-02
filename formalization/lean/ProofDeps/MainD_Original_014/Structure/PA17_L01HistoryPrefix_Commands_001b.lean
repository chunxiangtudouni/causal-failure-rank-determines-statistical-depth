module

public import Structure.PA17_L01HistoryPrefix_Commands_001a
public import Structure.PSTR_CommandPrefixes_054

/-! Pure stage/used alignment for the ORIGINAL command grammar. The explicit
correct/error transition facts must come from the actual TABLE history; they
are not an added native eligibility condition or an AllowedSequence oracle. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17L01HistoryPrefixCommands001

open CompactControllerClaims
open PaperProofs.Common PaperProofs.Common.Native

def stageConfiguration {q : Nat} (used : Nat → Finset (Fin q)) (stage : Nat) : Configuration q :=
  ⟨stage, used stage, false⟩

def StageTransition {q : Nat} (full : List (Finset (Fin q))) (declaration : Nat → Command)
    (used : Nat → Finset (Fin q)) (stage : Fin full.length) : Prop :=
  (declaration stage.val = .correct ∧ used (stage.val + 1) = used stage.val) ∨
    ∃ tool, declaration stage.val = .error ∧
      (callback q full ⟨stage.val, Nat.lt_succ_of_lt stage.isLt⟩ (used stage.val)).tool = some tool ∧
      used (stage.val + 1) = insert tool (used stage.val)

def StageTransitions {q : Nat} (full : List (Finset (Fin q))) (declaration : Nat → Command)
    (used : Nat → Finset (Fin q)) (count : Nat) : Prop :=
  ∀ stage : Fin full.length, stage.val < count → StageTransition full declaration used stage

theorem stageTransition_facts {q : Nat} (full : List (Finset (Fin q))) (declaration : Nat → Command)
    (used : Nat → Finset (Fin q)) (stage : Fin full.length)
    (transition : StageTransition full declaration used stage) :
    (declaration stage.val = .correct ∨ declaration stage.val = .error) ∧
      Allowed full (stageConfiguration used stage.val) (declaration stage.val) ∧
      nextConfiguration q full (stageConfiguration used stage.val) (declaration stage.val) =
        stageConfiguration used (stage.val + 1) := by
  have hstage : stage.val < full.length + 1 := by omega
  rcases transition with ⟨hd, hu⟩ | ⟨tool, hd, ht, hu⟩
  · refine ⟨Or.inl hd, ?_, ?_⟩
    · rw [hd]
      exact ⟨rfl, stage.isLt⟩
    · simp only [stageConfiguration, hd, nextConfiguration, hu]
  · refine ⟨Or.inr hd, ?_, ?_⟩
    · rw [hd]
      exact ⟨rfl, stage.isLt⟩
    · simp only [stageConfiguration, hd, nextConfiguration, hstage, ↓reduceDIte, ht, hu]

theorem pairCommands_stageScript {q : Nat} (full : List (Finset (Fin q)))
    (declaration : Nat → Command) (used : Nat → Finset (Fin q)) (limit : Nat)
    (hlimit : limit ≤ full.length) (transitions : StageTransitions full declaration used limit)
    (first count : Nat) (hcount : first + count ≤ limit) :
    StageScript q full (stageConfiguration used first) (pairCommands declaration first count) := by
  induction count generalizing first with
  | zero => exact StageScript.«prefix» _
  | succ count ih =>
    have hs : first < full.length := by omega
    have facts := stageTransition_facts full declaration used ⟨first, hs⟩
      (transitions ⟨first, hs⟩ (by change first < limit; omega))
    rw [pairCommands_cons]
    change StageScript q full (stageConfiguration used first)
      (.query :: declaration first :: pairCommands declaration (first + 1) count)
    refine StageScript.stage _ _ _ facts.1 facts.2.1 ?_
    rw [facts.2.2]
    exact ih (first + 1) (by omega)

theorem pairCommands_fold {q : Nat} (full : List (Finset (Fin q)))
    (declaration : Nat → Command) (used : Nat → Finset (Fin q)) (limit : Nat)
    (hlimit : limit ≤ full.length) (transitions : StageTransitions full declaration used limit)
    (first count : Nat) (hcount : first + count ≤ limit) :
    (pairCommands declaration first count).foldl (nextConfiguration q full) (stageConfiguration used first) =
      stageConfiguration used (first + count) := by
  induction count generalizing first with
  | zero => simp only [pairCommands_zero, List.foldl_nil, Nat.add_zero]
  | succ count ih =>
    have hs : first < full.length := by omega
    have facts := stageTransition_facts full declaration used ⟨first, hs⟩
      (transitions ⟨first, hs⟩ (by change first < limit; omega))
    rw [pairCommands_cons, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [show nextConfiguration q full (stageConfiguration used first) .query = stageConfiguration used first from rfl,
      facts.2.2]
    rw [show first + (count + 1) = (first + 1) + count by omega]
    exact ih (first + 1) (by omega)

theorem allowedSequence_append {q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (left right : List Command)
    (hleft : PSTRCommandPrefixes.AllowedSequence full configuration left)
    (hright : PSTRCommandPrefixes.AllowedSequence full
      (left.foldl (nextConfiguration q full) configuration) right) :
    PSTRCommandPrefixes.AllowedSequence full configuration (left ++ right) := by
  induction left generalizing configuration with
  | nil => exact hright
  | cons command left ih =>
    exact ⟨hleft.1, ih _ hleft.2 hright⟩

theorem commandsAt_stage_data {I : Instance} (history : List (VisibleEvent I))
    (used : Nat → Finset I.Tool)
    (transitions : StageTransitions I.compatibility (declarationAt history) used
      (min (historyCursor history) I.stageCount)) :
    let count := min (historyCursor history) I.stageCount
    StageScript I.toolCount I.compatibility (stageConfiguration used 0)
      (pairCommands (declarationAt history) 0 count) ∧
      PSTRCommandPrefixes.AllowedSequence I.compatibility (stageConfiguration used 0)
        (CompactPrice.commandsAt I history) ∧
      (CompactPrice.commandsAt I history).foldl (nextConfiguration I.toolCount I.compatibility)
        (stageConfiguration used 0) = stageConfiguration used count := by
  let count := min (historyCursor history) I.stageCount
  have hfull : I.compatibility.length = I.stageCount := rfl
  have hcount : count ≤ I.compatibility.length := by rw [hfull]; exact Nat.min_le_right _ _
  have script := pairCommands_stageScript I.compatibility (declarationAt history) used count hcount transitions 0 count (by omega)
  have folded := pairCommands_fold I.compatibility (declarationAt history) used count hcount transitions 0 count (by omega)
  simp only [Nat.zero_add] at folded
  have pairedAllowed := PSTRCommandPrefixes.stageScript_allowed I.compatibility _ _ script
  refine ⟨script, ?_, ?_⟩
  · rw [commandsAt_eq_pairs]
    apply allowedSequence_append I.compatibility _ _ _ pairedAllowed
    rw [folded]
    by_cases hcurrent : historyCursor history < I.stageCount
    · rw [ite_eq_left hcurrent]
      refine ⟨?_, trivial⟩
      exact ⟨rfl, by change count ≤ I.compatibility.length; exact hcount⟩
    · rw [ite_eq_right hcurrent]
      trivial
  · rw [commandsAt_eq_pairs, List.foldl_append, folded]
    split_ifs <;> simp only [List.foldl_cons, List.foldl_nil, nextConfiguration, count]

end PaperProofs.Structure.LaminarTree.PA17L01HistoryPrefixCommands001
