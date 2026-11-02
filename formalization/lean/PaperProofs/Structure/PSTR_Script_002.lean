module

public import PaperProofs.Structure.CompactControllerClaims
import Mathlib.Tactic.Ring

/-! Exact causal script accounting. The call assembler below is conditional
on the original single-call specification, and does not construct a machine. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRScript

open AlgorithmClaims CompactControllerClaims

theorem failed_script_nil {q : Nat} {full : List (Finset (Fin q))}
    {configuration : Configuration q} {commands : List Command}
    (script : StageScript q full configuration commands) (hf : configuration.failed = true) :
    commands = [] := by
  cases script with
  | «prefix» => rfl
  | stage configuration declaration later hd ha _ =>
    rcases hd with rfl | rfl <;> simp only [Allowed] at ha <;> simp [hf] at ha

theorem script_length {q : Nat} {full : List (Finset (Fin q))}
    {configuration : Configuration q} {commands : List Command}
    (script : StageScript q full configuration commands) :
    commands.length ≤ 2 * (full.length - configuration.stage) := by
  induction script with
  | «prefix» => simp
  | stage configuration declaration later hd ha continuation ih =>
    have hlt : configuration.stage < full.length := by
      rcases hd with rfl | rfl <;> exact ha.2
    have hlt' : configuration.stage < full.length + 1 := by omega
    rcases hd with rfl | rfl
    · simp only [nextConfiguration] at ih
      simp only [List.length_cons]
      omega
    · cases ht : (callback q full ⟨configuration.stage, hlt'⟩ configuration.used).tool with
      | none =>
        have hn := failed_script_nil continuation
          (show (nextConfiguration q full configuration .error).failed = true by
            simp only [nextConfiguration, hlt', ↓reduceDIte, ht])
        simp only [hn, List.length_cons, List.length_nil]
        omega
      | some tool =>
        simp only [nextConfiguration, hlt', ↓reduceDIte, ht] at ih
        simp only [List.length_cons]
        omega

theorem script_query_allowed {q : Nat} {full : List (Finset (Fin q))}
    (configuration : Configuration q) (declaration : Command)
    (hd : declaration = .correct ∨ declaration = .error)
    (ha : Allowed full configuration declaration) : Allowed full configuration .query := by
  rcases hd with rfl | rfl <;> exact ⟨ha.1, Nat.le_of_lt ha.2⟩

theorem commands_of_calls {bits q constant capWords heapWords : Nat}
    (full : List (Finset (Fin q))) (program : List PackingOp)
    (calls : ∀ (configuration : Configuration q) (heap : BitVec bits → BitVec bits),
      HeapRepresents q full capWords configuration heap →
      ∀ command : Command, Allowed full configuration command →
      ∃ steps : Nat, CallClaims constant q full capWords heapWords program configuration command steps heap)
    (configuration : Configuration q) (commands : List Command)
    (script : StageScript q full configuration commands)
    (heap : BitVec bits → BitVec bits) (rep : HeapRepresents q full capWords configuration heap) :
    ∃ counts : List Nat,
      counts.length = commands.length ∧
      CommandsRunClaims constant q full capWords heapWords program configuration commands counts heap ∧
      commandsCost q full program commands counts heap ≤
        constant * commands.length * liveWork q (treeSize q full) := by
  induction script generalizing heap with
  | «prefix» => exact ⟨[], rfl, trivial, by simp [commandsCost]⟩
  | stage configuration declaration later hd ha continuation ih =>
    have hq := script_query_allowed configuration declaration hd ha
    obtain ⟨querySteps, queryCall⟩ := calls configuration heap rep .query hq
    let queryHeap := (packingRun (callInput q full .query) program querySteps (packingInitial heap)).heap
    have queryRep : HeapRepresents q full capWords configuration queryHeap := queryCall.2.2.1
    obtain ⟨declSteps, declCall⟩ := calls configuration queryHeap queryRep declaration ha
    let declHeap := (packingRun (callInput q full declaration) program declSteps (packingInitial queryHeap)).heap
    have declRep : HeapRepresents q full capWords
        (nextConfiguration q full configuration declaration) declHeap := declCall.2.2.1
    obtain ⟨counts, hlen, hrun, hcost⟩ := ih declHeap declRep
    refine ⟨querySteps :: declSteps :: counts, ?_, ?_, ?_⟩
    · simpa only [List.length_cons] using congrArg (· + 2) hlen
    · exact ⟨hq, queryCall, ha, declCall, hrun⟩
    · change callCost q full program .query querySteps heap +
        (callCost q full program declaration declSteps queryHeap +
          commandsCost q full program later counts declHeap) ≤ _
      have hbq := queryCall.2.1
      have hbd := declCall.2.1
      simp only [List.length_cons]
      calc
        _ ≤ constant * liveWork q (treeSize q full) +
            (constant * liveWork q (treeSize q full) +
              constant * later.length * liveWork q (treeSize q full)) :=
          Nat.add_le_add hbq (Nat.add_le_add hbd hcost)
        _ = _ := by ring

theorem commands_original_bound {bits q constant capWords heapWords : Nat}
    (full : List (Finset (Fin q))) (program : List PackingOp)
    (calls : ∀ (configuration : Configuration q) (heap : BitVec bits → BitVec bits),
      HeapRepresents q full capWords configuration heap →
      ∀ command : Command, Allowed full configuration command →
      ∃ steps : Nat, CallClaims constant q full capWords heapWords program configuration command steps heap)
    (initialUsed : Finset (Fin q)) (commands : List Command)
    (script : StageScript q full ⟨0, initialUsed, false⟩ commands)
    (heap : BitVec bits → BitVec bits)
    (rep : HeapRepresents q full capWords ⟨0, initialUsed, false⟩ heap) :
    ∃ counts : List Nat,
      counts.length = commands.length ∧
      CommandsRunClaims constant q full capWords heapWords program
        ⟨0, initialUsed, false⟩ commands counts heap ∧
      commandsCost q full program commands counts heap ≤
        2 * constant * full.length * liveWork q (treeSize q full) := by
  obtain ⟨counts, hlen, hrun, hcost⟩ := commands_of_calls full program calls _ commands script heap rep
  refine ⟨counts, hlen, hrun, hcost.trans ?_⟩
  have hs := script_length script
  simp only [Nat.sub_zero] at hs
  calc
    constant * commands.length * liveWork q (treeSize q full) ≤
        constant * (2 * full.length) * liveWork q (treeSize q full) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hs)
    _ = _ := by ring

end PaperProofs.Structure.LaminarTree.PSTRScript
