module

public import Structure.PSTR_LiveControllerCalls_139
public import Structure.PSTR_CommandPrefixes_054

/-! Original stage-script and causal-prefix costs reuse the mature actual
call composer. One final count list is shared by all actual prefixes. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRLiveController

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PA17A19RuntimeEntry020 PSTRCommandPrefixes

theorem original_calls {q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full) :
    ∀ (configuration : Configuration q) (heap : BitVec (wordBits full) → BitVec (wordBits full)),
      HeapRepresents q full (capacity full) configuration heap →
      ∀ command : Command, Allowed full configuration command →
      ∃ steps : Nat, CallClaims 32768 q full (capacity full) (allocatedWords full)
        PSTRLiveControllerCode.program configuration command steps heap := by
  intro configuration heap rep command allowed
  obtain ⟨steps, _upper, call⟩ := actual_call full configuration command allowed hl heap rep
  exact ⟨steps, call⟩

theorem actual_script {q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (initialUsed : Finset (Fin q)) (commands : List Command)
    (script : StageScript q full ⟨0, initialUsed, false⟩ commands)
    (heap : BitVec (wordBits full) → BitVec (wordBits full))
    (rep : HeapRepresents q full (capacity full) ⟨0, initialUsed, false⟩ heap) :
    ∃ counts : List Nat,
      counts.length = commands.length ∧
      CommandsRunClaims 32768 q full (capacity full) (allocatedWords full) PSTRLiveControllerCode.program
        ⟨0, initialUsed, false⟩ commands counts heap ∧
      commandsCost q full PSTRLiveControllerCode.program commands counts heap ≤
        2 * 32768 * full.length * liveWork q (treeSize q full) :=
  PSTRScript.commands_original_bound full PSTRLiveControllerCode.program (original_calls full hl)
    initialUsed commands script heap rep

theorem actual_allowed_prefixes {q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (configuration : Configuration q) (commands : List Command)
    (allowed : AllowedSequence full configuration commands)
    (heap : BitVec (wordBits full) → BitVec (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration heap) :
    ∃ counts : List Nat,
      counts.length = commands.length ∧
      CommandsRunClaims 32768 q full (capacity full) (allocatedWords full) PSTRLiveControllerCode.program
        configuration commands counts heap ∧
      commandsCost q full PSTRLiveControllerCode.program commands counts heap ≤
        32768 * commands.length * liveWork q (treeSize q full) ∧
      ∀ current : List Command, current.IsPrefix commands →
        CommandsRunClaims 32768 q full (capacity full) (allocatedWords full) PSTRLiveControllerCode.program
          configuration current (counts.take current.length) heap :=
  calls_for_all_prefixes full PSTRLiveControllerCode.program (original_calls full hl)
    configuration commands allowed heap rep

theorem actual_bounded_prefixes {q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (configuration : Configuration q) (commands : List Command)
    (allowed : AllowedSequence full configuration commands) (length : commands.length ≤ 2 * full.length + 1)
    (heap : BitVec (wordBits full) → BitVec (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration heap) :
    ∃ counts : List Nat,
      counts.length = commands.length ∧
      CommandsRunClaims 65536 q full (capacity full) (allocatedWords full) PSTRLiveControllerCode.program
        configuration commands counts heap ∧
      commandsCost q full PSTRLiveControllerCode.program commands counts heap ≤
        65536 * (full.length + 1) * liveWork q (treeSize q full) ∧
      ∀ current : List Command, current.IsPrefix commands →
        CommandsRunClaims 65536 q full (capacity full) (allocatedWords full) PSTRLiveControllerCode.program
          configuration current (counts.take current.length) heap :=
  bounded_commands full PSTRLiveControllerCode.program (original_calls full hl)
    configuration commands allowed length (by decide : 2 * 32768 ≤ 65536) heap rep

end PaperProofs.Structure.LaminarTree.PSTRLiveController
