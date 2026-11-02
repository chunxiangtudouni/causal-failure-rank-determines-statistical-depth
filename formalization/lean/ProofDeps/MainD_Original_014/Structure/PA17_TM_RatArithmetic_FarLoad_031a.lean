module
public import Structure.PA17_TM_RatArithmetic_Restore_029b
public import Structure.PA17_TM_RatArithmetic_Width_018e

/-! Destination append for the far-field loader. The actual copied bit is
carried by entry20/21 of ONE fixed machine. HALT at the destination guard
prevents the nearest-source return code from entering nonzero source fields.
Original-field routes will consume the separately frozen023 core. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031

def appendMachine : Machine 58 := fun q symbol =>
  if q.val=36 ∧ symbol=false then none else PA17TMRatArithmeticBankCopy024.copyMachine q symbol

def appendTrace (bit : Bool) (left copied : List Bool) : List (MachineState 58) :=
  PA17TMRatArithmeticBankCopy024.workspaceTrace bit left copied

theorem appendTrace_labels (bit : Bool) (left copied : List Bool) (s : MachineState 58)
    (hs : s ∈ appendTrace bit left copied) : 20 ≤ s.q.val ∧ s.q.val ≤ 37 := by
  change s ∈ (PA17TMRatArithmeticCopy006.workspaceRound bit left copied).map
    PA17TMRatArithmeticBankCopy024.oldCfg at hs
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hs
  exact PA17TMRatArithmeticBankCopy024.workspaceRound_labels bit left copied original ho

theorem append_step_eq (s : MachineState 58)
    (h : ¬(s.q.val=36 ∧ s.Tape.head=false)) :
    Turing.TM0.step appendMachine s = Turing.TM0.step PA17TMRatArithmeticBankCopy024.copyMachine s := by
  cases s with
  | mk q tape => simp only [Turing.TM0.step,appendMachine,ite_eq_right h]

theorem old_guard_next (s : MachineState 58) (h : s.q.val=36 ∧ s.Tape.head=false) :
    (Turing.TM0.step PA17TMRatArithmeticBankCopy024.copyMachine s).map (fun t => t.q.val) = some 38 := by
  cases s with
  | mk q tape =>
    have ht : tape.head=false := h.2
    have hq : q=(36 : Fin 59) := Fin.ext h.1
    subst q
    simp [Turing.TM0.step,PA17TMRatArithmeticBankCopy024.copyMachine,
      PA17TMRatArithmeticCopy006.copyMachine,PA17TMRatArithmeticBankCopy024.oldLabel,
      PSTRTMSeq005.leftLabel,ht]

theorem appendTrace_chain (bit : Bool) (left copied : List Bool) :
    (appendTrace bit left copied).IsChain (fun a b => Turing.TM0.step appendMachine a = some b) := by
  apply List.IsChain.imp_of_mem_imp _ (PA17TMRatArithmeticBankCopy024.workspaceTrace_chain bit left copied)
  intro before after _ ha hstep
  by_cases hc : before.q.val=36 ∧ before.Tape.head=false
  · have hq := old_guard_next before hc
    rw [hstep] at hq
    have he : after.q.val=38 := Option.some.inj hq
    have hb := appendTrace_labels bit left copied after ha
    omega
  · simpa only [append_step_eq before hc] using hstep

theorem append_runsFrom (bit : Bool) (left copied : List Bool) :
    PSTRTMSeq005.RunsFrom appendMachine
      (PA17TMRatArithmeticBankCopy024.state
        (PA17TMRatArithmeticBankCopy024.oldLabel (PA17TMRatArithmeticCopy006.workData bit))
        (false::left) (PA17TMRatArithmeticCopy006.workspace copied))
      (appendTrace bit left copied)
      (PA17TMRatArithmeticBankCopy024.state 36 left
        (false::PA17TMRatArithmeticCopy006.workspace (copied ++ [bit]))) := by
  refine ⟨PA17TMRatArithmeticBankCopy024.workspaceTrace_head bit left copied,
    appendTrace_chain bit left copied,PA17TMRatArithmeticBankCopy024.workspaceTrace_last bit left copied,?_⟩
  simp [Turing.TM0.step,appendMachine,PA17TMRatArithmeticBankCopy024.state,Turing.Tape.mk₂]

theorem appendTrace_length (bit : Bool) (left copied : List Bool) :
    (appendTrace bit left copied).length=4*copied.length+14 :=
  PA17TMRatArithmeticBankCopy024.workspaceTrace_length bit left copied

theorem append_prefix_space (bit : Bool) (left copied : List Bool) (prefixLength inputLength : Nat) :
    visitedSpace appendMachine inputLength ((appendTrace bit left copied).take prefixLength) ≤
      inputLength+8*copied.length+29 := by
  have hs := PSTRTMTrace002.visitedSpace_le appendMachine inputLength ((appendTrace bit left copied).take prefixLength)
  have hp : ((appendTrace bit left copied).take prefixLength).length ≤ (appendTrace bit left copied).length := by
    simp only [List.length_take]
    omega
  have ht := appendTrace_length bit left copied
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
