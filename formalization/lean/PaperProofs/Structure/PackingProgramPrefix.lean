module

public import PaperProofs.Structure.PackingMachine

/-!
Appending instructions replaces the old trailing HALT word, while preserving
every fetch strictly inside the old instruction body.  The run lemmas below
only consume this fact before the stated clock; the endpoint may already be
at the old HALT address, but no halted state is restarted.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PackingMachine.ProgramPrefix

open IndexedRAM IndexedClosureRAM AlgorithmClaims

theorem bodyWords_append (left right : List PackingOp) :
    bodyWords (left ++ right) = bodyWords left ++ bodyWords right := by
  simp only [bodyWords, List.flatMap_append]

theorem packingCode_append (left right : List PackingOp) :
    packingCode (left ++ right) = bodyWords left ++ packingCode right := by
  change bodyWords (left ++ right) ++ haltWords.toArray.toList =
    bodyWords left ++ (bodyWords right ++ haltWords.toArray.toList)
  rw [bodyWords_append, List.append_assoc]

theorem natFetch_append_left (left right : List PackingOp) (index : Nat)
    (hindex : index < left.length) :
    natFetch (left ++ right) (5 * index) = natFetch left (5 * index) := by
  rw [natFetch_body (left ++ right) index (by simp only [List.length_append]; omega),
    natFetch_body left index hindex, List.getElem_append_left hindex]

theorem natFetch_append_right (left right : List PackingOp) (index : Nat)
    (hindex : index < right.length) :
    natFetch (left ++ right) (5 * (left.length + index)) =
      natFetch right (5 * index) := by
  rw [natFetch_body (left ++ right) (left.length + index) (by
      simp only [List.length_append]; omega), natFetch_body right index hindex,
    List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem natStep_append_left (rom : PhysicalROM) (left right : List PackingOp)
    (state : NatState) (index : Nat) (hindex : index < left.length)
    (hpc : state.pc = 5 * index) :
    natStep rom (left ++ right) state = natStep rom left state := by
  simp only [natStep, hpc, natFetch_append_left left right index hindex]

/-- Only the old body is fetched before `count`; nothing is required of its endpoint. -/
theorem natRun_append_of_body_prefix (rom : PhysicalROM) (left right : List PackingOp)
    (count : Nat) (state : NatState)
    (hprefix : ∀ clock < count, ∃ index < left.length,
      (natRun rom left clock state).pc = 5 * index) :
    natRun rom (left ++ right) count state = natRun rom left count state := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have hbefore := ih (fun clock hclock =>
      hprefix clock (Nat.lt_trans hclock (Nat.lt_succ_self count)))
    obtain ⟨index, hindex, hpc⟩ := hprefix count (Nat.lt_succ_self count)
    rw [natRun_succ, natRun_succ, hbefore]
    exact natStep_append_left rom left right _ index hindex hpc

theorem natRun_append_of_active_body_prefix (rom : PhysicalROM)
    (left right : List PackingOp) (count : Nat) (state : NatState)
    (hprefix : ∀ clock < count,
      (natRun rom left clock state).halted = false ∧
      ∃ index < left.length, (natRun rom left clock state).pc = 5 * index) :
    natRun rom (left ++ right) count state = natRun rom left count state := by
  exact natRun_append_of_body_prefix rom left right count state
    (fun clock hclock => (hprefix clock hclock).2)

theorem natRun_append_all_prefixes (rom : PhysicalROM) (left right : List PackingOp)
    (count : Nat) (state : NatState)
    (hprefix : ∀ clock < count, ∃ index < left.length,
      (natRun rom left clock state).pc = 5 * index) :
    ∀ clock ≤ count,
      natRun rom (left ++ right) clock state = natRun rom left clock state := by
  intro clock hclock
  exact natRun_append_of_body_prefix rom left right clock state
    (fun earlier hearlier => hprefix earlier (Nat.lt_of_lt_of_le hearlier hclock))

/-- At the old HALT address, an appended nonempty body executes its first instruction.
The original run is still active at this boundary; no HALT step has been taken. -/
theorem natRun_append_first_after_boundary (rom : PhysicalROM)
    (left right : List PackingOp) (count : Nat) (state : NatState)
    (hprefix : ∀ clock < count, ∃ index < left.length,
      (natRun rom left clock state).pc = 5 * index)
    (hpc : (natRun rom left count state).pc = 5 * left.length)
    (hactive : (natRun rom left count state).halted = false)
    (hright : 0 < right.length) :
    natRun rom (left ++ right) (count + 1) state =
      natExecuteOp rom (right[0]'hright) (natRun rom left count state) := by
  rw [natRun_succ, natRun_append_of_body_prefix rom left right count state hprefix]
  rw [natStep_of_index rom (left ++ right) _ left.length (by
    simp only [List.length_append]; omega) hpc hactive]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.sub_self]

end PaperProofs.Structure.LaminarTree.PackingMachine.ProgramPrefix
