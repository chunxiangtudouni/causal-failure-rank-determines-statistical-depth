module

public import Common.PSTR_SYM_RatExportRun_094

/-! SAME093/094 paths, charging both arbitrary old tails and all16 stacks.
Every boundary preserves C and all stacks outside1/7/15, including13/14.
All actual syntax nodes and scanner actions have finite workspace clocks. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRatExport

open Turing PaperProofs.Common.Native.PSTRWordVM PaperProofs.Common.Native.PSTRWordBool
open PSTRSymbolicNaturalExport PSTRTMRawNat010

theorem flagged_length (digits : List Bool) : (leftBlocks digits).length = 2*digits.length := by
  induction digits with
  | nil => rfl
  | cons digit later ih =>
    simp only [leftBlocks,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *
    omega

theorem restore_resources {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) :
    ∀ current ∈ restoreTrace context bit flag mode cells left scratch target background,
      Bounded context background (left.length+2*cells.length+scratch.length+target.length+1) current := by
  intro current present
  obtain ⟨old,member,rfl⟩ := List.mem_map.mp present
  exact PSTRSymbolicNaturalExport.restore_resources context bit flag mode cells left scratch target background old member

theorem numerator_resources {C : Type*} (context : C) (bit flag mode negative : Bool)
    (digits cells left scratch target : List Bool) (background : Slot → List Bool) :
    ∀ current ∈ numeratorTrace context bit flag mode negative digits cells left scratch target background,
      Bounded context background (left.length+scratch.length+target.length+2*cells.length+6*digits.length+7) current := by
  induction digits generalizing bit flag cells target with
  | nil =>
    intro current present
    rcases List.mem_cons.mp present with same | remaining
    · subst current
      apply state_bounded
      simp only [List.length_append,List.length_cons,List.length_nil,backups_length]
      omega
    · apply bounded_mono context background _ _ current
        (restore_resources context negative false mode (negative :: false :: cells) left scratch
          (true :: negative :: target) background current remaining)
      simp only [List.length_cons,List.length_nil]
      omega
  | cons digit later ih =>
    intro current present
    rcases List.mem_cons.mp present with same | remaining
    · subst current
      apply state_bounded
      simp only [List.length_append,List.length_cons,backups_length,flagged_length]
      omega
    · apply bounded_mono context background _ _ current
        (ih digit true (digit :: true :: cells) (true :: digit :: target) current remaining)
      simp only [List.length_cons]
      omega

theorem denominator_resources {C : Type*} (context : C) (bit flag mode negative : Bool)
    (digits numerator cells left scratch target : List Bool) (background : Slot → List Bool) :
    ∀ current ∈ denominatorTrace context bit flag mode negative digits numerator cells left scratch target background,
      Bounded context background
        (left.length+scratch.length+target.length+2*cells.length+6*(digits.length+numerator.length)+11) current := by
  induction digits generalizing bit flag cells target with
  | nil =>
    intro current present
    rcases List.mem_cons.mp present with same | remaining
    · subst current
      apply state_bounded
      simp only [List.length_append,List.length_cons,List.length_nil,backups_length,flagged_length]
      omega
    · apply bounded_mono context background _ _ current
        (numerator_resources context bit false mode negative numerator (false :: cells) left scratch
          (false :: false :: target) background current remaining)
      simp only [List.length_cons,List.length_nil]
      omega
  | cons digit later ih =>
    intro current present
    rcases List.mem_cons.mp present with same | remaining
    · subst current
      apply state_bounded
      simp only [List.length_append,List.length_cons,backups_length,flagged_length]
      omega
    · apply bounded_mono context background _ _ current
        (ih digit true (digit :: true :: cells) (true :: digit :: target) current remaining)
      simp only [List.length_cons]
      omega

theorem rat_resources {C : Type*} (context : C) (bit flag mode negative : Bool)
    (numerator denominator left scratch target : List Bool) (background : Slot → List Bool) :
    ∀ current ∈ ratTrace context bit flag mode negative numerator denominator left scratch target background,
      Bounded context background
        (left.length+scratch.length+target.length+6*(numerator.length+denominator.length)+15) current := by
  intro current present
  rcases List.mem_cons.mp present with same | remaining
  · subst current
    apply state_bounded
    simp only [archive,List.length_append,List.length_cons,flagged_length]
    omega
  · apply bounded_mono context background _ _ current
      (denominator_resources context false flag mode negative denominator numerator [false] left scratch
        (false :: false :: target) background current remaining)
    simp only [List.length_cons,List.length_nil]
    omega

theorem rat_pushes {C : Type*} (label : Label) : AuxWorkspace.pushes (ratProgram (C := C) label) ≤ 7 := by
  fin_cases label <;>
    dsimp [ratProgram,fieldBody,LabelMap.statement,AuxWorkspace.pushes,PSTRSymbolicNaturalExport.program] <;> decide

theorem rat_actions {C : Type*} (label : Label) : ScannerClock.actions (ratProgram (C := C) label) ≤ 9 := by
  fin_cases label <;>
    dsimp [ratProgram,fieldBody,LabelMap.statement,ScannerClock.actions,PSTRSymbolicNaturalExport.program] <;> decide

theorem rat_node_resources {C : Type*} (label : Label) (memory : Memory C) (bank : Slot → List Bool)
    (bound : Nat) (mass : VirtualReturn.occupiedSlots bank ≤ bound) :
    (∀ node ∈ AuxWorkspace.nodes (ratProgram label) memory bank,
      VirtualReturn.occupiedSlots node.2 ≤ 16*(bound+7)) ∧
    ScannerStatement.clock (ratProgram label) memory bank ≤ 18*(bound+8) := by
  have bounded : ∀ slot, (bank slot).length ≤ bound := fun slot => (slot_mass bank slot).trans mass
  constructor
  · intro node present
    have perSlot := AuxWorkspace.node_bound (ratProgram label) memory bank bound bounded node present
    have cap := rat_pushes (C := C) label
    have s0 := perSlot 0; have s1 := perSlot 1; have s2 := perSlot 2; have s3 := perSlot 3
    have s4 := perSlot 4; have s5 := perSlot 5; have s6 := perSlot 6; have s7 := perSlot 7
    have s8 := perSlot 8; have s9 := perSlot 9; have s10 := perSlot 10; have s11 := perSlot 11
    have s12 := perSlot 12; have s13 := perSlot 13; have s14 := perSlot 14; have s15 := perSlot 15
    simp only [VirtualReturn.occupiedSlots]
    omega
  · have clock := ScannerClock.clock_bound (ratProgram label) memory bank bound bounded
    have actions := rat_actions (C := C) label
    have pushes := rat_pushes (C := C) label
    have first := Nat.mul_le_mul_right (bound+AuxWorkspace.pushes (ratProgram (C := C) label)+1)
      (Nat.mul_le_mul_left 2 actions)
    have second := Nat.mul_le_mul_left 18
      (show bound+AuxWorkspace.pushes (ratProgram (C := C) label)+1 ≤ bound+8 by omega)
    exact clock.trans (first.trans second)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRatExport
