module

public import Common.PSTR_SYM_NaturalExportRun_087
public import Common.PSTR_SYM_DualStackResources_083

/-! The SAME086 paths have explicit boundary and every-statement-node
workspace bounds. Arbitrary old tails and all untouched stacks are charged.
The syntax-derived scanner clock also bounds actual stack operations. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport

open Turing PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM

def outside (background : Slot → List Bool) : Nat :=
  VirtualReturn.occupiedSlots (slots [] [] [] background)

theorem occupied_slots (left scratch target : List Bool) (background : Slot → List Bool) :
    VirtualReturn.occupiedSlots (slots left scratch target background) =
      outside background + left.length + scratch.length + target.length := by
  unfold outside VirtualReturn.occupiedSlots slots
  dsimp
  omega

def Bounded {C : Type*} (context : C) (background : Slot → List Bool) (bound : Nat)
    (current : State C) : Prop :=
  current.var.1 = context ∧
    (∀ slot, slot ≠ 1 → slot ≠ 7 → slot ≠ 15 → current.stk slot = background slot) ∧
    VirtualReturn.occupiedSlots current.stk ≤ outside background + bound

theorem state_bounded {C : Type*} (context : C) (bit flag mode : Bool) (label : Option Label)
    (left scratch target : List Bool) (background : Slot → List Bool) (bound : Nat)
    (mass : left.length + scratch.length + target.length ≤ bound) :
    Bounded context background bound (state label (context,(bit,flag,mode)) left scratch target background) := by
  refine ⟨rfl,fun slot notLeft notScratch notTarget => slots_frame left scratch target background
    slot notLeft notScratch notTarget,?_⟩
  change VirtualReturn.occupiedSlots (slots left scratch target background) ≤ _
  rw [occupied_slots]
  omega

theorem bounded_mono {C : Type*} (context : C) (background : Slot → List Bool)
    (first second : Nat) (current : State C) (bounded : Bounded context background first current)
    (less : first ≤ second) : Bounded context background second current := by
  exact ⟨bounded.1,bounded.2.1,bounded.2.2.trans (Nat.add_le_add_left less _)⟩

theorem restore_resources {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch target : List Bool) (background : Slot → List Bool) :
    ∀ current ∈ restoreTrace context bit flag mode cells left scratch target background,
      Bounded context background
        (left.length + 2*cells.length + scratch.length + target.length + 1) current := by
  induction cells generalizing bit flag left with
  | nil =>
    intro current present
    rcases List.mem_cons.mp present with first | later
    · subst current
      apply state_bounded
      simp only [List.length_cons,List.length_nil]
      omega
    · have same := List.mem_singleton.mp later
      subst current
      apply state_bounded
      simp only [List.length_nil]
      omega
  | cons cell later ih =>
    intro current present
    rcases List.mem_cons.mp present with first | remaining
    · subst current
      apply state_bounded
      simp only [List.length_append,backups_length,List.length_cons]
      omega
    · apply bounded_mono context background _ _ current (ih cell false (cell :: left) current remaining)
      simp only [List.length_cons]
      omega

theorem loop_resources {C : Type*} (context : C) (bit flag : Bool)
    (digits cells left scratch target : List Bool) (background : Slot → List Bool) :
    ∀ current ∈ loopTrace context bit flag digits cells left scratch target background,
      Bounded context background
        (left.length + scratch.length + target.length + 2*cells.length + 6*digits.length + 3) current := by
  induction digits generalizing bit flag cells target with
  | nil =>
    intro current present
    rcases List.mem_cons.mp present with first | remaining
    · subst current
      apply state_bounded
      simp only [List.length_append,backups_length,List.length_cons,List.length_nil]
      omega
    · apply bounded_mono context background _ _ current
        (restore_resources context false true true cells (false :: true :: left) scratch target background current remaining)
      simp only [List.length_cons,List.length_nil]
      omega
  | cons digit later ih =>
    intro current present
    rcases List.mem_cons.mp present with first | remaining
    · subst current
      apply state_bounded
      simp only [List.length_append,backups_length,lane_length,List.length_cons]
      omega
    · apply bounded_mono context background _ _ current
        (ih digit false (false :: digit :: cells) (true :: digit :: target) current remaining)
      simp only [List.length_cons]
      omega

theorem positive_resources {C : Type*} (context : C) (bit flag mode : Bool)
    (digits left scratch target : List Bool) (background : Slot → List Bool) :
    ∀ current ∈ positiveTrace context bit flag mode digits left scratch target background,
      Bounded context background (left.length + scratch.length + target.length + 6*digits.length + 9) current := by
  intro current present
  rcases List.mem_cons.mp present with first | remaining
  · subst current
    apply state_bounded
    simp only [List.length_append,lane_length,List.length_cons]
    omega
  · apply bounded_mono context background _ _ current
      (loop_resources context false flag digits [true,false] left scratch (false :: false :: target) background current remaining)
    simp only [List.length_cons,List.length_nil]
    omega

theorem zero_resources {C : Type*} (context : C) (bit flag mode : Bool)
    (left scratch target : List Bool) (background : Slot → List Bool) :
    ∀ current ∈ zeroTrace context bit flag mode left scratch target background,
      Bounded context background (left.length + scratch.length + target.length + 7) current := by
  intro current present
  rcases List.mem_cons.mp present with first | remaining
  · subst current
    apply state_bounded
    simp only [List.length_cons]
    omega
  · apply bounded_mono context background _ _ current
      (restore_resources context false flag false [false,false] left scratch (false :: false :: target) background current remaining)
    simp only [List.length_cons,List.length_nil]
    omega

theorem source_pushes {C : Type*} (label : Label) :
    AuxWorkspace.pushes (program (C := C) label) ≤ 7 := by
  fin_cases label <;> simp [program,AuxWorkspace.pushes]

theorem source_actions {C : Type*} (label : Label) :
    ScannerClock.actions (program (C := C) label) ≤ 9 := by
  fin_cases label <;> simp [program,ScannerClock.actions]

theorem slot_mass (bank : Slot → List Bool) (slot : Slot) :
    (bank slot).length ≤ VirtualReturn.occupiedSlots bank := by
  unfold VirtualReturn.occupiedSlots
  fin_cases slot <;> dsimp <;> omega

theorem node_resources {C : Type*} (label : Label) (memory : Memory C) (bank : Slot → List Bool)
    (bound : Nat) (mass : VirtualReturn.occupiedSlots bank ≤ bound) :
    (∀ node ∈ AuxWorkspace.nodes (program label) memory bank,
      VirtualReturn.occupiedSlots node.2 ≤ 16*(bound+7)) ∧
    ScannerStatement.clock (program label) memory bank ≤ 18*(bound+8) := by
  have bounded : ∀ slot, (bank slot).length ≤ bound := fun slot => (slot_mass bank slot).trans mass
  constructor
  · intro node present
    have perSlot := AuxWorkspace.node_bound (program label) memory bank bound bounded node present
    have cap := source_pushes (C := C) label
    have s0 := perSlot 0; have s1 := perSlot 1; have s2 := perSlot 2; have s3 := perSlot 3
    have s4 := perSlot 4; have s5 := perSlot 5; have s6 := perSlot 6; have s7 := perSlot 7
    have s8 := perSlot 8; have s9 := perSlot 9; have s10 := perSlot 10; have s11 := perSlot 11
    have s12 := perSlot 12; have s13 := perSlot 13; have s14 := perSlot 14; have s15 := perSlot 15
    simp only [VirtualReturn.occupiedSlots]
    omega
  · have clock := ScannerClock.clock_bound (program label) memory bank bound bounded
    have actions := source_actions (C := C) label
    have pushes := source_pushes (C := C) label
    have first := Nat.mul_le_mul_right (bound + AuxWorkspace.pushes (program (C := C) label) + 1)
      (Nat.mul_le_mul_left 2 actions)
    have second := Nat.mul_le_mul_left 18 (show bound + AuxWorkspace.pushes (program (C := C) label) + 1 ≤ bound + 8 by omega)
    exact clock.trans (first.trans second)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport
