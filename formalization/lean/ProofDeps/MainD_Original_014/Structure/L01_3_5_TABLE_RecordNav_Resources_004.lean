module

public import Structure.L01_3_5_TABLE_RecordNav_Code_003

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000

namespace PaperProofs.Common.Native.L01_3_5_TABLE_RecordNav003

open Turing
open PaperProofs.Common.Native.PSTRWordVM
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRSymbolicNaturalExport

def outside (bank : Slot → List Bool) : Nat :=
  VirtualReturn.occupiedSlots (slots [] [] bank)

theorem occupied_slots (left scratch : List Bool) (bank : Slot → List Bool) :
    VirtualReturn.occupiedSlots (slots left scratch bank) = outside bank + left.length + scratch.length := by
  unfold outside VirtualReturn.occupiedSlots slots
  dsimp
  omega

def Bounded {C : Type*} (context : C) (bank : Slot → List Bool) (bound : Nat) (current : State C) : Prop :=
  current.var.1 = context ∧
    (∀ slot, slot ≠ 1 → slot ≠ 6 → current.stk slot = bank slot) ∧
    VirtualReturn.occupiedSlots current.stk ≤ outside bank + bound

theorem state_bounded {C : Type*} (context : C) (bit flag mode : Bool) (label : Option Label)
    (left scratch : List Bool) (bank : Slot → List Bool) (bound : Nat)
    (mass : left.length + scratch.length ≤ bound) :
    Bounded context bank bound (state label (context,(bit,flag,mode)) left scratch bank) := by
  refine ⟨rfl,fun slot nl ns => slots_frame left scratch bank slot nl ns,?_⟩
  change VirtualReturn.occupiedSlots (slots left scratch bank) ≤ _
  rw [occupied_slots]
  omega

theorem bounded_mono {C : Type*} (context : C) (bank : Slot → List Bool)
    (first second : Nat) (current : State C) (bounded : Bounded context bank first current)
    (less : first ≤ second) : Bounded context bank second current := by
  exact ⟨bounded.1,bounded.2.1,bounded.2.2.trans (Nat.add_le_add_left less _)⟩

theorem loop_resources {C : Type*} (context : C) (bit flag mode : Bool)
    (digits cells left scratch : List Bool) (bank : Slot → List Bool) :
    ∀ current ∈ loopTrace context bit flag mode digits cells left scratch bank,
      Bounded context bank (left.length + scratch.length + 2*cells.length + 4*digits.length + 3) current := by
  induction digits generalizing bit flag cells with
  | nil =>
      intro current present
      rcases List.mem_cons.mp present with first | later
      · subst current
        apply state_bounded
        simp only [List.length_cons,List.length_append,backups_length,List.length_nil]
        omega
      · have same := List.mem_singleton.mp later
        subst current
        apply state_bounded
        simp only [List.length_cons,List.length_append,backups_length,List.length_nil]
        omega
  | cons digit later ih =>
      intro current present
      rcases List.mem_cons.mp present with first | laterMember
      · subst current
        apply state_bounded
        simp only [List.length_append,lane_length,backups_length,List.length_cons]
        omega
      · apply bounded_mono context bank _ _ current
          (ih digit false (false :: digit :: cells) current laterMember)
        simp only [List.length_cons]
        omega

theorem skip_resources {C : Type*} (context : C) (bit flag mode : Bool)
    (digits left scratch : List Bool) (bank : Slot → List Bool) :
    ∀ current ∈ skipTrace context bit flag mode digits left scratch bank,
      Bounded context bank (left.length + scratch.length + 4*digits.length + 7) current := by
  intro current present
  rcases List.mem_cons.mp present with first | later
  · subst current
    apply state_bounded
    simp only [skipped,List.length_cons,List.length_append,lane_length]
    omega
  · apply bounded_mono context bank _ _ current
      (loop_resources context false true mode digits [true,false] left scratch bank current later)
    simp only [List.length_cons,List.length_nil]
    omega

theorem restore_resources {C : Type*} (context : C) (bit flag mode : Bool)
    (cells left scratch : List Bool) (bank : Slot → List Bool) :
    ∀ current ∈ restoreTrace context bit flag mode cells left scratch bank,
      Bounded context bank (left.length + 2*cells.length + scratch.length + 1) current := by
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
      rcases List.mem_cons.mp present with first | laterMember
      · subst current
        apply state_bounded
        simp only [List.length_append,backups_length,List.length_cons]
        omega
      · apply bounded_mono context bank _ _ current
          (ih cell false (cell :: left) current laterMember)
        simp only [List.length_cons]
        omega

theorem bank_rebuild (bank : Slot → List Bool) : slots (bank 1) (bank 6) bank = bank := by
  funext slot
  fin_cases slot <;> rfl

theorem bank_mass (bank : Slot → List Bool) :
    VirtualReturn.occupiedSlots bank = outside bank + (bank 1).length + (bank 6).length := by
  have result := occupied_slots (bank 1) (bank 6) bank
  rw [bank_rebuild] at result
  exact result

theorem state_rebuild {C : Type*} (label : Option Label) (memory : Memory C) (bank : Slot → List Bool) :
    state label memory (bank 1) (bank 6) bank = ⟨label,memory,bank⟩ := by
  exact congrArg (TM2.Cfg.mk label memory) (bank_rebuild bank)

theorem bank_replace (bank : Slot → List Bool) (left scratch : List Bool) :
    slots left scratch bank = Function.update (Function.update bank 1 left) 6 scratch := by
  funext slot
  fin_cases slot <;> simp [slots]

theorem source_pushes {C : Type*} (label : Label) :
    AuxWorkspace.pushes (program (C := C) label) ≤ 5 := by
  fin_cases label <;> simp [program,AuxWorkspace.pushes]

theorem source_actions {C : Type*} (label : Label) :
    ScannerClock.actions (program (C := C) label) ≤ 8 := by
  fin_cases label <;> simp [program,ScannerClock.actions]

theorem node_resources {C : Type*} (label : Label) (memory : Memory C) (bank : Slot → List Bool)
    (bound : Nat) (mass : VirtualReturn.occupiedSlots bank ≤ bound) :
    (∀ node ∈ AuxWorkspace.nodes (program label) memory bank,
      VirtualReturn.occupiedSlots node.2 ≤ 16*(bound+5)) ∧
    ScannerStatement.clock (program label) memory bank ≤ 16*(bound+6) := by
  have bounded : ∀ slot, (bank slot).length ≤ bound :=
    fun slot => (PSTRSymbolicNaturalExport.slot_mass bank slot).trans mass
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
    have second := Nat.mul_le_mul_left 16
      (show bound + AuxWorkspace.pushes (program (C := C) label) + 1 ≤ bound + 6 by omega)
    exact clock.trans (first.trans second)

end PaperProofs.Common.Native.L01_3_5_TABLE_RecordNav003
