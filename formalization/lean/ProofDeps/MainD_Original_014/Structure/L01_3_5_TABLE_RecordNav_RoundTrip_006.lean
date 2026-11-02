module

public import Structure.L01_3_5_TABLE_Trace_005

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000

namespace PaperProofs.Common.Native.L01_3_5_TABLE_RecordNav003

open Turing
open PaperProofs.Common.Native.PSTRWordVM
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRSymbolicNaturalExport
open L01_3_5_TABLE_Trace005

def roundTripProgram {C : Type*} (label : Label) : TM2.Stmt Alphabet Label (Memory C) :=
  if label = 2 then .goto (fun _ => 3) else program label

theorem roundTrip_lift {C : Type*} (path : List (State C)) (final : State C)
    (chain : path.IsChain (fun before after => TM2.step program before = some after))
    (last : path.getLast? = some final) (active : final.l ≠ none) :
    path.IsChain (fun before after => TM2.step roundTripProgram before = some after) := by
  apply chain_on program roundTripProgram path chain
  intro current present label position
  have notHalt := proper_not_halt program path final chain last active current present label position
  have notTwo : label ≠ 2 := by
    intro two
    subst label
    exact notHalt rfl
  simp only [roundTripProgram,notTwo,ite_false]

theorem actual_roundTrip {C : Type*} (context : C) (bit flag mode : Bool)
    (digits left scratch : List Bool) (background : Slot → List Bool) :
    ∃ (path : List (State C)) (final : State C),
      path.head? = some (state (some 0) (context,(bit,flag,mode))
        (skipped digits ++ false :: true :: left) scratch background) ∧
      path.IsChain (fun before after => TM2.step roundTripProgram before = some after) ∧
      path.getLast? = some final ∧ final.l = some 4 ∧ final.var.1 = context ∧
      final.stk = slots (skipped digits ++ false :: true :: left) scratch background ∧
      path.length = 3*digits.length+7 ∧
      (∀ current ∈ path, current.var.1 = context ∧
        (∀ slot, slot ≠ 1 → slot ≠ 6 → current.stk slot = background slot) ∧
        VirtualReturn.occupiedSlots current.stk ≤
          2*VirtualReturn.occupiedSlots
            (slots (skipped digits ++ false :: true :: left) scratch background)+1) ∧
      ∀ current ∈ path, ∀ label, current.l = some label →
        (∀ node ∈ AuxWorkspace.nodes (roundTripProgram label) current.var current.stk,
          VirtualReturn.occupiedSlots node.2 ≤
            16*(2*VirtualReturn.occupiedSlots
              (slots (skipped digits ++ false :: true :: left) scratch background)+6)) ∧
        ScannerStatement.clock (roundTripProgram label) current.var current.stk ≤
          16*(2*VirtualReturn.occupiedSlots
            (slots (skipped digits ++ false :: true :: left) scratch background)+7) := by
  let moved := state (some 2) (context,(false,true,mode)) (false :: true :: left)
    (backups (skipped digits).reverse ++ true :: scratch) background
  let restored := state (some 4) (context,(finalBit (skipped digits).reverse false,true,mode))
    (skipped digits ++ false :: true :: left) scratch background
  obtain ⟨skipFirst,skipChain,skipLast,skipLength⟩ := actual_skip context bit flag mode digits left scratch background
  have movedActive : moved.l ≠ none := by intro impossible; cases impossible
  have restoredActive : restored.l ≠ none := by intro impossible; cases impossible
  have restoreLast := restore_last context false true mode (skipped digits).reverse
    (false :: true :: left) scratch background
  rw [List.reverse_reverse] at restoreLast
  let front : Part roundTripProgram
      (state (some 0) (context,(bit,flag,mode))
        (skipped digits ++ false :: true :: left) scratch background) moved :=
    ⟨skipTrace context bit flag mode digits left scratch background,skipFirst,
      roundTrip_lift _ moved skipChain skipLast movedActive,skipLast⟩
  let back : Part roundTripProgram
      (state (some 3) (context,(false,true,mode)) (false :: true :: left)
        (backups (skipped digits).reverse ++ true :: scratch) background) restored :=
    ⟨restoreTrace context false true mode (skipped digits).reverse (false :: true :: left) scratch background,
      restore_head context false true mode _ _ _ _,
      roundTrip_lift _ restored (restore_chain context false true mode _ _ _ _) restoreLast restoredActive,
      restoreLast⟩
  have bridge : TM2.step roundTripProgram moved = some
      (state (some 3) (context,(false,true,mode)) (false :: true :: left)
        (backups (skipped digits).reverse ++ true :: scratch) background) := rfl
  let all := front.append back bridge
  let mass := VirtualReturn.occupiedSlots (slots (skipped digits ++ false :: true :: left) scratch background)
  have massValue : mass = outside background + 2*digits.length+4+left.length+scratch.length := by
    simp only [mass,occupied_slots,skipped,List.length_cons,List.length_append,lane_length]
    omega
  have resources : ∀ current ∈ all.trace,
      current.var.1 = context ∧
      (∀ slot, slot ≠ 1 → slot ≠ 6 → current.stk slot = background slot) ∧
      VirtualReturn.occupiedSlots current.stk ≤ 2*mass+1 := by
    intro current present
    rcases List.mem_append.mp present with before | after
    · have bound := skip_resources context bit flag mode digits left scratch background current before
      exact ⟨bound.1,bound.2.1,by have cap := bound.2.2; omega⟩
    · have bound := restore_resources context false true mode (skipped digits).reverse
        (false :: true :: left) scratch background current after
      have length : (skipped digits).reverse.length = 2+2*digits.length := by
        simp only [List.length_reverse,skipped,List.length_cons,lane_length]
        omega
      exact ⟨bound.1,bound.2.1,by
        have cap := bound.2.2
        simp only [List.length_cons] at cap
        omega⟩
  refine ⟨all.trace,restored,all.head,all.chain,all.last,rfl,rfl,rfl,?_,resources,?_⟩
  · change ((skipTrace context bit flag mode digits left scratch background) ++
      restoreTrace context false true mode (skipped digits).reverse (false :: true :: left) scratch background).length = _
    rw [List.length_append,skipLength,restore_length]
    simp only [List.length_reverse,skipped,List.length_cons,lane_length]
    omega
  · intro current present label _active
    have bound := (resources current present).2.2
    by_cases two : label = 2
    · subst label
      constructor
      · intro node member
        have same : node = (current.var,current.stk) := by
          exact List.mem_singleton.mp member
        subst node
        change VirtualReturn.occupiedSlots current.stk ≤ _
        omega
      · change 0 ≤ _
        omega
    · simpa only [roundTripProgram,two,ite_false] using
        node_resources label current.var current.stk (2*mass+1) bound

end PaperProofs.Common.Native.L01_3_5_TABLE_RecordNav003
