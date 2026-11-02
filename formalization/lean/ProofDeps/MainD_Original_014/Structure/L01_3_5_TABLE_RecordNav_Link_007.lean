module

public import Structure.L01_3_5_TABLE_RecordNav_RoundTrip_006

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000

namespace PaperProofs.Common.Native.L01_3_5_TABLE_RecordNavLink007

open Turing
open PaperProofs.Common.Native.PSTRWordVM
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open L01_3_5_TABLE_Trace005


abbrev Label := Fin 11
abbrev Memory (C : Type*) := PSTRSymbolicNaturalExport.Joined.GlobalMemory C
abbrev State (C : Type*) := TM2.Cfg PSTRSymbolicNaturalExport.Alphabet Label (Memory C)

def oldLabel (label : PSTRSymbolicNaturalExport.Joined.GlobalLabel) : Label := ⟨label.val,by omega⟩
def navLabel (label : L01_3_5_TABLE_RecordNav003.Label) : Label := ⟨label.val+6,by omega⟩

noncomputable def program {C : Type*} (label : Label) : TM2.Stmt PSTRSymbolicNaturalExport.Alphabet Label (Memory C) :=
  if label = 4 then .goto (fun _ => 10) else
  if label = 5 then .goto (fun _ => 6) else
  if before : label.val < 6 then
    LabelMap.statement oldLabel (PSTRSymbolicNaturalExport.Joined.combinedProgram ⟨label.val,before⟩)
  else LabelMap.statement navLabel (L01_3_5_TABLE_RecordNav003.roundTripProgram ⟨label.val-6,by omega⟩)

theorem nav_code {C : Type*} (label : L01_3_5_TABLE_RecordNav003.Label) :
    program (C := C) (navLabel label) = LabelMap.statement navLabel (L01_3_5_TABLE_RecordNav003.roundTripProgram label) := by
  fin_cases label <;> rfl

theorem old_code {C : Type*} (label : PSTRSymbolicNaturalExport.Joined.GlobalLabel)
    (notHalt : PSTRSymbolicNaturalExport.Joined.combinedProgram (C := C) label ≠ .halt) :
    program (C := C) (oldLabel label) =
      LabelMap.statement oldLabel (PSTRSymbolicNaturalExport.Joined.combinedProgram label) := by
  fin_cases label
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim (notHalt rfl)
  · exact False.elim (notHalt rfl)

theorem old_lift {C : Type*} (path : List (PSTRSymbolicNaturalExport.Joined.GlobalState C)) (final : PSTRSymbolicNaturalExport.Joined.GlobalState C)
    (chain : path.IsChain (fun before after => TM2.step PSTRSymbolicNaturalExport.Joined.combinedProgram before = some after))
    (last : path.getLast? = some final) (active : final.l ≠ none) :
    (path.map (LabelMap.configuration oldLabel)).IsChain
      (fun before after => TM2.step program before = some after) := by
  apply LabelMap.chain_configuration_on oldLabel PSTRSymbolicNaturalExport.Joined.combinedProgram program path chain
  intro current present label position
  exact old_code label (proper_not_halt PSTRSymbolicNaturalExport.Joined.combinedProgram path final chain last active
    current present label position)

theorem nav_lift {C : Type*} (path : List (L01_3_5_TABLE_RecordNav003.State (C × PSTRSymbolicDualStack.Store)))
    (chain : path.IsChain (fun before after => TM2.step L01_3_5_TABLE_RecordNav003.roundTripProgram before = some after)) :
    (path.map (LabelMap.configuration navLabel)).IsChain
      (fun before after => TM2.step program before = some after) := by
  apply LabelMap.chain_configuration_on navLabel L01_3_5_TABLE_RecordNav003.roundTripProgram program path chain
  intro _current _present label _position
  exact nav_code label

def tailInitial {C : Type*} (records : List Nat) (memory : Memory C) (bank : PSTRSymbolicNaturalExport.Slot → List Bool) : State C :=
  ⟨some (oldLabel (if records = [] then 4 else 5)),memory,bank⟩

theorem actual_tail {C : Type*} (records : List Nat) (memory : Memory C) (bank : PSTRSymbolicNaturalExport.Slot → List Bool)
    (entry : PSTRSymbolicNaturalExport.FiniteEntry records bank) :
    ∃ (path : List (State C)) (final : State C),
      path.head? = some (tailInitial records memory bank) ∧
      path.IsChain (fun before after => TM2.step program before = some after) ∧
      path.getLast? = some final ∧ final.l = some 10 ∧ final.var.1 = memory.1 ∧ final.stk = bank ∧
      path.length ≤ 3*VirtualReturn.occupiedSlots bank+8 ∧
      ∀ current ∈ path, current.var.1 = memory.1 ∧
        VirtualReturn.occupiedSlots current.stk ≤ 2*VirtualReturn.occupiedSlots bank+1 := by
  by_cases empty : records = []
  · subst records
    let first : State C := tailInitial [] memory bank
    let final : State C := ⟨some 10,memory,bank⟩
    refine ⟨[first,final],final,rfl,?_,rfl,rfl,rfl,rfl,?_,?_⟩
    · exact List.isChain_cons_cons.mpr ⟨rfl,List.isChain_singleton _⟩
    · change 2 ≤ _
      omega
    · intro current present
      rcases List.mem_cons.mp present with same | later
      · subst current
        exact ⟨rfl,by change VirtualReturn.occupiedSlots bank ≤ _; omega⟩
      · have same := List.mem_singleton.mp later
        subst current
        exact ⟨rfl,by change VirtualReturn.occupiedSlots bank ≤ _; omega⟩
  · rcases entry with ⟨impossible,_⟩ | ⟨older,previous,selected,left,_recordShape,shape⟩
    · exact False.elim (empty impossible)
    rcases memory with ⟨context,bit,flag,mode⟩
    let digits := (PSTRTMNatValue017.rawPayload selected).reverse
    obtain ⟨path,final,first,chain,last,port,sameContext,sameBank,time,resources,_nodes⟩ :=
      L01_3_5_TABLE_RecordNav003.actual_roundTrip context bit flag mode digits left (bank 6) bank
    have sourceShape : L01_3_5_TABLE_RecordNav003.skipped digits ++ false :: true :: left = bank 1 := by
      exact shape.symm
    have bankEq : L01_3_5_TABLE_RecordNav003.slots (L01_3_5_TABLE_RecordNav003.skipped digits ++ false :: true :: left) (bank 6) bank = bank := by
      rw [sourceShape,L01_3_5_TABLE_RecordNav003.bank_rebuild]
    have firstEq : L01_3_5_TABLE_RecordNav003.state (some 0) (context,(bit,flag,mode))
        (L01_3_5_TABLE_RecordNav003.skipped digits ++ false :: true :: left) (bank 6) bank =
        (⟨some 0,(context,(bit,flag,mode)),bank⟩ : L01_3_5_TABLE_RecordNav003.State _) := by
      exact congrArg (TM2.Cfg.mk (some 0) (context,(bit,flag,mode))) bankEq
    have firstMapped : (path.map (LabelMap.configuration navLabel)).head? =
        some (⟨some 6,(context,(bit,flag,mode)),bank⟩ : State C) := by
      rw [List.head?_map,first,firstEq,Option.map_some]
      rfl
    let next : State C := ⟨some 6,(context,(bit,flag,mode)),bank⟩
    let returned : State C := LabelMap.configuration navLabel final
    let front : Part program (tailInitial records (context,(bit,flag,mode)) bank)
        (tailInitial records (context,(bit,flag,mode)) bank) :=
      ⟨[tailInitial records (context,(bit,flag,mode)) bank],rfl,List.isChain_singleton _,rfl⟩
    let back : Part program next returned :=
      ⟨path.map (LabelMap.configuration navLabel),firstMapped,nav_lift path chain,
        by rw [List.getLast?_map,last,Option.map_some]⟩
    have bridge : TM2.step program (tailInitial records (context,(bit,flag,mode)) bank) = some next := by
      simp only [tailInitial,empty,ite_false]
      rfl
    let all := front.append back bridge
    have lengthDigits : digits.length ≤ VirtualReturn.occupiedSlots bank := by
      have length := congrArg List.length shape
      simp only [List.length_cons,List.length_append,PSTRSymbolicNaturalExport.lane_length] at length
      have cap := PSTRSymbolicNaturalExport.slot_mass bank 1
      have sameLength : digits.length = (PSTRTMNatValue017.rawPayload selected).reverse.length := rfl
      omega
    refine ⟨all.trace,returned,all.head,all.chain,all.last,?_,sameContext,?_,?_,?_⟩
    · change final.l.map navLabel = some 10
      rw [port,Option.map_some]
      rfl
    · exact sameBank.trans bankEq
    · change ([tailInitial records (context,(bit,flag,mode)) bank] ++
        path.map (LabelMap.configuration navLabel)).length ≤ _
      simp only [List.length_append,List.length_singleton,List.length_map,time]
      omega
    · intro current present
      rcases List.mem_append.mp present with inFront | inBack
      · have same := List.mem_singleton.mp inFront
        subst current
        exact ⟨rfl,by change VirtualReturn.occupiedSlots bank ≤ _; omega⟩
      · obtain ⟨source,member,rfl⟩ := List.mem_map.mp inBack
        have bound := resources source member
        exact ⟨bound.1,by simpa only [LabelMap.configuration,bankEq] using bound.2.2⟩

theorem source_pushes {C : Type*} (label : Label) :
    AuxWorkspace.pushes (program (C := C) label) ≤ 7 := by
  unfold program
  split_ifs
  · exact Nat.zero_le 7
  · exact Nat.zero_le 7
  · rw [LabelMap.statement_pushes]
    exact PSTRSymbolicNaturalExport.Joined.combined_pushes _
  · rw [LabelMap.statement_pushes]
    unfold L01_3_5_TABLE_RecordNav003.roundTripProgram
    split_ifs
    · exact Nat.zero_le 7
    · exact (L01_3_5_TABLE_RecordNav003.source_pushes _).trans (by decide)

theorem source_actions {C : Type*} (label : Label) :
    ScannerClock.actions (program (C := C) label) ≤ 9 := by
  unfold program
  split_ifs
  · exact Nat.zero_le 9
  · exact Nat.zero_le 9
  · rw [LabelMap.statement_actions]
    exact PSTRSymbolicNaturalExport.Joined.combined_actions _
  · rw [LabelMap.statement_actions]
    unfold L01_3_5_TABLE_RecordNav003.roundTripProgram
    split_ifs
    · exact Nat.zero_le 9
    · exact (L01_3_5_TABLE_RecordNav003.source_actions _).trans (by decide)

theorem node_resources {C : Type*} (label : Label) (memory : Memory C)
    (bank : PSTRSymbolicNaturalExport.Slot → List Bool)
    (bound : Nat) (mass : VirtualReturn.occupiedSlots bank ≤ bound) :
    (∀ node ∈ AuxWorkspace.nodes (program label) memory bank,
      VirtualReturn.occupiedSlots node.2 ≤ 16*(bound+7)) ∧
    ScannerStatement.clock (program label) memory bank ≤ 18*(bound+8) := by
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
    have second := Nat.mul_le_mul_left 18
      (show bound + AuxWorkspace.pushes (program (C := C) label) + 1 ≤ bound + 8 by omega)
    exact clock.trans (first.trans second)

end PaperProofs.Common.Native.L01_3_5_TABLE_RecordNavLink007
