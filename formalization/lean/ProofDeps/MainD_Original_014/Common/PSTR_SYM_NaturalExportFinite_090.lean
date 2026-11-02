module

public import Common.PSTR_SYM_OriginalNaturalExport_089

/-! A genuine getter from the finite prefix produced by020. The SAME
086 program selects ZERO/POS itself. Every original stack is carried;
only destination15 changes at return, with an owned self-delimiter. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport

open Turing PaperProofs.Common.Native.PSTRWordVM PSTRTMRawNat010

theorem bank_rebuild (bank : Slot → List Bool) :
    slots (bank 1) (bank 7) (bank 15) bank = bank := by
  funext slot
  by_cases left : slot = 1
  · subst slot; rfl
  by_cases scratch : slot = 7
  · subst slot; rfl
  by_cases target : slot = 15
  · subst slot; rfl
  simp only [slots,left,scratch,target,ite_false]

theorem bank_target (bank : Slot → List Bool) (target : List Bool) :
    slots (bank 1) (bank 7) target bank = Function.update bank 15 target := by
  funext slot
  fin_cases slot <;> simp [slots]

theorem state_rebuild {C : Type*} (label : Option Label) (memory : Memory C) (bank : Slot → List Bool) :
    state label memory (bank 1) (bank 7) (bank 15) bank = ⟨label,memory,bank⟩ := by
  exact congrArg (TM2.Cfg.mk label memory) (bank_rebuild bank)

theorem bank_mass (bank : Slot → List Bool) :
    VirtualReturn.occupiedSlots bank = outside bank + (bank 1).length + (bank 7).length + (bank 15).length := by
  have result := occupied_slots (bank 1) (bank 7) (bank 15) bank
  rw [bank_rebuild] at result
  exact result

def selectedOutput (records : List Nat) : List Bool :=
  match records.getLast? with
  | none => []
  | some value => leftBlocks (PSTRTMNatValue017.rawPayload value)

def Return {C : Type*} (records : List Nat) (memory : Memory C) (bank : Slot → List Bool)
    (path : List (State C)) (final : State C) : Prop :=
  path.head? = some ⟨some 0,memory,bank⟩ ∧
  path.IsChain (fun before after => TM2.step program before = some after) ∧
  path.getLast? = some final ∧
  final.l = some (if records = [] then 3 else 4) ∧ final.var.1 = memory.1 ∧
  final.stk = Function.update bank 15 (selectedOutput records ++ false :: false :: bank 15) ∧
  path.length ≤ 3*(bank 1).length+6 ∧
  (∀ current ∈ path, Bounded memory.1 bank (3*VirtualReturn.occupiedSlots bank+9-outside bank) current) ∧
  ∀ current ∈ path, ∀ label, current.l = some label →
    (∀ node ∈ PaperProofs.Common.Native.PSTRWordBool.AuxWorkspace.nodes (program label) current.var current.stk,
      VirtualReturn.occupiedSlots node.2 ≤ 16*(3*VirtualReturn.occupiedSlots bank+16)) ∧
    PaperProofs.Common.Native.PSTRWordBool.ScannerStatement.clock (program label) current.var current.stk ≤
      18*(3*VirtualReturn.occupiedSlots bank+17)

theorem return_resources {C : Type*} (records : List Nat) (memory : Memory C) (bank : Slot → List Bool)
    (path : List (State C)) (final : State C)
    (first : path.head? = some ⟨some 0,memory,bank⟩)
    (chain : path.IsChain (fun before after => TM2.step program before = some after))
    (last : path.getLast? = some final)
    (port : final.l = some (if records = [] then 3 else 4)) (context : final.var.1 = memory.1)
    (output : final.stk = Function.update bank 15 (selectedOutput records ++ false :: false :: bank 15))
    (time : path.length ≤ 3*(bank 1).length+6)
    (resources : ∀ current ∈ path, Bounded memory.1 bank
      (3*VirtualReturn.occupiedSlots bank+9-outside bank) current) :
    Return records memory bank path final := by
  refine ⟨first,chain,last,port,context,output,time,resources,?_⟩
  intro current present label _active
  have mass := (resources current present).2.2
  have outside_le : outside bank ≤ VirtualReturn.occupiedSlots bank := by rw [bank_mass]; omega
  have bounded : VirtualReturn.occupiedSlots current.stk ≤ 3*VirtualReturn.occupiedSlots bank+9 := by omega
  exact node_resources label current.var current.stk (3*VirtualReturn.occupiedSlots bank+9) bounded

theorem actual_finite_getter {C : Type*} (records : List Nat) (memory : Memory C) (bank : Slot → List Bool)
    (entry : FiniteEntry records bank) :
    ∃ (path : List (State C)) (final : State C), Return records memory bank path final := by
  rcases memory with ⟨context,bit,flag,mode⟩
  have mass := bank_mass bank
  rcases entry with ⟨empty,tail,shape⟩ | ⟨older,previous,selected,tail,recordShape,shape⟩
  · subst records
    let path := zeroTrace context bit flag mode (true :: tail) (bank 7) (bank 15) bank
    let final := state (some 3) (context,(false,true,false)) (bank 1) (bank 7)
      (false :: false :: bank 15) bank
    obtain ⟨first,chain,last,time⟩ := actual_zero context bit flag mode (true :: tail) (bank 7) (bank 15) bank
    have start : state (some 0) (context,(bit,flag,mode)) (false :: false :: true :: tail)
        (bank 7) (bank 15) bank = ⟨some 0,(context,(bit,flag,mode)),bank⟩ := by
      rw [← shape]
      exact state_rebuild _ _ bank
    refine ⟨path,final,return_resources [] (context,(bit,flag,mode)) bank path final
      (first.trans (congrArg some start)) chain ?_ rfl rfl ?_ ?_ ?_⟩
    · simpa only [path,final,shape] using last
    · exact bank_target bank (false :: false :: bank 15)
    · rw [show path.length = 5 from time]
      omega
    · intro current present
      apply bounded_mono context bank _ _ current
        (zero_resources context bit flag mode (true :: tail) (bank 7) (bank 15) bank current present)
      have length := congrArg List.length shape
      simp only [List.length_cons] at length ⊢
      omega
  · have nonempty : records ≠ [] := by
      intro empty
      have length := congrArg List.length (recordShape.symm.trans empty)
      simp only [List.length_append,List.length_cons,List.length_nil] at length
      omega
    let digits := (PSTRTMNatValue017.rawPayload selected).reverse
    let path := positiveTrace context bit flag mode digits tail (bank 7) (bank 15) bank
    obtain ⟨resultBit,first,chain,last,time⟩ := actual_positive context bit flag mode digits tail (bank 7) (bank 15) bank
    let final := state (some 4) (context,(resultBit,true,true)) (bank 1) (bank 7)
      (leftBlocks (PSTRTMNatValue017.rawPayload selected) ++ false :: false :: bank 15) bank
    have start : state (some 0) (context,(bit,flag,mode))
        (false :: true :: (lane digits ++ false :: true :: tail)) (bank 7) (bank 15) bank =
        ⟨some 0,(context,(bit,flag,mode)),bank⟩ := by
      rw [← shape]
      exact state_rebuild _ _ bank
    have selectedLast : records.getLast? = some selected := by simp [recordShape]
    refine ⟨path,final,return_resources records (context,(bit,flag,mode)) bank path final
      (first.trans (congrArg some start)) chain ?_ ?_ rfl ?_ ?_ ?_⟩
    · simpa only [path,final,digits,List.reverse_reverse,shape] using last
    · exact congrArg some (ite_eq_right nonempty).symm
    · change slots (bank 1) (bank 7) _ bank = _
      rw [bank_target]
      simp only [selectedOutput,selectedLast]
    · rw [show path.length = 3*digits.length+6 from time]
      have length := congrArg List.length shape
      change (bank 1).length = (false :: true :: (lane digits ++ false :: true :: tail)).length at length
      simp only [List.length_cons,List.length_append,lane_length] at length
      omega
    · intro current present
      apply bounded_mono context bank _ _ current
        (positive_resources context bit flag mode digits tail (bank 7) (bank 15) bank current present)
      have length := congrArg List.length shape
      change (bank 1).length = (false :: true :: (lane digits ++ false :: true :: tail)).length at length
      simp only [List.length_cons,List.length_append,lane_length] at length
      omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport
