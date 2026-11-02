module

public import Common.PSTR_SYM_NaturalExportResources_088

/-! The actual020 whole Tape produces a TRUE-delimited finite L1 prefix.
No exact finite archive, empty destination, host width or supplied record
is inferred from ListBlank equality. The selected integer is extracted
from the SAME original nativeRecords, after its real parser run. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport

open Turing PaperProofs.Common PaperProofs.Common.Native PSTRWordVM
open PSTRSymbolicDualStream PSTRSymbolicLaneScan PSTRSymbolicLaneArchive
open PSTRSymbolicPairedArchive PSTRSymbolicCursorArchive PSTRTMRawNat010

theorem finite_marked_prefix (frontBits tail actual : List Bool)
    (same : ListBlank.mk actual = ListBlank.mk (frontBits ++ true :: tail)) :
    ∃ remaining, actual = frontBits ++ true :: remaining := by
  induction frontBits generalizing actual with
  | nil =>
    cases actual with
    | nil =>
      have impossible := congrArg ListBlank.head same
      change false = true at impossible
      cases impossible
    | cons bit later =>
      have head := congrArg ListBlank.head same
      change bit = true at head
      subst bit
      exact ⟨later,rfl⟩
  | cons bit frontBits ih =>
    have tails := congrArg ListBlank.tail same
    cases actual with
    | nil =>
      change ListBlank.mk [] = ListBlank.mk (frontBits ++ true :: tail) at tails
      obtain ⟨remaining,impossible⟩ := ih [] tails
      have length := congrArg List.length impossible
      simp only [List.length_nil,List.length_append,List.length_cons] at length
      omega
    | cons first later =>
      have heads := congrArg ListBlank.head same
      change first = bit at heads
      change ListBlank.mk later = ListBlank.mk (frontBits ++ true :: tail) at tails
      obtain ⟨remaining,shape⟩ := ih later tails
      exact ⟨remaining,by rw [heads,shape]; rfl⟩

theorem raw_lane_reverse (digits : List Bool) :
    (digits.flatMap (fun bit => [false,bit])).reverse = lane digits.reverse := by
  induction digits with
  | nil => rfl
  | cons digit later ih =>
    simp only [List.flatMap_cons,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,ih,lane,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.singleton_append]

theorem natural_word_reverse (digits : List Bool) :
    (naturalWord digits).reverse = false :: true :: lane digits.reverse := by
  rw [naturalWord,List.reverse_append,raw_lane_reverse]
  rfl

theorem last_two (records : List Nat) (room : 2 ≤ records.length) :
    ∃ older previous selected, records = older ++ [previous,selected] := by
  have length : 2 ≤ records.reverse.length := by simpa only [List.length_reverse] using room
  cases shape : records.reverse with
  | nil => simp only [shape,List.length_nil] at length; omega
  | cons selected rest =>
    cases rest with
    | nil => simp only [shape,List.length_cons,List.length_nil] at length; omega
    | cons previous older =>
      refine ⟨older.reverse,previous,selected,?_⟩
      have reversed := congrArg List.reverse shape
      simpa only [List.reverse_reverse,List.reverse_cons,List.reverse_nil,List.nil_append,
        List.append_assoc,List.singleton_append] using reversed

def recordRemainder (data : List Datum) (firstDigits secondDigits : List Bool)
    (older : List Nat) (previous : Nat) : List Bool :=
  lane (PSTRTMNatValue017.rawPayload previous).reverse ++
    (navigationCells (allDatumPairs (older.map Datum.natural))).reverse ++
    false :: (leftBlocks secondDigits.reverse ++ false :: PSTRSymbolicRawStack.archiveLeft data firstDigits)

theorem record_two_left (data : List Datum) (firstDigits secondDigits : List Bool)
    (older : List Nat) (previous selected : Nat) :
    (recordEndTape data firstDigits (older ++ [previous,selected]) secondDigits).left =
      ListBlank.mk (false :: true :: (lane (PSTRTMNatValue017.rawPayload selected).reverse ++
        false :: true :: recordRemainder data firstDigits secondDigits older previous)) := by
  have nonempty : older ++ [previous,selected] ≠ [] := by
    intro empty
    have length := congrArg List.length empty
    simp only [List.length_append,List.length_cons,List.length_nil] at length
    omega
  rw [recordEndTape,ite_eq_right nonempty,archiveTape,Tape.mk₂,Tape.mk'_left]
  rw [allDatumPairs_cells]
  simp only [List.map_append,List.map_cons,List.map_nil,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,pairedDatum,List.reverse_append,natural_word_reverse,
    recordRemainder,List.append_assoc,List.cons_append]
  rw [← allDatumPairs_cells]

def FiniteEntry (records : List Nat) (bank : Slot → List Bool) : Prop :=
  (records = [] ∧ ∃ tail, bank 1 = false :: false :: true :: tail) ∨
  ∃ older previous selected tail, records = older ++ [previous,selected] ∧
    bank 1 = false :: true :: (lane (PSTRTMNatValue017.rawPayload selected).reverse ++ false :: true :: tail)

theorem record_finite_entry (data : List Datum) (firstDigits secondDigits : List Bool)
    (records : List Nat) (bank : Slot → List Bool)
    (domain : records = [] ∨ 4 ≤ records.length)
    (wholeLeft : ListBlank.mk (bank 1) = (recordEndTape data firstDigits records secondDigits).left) :
    FiniteEntry records bank := by
  rcases domain with empty | room
  · subst records
    change ListBlank.mk (bank 1) = ListBlank.mk
      (false :: false :: true :: false :: PSTRSymbolicRawStack.archiveLeft data firstDigits) at wholeLeft
    obtain ⟨tail,shape⟩ := finite_marked_prefix [false,false]
      (false :: PSTRSymbolicRawStack.archiveLeft data firstDigits) (bank 1) wholeLeft
    exact Or.inl ⟨rfl,tail,shape⟩
  · obtain ⟨older,previous,selected,shape⟩ := last_two records (by omega)
    rw [shape,record_two_left] at wholeLeft
    obtain ⟨tail,actual⟩ := finite_marked_prefix
      (false :: true :: (lane (PSTRTMNatValue017.rawPayload selected).reverse ++ [false]))
      (recordRemainder data firstDigits secondDigits older previous) (bank 1)
      (by simpa only [List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using wholeLeft)
    exact Or.inr ⟨older,previous,selected,tail,shape,
      by simpa only [List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using actual⟩

theorem actual_native_finite_entry {C : Type*} {I : Instance}
    (caller : PSTRSymbolicDualStack.Statement C) (context : C) (background : Slot → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (available : Finset I.Tool)
    (budget : Rat) (history : List (VisibleEvent I)) :
    ∃ (path : List (PSTRSymbolicDualStack.State C)) (final : PSTRSymbolicDualStack.State C),
      path.head? = some (VirtualReturn.configuration context background
        (TM2.init (Γ := PSTRWordBool.PushPop.Alphabet) (Λ := Unit) (σ := PSTRSymbolicDualStack.Store) 0
          (CompactPrice.plannerInput input contract available budget history (PSTRQueryRecords.nativeRecords available history)))) ∧
      path.IsChain (fun before after => TM2.step (PSTRSymbolicDualStack.program caller) before = some after) ∧
      path.getLast? = some final ∧ final.l = some 1 ∧
      FiniteEntry (PSTRQueryRecords.nativeRecords available history) final.stk ∧
      path.length ≤ 16385*((CompactPrice.plannerInput input contract available budget history
        (PSTRQueryRecords.nativeRecords available history)).length+1)^3 ∧
      (∀ current ∈ path, current.var.1 = context ∧
        ∀ slot, slot ≠ 0 → slot ≠ 1 → current.stk slot = background slot) ∧
      ∀ current ∈ path, VirtualReturn.occupiedSlots current.stk ≤ VirtualReturn.outside background +
        65536*((CompactPrice.plannerInput input contract available budget history
          (PSTRQueryRecords.nativeRecords available history)).length+1)^3 := by
  obtain ⟨firstDigits,secondDigits,path,final,first,chain,last,returned,tape,_right,
    _value,_width,_endValue,time,frame,mass,_nodes⟩ :=
    PSTRSymbolicDualStack.actual_dual_stack_resources caller context background input contract available budget history
  have wholeLeft := congrArg Tape.left tape
  change ListBlank.mk (final.stk 1) = _ at wholeLeft
  exact ⟨path,final,first,chain,last,returned,
    record_finite_entry _ _ _ _ _ (native_records_domain available history) wholeLeft,time,frame,mass⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport
