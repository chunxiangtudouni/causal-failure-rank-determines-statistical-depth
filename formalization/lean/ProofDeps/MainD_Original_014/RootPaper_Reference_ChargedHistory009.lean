module
public import RootPaper_Reference_Algorithm003
public import Mathlib.Data.Finset.Fold

/-! Dedicated history traversals return their data and visit counter together.
The current-used set is built by a full explicit membership fold followed by
proof-erased fresh cons; insertion never hides a second membership search.
One visit pays a bounded number of binary guards, pointer operations and
copies, priced later using the closed scalar primitives. No bind/VM is used. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RootPaper.Reference
variable {I : Instance}

def collect {α β : Type*} (f : α→Option β) : List α→List β×Nat
  | [] => ([],1)
  | item::rest =>
      let tail:=collect f rest
      match f item with
      | none => (tail.1,tail.2+3)
      | some value => (value::tail.1,tail.2+4)

theorem collect_value {α β : Type*} (f : α→Option β) (items : List α) :
    (collect f items).1=items.filterMap f := by
  induction items with
  | nil => rfl
  | cons item rest ih => cases call : f item <;> simp_all [collect]

theorem collect_work {α β : Type*} (f : α→Option β) (items : List α) :
    (collect f items).2≤4*(items.length+1) := by
  induction items with
  | nil => simp [collect]
  | cons item rest ih =>
      unfold collect
      cases f item <;> simp only [List.length_cons] <;> omega

def count {α : Type*} : List α→Nat×Nat
  | [] => (0,1)
  | _::rest => let tail:=count rest;(tail.1+1,tail.2+3)

theorem count_spec {α : Type*} (items : List α) :
    (count items).1=items.length ∧ (count items).2=3*items.length+1 := by
  induction items with
  | nil => exact ⟨rfl,rfl⟩
  | cons item rest ih => simp only [count,List.length_cons];omega

def last {α : Type*} : List α→Option α×Nat
  | [] => (none,1)
  | item::rest =>
      let tail:=last rest
      ((match tail.1 with | none => some item | some value => some value),tail.2+3)

theorem last_value {α : Type*} (items : List α) : (last items).1=items.getLast? := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [last,ih]
      cases rest <;> rfl

theorem last_work {α : Type*} (items : List α) : (last items).2=3*items.length+1 := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [last,List.length_cons];omega

def combine (left right : Bool×Nat) : Bool×Nat := (left.1||right.1,left.2+right.2)
instance combine_comm : Std.Commutative combine := ⟨by
  rintro ⟨a,n⟩ ⟨b,m⟩
  exact Prod.ext (Bool.or_comm a b) (Nat.add_comm n m)⟩
instance combine_assoc : Std.Associative combine := ⟨by
  rintro ⟨a,n⟩ ⟨b,m⟩ ⟨c,k⟩
  exact Prod.ext (Bool.or_assoc a b c) (Nat.add_assoc n m k)⟩

def probe (tool : I.Tool) (used : Finset I.Tool) : Bool×Nat :=
  let result:=used.fold combine (false,0) (fun item => (decide (tool=item),1))
  (result.1,3*result.2+1)

theorem probe_spec (tool : I.Tool) (used : Finset I.Tool) :
    (probe tool used).1=decide (tool∈used) ∧ (probe tool used).2=3*used.card+1 := by
  have exactFold : used.fold combine (false,0) (fun item => (decide (tool=item),1))=
      (decide (tool∈used),used.card) := by
    induction used using Finset.induction_on with
    | empty => rfl
    | @insert item used fresh ih =>
        simp only [Finset.fold_insert fresh,ih,combine,Finset.card_insert_of_notMem fresh]
        simp only [Finset.mem_insert]
        apply Prod.ext
        · by_cases equal : tool=item <;> by_cases member : tool∈used <;> simp_all
        · exact Nat.add_comm 1 used.card
  simp only [probe,exactFold,and_self]

def used (history : List (VisibleEvent I)) : Finset I.Tool×Nat :=
  match history with
  | [] => (∅,1)
  | event::rest =>
      let tail:=used rest
      match eventCommitment event with
      | none => (tail.1,tail.2+2)
      | some pair =>
          let inspected:=probe pair.2 tail.1
          if present : inspected.1=true then (tail.1,tail.2+inspected.2+3) else
            have fresh : pair.2∉tail.1 := by
              intro member
              exact present ((probe_spec pair.2 tail.1).1.trans (decide_eq_true_eq.mpr member))
            (tail.1.cons pair.2 fresh,tail.2+inspected.2+4)

private theorem historyUsed_cons (event : VisibleEvent I) (rest : List (VisibleEvent I)) :
    historyUsed (event::rest)=(match eventCommitment event with
      | none => historyUsed rest
      | some pair => insert pair.2 (historyUsed rest)) := by
  cases entry : eventCommitment event <;> simp [historyUsed,historyCommitments,entry]

theorem used_value (history : List (VisibleEvent I)) : (used history).1=historyUsed history := by
  induction history with
  | nil => rfl
  | cons event rest ih =>
      rw [historyUsed_cons]
      dsimp only [used]
      cases entry : eventCommitment event with
      | none => exact ih
      | some pair =>
          dsimp only
          split_ifs with present
          · have member : pair.2∈(used rest).1 :=
              decide_eq_true_eq.mp ((probe_spec _ _).1.symm.trans present)
            simpa only [ih] using (Finset.insert_eq_of_mem member).symm
          · simp only [Finset.cons_eq_insert,ih]

theorem used_work (history : List (VisibleEvent I)) :
    (used history).2≤(3*I.toolCount+6)*(history.length+1) := by
  induction history with
  | nil => simp [used]
  | cons event rest ih =>
      have cardinal : (used rest).1.card≤I.toolCount := by simpa using Finset.card_le_univ (used rest).1
      dsimp only [used]
      cases entry : eventCommitment event with
      | none => simp only [List.length_cons];nlinarith
      | some payload =>
          dsimp only
          have scanned:=(probe_spec payload.2 (used rest).1).2
          split_ifs <;> simp only [List.length_cons] <;> nlinarith

def lengthOf {α β : Type*} (f : α→Option β) (items : List α) : Nat×Nat :=
  let selected:=collect f items
  let measured:=count selected.1
  (measured.1,selected.2+measured.2+2)

theorem lengthOf_spec {α β : Type*} (f : α→Option β) (items : List α) :
    (lengthOf f items).1=(items.filterMap f).length ∧
    (lengthOf f items).2≤10*(items.length+1) := by
  have data:=collect_value f items
  have collectBound:=collect_work f items
  have counted:=count_spec (collect f items).1
  have smaller : (collect f items).1.length ≤ items.length := by rw [data];exact List.length_filterMap_le _ _
  exact ⟨by simpa only [lengthOf,data] using counted.1,by dsimp only [lengthOf];omega⟩

def lastOf {α β : Type*} (f : α→Option β) (items : List α) : Option β×Nat :=
  let selected:=collect f items
  let measured:=last selected.1
  (measured.1,selected.2+measured.2+2)

theorem lastOf_spec {α β : Type*} (f : α→Option β) (items : List α) :
    (lastOf f items).1=(items.filterMap f).getLast? ∧
    (lastOf f items).2≤10*(items.length+1) := by
  have data:=collect_value f items
  have collectBound:=collect_work f items
  have returned:=last_value (collect f items).1
  have counted:=last_work (collect f items).1
  have smaller : (collect f items).1.length ≤ items.length := by rw [data];exact List.length_filterMap_le _ _
  exact ⟨by simpa only [lastOf,data] using returned,by dsimp only [lastOf];omega⟩

/-- The predicate returns both its value and its own actual traversal count. -/
def select {α : Type*} (test : α→Bool×Nat) : List α→List α×Nat
  | [] => ([],1)
  | item::rest =>
      let checked:=test item
      let tail:=select test rest
      if checked.1 then (item::tail.1,checked.2+tail.2+3)
      else (tail.1,checked.2+tail.2+2)

theorem select_value {α : Type*} (test : α→Bool×Nat) (items : List α) :
    (select test items).1=items.filter (fun item => (test item).1) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases checked : (test item).1 <;> simp_all [select]

theorem select_work {α : Type*} (test : α→Bool×Nat) (items : List α) (width : Nat)
    (bounded : ∀ item∈items,(test item).2≤width) :
    (select test items).2≤(width+4)*(items.length+1) := by
  induction items with
  | nil => simp [select]
  | cons item rest ih =>
      have first:=bounded item (by simp)
      have tail:=ih (by intro other member;exact bounded other (by simp [member]))
      dsimp only [select]
      cases (test item).1 with
      | false => simp only [Bool.false_eq_true,ite_false,List.length_cons];nlinarith
      | true => simp only [ite_true,List.length_cons];nlinarith

def differenceTest (available excluded : Finset I.Tool) (tool : I.Tool) : Bool×Nat :=
  let left:=probe tool available
  let right:=probe tool excluded
  (left.1 && !right.1,left.2+right.2+3)

theorem differenceTest_value (available excluded : Finset I.Tool) (tool : I.Tool) :
    (differenceTest available excluded tool).1=decide (tool∈available\excluded) := by
  simp only [differenceTest,(probe_spec tool available).1,(probe_spec tool excluded).1,
    Finset.mem_sdiff]
  by_cases left : tool∈available <;> by_cases right : tool∈excluded <;> simp_all

def difference (available excluded : Finset I.Tool) : Finset I.Tool×Nat :=
  let selected:=select (differenceTest available excluded) (List.finRange I.toolCount)
  have unique : selected.1.Nodup := by
    rw [select_value]
    exact (List.nodup_finRange I.toolCount).filter _
  (⟨(selected.1 : Multiset I.Tool),by simpa using unique⟩,selected.2+I.toolCount+3)

theorem difference_value (available excluded : Finset I.Tool) :
    (difference available excluded).1=available\excluded := by
  ext tool
  simp only [difference,Finset.mem_mk,Multiset.mem_coe,select_value,List.mem_filter,List.mem_finRange,
    true_and,differenceTest_value,decide_eq_true_eq]

theorem difference_work (available excluded : Finset I.Tool) :
    (difference available excluded).2≤(6*I.toolCount+12)*(I.toolCount+1) := by
  have left : available.card≤I.toolCount := by simpa using Finset.card_le_univ available
  have right : excluded.card≤I.toolCount := by simpa using Finset.card_le_univ excluded
  have each : ∀ tool∈List.finRange I.toolCount,
      (differenceTest available excluded tool).2≤6*I.toolCount+5 := by
    intro tool _
    simp only [differenceTest,(probe_spec tool available).2,(probe_spec tool excluded).2]
    omega
  have measured:=select_work (differenceTest available excluded) (List.finRange I.toolCount) _ each
  simp only [List.length_finRange] at measured
  change (select (differenceTest available excluded) (List.finRange I.toolCount)).2+I.toolCount+3≤_
  nlinarith

def appendOne {α : Type*} : List α→α→List α×Nat
  | [],value => ([value],2)
  | item::rest,value =>
      let tail:=appendOne rest value
      (item::tail.1,tail.2+3)

theorem appendOne_spec {α : Type*} (items : List α) (value : α) :
    (appendOne items value).1=items++[value] ∧ (appendOne items value).2=3*items.length+2 := by
  induction items with
  | nil => exact ⟨rfl,rfl⟩
  | cons item rest ih => simp only [appendOne,List.cons_append,List.length_cons];exact ⟨by rw [ih.1],by omega⟩

def validate {α : Type*} (test : α→Bool) : List α→Bool×Nat
  | [] => (true,1)
  | item::rest =>
      if test item then
        let tail:=validate test rest
        (tail.1,tail.2+4)
      else (false,3)

theorem validate_value {α : Type*} (test : α→Bool) (items : List α) :
    (validate test items).1=items.all test := by
  induction items with
  | nil => rfl
  | cons item rest ih => cases checked : test item <;> simp_all [validate]

theorem validate_work {α : Type*} (test : α→Bool) (items : List α) :
    (validate test items).2≤5*(items.length+1) := by
  induction items with
  | nil => simp [validate]
  | cons item rest ih =>
      dsimp only [validate]
      cases checked : test item with
      | false => simp only [Bool.false_eq_true,ite_false,List.length_cons];omega
      | true => simp only [ite_true,List.length_cons];omega

end RootPaper.Reference.Charged
