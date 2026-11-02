module

public import Paid.PDROC_BitVM_Native_Copy_010
public import Paid.PDROC_BitVM_Codec_Output_List_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.NatResult

open Turing PDROC.BitVM.Log.TwoStack PDROC.BitVM.Native
open PaperProofs.Common.Native.RationalControllerComputation

abbrev State := TM2.Cfg Alphabet Unit (Option Bool)
abbrev Statement := TM2.Stmt Alphabet Unit (Option Bool)

/-- A fixed twelve-operation physical round trip. Empty reads explicitly
write FALSE, so the first three right cells exist even for numeric zero.
The caller's left stack is restored byte for byte, including blank bytes. -/
def transfer (source target : Stack) (next : Statement) : Statement :=
  .pop source (fun _ symbol=>symbol) (.push target (fun symbol=>symbol.getD false) next)

def program (_ : Unit) : Statement :=
  transfer 0 1 (transfer 0 1 (transfer 0 1
    (transfer 1 0 (transfer 1 0 (transfer 1 0 (.load (fun _=>none) .halt))))))

def padded : List Bool → List Bool
  | [] => [false,false,false]
  | [a] => [a,false,false]
  | [a,b] => [a,b,false]
  | a::b::c::rest => a::b::c::rest

def before (right left spare : List Bool) (store : Option Bool) : State :=
  ⟨some (),store,threeStacks right left spare⟩

def after (right left spare : List Bool) : State :=
  ⟨none,none,threeStacks (padded right) left spare⟩

theorem transfer_right (next : Statement) (right left spare : List Bool) (store : Option Bool) :
    TM2.stepAux (transfer 0 1 next) store (threeStacks right left spare)=
      TM2.stepAux next right.head? (threeStacks right.tail (right.head?.getD false::left) spare) := by
  change TM2.stepAux next right.head?
    (Function.update (Function.update (threeStacks right left spare) 0 right.tail)
      1 (right.head?.getD false::left))=_
  rw [Copy.update_first,Copy.update_second]

theorem transfer_left (next : Statement) (right left spare : List Bool) (store : Option Bool) :
    TM2.stepAux (transfer 1 0 next) store (threeStacks right left spare)=
      TM2.stepAux next left.head? (threeStacks (left.head?.getD false::right) left.tail spare) := by
  change TM2.stepAux next left.head?
    (Function.update (Function.update (threeStacks right left spare) 1 left.tail)
      0 (left.head?.getD false::right))=_
  rw [Copy.update_second,Copy.update_first]

theorem actual_step (right left spare : List Bool) (store : Option Bool) :
    TM2.step program (before right left spare store)=some (after right left spare) := by
  simp only [before,TM2.step,program,transfer_right,transfer_left,TM2.stepAux]
  cases right with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      cases rest with
      | nil => rfl
      | cons c rest => rfl

theorem padded_extends (right : List Bool) :
    ∃ count,padded right=right++List.replicate count false := by
  cases right with
  | nil => exact ⟨3,rfl⟩
  | cons a rest =>
    cases rest with
    | nil => exact ⟨2,rfl⟩
    | cons b rest =>
      cases rest with
      | nil => exact ⟨1,rfl⟩
      | cons c rest => exact ⟨0,by simp only [padded,List.replicate_zero,List.append_nil]⟩

theorem padded_length (right : List Bool) : 3≤(padded right).length := by
  cases right with
  | nil => decide
  | cons a rest =>
    cases rest with
    | nil => change 3≤3;decide
    | cons b rest =>
      cases rest with
      | nil => change 3≤3;decide
      | cons c rest => simp only [padded,List.length_cons];omega

theorem padded_same (right : List Bool) : ListBlank.mk (padded right)=ListBlank.mk right := by
  obtain ⟨count,equal⟩ := padded_extends right
  exact Quotient.sound (Or.inr ⟨count,equal⟩)

theorem tape_preserved (right left : List Bool) :
    Tape.mk₂ left (padded right)=Tape.mk₂ left right := by
  unfold Tape.mk₂
  rw [padded_same]

/-- For zero, the length-three physical writer supplies the missing FALSE
bytes; ListBlank equality by itself would not justify this prefix. -/
theorem zero_prefix (right : List Bool)
    (same : ListBlank.mk right=ListBlank.mk (encodeNat 0)) :
    ∃ suffix,padded right=encodeNat 0++suffix := by
  have related : BlankRel (padded right) (encodeNat 0) :=
    Quotient.exact ((padded_same right).trans same)
  rcases related with ⟨count,equal⟩ | ⟨count,equal⟩
  · have length := congrArg List.length equal
    have enough := padded_length right
    have zero : count=0 := by
      simp only [List.length_append,List.length_replicate] at length
      change 3=(padded right).length+count at length
      omega
    subst count
    refine ⟨[],?_⟩
    simpa only [List.replicate_zero,List.append_nil] using equal.symm
  · exact ⟨List.replicate count false,equal⟩

/-- The actual fixed machine materializes a whole canonical Nat prefix
for every value, not just a quotient of the right half-tape. -/
theorem canonical_prefix (value : ℕ) (right : List Bool)
    (same : ListBlank.mk right=ListBlank.mk (encodeNat value)) :
    ∃ suffix,padded right=encodeNat value++suffix := by
  by_cases zero : value=0
  · subst value
    exact zero_prefix right same
  · exact PDROC.BitVM.Codec.OutputList.physical_prefix_of_last_true (padded right)
      (encodeNat value) (PDROC.BitVM.Codec.OutputList.count_word_last value zero)
      ((padded_same right).trans same)

theorem runs (right left spare : List Bool) (store : Option Bool) :
    ∃ run : List State,run.head?=some (before right left spare store) ∧
      run.IsChain (fun a b=>TM2.step program a=some b) ∧
      run.getLast?=some (after right left spare) ∧
      TM2.step program (after right left spare)=none ∧ run.length=2 ∧
      (after right left spare).stk 1=left ∧ (after right left spare).stk 2=spare := by
  exact ⟨[before right left spare store,after right left spare],rfl,
    List.isChain_cons_cons.mpr ⟨actual_step right left spare store,List.isChain_singleton _⟩,
    rfl,rfl,rfl,rfl,rfl⟩

theorem supports : TM2.Supports program (Finset.univ : Finset Unit) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    cases label
    trivial

end PDROC.BitVM.Kernel.NatResult
