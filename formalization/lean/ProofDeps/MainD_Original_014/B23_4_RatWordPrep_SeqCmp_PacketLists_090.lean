module

public import B23_4_RatWordPrep_SeqCmp_WordFieldsOriginal_089

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.PacketLists

open PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

def rats (values : List Rat) (tail : List Bool) : List Bool :=
  values.foldr RatInput.Encoder.packet tail
def naturals (values : List Nat) (tail : List Bool) : List Bool :=
  values.foldr NatField.packet tail

theorem rats_append (front back : List Rat) (tail : List Bool) :
    rats (front++back) tail=rats front (rats back tail) := by
  simp only [rats,List.foldr_append]

theorem naturals_append (front back : List Nat) (tail : List Bool) :
    naturals (front++back) tail=naturals front (naturals back tail) := by
  simp only [naturals,List.foldr_append]

theorem rat_packet_append (x : Rat) (front back : List Bool) :
    RatInput.Encoder.packet x (front++back)=RatInput.Encoder.packet x front++back := by
  simp only [RatInput.Encoder.packet,PSTRSymbolicRatExport.packet,List.append_assoc,List.cons_append]

theorem natural_packet_append (x : Nat) (front back : List Bool) :
    NatField.packet x (front++back)=NatField.packet x front++back := by
  simp only [NatField.packet,List.append_assoc,List.cons_append]

theorem rat_packet_head (x : Rat) (tail : List Bool) : (RatInput.Encoder.packet x tail).head?=some true := rfl

theorem rats_cells (values : List Rat) (tail : List Bool) : rats values tail=rats values []++tail := by
  induction values with
  | nil => rfl
  | cons x values ih =>
    change RatInput.Encoder.packet x (rats values tail)=RatInput.Encoder.packet x (rats values [])++tail
    rw [ih,rat_packet_append]

theorem naturals_cells (values : List Nat) (tail : List Bool) : naturals values tail=naturals values []++tail := by
  induction values with
  | nil => rfl
  | cons x values ih =>
    change NatField.packet x (naturals values tail)=NatField.packet x (naturals values [])++tail
    rw [ih,natural_packet_append]

theorem channel_archive (values : List Rat) (tail : List Bool) :
    Channels.archived values tail=rats values.reverse tail := by
  induction values generalizing tail with
  | nil => rfl
  | cons x values ih =>
    change Channels.archived values (RatInput.Encoder.packet x tail)=_
    rw [ih,List.reverse_cons,rats_append]
    rfl

theorem symbol_archive (values : List Nat) (tail : List Bool) :
    WordFields.archived values tail=naturals values.reverse tail := by
  induction values generalizing tail with
  | nil => rfl
  | cons x values ih =>
    change WordFields.archived values (NatField.packet x tail)=_
    rw [ih,List.reverse_cons,naturals_append]
    rfl

theorem split_index {α : Type*} (values : List α) (index : Nat) (bound : index<values.length) :
    ∃ front back,values=front++values[index]::back ∧ front.length=index := by
  induction values generalizing index with
  | nil => simp at bound
  | cons x values ih =>
    cases index with
    | zero => exact ⟨[],values,rfl,rfl⟩
    | succ index =>
      have small : index<values.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using bound
      obtain ⟨front,back,split,length⟩ := ih index small
      refine ⟨x::front,back,?_,by simp only [List.length_cons,length]⟩
      simpa only [List.cons_append,List.getElem_cons_succ] using congrArg (List.cons x) split

def row (E : BinaryExperiment) (truth : Bool) : List Rat :=
  (List.finRange E.alphabetSize).map (fun symbol => E.channel truth symbol)

theorem row_split (E : BinaryExperiment) (truth : Bool) (symbol : Fin E.alphabetSize) :
    ∃ front back,row E truth=front++E.channel truth symbol::back ∧ front.length=symbol.val := by
  have bound : symbol.val<(List.finRange E.alphabetSize).length := by simpa only [List.length_finRange] using symbol.isLt
  obtain ⟨front,back,split,length⟩ := split_index (List.finRange E.alphabetSize) symbol.val bound
  refine ⟨front.map (fun j => E.channel truth j),back.map (fun j => E.channel truth j),?_,?_⟩
  · unfold row
    rw [split,List.map_append,List.map_cons]
    congr 2
    rw [List.getElem_finRange]
    rfl
  · simpa only [List.length_map] using length

theorem channel_rows (E : BinaryExperiment) : Channels.channelValues E=row E false++row E true := by
  simp only [Channels.channelValues,List.flatMap_cons,List.flatMap_nil,List.append_nil,row]

end B23_4_RatWordPrep.PacketLists
