module

public import B23_4_RatWordPrep_SeqCmp_WordFoldLoop_123
public import B23_4_RatWordPrep_SeqCmp_WordPrimitiveMass_158
public import B23_4_RatWordPrep_SeqCmp_WordOriginalSizeBounds_162
public import B23_4_RatWordPrep_SeqCmp_WordCountToResources_157

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFold.Count

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

noncomputable def pushCap (caller : Statement C) : Nat :=
  Classical.choose (WordFinish.Resources.finite_push_bound (program caller))

theorem pushes (caller : Statement C) : ∀ point,AuxWorkspace.pushes (program caller point)≤pushCap caller :=
  Classical.choose_spec (WordFinish.Resources.finite_push_bound (program caller))

def CounterSafe (bound : Nat) (bank : RatInput.Stack → List Bool) : Prop :=
  bank 7=[] ∧ bank 11=[false] ∧ (bank 10).length≤2*(bound+1)+3

def massBudget (bound : Nat) : Nat := 128*(bound+1)^2

theorem natural_packets_length (values : List Nat) (tail : List Bool) (width : Nat)
    (fields : ∀ n∈values,(PSTRTMNatValue017.rawPayload n).length≤width) :
    (PacketLists.naturals values tail).length≤values.length*(2*width+2)+tail.length := by
  induction values with
  | nil => simp [PacketLists.naturals]
  | cons n values ih =>
    have first := fields n (List.mem_cons_self)
    have later := ih (by intro m member; exact fields m (List.mem_cons_of_mem n member))
    change (NatField.packet n (PacketLists.naturals values tail)).length≤_
    rw [WordFinish.Resources.natural_packet_length]
    simp only [List.length_cons]
    nlinarith

theorem binary_mass (before after : RatInput.Stack → List Bool)
    (oldOwned : ∀ slot,Owned slot→before slot=[]) (newOwned : ∀ slot,Owned slot→after slot=[])
    (scratch : after 7=before 7) (frame : ∀ slot,¬RatPair.Link.Work slot→after slot=before slot) :
    RatInput.occupied after≤RatInput.occupied before+(after 15).length := by
  have bank : after=Function.update before 15 (after 15) := by
    funext slot
    fin_cases slot
    all_goals first
    | rfl
    | exact frame _ (by decide)
    | exact scratch
    | exact (newOwned _ (by decide)).trans (oldOwned _ (by decide)).symm
  have mass := WordFinish.Resources.update_mass before 15 (after 15)
  rw [←bank] at mass
  omega

theorem ratio_field (x y : Rat) :
    RatInput.Encoder.fieldSize (x/y)≤RatInput.Encoder.fieldSize x+RatInput.Encoder.fieldSize y := by
  simp only [RootB23.WordOddsBits.ratInput_fieldSize_eq]
  exact RootB23.WordOddsBits.div_width_le x y

theorem step_field (E : BinaryExperiment) (odds : Rat) (symbol : Fin E.alphabetSize) :
    RatInput.Encoder.fieldSize (stepOdds E odds symbol)≤
      RatInput.Encoder.fieldSize odds+RatInput.Encoder.fieldSize (E.channel true symbol)+
        RatInput.Encoder.fieldSize (E.channel false symbol) := by
  have division := ratio_field (E.channel true symbol) (E.channel false symbol)
  have product : RatInput.Encoder.fieldSize ((E.channel true symbol/E.channel false symbol)*odds)≤
      RatInput.Encoder.fieldSize (E.channel true symbol/E.channel false symbol)+RatInput.Encoder.fieldSize odds := by
    simp only [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    exact RootB23.WordOddsBits.mul_width_le _ _
  unfold stepOdds
  omega

def potential (E : BinaryExperiment) (symbols : List (Fin E.alphabetSize)) (odds : Rat) : Nat :=
  RatInput.Encoder.fieldSize odds+
    (symbols.map (fun symbol => RatInput.Encoder.fieldSize (E.channel true symbol)+RatInput.Encoder.fieldSize (E.channel false symbol))).sum

theorem potential_step (E : BinaryExperiment) (symbol : Fin E.alphabetSize) (symbols : List (Fin E.alphabetSize)) (odds : Rat) :
    potential E symbols (stepOdds E odds symbol)≤potential E (symbol::symbols) odds := by
  have step := step_field E odds symbol
  simp only [potential,List.map_cons,List.sum_cons]
  omega

theorem canonical_mass (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (symbols : List (Fin E.alphabetSize)) (before : State C) (odds : Rat)
    (count : symbols.length≤(wordInput E target word).length)
    (query : before.stk 0=PacketLists.naturals (symbols.map Fin.val) [])
    (metadata : before.stk 1=NatField.packet E.alphabetSize (RatInput.Encoder.packet target []))
    (table : before.stk 2=PacketLists.rats (Channels.channelValues E) [])
    (packet : before.stk 15=RatInput.Encoder.packet odds [])
    (owned : ∀ slot,Owned slot→before.stk slot=[])
    (safe : CounterSafe (wordInput E target word).length before.stk)
    (width : RatInput.Encoder.fieldSize odds≤8*((wordInput E target word).length+1)^2) :
    RatInput.occupied before.stk≤massBudget (wordInput E target word).length := by
  let B := (wordInput E target word).length
  change RatInput.Encoder.fieldSize odds≤8*(B+1)^2 at width
  have alphabet := WordFinish.Resources.alphabet_le_input E target word
  have symbolWidth (symbol : Fin E.alphabetSize) : (PSTRTMNatValue017.rawPayload symbol.val).length≤B+1 :=
    (WordFinish.Resources.rawPayload_le_number symbol.val).trans
      (Nat.add_le_add_right (symbol.isLt.le.trans alphabet) 1)
  have queries := natural_packets_length (symbols.map Fin.val) [] (B+1)
    (by intro n member; obtain ⟨symbol,_present,rfl⟩ := List.mem_map.mp member; exact symbolWidth symbol)
  simp only [List.length_map,List.length_nil,Nat.add_zero] at queries
  have queryBound : (before.stk 0).length≤B*(2*(B+1)+2) := by
    rw [query]
    exact queries.trans (Nat.mul_le_mul_right _ count)
  have naturalWidth := (WordFinish.Resources.rawPayload_le_number E.alphabetSize).trans (Nat.add_le_add_right alphabet 1)
  have targetWidth : RatInput.Encoder.fieldSize target≤B := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    exact RootB23.WordOddsBits.target_width_le_input E target word
  have metadataBound : (before.stk 1).length≤4*B+10 := by
    rw [metadata,WordFinish.Resources.natural_packet_length,RatInput.Encoder.packet_length]
    simp only [List.length_nil]
    omega
  have tableBound : (before.stk 2).length≤2*B := by rw [table]; exact WordFinish.Resources.channel_packets_le_input E target word
  have packetBound : (before.stk 15).length≤16*(B+1)^2+6 := by
    rw [packet,RatInput.Encoder.packet_length]
    simp only [List.length_nil]
    omega
  have e3 := owned 3 (by decide)
  have e4 := owned 4 (by decide)
  have e5 := owned 5 (by decide)
  have e6 := owned 6 (by decide)
  have e8 := owned 8 (by decide)
  have e9 := owned 9 (by decide)
  have e12 := owned 12 (by decide)
  have e13 := owned 13 (by decide)
  have e14 := owned 14 (by decide)
  have mass : RatInput.occupied before.stk=(before.stk 0).length+(before.stk 1).length+
      (before.stk 2).length+(before.stk 15).length+(before.stk 10).length+1 := by
    simp [RatInput.occupied,Fin.sum_univ_succ,e3,e4,e5,e6,e8,e9,e12,e13,e14,safe.1,safe.2.1]
    omega
  have counter := safe.2.2
  change (before.stk 10).length≤2*(B+1)+3 at counter
  change RatInput.occupied before.stk≤128*(B+1)^2
  rw [mass]
  nlinarith

end B23_4_RatWordPrep.WordFold.Count
