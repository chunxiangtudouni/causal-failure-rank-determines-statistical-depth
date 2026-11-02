module

public import B23_4_RatWordPrep_SeqCmp_WordPacketBounds_144
public import B23_4_RatWordPrep_SeqCmp_WordBinaryResources_143

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

def frameMass (frame : RatInput.Stack → List Bool) : Nat :=
  (frame 7).length+(frame 10).length+(frame 11).length

/-- Canonical return layouts expose their actual data mass. This is the
quantity reused at each native entry, rather than an earlier quartic
workspace envelope. -/
theorem layout_mass (frame : RatInput.Stack → List Bool) (data : Data) :
    RatInput.occupied (layout frame data)=frameMass frame+
      (PacketLists.rats (data 0) []).length+(PacketLists.rats (data 1) []).length+
      (PacketLists.rats (data 2) []).length+(PacketLists.rats (data 15) []).length := by
  simp [RatInput.occupied,layout,DataSlot,Owned,Fin.sum_univ_succ,frameMass]
  omega

theorem packets_length_le (values : List Rat) (tail : List Bool) (width : Nat)
    (bounded : ∀ q∈values,RatInput.Encoder.fieldSize q≤width) :
    (PacketLists.rats values tail).length≤values.length*(2*width+6)+tail.length := by
  induction values with
  | nil => simp only [PacketLists.rats,List.foldr_nil,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons x values ih =>
    have field := bounded x (List.mem_cons_self)
    have rest := ih (by intro q member; exact bounded q (List.mem_cons_of_mem x member))
    calc
      _=2*RatInput.Encoder.fieldSize x+6+(PacketLists.rats values tail).length := RatInput.Encoder.packet_length x _
      _≤2*width+6+(values.length*(2*width+6)+tail.length) := Nat.add_le_add (by omega) rest
      _=(x::values).length*(2*width+6)+tail.length := by simp only [List.length_cons]; ring

def operands (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : List Rat :=
  [target,1-target,target/(1-target),(1-target)/target,E.rationalWordOdds word,1]

theorem operands_field_bound (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∀ q∈operands E target word,
      RatInput.Encoder.fieldSize q≤8*((wordInput E target word).length+1)^2 := by
  have wp := RootB23.WordOddsBits.target_width_le_input E target word
  have wc := RootB23.WordOddsBits.one_sub_width_le target
  have wl := RootB23.WordOddsBits.lower_width_le_input E target word
  have wh := RootB23.WordOddsBits.upper_width_le_input E target word
  have wr := original_odds_field_quadratic E target word
  have square : (wordInput E target word).length+1≤((wordInput E target word).length+1)^2 := by nlinarith
  intro q member
  simp [operands] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    nlinarith
  · rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    nlinarith
  · rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    nlinarith
  · rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    nlinarith
  · exact wr
  · change 2≤8*((wordInput E target word).length+1)^2
    nlinarith

/-- A fixed capacity of actual canonical packets plus the untouched
original channel table gives one original-input mass at every stage. -/
theorem canonical_mass (frame : RatInput.Stack → List Bool) (data : Data)
    (table : List Rat) (width count : Nat)
    (small : ∀ slot,slot=0 ∨ slot=1 ∨ slot=15→
      (data slot).length≤count ∧ ∀ q∈data slot,RatInput.Encoder.fieldSize q≤width)
    (tableHead : ∃ front,data 2=front++table ∧ front.length≤count ∧
      ∀ q∈front,RatInput.Encoder.fieldSize q≤width) :
    RatInput.occupied (layout frame data)≤frameMass frame+
      (PacketLists.rats table []).length+4*count*(2*width+6) := by
  obtain ⟨front,split,size,fields⟩ := tableHead
  have bound (slot : RatInput.Stack) (selected : slot=0 ∨ slot=1 ∨ slot=15) :
      (PacketLists.rats (data slot) []).length≤count*(2*width+6) := by
    have bounded := packets_length_le (data slot) [] width (small slot selected).2
    simp only [List.length_nil,Nat.add_zero] at bounded
    exact bounded.trans (Nat.mul_le_mul_right _ (small slot selected).1)
  have zero := bound 0 (by decide)
  have one := bound 1 (by decide)
  have main := bound 15 (by decide)
  have tableBound : (PacketLists.rats (data 2) []).length≤count*(2*width+6)+(PacketLists.rats table []).length := by
    rw [split,PacketLists.rats_append]
    exact (packets_length_le front (PacketLists.rats table []) width fields).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ size) _)
  rw [layout_mass]
  nlinarith

end B23_4_RatWordPrep.WordFinish.Resources
