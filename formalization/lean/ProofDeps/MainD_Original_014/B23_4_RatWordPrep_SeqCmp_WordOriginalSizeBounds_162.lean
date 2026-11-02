module

public import B23_4_RatWordPrep_SeqCmp_WordInputSizes_138

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

theorem rawPayload_length (number : Nat) : (PSTRTMNatValue017.rawPayload number).length=natBits number := by
  simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]

theorem rawPayload_le_number (number : Nat) : (PSTRTMNatValue017.rawPayload number).length≤number+1 := by
  rw [rawPayload_length]
  unfold natBits
  exact Nat.add_le_add_right (Nat.log2_le_self number) 1

theorem rat_getter_time (x : Rat) : RawGetter.time x≤32*(RatInput.Encoder.fieldSize x+1)^2 := by
  have bound := RawGetter.time_le (fun _ => []) x
  have emptyMass : RatInput.occupied (fun _ : RatInput.Stack => [])=0 := by simp [RatInput.occupied]
  simpa only [RawGetter.inputScale,emptyMass,Nat.zero_add] using bound

theorem nat_getter_time (number : Nat) : RawNat.time number≤32*((PSTRTMNatValue017.rawPayload number).length+1)^2 := by
  have bound := RawNat.time_le (fun _ => []) number
  have emptyMass : RatInput.occupied (fun _ : RatInput.Stack => [])=0 := by simp [RatInput.occupied]
  simpa only [RawNat.inputScale,emptyMass,Nat.zero_add] using bound

theorem channel_field_le_input (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (q : Rat) (member : q∈Channels.channelValues E) :
    RatInput.Encoder.fieldSize q≤(wordInput E target word).length := by
  obtain ⟨truth,_truth,position⟩ := List.mem_flatMap.mp member
  obtain ⟨symbol,_symbol,rfl⟩ := List.mem_map.mp position
  rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
  exact RootB23.WordOddsBits.channel_width_le_input E target word truth symbol

theorem rat_times_sum (values : List Rat) (width : Nat)
    (fields : ∀ q∈values,RatInput.Encoder.fieldSize q≤width) :
    (values.map RawGetter.time).sum≤values.length*(32*(width+1)^2) := by
  have terms : ∀ value∈values.map RawGetter.time,value≤32*(width+1)^2 := by
    intro value member
    obtain ⟨q,present,rfl⟩ := List.mem_map.mp member
    exact (rat_getter_time q).trans (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left (Nat.add_le_add_right (fields q present) 1) 2))
  simpa only [List.length_map,Nat.nsmul_eq_mul] using List.sum_le_length_nsmul (values.map RawGetter.time) (32*(width+1)^2) terms

theorem channel_readWork_le (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ((Channels.channelValues E).map RawGetter.time).sum≤64*((wordInput E target word).length+1)^3 := by
  have sumBound := rat_times_sum (Channels.channelValues E) (wordInput E target word).length
    (channel_field_le_input E target word)
  rw [Channels.channel_count] at sumBound
  have count := alphabet_le_input E target word
  calc
    _≤(2*E.alphabetSize)*(32*((wordInput E target word).length+1)^2) := sumBound
    _≤(2*((wordInput E target word).length+1))*(32*((wordInput E target word).length+1)^2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (by omega))
    _=64*((wordInput E target word).length+1)^3 := by ring

theorem move_times_sum (values : List Rat) (width : Nat)
    (fields : ∀ q∈values,RatInput.Encoder.fieldSize q≤width) :
    (values.map (fun x => 3*RatInput.Encoder.fieldSize x+14)).sum≤values.length*(3*width+14) := by
  have terms : ∀ value∈values.map (fun x => 3*RatInput.Encoder.fieldSize x+14),value≤3*width+14 := by
    intro value member
    obtain ⟨q,present,rfl⟩ := List.mem_map.mp member
    have field := fields q present
    omega
  simpa only [List.length_map,Nat.nsmul_eq_mul] using
    List.sum_le_length_nsmul (values.map (fun x => 3*RatInput.Encoder.fieldSize x+14)) (3*width+14) terms

theorem channel_moveWork_le (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ((Channels.channelValues E).map (fun x => 3*RatInput.Encoder.fieldSize x+14)).sum≤
      34*((wordInput E target word).length+1)^2 := by
  have sumBound := move_times_sum (Channels.channelValues E) (wordInput E target word).length
    (channel_field_le_input E target word)
  rw [Channels.channel_count] at sumBound
  have count := alphabet_le_input E target word
  have factor : 3*(wordInput E target word).length+14≤17*((wordInput E target word).length+1) := by omega
  calc
    _≤(2*E.alphabetSize)*(3*(wordInput E target word).length+14) := sumBound
    _≤(2*((wordInput E target word).length+1))*(17*((wordInput E target word).length+1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) factor
    _=34*((wordInput E target word).length+1)^2 := by ring

end B23_4_RatWordPrep.WordFinish.Resources
