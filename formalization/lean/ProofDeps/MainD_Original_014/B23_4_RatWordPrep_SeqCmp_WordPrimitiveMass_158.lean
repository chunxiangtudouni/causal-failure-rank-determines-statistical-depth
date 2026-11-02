module

public import B23_4_RatWordPrep_SeqCmp_WordMassGrowth_156

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

theorem two_bank_mass (before after : RatInput.Stack → List Bool) (source target : RatInput.Stack)
    (different : source≠target)
    (frame : ∀ slot,slot≠source→slot≠target→after slot=before slot)
    (total : (after source).length+(after target).length=(before source).length+(before target).length) :
    RatInput.occupied after=RatInput.occupied before := by
  let middle := Function.update before source (after source)
  have finalBank : Function.update middle target (after target)=after := by
    funext slot
    by_cases atTarget : slot=target
    · subst slot; rw [Function.update_self]
    · rw [Function.update_of_ne atTarget]
      by_cases atSource : slot=source
      · subst slot; exact Function.update_self _ _ _
      · exact (Function.update_of_ne atSource _ _).trans (frame slot atSource atTarget).symm
  have a := update_mass before source (after source)
  have b := update_mass middle target (after target)
  have middleTarget : middle target=before target := Function.update_of_ne different.symm _ _
  rw [finalBank,middleTarget] at b
  change RatInput.occupied middle+(before source).length=RatInput.occupied before+(after source).length at a
  omega

theorem rational_move_mass (before after : RatInput.Stack → List Bool)
    (source target temporary : RatInput.Stack) (different : source≠target)
    (x : Rat) (tail : List Bool)
    (oldSource : before source=RatInput.Encoder.packet x tail) (newSource : after source=tail)
    (newTarget : after target=RatInput.Encoder.packet x (before target))
    (scratch : after temporary=before temporary)
    (frame : ∀ slot,slot≠source→slot≠target→slot≠temporary→after slot=before slot) :
    RatInput.occupied after=RatInput.occupied before := by
  apply two_bank_mass before after source target different
  · intro slot nSource nTarget
    by_cases selected : slot=temporary
    · subst slot; exact scratch
    · exact frame slot nSource nTarget selected
  · rw [newSource,newTarget,oldSource,RatInput.Encoder.packet_length,RatInput.Encoder.packet_length]
    omega

theorem natural_packet_length (number : Nat) (tail : List Bool) :
    (NatField.packet number tail).length=2*(PSTRTMNatValue017.rawPayload number).length+2+tail.length := by
  simp only [NatField.packet,List.length_append,List.length_cons,PSTRSymbolicRatExport.flagged_length]
  omega

theorem natural_move_mass (before after : RatInput.Stack → List Bool)
    (source target temporary : RatInput.Stack) (different : source≠target)
    (number : Nat) (tail : List Bool)
    (oldSource : before source=NatField.packet number tail) (newSource : after source=tail)
    (newTarget : after target=NatField.packet number (before target))
    (scratch : after temporary=before temporary)
    (frame : ∀ slot,slot≠source→slot≠target→slot≠temporary→after slot=before slot) :
    RatInput.occupied after=RatInput.occupied before := by
  apply two_bank_mass before after source target different
  · intro slot nSource nTarget
    by_cases selected : slot=temporary
    · subst slot; exact scratch
    · exact frame slot nSource nTarget selected
  · rw [newSource,newTarget,oldSource,natural_packet_length,natural_packet_length]
    omega

theorem round_mass (before after : RatInput.Stack → List Bool) (digits : List Bool)
    (oldRight : before 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (newRight : after 10=RootB234.RuntimeCounter.Round.Raw.packet (RootB234.RuntimeCounter.Round.Raw.outputDigits digits))
    (left : after 11=before 11) (scratch : after 4=before 4)
    (frame : ∀ slot,slot≠4→slot≠10→slot≠11→after slot=before slot) :
    RatInput.occupied after=RatInput.occupied before := by
  unfold RatInput.occupied
  apply Finset.sum_congr rfl
  intro slot _member
  by_cases at4 : slot=4
  · subst slot; rw [scratch]
  by_cases at10 : slot=10
  · subst slot
    rw [newRight,oldRight,RootB234.RuntimeCounter.Round.packet_length,RootB234.RuntimeCounter.Round.packet_length,
      RootB234.RuntimeCounter.Round.output_width]
  by_cases at11 : slot=11
  · subst slot; rw [left]
  rw [frame slot at4 at10 at11]

theorem round_scale (before : RatInput.Stack → List Bool) (digits : List Bool)
    (right : before 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before 11=[false]) (scratch : before 4=[]) :
    RootB234.RuntimeCounter.Round.scale before digits=RatInput.occupied before+1 := by
  have bank : RootB234.RuntimeCounter.Round.cells before (RootB234.RuntimeCounter.Round.Raw.packet digits) [false] []=before := by
    funext slot
    fin_cases slot <;> first | rfl | exact right.symm | exact left.symm | exact scratch.symm
  unfold RootB234.RuntimeCounter.Round.scale
  rw [bank]
  rfl

end B23_4_RatWordPrep.WordFinish.Resources
