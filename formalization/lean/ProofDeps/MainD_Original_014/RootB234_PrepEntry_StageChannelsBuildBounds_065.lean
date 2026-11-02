module

public import RootB234_PrepEntry_StageChannelsCalls_059

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageChannels

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*}

def buildSpace (number bound : Nat) : Nat := bound+2*(PSTRTMNatValue017.rawPayload number).length+4
def buildLimit (number bound : Nat) : Nat := 2*bound+2*(PSTRTMNatValue017.rawPayload number).length+14

theorem actual_build_bounded (right : Bool) (caller : Statement C) (before : State C)
    (number : Nat) (tail : List Bool) (bound : Nat)
    (active : before.l=some (buildPoint right)) (source : before.stk 14=NatField.packet number tail)
    (scratch : before.stk 4=[]) (bounded : ∀ slot,(before.stk slot).length≤bound) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (roundPoint right) ∧ final.var.2=before.var.2 ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet (PSTRTMNatValue017.rawPayload number) ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (∀ slot,slot≠4→slot≠10→slot≠11→final.stk slot=before.stk slot) ∧
      run.trace.length≤buildLimit number bound ∧
      ∀ slot,(final.stk slot).length≤buildSpace number bound := by
  obtain ⟨final,run,port,context,counter,left,empty,frame,time⟩:=actual_build right caller before number tail active source scratch
  refine ⟨final,run,port,context,counter,left,empty,frame,?_,?_⟩
  · have ten:=bounded 10
    have eleven:=bounded 11
    dsimp only [buildLimit]
    omega
  · intro slot
    by_cases s4 : slot=4
    · subst slot; rw [empty]; exact Nat.zero_le _
    by_cases s10 : slot=10
    · subst slot; rw [counter,RootB234.RuntimeCounter.Round.packet_length]
      dsimp only [buildSpace]
      omega
    by_cases s11 : slot=11
    · subst slot; rw [left]
      dsimp only [buildSpace]
      simp only [List.length_cons,List.length_nil]
      omega
    rw [frame slot s4 s10 s11]
    exact (bounded slot).trans (by unfold buildSpace; omega)

theorem append_count {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    (front.append back).trace.length≤front.trace.length+back.trace.length := by
  change (front.trace++back.trace.tail).length≤_
  simp only [List.length_append,List.length_tail]
  omega

end RootB234.PrepEntry.StageChannels
