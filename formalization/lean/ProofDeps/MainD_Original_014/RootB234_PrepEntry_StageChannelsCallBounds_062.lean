module

public import RootB234_PrepEntry_StageChannelsLoop_060

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageChannels.Bounds

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*}

def credit (x : Rat) : Nat := 16*RawGetter.time x+5*RatInput.Encoder.fieldSize x+20
def credits (values : List Rat) : Nat := (values.map credit).sum
def limit (values : List Rat) (bound : Nat) : Nat :=
  (values.length+1)*(4096*(bound+credits values)+256)+credits values

theorem credits_nil : credits []=0 := rfl
theorem credits_cons (x : Rat) (values : List Rat) : credits (x::values)=credit x+credits values := rfl

theorem append_count {caller : Channels.Statement C} {before middle final : Channels.State C}
    (front : Channels.Segment caller before middle) (back : Channels.Segment caller middle final) :
    (front.append back).trace.length≤front.trace.length+back.trace.length := by
  change (front.trace++back.trace.tail).length≤_
  simp only [List.length_append,List.length_tail]
  omega

theorem round_scale (before : Channels.State C) (digits : List Bool) (bound : Nat)
    (counter : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[])
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    RootB234.RuntimeCounter.Round.scale before.stk digits≤16*bound+1 := by
  have same : RootB234.RuntimeCounter.Round.cells before.stk
      (RootB234.RuntimeCounter.Round.Raw.packet digits) [false] []=before.stk := by
    funext slot
    fin_cases slot <;> simp_all [RootB234.RuntimeCounter.Round.cells]
  change RatInput.occupied (RootB234.RuntimeCounter.Round.cells before.stk _ _ _)+1≤_
  rw [same]
  exact Nat.add_le_add_right (RatInput.Encoder.occupied_bound before.stk bound bounded) 1

theorem round_bound (before final : Channels.State C) (digits : List Bool) (bound : Nat)
    (counter : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false])
    (rightFinal : final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet (RootB234.RuntimeCounter.Round.Raw.outputDigits digits))
    (leftFinal : final.stk 11=[false]) (scratchFinal : final.stk 4=[])
    (frame : ∀ slot,slot≠4→slot≠10→slot≠11→final.stk slot=before.stk slot)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    ∀ slot,(final.stk slot).length≤bound := by
  intro slot
  by_cases s4 : slot=4
  · subst slot; rw [scratchFinal]; exact Nat.zero_le _
  by_cases s10 : slot=10
  · subst slot
    rw [rightFinal,RootB234.RuntimeCounter.Round.packet_length,RootB234.RuntimeCounter.Round.output_width,
      ←RootB234.RuntimeCounter.Round.packet_length,←counter]
    exact bounded 10
  by_cases s11 : slot=11
  · subst slot; rw [leftFinal,←left]; exact bounded 11
  rw [frame slot s4 s10 s11]
  exact bounded slot

theorem move_bound (before final : Channels.State C) (x : Rat) (tail : List Bool) (bound : Nat)
    (source : before.stk 15=RatInput.Encoder.packet x tail)
    (restored : final.stk 15=tail) (stored : final.stk 2=RatInput.Encoder.packet x (before.stk 2))
    (scratch : final.stk 4=[])
    (frame : ∀ slot,slot≠2→slot≠4→slot≠15→final.stk slot=before.stk slot)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    ∀ slot,(final.stk slot).length≤bound+2*RatInput.Encoder.fieldSize x+6 := by
  intro slot
  by_cases s2 : slot=2
  · subst slot; rw [stored,RatInput.Encoder.packet_length]; have old:=bounded 2; omega
  by_cases s4 : slot=4
  · subst slot; rw [scratch]; exact Nat.zero_le _
  by_cases s15 : slot=15
  · subst slot; rw [restored]
    have old:=bounded 15
    rw [source,RatInput.Encoder.packet_length] at old
    omega
  rw [frame slot s2 s4 s15]
  exact (bounded slot).trans (by omega)

/-- The same frozen getter path, with an additive endpoint bound relative
to the actual incoming maximum stack length. No occupied-mass multiplier
is iterated through the vector. -/
theorem actual_read (caller : Channels.Statement C) (before : Channels.State C)
    (x : Rat) (suffix : List Bool) (bound : Nat)
    (active : before.l=some (.read .boot))
    (right : ListBlank.mk (before.stk 0)=ListBlank.mk (encodeDatum (.rational x)++suffix++[true]))
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    ∃ (final : Channels.State C) (run : Channels.Segment caller before final),
      final.l=some (.move 0) ∧ final.var.2=before.var.2 ∧
      final.stk 15=RatInput.Encoder.packet x (before.stk 15) ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (suffix++[true]) ∧
      (∀ slot,slot≠0→slot≠1→slot≠15→final.stk slot=before.stk slot) ∧
      run.trace.length≤RawGetter.time x ∧
      ∀ slot,(final.stk slot).length≤bound+16*RawGetter.time x := by
  obtain ⟨trace,final,parsed,first,chain,last,_member,activeFinal,context,contents,tape,
      scratch,_target,time⟩:=RawGetter.actual_current_field .halt before.stk ((Channels.rawIso C).symm before.var) x suffix right
  let start : RawGetter.State (Channels.RawContext C):=⟨some .boot,(Channels.rawIso C).symm before.var,before.stk⟩
  have resources:=RawGetter.trace_resources trace start before.stk bound first chain bounded (by intros; rfl)
  have path:=Channels.read_path caller trace _ final first chain last activeFinal
  let run : Channels.Segment caller before (Channels.readCfg final):=
    ⟨trace.map Channels.readCfg,path.1.trans (congrArg some (Channels.read_shared before active)),path.2.1,path.2.2⟩
  have finalFrame := (resources final (List.mem_of_getLast? last)).2
  refine ⟨Channels.readCfg final,run,?_,?_,?_,?_,?_,?_,?_⟩
  · change final.l.map Channels.readLabel=some (.move 0)
    rw [activeFinal]; rfl
  · exact congrArg (fun v : Channels.RawContext C => v.2) context
  · change final.stk 15=_
    rw [contents,Function.update_self]
  · have rightTape:=congrArg Tape.right₀ tape
    simp only [Tape.mk₂,Tape.mk'_right₀] at rightTape
    change ListBlank.mk (final.stk 0)=_
    rw [contents,Function.update_of_ne (by decide : (0 : RatInput.Stack)≠15)]
    exact rightTape
  · intro slot n0 n1 n15
    change final.stk slot=_
    by_cases s7 : slot=7
    · subst slot
      rw [contents,Function.update_of_ne (by decide : (7 : RatInput.Stack)≠15)]
      exact scratch
    · exact finalFrame slot (by simp only [RawGetter.Work,n0,n1,n15,s7,or_self,not_false_eq_true])
  · simpa only [run,List.length_map] using time
  · intro slot
    exact ((resources final (List.mem_of_getLast? last)).1 slot).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 16 time) bound)

end RootB234.PrepEntry.StageChannels.Bounds
