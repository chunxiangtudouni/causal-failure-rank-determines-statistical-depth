module

public import B23_4_RatWordPrep_SeqCmp_OddsInitOriginal_116
public import B23_4_RatWordPrep_SeqCmp_WordBinaryScale_146
public import B23_4_RatWordPrep_SeqCmp_WordCountToResources_157

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.OddsInit.Count

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

noncomputable def pushCap (caller : Statement C) : Nat :=
  Classical.choose (WordFinish.Resources.finite_push_bound (program caller))

theorem pushes (caller : Statement C) :
    ∀ point,AuxWorkspace.pushes (program caller point)≤pushCap caller :=
  Classical.choose_spec (WordFinish.Resources.finite_push_bound (program caller))

def swapWork (fee prior comp : Rat) : Nat :=
  8*(RatInput.Encoder.fieldSize fee+RatInput.Encoder.fieldSize prior+RatInput.Encoder.fieldSize comp)+80

noncomputable def initializeBudget (caller : Statement C) (before : State C) (fee prior comp : Rat) : Nat :=
  swapWork fee prior comp+
    (7*WordFinish.Resources.binaryScaleCoefficient RatMulDiv.divCoefficient+137)*
      (RatInput.occupied before.stk+pushCap caller*swapWork fee prior comp+1)^4

theorem actual_initialize (caller : Statement C) (before : State C) (fee prior comp : Rat)
    (active : before.l=some (.fee 0)) (owned : ∀ slot,Owned slot→before.stk slot=[])
    (source : before.stk 15=RatInput.Encoder.packet fee
      (RatInput.Encoder.packet comp (RatInput.Encoder.packet prior []))) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some .done ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk 15=RatInput.Encoder.packet (prior/comp) [] ∧ final.stk 7=before.stk 7 ∧
      (∀ slot,Owned slot→final.stk slot=[]) ∧
      (∀ slot,¬RatPair.Link.Work slot→final.stk slot=before.stk slot) ∧
      run.trace.length ≤ initializeBudget caller before fee prior comp := by
  obtain ⟨middle,swapRun,port,context,packet,empty4,empty13,empty14,frame,swapTime⟩ :=
    actual_swap caller before fee prior comp active (owned 4 (by decide)) (owned 13 (by decide)) (owned 14 (by decide)) source
  have middleOwned : ∀ slot,Owned slot→middle.stk slot=[] := by
    intro slot selected
    fin_cases slot <;> first
    | exact empty4
    | exact empty13
    | exact empty14
    | exact (frame _ (by decide)).trans (owned _ (by decide))
    | simp [Owned] at selected
  obtain ⟨final,divRun,finalPort,divContext,output,scratch,finalOwned,finalFrame,divTime⟩ :=
    actual_divide caller middle prior comp [] port packet middleOwned
  have middleMass := WordFinish.Resources.trace_mass (pushCap caller) (pushes caller)
    swapRun.trace before (RatInput.occupied before.stk) swapRun.first swapRun.chain (Nat.le_refl _)
      middle (List.mem_of_getLast? swapRun.last)
  have massBound : RatInput.occupied middle.stk≤RatInput.occupied before.stk+pushCap caller*swapWork fee prior comp :=
    middleMass.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ swapTime) _)
  let current : WordFinish.State C := ⟨none,middle.var,middle.stk⟩
  have binaryTime := WordFinish.Resources.binary_time_le_mass RatMulDiv.divCoefficient current prior comp [] packet
  have scaleBound : WordFinish.Resources.scale current≤
      RatInput.occupied before.stk+pushCap caller*swapWork fee prior comp+1 := Nat.add_le_add_right massBound 1
  have paidDivision := divTime.trans (binaryTime.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left scaleBound 4)))
  let whole := swapRun.append divRun
  refine ⟨final,whole,finalPort,?_,output,?_,finalOwned,?_,?_⟩
  · exact (congrArg (fun memory : WordPack.Store C => memory.2.2) divContext).trans context
  · exact scratch.trans (frame 7 (by decide))
  · intro slot untouched
    have n4 : slot≠4 := by intro equal; subst slot; exact untouched (by decide)
    have n13 : slot≠13 := by intro equal; subst slot; exact untouched (by decide)
    have n14 : slot≠14 := by intro equal; subst slot; exact untouched (by decide)
    have n15 : slot≠15 := by intro equal; subst slot; exact untouched (by decide)
    exact (finalFrame slot untouched).trans (frame slot ⟨n4,n13,n14,n15⟩)
  · have joined := swapRun.append_length_le divRun
    change (swapRun.append divRun).trace.length≤_
    change swapRun.trace.length≤swapWork fee prior comp at swapTime
    unfold initializeBudget
    omega

end B23_4_RatWordPrep.OddsInit.Count
