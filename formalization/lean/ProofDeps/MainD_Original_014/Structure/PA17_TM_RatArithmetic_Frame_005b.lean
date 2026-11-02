module
public import Structure.PA17_TM_RatArithmetic_Frame_005a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFrame005

open Turing
open PSTRTMSeq005
variable {states : Nat}

/-- Lift a whole actual run to a physically present finite window. The SAME
machine executes each step and its true HALT. Its ordered displacement list,
not just a final cost inequality, is unchanged. The caller must produce this
window by real charged work; no allocation is claimed by this theorem. -/
theorem frame_runsFrom (machine : Machine states) (archive suffix : List Bool)
    (trace : List (MachineState states)) :
    ∀ (initial final : MachineState states) (left right : Nat),
      RunsFrom machine initial trace final → trace.length ≤ left → trace.length ≤ right →
      ∃ (finalLeft finalRight : Nat) (framed : List (MachineState states)),
        RunsFrom machine (frameCfg left right archive suffix initial) framed
          (frameCfg finalLeft finalRight archive suffix final) ∧
        framed.length = trace.length ∧
        framed.map (displacement machine) = trace.map (displacement machine) ∧
        finalLeft+finalRight = left+right := by
  induction trace with
  | nil =>
    intro initial final left right run hl hr
    have hh := run.1
    simp at hh
  | cons state tail ih =>
    intro initial final left right run hl hr
    obtain ⟨hh,hc,ht,halt⟩ := run
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst initial
    have hleft : 0 < left := by simp only [List.length_cons] at hl; omega
    have hright : 0 < right := by simp only [List.length_cons] at hr; omega
    cases tail with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at ht
      subst final
      refine ⟨left,right,[frameCfg left right archive suffix state],?_,by simp,by simp,rfl⟩
      refine ⟨rfl,by simp,rfl,?_⟩
      rw [step_frame machine state left right archive suffix hleft hright, halt]
      rfl
    | cons second later =>
      have hs := (List.isChain_cons_cons.mp hc).1
      have htchain := (List.isChain_cons_cons.mp hc).2
      have htlast : (second::later).getLast? = some final := by simpa using ht
      have hl' : (second::later).length ≤ nextLeft machine state left := by
        have hb := nextLeft_lower machine state left
        simp only [List.length_cons] at hl ⊢
        omega
      have hr' : (second::later).length ≤ nextRight machine state right := by
        have hb := nextRight_lower machine state right
        simp only [List.length_cons] at hr ⊢
        omega
      obtain ⟨finalLeft,finalRight,framed,hfrun,hlen,hmap,hsum⟩ :=
        ih second final (nextLeft machine state left) (nextRight machine state right)
          ⟨rfl,htchain,htlast,halt⟩ hl' hr'
      have hne : framed ≠ [] := by
        intro he
        have hehead := hfrun.1
        simp [he] at hehead
      refine ⟨finalLeft,finalRight,frameCfg left right archive suffix state::framed,?_,?_,?_,?_⟩
      · refine ⟨rfl,?_,?_,hfrun.2.2.2⟩
        · apply hfrun.2.1.cons
          intro y hy
          rw [hfrun.1] at hy
          simp only [Option.mem_some_iff] at hy
          subst y
          rw [step_frame machine state left right archive suffix hleft hright, hs]
          rfl
        · rw [List.getLast?_cons_of_ne_nil hne]
          exact hfrun.2.2.1
      · simpa only [List.length_cons] using congrArg (·+1) hlen
      · simp only [List.map_cons,displacement_frame,hmap]
      · rw [hsum, next_sum machine state left right hleft hright]

/-- Original space is literally the same functional of the same ordered
head displacements, for every chosen charged initial length. Hence this is
also an all-prefix statement rather than a final-tape-only simulation. -/
theorem visitedSpace_of_displacements (machine : Machine states)
    (trace framed : List (MachineState states))
    (same : framed.map (displacement machine) = trace.map (displacement machine))
    (inputLength : Nat) :
    visitedSpace machine inputLength framed = visitedSpace machine inputLength trace := by
  unfold visitedSpace
  rw [same]

theorem frame_run_cost (machine : Machine states) (archive suffix : List Bool)
    (trace : List (MachineState states)) (initial final : MachineState states)
    (left right : Nat) (run : RunsFrom machine initial trace final)
    (hl : trace.length ≤ left) (hr : trace.length ≤ right) :
    ∃ (finalLeft finalRight : Nat) (framed : List (MachineState states)),
      RunsFrom machine (frameCfg left right archive suffix initial) framed
        (frameCfg finalLeft finalRight archive suffix final) ∧
      framed.length = trace.length ∧
      (∀ inputLength, visitedSpace machine inputLength framed = visitedSpace machine inputLength trace) ∧
      finalLeft+finalRight = left+right := by
  obtain ⟨finalLeft,finalRight,framed,hfrun,hlen,hmap,hsum⟩ :=
    frame_runsFrom machine archive suffix trace initial final left right run hl hr
  exact ⟨finalLeft,finalRight,framed,hfrun,hlen,
    visitedSpace_of_displacements machine trace framed hmap,hsum⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFrame005
