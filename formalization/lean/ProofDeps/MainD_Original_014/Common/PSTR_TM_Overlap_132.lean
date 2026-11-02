module
public import Common.PSTR_TM_ThresholdCopyRestore_131

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMOverlap132
open PaperProofs.Common.Native.RationalControllerComputation

/-- Join two actual SAME-machine segments at ONE IDENTICAL configuration.
Only the duplicated list entry is removed; no transition, field movement,
label transfer or head reset is omitted. This is used inside copier126
where adjacent physical scans share the same actual boundary control. -/
def glue {states : Nat} (first second : List (MachineState states)) : List (MachineState states) :=
  first.dropLast++second

theorem glue_chain {states : Nat} (machine : Machine states) (first second : List (MachineState states))
    (shared : MachineState states)
    (hf : first.IsChain (fun before after => Turing.TM0.step machine before=some after))
    (hs : second.IsChain (fun before after => Turing.TM0.step machine before=some after))
    (hl : first.getLast?=some shared) (hh : second.head?=some shared) :
    (glue first second).IsChain (fun before after => Turing.TM0.step machine before=some after) := by
  obtain ⟨rest,rfl⟩ : ∃ rest,second=shared::rest := by
    cases second with
    | nil => simp at hh
    | cons current rest =>
      simp only [List.head?_cons,Option.some.injEq] at hh
      subst current
      exact ⟨rest,rfl⟩
  have he : first.dropLast++[shared]=first := List.dropLast_append_getLast? shared hl
  have hfirst : (first.dropLast++[shared]).IsChain
      (fun before after => Turing.TM0.step machine before=some after) := by rw [he]; exact hf
  have hsecond : ([shared]++rest).IsChain
      (fun before after => Turing.TM0.step machine before=some after) := hs
  have h := List.IsChain.append_overlap hfirst hsecond (by simp)
  simpa only [glue,List.append_assoc,List.singleton_append] using h

theorem glue_head {states : Nat} (first second : List (MachineState states))
    (initial shared : MachineState states)
    (hf : first.head?=some initial) (hl : first.getLast?=some shared) (hs : second.head?=some shared) :
    (glue first second).head?=some initial := by
  cases first with
  | nil => simp at hf
  | cons current rest =>
    cases rest with
    | nil =>
      simp only [List.head?_cons,Option.some.injEq] at hf
      simp only [List.getLast?_singleton,Option.some.injEq] at hl
      subst current
      subst shared
      simpa only [glue,List.dropLast_singleton,List.nil_append] using hs
    | cons next later =>
      simpa only [glue,List.dropLast_cons_cons,List.cons_append,List.head?_cons] using hf

theorem glue_last {states : Nat} (first second : List (MachineState states)) (final : MachineState states)
    (hs : second.getLast?=some final) : (glue first second).getLast?=some final := by
  simp only [glue,List.getLast?_append,hs,Option.some_or]

theorem glue_length {states : Nat} (first second : List (MachineState states)) :
    (glue first second).length=first.length-1+second.length := by
  simp only [glue,List.length_append,List.length_dropLast]

theorem glue_length_le {states : Nat} (first second : List (MachineState states)) :
    (glue first second).length≤first.length+second.length := by rw [glue_length]; omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMOverlap132
