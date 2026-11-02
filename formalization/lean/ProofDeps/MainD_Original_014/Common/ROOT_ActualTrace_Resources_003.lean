module
public import Common.ROOT_ActualTrace_FirstExit_001
public import Common.ROOT_ActualTrace_Halting_002

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace ROOT.ActualTrace
universe u
variable {α : Type u}

/-- Resource certificates migrate only AFTER deterministic first-exit
identity is proved. Resource may quantify EVERY state or any peak/time. -/
theorem FirstExit.transfer {next : α → Option α} {terminal : α → Prop} {start : α} {left right : List α}
    (first : FirstExit next terminal start left) (second : FirstExit next terminal start right)
    (Resource : List α → Prop) (certificate : Resource right) : Resource left :=
  (first.unique second).symm ▸ certificate

/-- Combine separate functional/numeric existentials into one actual
witness. Neither input assumes equality of traces or combined resources. -/
theorem exists_sameWitness {next : α → Option α} {terminal : α → Prop} {start : α}
    (Functional Numeric : List α → Prop)
    (functional : ∃ trace,FirstExit next terminal start trace ∧ Functional trace)
    (numeric : ∃ trace,FirstExit next terminal start trace ∧ Numeric trace) :
    ∃ trace,FirstExit next terminal start trace ∧ Functional trace ∧ Numeric trace := by
  obtain ⟨left,first,behavior⟩:=functional
  obtain ⟨right,second,bits⟩:=numeric
  exact ⟨left,first,behavior,first.transfer second Numeric bits⟩

end ROOT.ActualTrace
