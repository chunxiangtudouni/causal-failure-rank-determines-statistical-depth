module
public import B23_6_DFSFrame_Pop008

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace B23_6.DFSFrame
open Turing PaperProofs.Common.Native.PSTRWordBool
variable {C : Type*}

def parkCells (before : Bank) (sourceBits temporary rank : List Bool) : Bank := fun slot =>
  if slot=10 then sourceBits else if slot=12 then temporary else if slot=15 then rank else before slot
def parkBank (before : Bank) : Bank := parkCells before [] [] (before 10)
theorem park_at10 (before : Bank) (a b c : List Bool) : parkCells before a b c 10=a := rfl
theorem park_at12 (before : Bank) (a b c : List Bool) : parkCells before a b c 12=b := rfl
theorem park_at15 (before : Bank) (a b c : List Bool) : parkCells before a b c 15=c := rfl
theorem park_initial (before : Bank) : parkCells before (before 10) (before 12) (before 15)=before := by
  funext slot;fin_cases slot <;> rfl
theorem park_set10 (before : Bank) (a b c value : List Bool) :
    Function.update (parkCells before a b c) 10 value=parkCells before value b c := by
  funext slot;fin_cases slot <;> rfl
theorem park_set12 (before : Bank) (a b c value : List Bool) :
    Function.update (parkCells before a b c) 12 value=parkCells before a value c := by
  funext slot;fin_cases slot <;> rfl
theorem park_set15 (before : Bank) (a b c value : List Bool) :
    Function.update (parkCells before a b c) 15 value=parkCells before a b value := by
  funext slot;fin_cases slot <;> rfl

theorem park_run (memory : Store C) (before : Bank) :
    ∃ steps,Run (state .parkClear15 memory before) (state .popBoot (clean memory) (parkBank before)) steps ∧
      steps≤4*(RatInput.occupied before+1) := by
  have a:=clear_run 15 .parkClear15 .parkClear12 rfl (by decide) memory
    (parkCells before (before 10) (before 12) (before 15))
  rw [park_set15] at a
  rw [park_initial] at a
  have b:=clear_run 12 .parkClear12 .park10To12 rfl (by decide) (clean memory)
    (parkCells before (before 10) (before 12) [])
  rw [park_set12] at b
  simp only [park_at12] at b
  have c:=reverse_run park10Roles .park10To12 .park12To15 rfl (by decide) (clean memory)
    (parkCells before (before 10) [] [])
  simp only [park10_source,park10_target,two,park_set10,park_set12,park_at10,park_at12,List.append_nil] at c
  have d:=reverse_run park12Roles .park12To15 .popBoot rfl (by decide) (clean memory)
    (parkCells before [] (before 10).reverse [])
  simp only [park12_source,park12_target,two,park_set12,park_set15,park_at12,park_at15,List.reverse_reverse,
    List.append_nil,List.length_reverse] at d
  simp only [clean] at a b c d
  have whole:=a.trans (b.trans (c.trans d))
  refine ⟨(before 15).length+1+((before 12).length+1+((before 10).length+1+((before 10).length+1))),?_,?_⟩
  · simpa only [parkBank,clean] using whole
  · have r10:=RatInput.Encoder.point_mass before 10
    have r12:=RatInput.Encoder.point_mass before 12
    have r15:=RatInput.Encoder.point_mass before 15
    omega

theorem park_spool (before : Bank) : parkBank before 13=before 13 := rfl
theorem park_rank (before : Bank) : parkBank before 15=before 10 := rfl
theorem park_field_bound (before : Bank) (i : Field) :
    (parkBank before (field i)).length≤RatInput.occupied before := by
  unfold parkBank parkCells
  split_ifs with a b c
  · simp only [List.length_nil,Nat.zero_le]
  · simp only [List.length_nil,Nat.zero_le]
  · exact False.elim (field_ne15 i c)
  · exact RatInput.Encoder.point_mass before (field i)

theorem rank_return_run (memory : Store C) (parent child : Bank) (kind flag : Bool)
    (spool : child 13=flag::framePrefix parent kind 14) :
    ∃ steps,Run (state .parkClear15 memory child)
      (state (.popDone kind) (clean memory) (restoreBank parent (child 10))) steps ∧
      steps≤34*(RatInput.occupied child+1) := by
  obtain ⟨a,park,acap⟩:=park_run memory child
  have saved : parkBank child 13=flag::framePrefix parent kind 14:=spool
  obtain ⟨b,pop,bcap⟩:=pop_run_caps (clean memory) parent (parkBank child) kind flag saved (RatInput.occupied child)
    (parent_cap_from_spool parent child kind flag spool) (park_field_bound child)
  refine ⟨a+b,?_,by omega⟩
  simpa only [clean,park_rank] using park.trans pop

end B23_6.DFSFrame
