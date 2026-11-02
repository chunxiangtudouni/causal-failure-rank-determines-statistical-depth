module

public import B23_4_RatWordPrep_SeqCmp_OriginalFeePublic_038

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.OriginalFee.Public

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

theorem initial_default {C : Type*} [Inhabited C] (bits : List Bool) :
    entry (default : RawGetter.Store C) default default bits=
      TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store C) 0 bits := by
  change (⟨some (default : Label),(default : Store C),_⟩ : State C)=⟨some default,default,_⟩
  congr 1
  funext slot
  fin_cases slot <;> rfl

private theorem supports_univ_stmt {C : Type*} (body : Statement C) :
    TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports {C : Type*} : TM2.Supports (program (C := C) .halt) (Finset.univ : Finset Label) := by
  exact ⟨Finset.mem_univ _,fun point _ => supports_univ_stmt _⟩

/-- No initial finite-store argument is supplied by the original caller.
This is an actual TM2.init original-input prefix, not yet the final Word
output/stack0/true-halt endpoint required by the native adapter. -/
theorem from_default (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ trace final beforeRead,Facts (program (C := Unit) .halt) default default default E target word trace final beforeRead ∧
      trace.head?=some (TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store Unit) 0 (wordInput E target word)) := by
  obtain ⟨trace,final,beforeRead,facts⟩ := actual_polynomial (C := Unit) default default default E target word
  exact ⟨trace,final,beforeRead,facts,facts.first.trans (congrArg some (initial_default _))⟩

end B23_4_RatWordPrep.OriginalFee.Public
