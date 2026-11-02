module

public import B23_4_RatWordPrep_SeqCmp_WordFinishLayout_130

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

def initialData (target odds : Rat) (table : List Rat) : Data :=
  fun slot => if slot=1 then [target] else if slot=2 then table else if slot=15 then [odds] else []

/-- Removes the already-consumed alphabet-size metadata by one actual
natural transport and actual finite-cell clear, leaving the target packet
at1. Odds15, table2, scratch7, and all other frame cells are preserved. -/
theorem actual_bootstrap (caller : Statement C) (before : State C)
    (number : Nat) (target odds : Rat) (table : List Rat)
    (active : before.l=some (.metadata 2))
    (_queryEmpty : before.stk 0=[])
    (metadata : before.stk 1=NatField.packet number (RatInput.Encoder.packet target []))
    (channels : before.stk 2=PacketLists.rats table [])
    (packet : before.stk 15=RatInput.Encoder.packet odds [])
    (owned : ∀ slot,Owned slot→before.stk slot=[]) :
    ∃ (final : State C) (_run : Segment caller before final),
      final.l=some (.packet .targetForSub 0) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=layout before.stk (initialData target odds table) := by
  obtain ⟨middle,moveRun,port,context,contents,_moveTime⟩ := actual_natural caller metadataLabel metadataRoles
    before number (RatInput.Encoder.packet target []) active metadata (owned 4 (by decide))
      (by intro point different; simp only [metadataLabel,different,ite_false,program])
  obtain ⟨final,clearRun,finalPort,clearContext,clearContents,_clearTime⟩ := actual_clear caller middle port
  refine ⟨final,moveRun.append clearRun,finalPort,clearContext.trans context,?_⟩
  rw [clearContents,contents]
  funext slot
  fin_cases slot <;> first
  | rfl
  | exact channels
  | exact packet
  | exact owned _ (by decide)

end B23_4_RatWordPrep.WordFinish
