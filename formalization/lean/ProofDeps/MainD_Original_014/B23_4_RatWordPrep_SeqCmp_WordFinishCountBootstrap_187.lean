module

public import B23_4_RatWordPrep_SeqCmp_WordFinishBootstrap_131
public import B23_4_RatWordPrep_SeqCmp_WordPrimitiveMass_158

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

theorem actual_bootstrap_count (caller : Statement C) (before : State C)
    (number : Nat) (target odds : Rat) (table : List Rat)
    (active : before.l=some (.metadata 2)) (queryEmpty : before.stk 0=[])
    (metadata : before.stk 1=NatField.packet number (RatInput.Encoder.packet target []))
    (channels : before.stk 2=PacketLists.rats table [])
    (packet : before.stk 15=RatInput.Encoder.packet odds [])
    (owned : ∀ slot,Owned slot→before.stk slot=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.packet .targetForSub 0) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=layout before.stk (initialData target odds table) ∧
      run.trace.length≤5*(PSTRTMNatValue017.rawPayload number).length+10 := by
  obtain ⟨middle,moveRun,port,context,contents,moveTime⟩ := actual_natural caller metadataLabel metadataRoles
    before number (RatInput.Encoder.packet target []) active metadata (owned 4 (by decide))
      (by intro point different; simp only [metadataLabel,different,ite_false,program])
  obtain ⟨final,clearRun,finalPort,clearContext,clearContents,clearTime⟩ := actual_clear caller middle port
  refine ⟨final,moveRun.append clearRun,finalPort,clearContext.trans context,?_,?_⟩
  · rw [clearContents,contents]
    funext slot
    fin_cases slot <;> first
    | rfl
    | exact channels
    | exact packet
    | exact owned _ (by decide)
  · have destination : middle.stk 0=NatField.packet number [] := by
      rw [contents]
      change NatField.packet number (before.stk 0)=_
      rw [queryEmpty]
    have paidClear : clearRun.trace.length=2*(PSTRTMNatValue017.rawPayload number).length+4 := by
      rw [clearTime,destination,natural_packet_length]
      simp only [List.length_nil]
    have joined := WordFinish.Segment.append_length_le moveRun clearRun
    change (moveRun.append clearRun).trace.length≤_
    omega

end B23_4_RatWordPrep.WordFinish.Resources
