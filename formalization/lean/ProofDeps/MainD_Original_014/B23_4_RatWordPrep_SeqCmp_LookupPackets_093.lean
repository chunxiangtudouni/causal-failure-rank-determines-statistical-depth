module

public import B23_4_RatWordPrep_SeqCmp_LookupPaths_092

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem packet_shared (rename : RootB234.RatPacketTransport.Label → Label)
    (roles : RatInput.Stack ≃ RatInput.Stack) (before : State C) (x : Rat) (tail : List Bool)
    (active : before.l=some (rename 0))
    (source : before.stk (roles 15)=RatInput.Encoder.packet x tail) (scratch : before.stk (roles 4)=[]) :
    packetCfg rename (RootB234.RatPacketTransport.atState roles before.stk 0
      ((WordFields.packetIso C).symm before.var).1 ((WordFields.packetIso C).symm before.var).2
      (RatInput.Encoder.packet x tail) [] (before.stk (roles 2)))=before := by
  have bank : RootB234.RatPacketTransport.atBank roles before.stk
      (RatInput.Encoder.packet x tail) [] (before.stk (roles 2))=before.stk := by
    funext slot
    unfold RootB234.RatPacketTransport.atBank
    split_ifs with h15 h4 h2
    · subst slot; exact source.symm
    · subst slot; exact scratch.symm
    · subst slot; rfl
    · rfl
  cases before with
  | mk point memory slots =>
    change point=some (rename 0) at active
    subst point
    change (⟨some (rename 0),WordFields.packetIso C ((WordFields.packetIso C).symm memory),
      RootB234.RatPacketTransport.atBank roles slots _ _ _⟩ : State C)=_
    rw [Equiv.apply_symm_apply]
    exact congrArg (fun cells => (⟨some (rename 0),memory,cells⟩ : State C)) bank

/-- The concrete caller selects roles/copy/return maps before input.
Only the actual current source packet is assumed; all paths and copied
data are produced by the existing physical transport theorem. -/
theorem actual_packet (truth : Bool) (caller : Statement C)
    (rename : RootB234.RatPacketTransport.Label → Label) (roles : RatInput.Stack ≃ RatInput.Stack)
    (copy : Bool) (before : State C) (x : Rat) (tail : List Bool)
    (active : before.l=some (rename 0))
    (source : before.stk (roles 15)=RatInput.Encoder.packet x tail) (scratch : before.stk (roles 4)=[])
    (same : ∀ point,point≠4→program truth caller (rename point)=
      LabelMap.statement rename (StoreIso.statement (WordFields.packetIso C)
        (RootB234.RatPacketTransport.atProgram roles copy point))) :
    ∃ (final : State C) (run : Segment truth caller before final),
      final.l=some (rename 4) ∧ final.var.2.2=before.var.2.2 ∧
      final.stk=RootB234.RatPacketTransport.atBank roles before.stk
        (if copy then RatInput.Encoder.packet x tail else tail) []
        (RatInput.Encoder.packet x (before.stk (roles 2))) ∧
      run.trace.length≤3*RatInput.Encoder.fieldSize x+14 := by
  let registers := (WordFields.packetIso C).symm before.var
  obtain ⟨trace,facts⟩ := RootB234.RatPacketTransport.at_actual roles copy
    before.stk registers.1 registers.2 x tail (before.stk (roles 2))
  let final := RootB234.RatPacketTransport.atState roles before.stk 4 registers.1 (false,false)
    (if copy then RatInput.Encoder.packet x tail else tail) [] (RatInput.Encoder.packet x (before.stk (roles 2)))
  have path := single_port_path (WordFields.packetIso C) rename _ truth caller 4 rfl
    trace _ final facts.first facts.chain facts.last rfl same
  let run : Segment truth caller before (packetCfg rename final) :=
    ⟨trace.map (packetCfg rename),path.1.trans (congrArg some (packet_shared rename roles before x tail active source scratch)),
      path.2.1,path.2.2⟩
  refine ⟨packetCfg rename final,run,rfl,?_,rfl,?_⟩
  · change registers.1.2.2=before.var.2.2
    rfl
  · simpa only [run,List.length_map] using facts.count

end B23_4_RatWordPrep.Lookup
