module

public import B23_4_RatWordPrep_SeqCmp_WordPacketResources_141
public import B23_4_RatWordPrep_SeqCmp_WordResourceJoin_142

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

theorem actual_packet_bounds (caller : Statement C) (job : Job) (before : State C)
    (x : Rat) (tail : List Bool) (active : before.l=some (.packet job 0))
    (source : before.stk (source job)=RatInput.Encoder.packet x tail) (scratch : before.stk 4=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (next job) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=RootB234.RatPacketTransport.atBank (roles job) before.stk
        (if copy job then RatInput.Encoder.packet x tail else tail) []
        (RatInput.Encoder.packet x (before.stk (destination job))) ∧
      RunBounds caller run (3*RatInput.Encoder.fieldSize x+14)
        (RootB234.RatPacketTransport.coefficient*scale before) (RootB234.RatPacketTransport.coefficient*scale before) := by
  obtain ⟨final,run,port,context,contents,count,boundary,internal,_clocks,_charge⟩ :=
    actual_packet_resources caller job before x tail active source scratch
  refine ⟨final,run,port,context,contents,⟨count,?_,?_,?_⟩⟩
  · intro current member slot
    exact (boundary current member).1 slot
  · intro current member point selected node inside slot
    exact ((internal current member point selected).1 node inside).1 slot
  · intro current member point selected
    exact (internal current member point selected).2

theorem actual_packet_data_bounds (caller : Statement C) (job : Job) (before : State C)
    (frame : RatInput.Stack → List Bool) (data : Data) (x : Rat) (tail : List Rat)
    (active : before.l=some (.packet job 0)) (shape : before.stk=layout frame data)
    (head : data (source job)=x::tail) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (next job) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=layout frame (packetData job data x tail) ∧
      RunBounds caller run (3*RatInput.Encoder.fieldSize x+14)
        (RootB234.RatPacketTransport.coefficient*scale before) (RootB234.RatPacketTransport.coefficient*scale before) := by
  have sourcePacket : before.stk (source job)=RatInput.Encoder.packet x (PacketLists.rats tail []) := by
    rw [shape]
    cases job <;> change PacketLists.rats (data _) []=_ <;> rw [head] <;> rfl
  have scratch : before.stk 4=[] := by rw [shape]; rfl
  obtain ⟨final,run,port,context,contents,bounds⟩ := actual_packet_bounds caller job before x
    (PacketLists.rats tail []) active sourcePacket scratch
  refine ⟨final,run,port,context,?_,bounds⟩
  rw [contents,shape]
  exact packetBank_layout job frame data x tail head

theorem actual_one_bounds (caller : Statement C) (job : OneJob) (before : State C)
    (active : before.l=some (.one job)) :
    RunBounds caller (actual_one caller job before active) 2 (scale before+10) (20*(scale before+11)) := by
  have initialBound (slot : RatInput.Stack) : (before.stk slot).length≤scale before :=
    (RatInput.Encoder.point_mass before.stk slot).trans (by unfold scale; omega)
  have pushes : AuxWorkspace.pushes (program caller (.one job))=10 := rfl
  have actions : ScannerClock.actions (program caller (.one job))=10 := rfl
  have proper (current : State C) (member : current∈(actual_one caller job before active).trace.dropLast) : current=before := by
    simpa only [actual_one,List.dropLast_cons_cons,List.dropLast_singleton,List.mem_singleton] using member
  constructor
  · rfl
  · intro current member slot
    change current∈[before,oneResult job before] at member
    rcases List.mem_cons.mp member with equal | later
    · subst current
      exact (initialBound slot).trans (by omega)
    · have equal := List.mem_singleton.mp later
      subst current
      change (Function.update before.stk 15 (RatInput.Encoder.packet (1:Rat) []++before.stk 15) slot).length≤_
      by_cases selected : slot=15
      · subst slot
        rw [Function.update_self,List.length_append]
        have constant : (RatInput.Encoder.packet (1:Rat) []).length=10 := rfl
        rw [constant]
        have old := initialBound 15
        omega
      · rw [Function.update_of_ne selected]
        exact (initialBound slot).trans (by omega)
  · intro current member point selected node inside slot
    have equal := proper current member
    subst current
    have pointEq : point=.one job := Option.some.inj (selected.symm.trans active)
    subst point
    have bound := AuxWorkspace.node_bound (program caller (.one job)) before.var before.stk
      (scale before) initialBound node inside slot
    rw [pushes] at bound
    exact bound
  · intro current member point selected
    have equal := proper current member
    subst current
    have pointEq : point=.one job := Option.some.inj (selected.symm.trans active)
    subst point
    have bound := ScannerClock.clock_bound (program caller (.one job)) before.var before.stk
      (scale before) initialBound
    rw [actions,pushes] at bound
    simpa only [Nat.add_assoc] using bound

theorem actual_one_data_bounds (caller : Statement C) (job : OneJob) (before : State C)
    (frame : RatInput.Stack → List Bool) (data : Data)
    (active : before.l=some (.one job)) (shape : before.stk=layout frame data) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (oneNext job) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=layout frame (Function.update data 15 (1::data 15)) ∧
      RunBounds caller run 2 (scale before+10) (20*(scale before+11)) := by
  refine ⟨oneResult job before,actual_one caller job before active,rfl,rfl,?_,actual_one_bounds caller job before active⟩
  change Function.update before.stk 15 (RatInput.Encoder.packet (1:Rat) []++before.stk 15)=_
  rw [shape,oneBank_layout]

end B23_4_RatWordPrep.WordFinish.Resources
