module

public import B23_4_RatWordPrep_SeqCmp_WordResourceTransport_140

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

def scale (before : State C) : Nat := RatInput.occupied before.stk+1

/-- Complete resources of the SAME actual transport witness installed at
each fixed WordFinish packet call. The scale is actual incoming mass;
no path, fuel, cost, result or workspace premise is supplied by caller. -/
theorem actual_packet_resources (caller : Statement C) (job : Job) (before : State C)
    (x : Rat) (tail : List Bool) (active : before.l=some (.packet job 0))
    (source : before.stk (source job)=RatInput.Encoder.packet x tail) (scratch : before.stk 4=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (next job) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=RootB234.RatPacketTransport.atBank (roles job) before.stk
        (if copy job then RatInput.Encoder.packet x tail else tail) []
        (RatInput.Encoder.packet x (before.stk (destination job))) ∧
      run.trace.length≤3*RatInput.Encoder.fieldSize x+14 ∧
      (∀ current∈run.trace,
        (∀ slot,(current.stk slot).length≤RootB234.RatPacketTransport.coefficient*scale before) ∧
        RatInput.occupied current.stk≤RootB234.RatPacketTransport.coefficient*scale before) ∧
      (∀ current∈run.trace.dropLast,∀ point,current.l=some point→
        (∀ node∈AuxWorkspace.nodes (program caller point) current.var current.stk,
          (∀ slot,(node.2 slot).length≤RootB234.RatPacketTransport.coefficient*scale before) ∧
          RatInput.occupied node.2≤RootB234.RatPacketTransport.coefficient*scale before) ∧
        ScannerStatement.clock (program caller point) current.var current.stk≤
          RootB234.RatPacketTransport.coefficient*scale before) ∧
      traceClockSum (program caller) run.trace≤RootB234.RatPacketTransport.coefficient^2*(scale before)^2 ∧
      run.trace.length+traceClockSum (program caller) run.trace≤
        (RootB234.RatPacketTransport.coefficient^2+RootB234.RatPacketTransport.coefficient)*(scale before)^2 := by
  let iso := OddsInit.packetIso C
  let rename := packetLabel job
  let old := RootB234.RatPacketTransport.atProgram (C := PacketContext C) (roles job) (copy job)
  let memory := iso.symm before.var
  have src : before.stk (roles job 15)=RatInput.Encoder.packet x tail := by rw [roles_source]; exact source
  have temp : before.stk (roles job 4)=[] := by rw [roles_scratch]; exact scratch
  have shared := packet_shared rename (roles job) before x tail active src temp
  have bank : RootB234.RatPacketTransport.atBank (roles job) before.stk
      (RatInput.Encoder.packet x tail) [] (before.stk (roles job 2))=before.stk :=
    congrArg (fun current : State C => current.stk) shared
  have actualScale : RootB234.RatPacketTransport.atScale (roles job) before.stk x tail
      (before.stk (roles job 2))=scale before := by
    unfold RootB234.RatPacketTransport.atScale
    rw [bank]
    rfl
  have same (point : RootB234.RatPacketTransport.Label) (different : point≠4) :
      program caller (rename point)=LabelMap.statement rename (StoreIso.statement iso (old point)) := by
    simp only [rename,packetLabel,different,ite_false,program]
    rfl
  obtain ⟨trace,facts⟩ := RootB234.RatPacketTransport.at_actual (roles job) (copy job)
    before.stk memory.1 memory.2 x tail (before.stk (roles job 2))
  let last := RootB234.RatPacketTransport.atState (roles job) before.stk 4 memory.1 (false,false)
    (if copy job then RatInput.Encoder.packet x tail else tail) []
    (RatInput.Encoder.packet x (before.stk (roles job 2)))
  have path := single_port_path iso rename old caller 4 rfl trace _ last
    facts.first facts.chain facts.last rfl same
  let run : Segment caller before (mappedCfg iso rename last) :=
    ⟨trace.map (mappedCfg iso rename),path.1.trans (congrArg some shared),path.2.1,path.2.2⟩
  have clocks : traceClockSum (program caller) run.trace=RootB234.RatPacketTransport.atClockSum (roles job) (copy job) trace := by
    have lifted := mapped_clockSum iso rename old caller trace (by
      intro current member point selected
      apply same point
      intro equal
      subst point
      exact (facts.proper current member).1 selected)
    change traceClockSum (program caller) (trace.map (mappedCfg iso rename))=_
    rw [lifted]
    unfold traceClockSum RootB234.RatPacketTransport.atClockSum
    apply congrArg List.sum
    apply List.map_congr_left
    intro current _member
    cases current with
    | mk point registers slots => cases point <;> rfl
  refine ⟨mappedCfg iso rename last,run,rfl,?_,?_,?_,?_,?_,?_,?_⟩
  · change memory.1.2.2.2=before.var.2.2.2
    rfl
  · change RootB234.RatPacketTransport.atBank (roles job) before.stk _ []
      (RatInput.Encoder.packet x (before.stk (roles job 2)))=_
    rw [roles_destination]
  · simpa only [run,List.length_map] using facts.count
  · intro current member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    have bounds := facts.boundaries original present
    rw [actualScale] at bounds
    exact ⟨bounds.2.1,bounds.2.2.1⟩
  · intro current member point selected
    change current∈(trace.map (mappedCfg iso rename)).dropLast at member
    rw [←List.map_dropLast] at member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    change original.l.map rename=some point at selected
    obtain ⟨oldPoint,oldActive,renamed⟩ := Option.map_eq_some_iff.mp selected
    have different : oldPoint≠4 := by intro equal; subst oldPoint; exact (facts.proper original present).1 oldActive
    have body := same oldPoint different
    have bounds := (facts.proper original present).2 oldPoint oldActive
    rw [actualScale] at bounds
    rw [←renamed]
    constructor
    · intro node inside
      change node∈AuxWorkspace.nodes (program caller (rename oldPoint)) (iso original.var) original.stk at inside
      rw [mapped_nodes iso rename old caller oldPoint original.var original.stk body] at inside
      obtain ⟨oldNode,oldInside,rfl⟩ := List.mem_map.mp inside
      exact ⟨(bounds.1 oldNode oldInside).2.1,(bounds.1 oldNode oldInside).2.2.1⟩
    · change ScannerStatement.clock (program caller (rename oldPoint)) (iso original.var) original.stk≤_
      rw [body,clock_labelMap,clock_storeIso]
      exact bounds.2
  · rw [clocks]
    simpa only [actualScale] using facts.clockSum
  · rw [clocks]
    simpa only [run,List.length_map,RootB234.RatPacketTransport.atCharge,actualScale] using facts.charge

end B23_4_RatWordPrep.WordFinish.Resources
