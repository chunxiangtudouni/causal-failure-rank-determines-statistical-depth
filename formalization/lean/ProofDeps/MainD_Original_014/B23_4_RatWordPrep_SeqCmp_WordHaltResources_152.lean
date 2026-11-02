module

public import B23_4_RatWordPrep_SeqCmp_WordResourceJoin_142
public import B23_4_RatWordPrep_SeqCmp_WordPacketResources_141
public import B23_4_RatWordPrep_SeqCmp_WordFinishHalt_134

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

theorem actual_halt_resources (caller : Statement C) (before : State C) (bits : List Bool)
    (active : before.l=some (.finalize .clear)) (empty : before.stk 3=[]) (output : before.stk 13=bits) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=none ∧ TM2.step (program caller) final=none ∧
      final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=RootB234.WordFinalizer.cells before.stk bits [] [] ∧
      RunBounds caller run (12*scale before) (18*scale before) (84*scale before) ∧
      traceClockSum (program caller) run.trace≤1008*(scale before)^2 ∧
      run.trace.length+traceClockSum (program caller) run.trace≤1020*(scale before)^2 := by
  let iso := OddsInit.packetIso C
  let memory := iso.symm before.var
  let old := RootB234.WordFinalizer.program (C := PacketContext C)
  obtain ⟨trace,final,facts⟩ := RootB234.WordFinalizer.actual_polynomial before.stk memory (before.stk 0) bits
  have same (point : RootB234.WordFinalizer.Label) :
      program caller (finalLabel point)=LabelMap.statement finalLabel (StoreIso.statement iso (old point)) := rfl
  have path := transport_path iso finalLabel old caller (fun _ => True) trace _ final
    facts.first facts.chain facts.last (by intros; trivial) (by intro point _; exact same point)
  let run : Segment caller before (mappedCfg iso finalLabel final) :=
    ⟨trace.map (mappedCfg iso finalLabel),path.1.trans
      (congrArg some (final_shared before bits active empty output)),path.2.1,path.2.2⟩
  have actualScale : RootB234.WordFinalizer.scale before.stk (before.stk 0) bits≤3*scale before := by
    unfold RootB234.WordFinalizer.scale scale
    have oldMass := RatInput.Encoder.point_mass before.stk 0
    have outputMass := RatInput.Encoder.point_mass before.stk 13
    rw [output] at outputMass
    omega
  have halted : (mappedCfg iso finalLabel final).l=none := by
    change final.l.map finalLabel=none
    rw [facts.halted]
    rfl
  have bounds : RunBounds caller run (12*scale before) (18*scale before) (84*scale before) := by
    constructor
    · have count : run.trace.length≤4*RootB234.WordFinalizer.scale before.stk (before.stk 0) bits := by
        simpa only [run,List.length_map] using facts.time
      omega
    · intro current member slot
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      have bound := (facts.boundary original present).2.1 slot
      exact bound.trans (by omega)
    · intro current member point selected node inside slot
      change current∈(trace.map (mappedCfg iso finalLabel)).dropLast at member
      rw [←List.map_dropLast] at member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      change original.l.map finalLabel=some point at selected
      obtain ⟨oldPoint,oldActive,renamed⟩ := Option.map_eq_some_iff.mp selected
      rw [←renamed] at inside
      change node∈AuxWorkspace.nodes (program caller (finalLabel oldPoint)) (iso original.var) original.stk at inside
      rw [mapped_nodes iso finalLabel old caller oldPoint original.var original.stk (same oldPoint)] at inside
      obtain ⟨oldNode,oldInside,rfl⟩ := List.mem_map.mp inside
      have bound := ((facts.internal original present oldPoint oldActive).1 oldNode oldInside).2.1 slot
      change (oldNode.2 slot).length≤18*scale before
      omega
    · intro current member point selected
      change current∈(trace.map (mappedCfg iso finalLabel)).dropLast at member
      rw [←List.map_dropLast] at member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      change original.l.map finalLabel=some point at selected
      obtain ⟨oldPoint,oldActive,renamed⟩ := Option.map_eq_some_iff.mp selected
      rw [←renamed]
      change ScannerStatement.clock (program caller (finalLabel oldPoint)) (iso original.var) original.stk≤_
      rw [same,clock_labelMap,clock_storeIso]
      have bound := (facts.internal original present oldPoint oldActive).2.2
      change ScannerStatement.clock (RootB234.WordFinalizer.program oldPoint) original.var original.stk≤84*scale before
      omega
  refine ⟨mappedCfg iso finalLabel final,run,halted,step_of_halted _ _ halted,?_,facts.contents,bounds,?_,?_⟩
  · exact congrArg (fun context : PacketContext C => context.2.2.2) facts.context
  · exact bounds.clockSum.trans_eq (by ring)
  · have positive : 1≤scale before := by unfold scale; omega
    have charged := bounds.charge
    nlinarith

end B23_4_RatWordPrep.WordFinish.Resources
