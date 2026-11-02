module
public import Structure.PA17_TM_RatArithmetic_CachedPass_036c

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
open PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticAllocatePass023 (pushField)

/-- A compile-time-cap foreach compiler. The only loop predicate is the
actual source flag. Ending/growth/fee below occur solely in trace proofs. -/
def sourceLoopCap (s : Nat) : Nat := totalStates 1 s
attribute [local implicit_reducible] sourceLoopCap

def sourceFamily (s : Nat) (hs : 3≤s) (cycle : Machine s) (phase : Fin 2) : Machine s :=
  if phase.val=0 then padMachine hs probeMachine else cycle

def sourcePorts (s : Nat) (phase : Fin 2) (q : Fin (s+1)) : Option (Fin 2 × Fin (s+1)) :=
  if phase.val=0 then (if q.val=3 then some (1,0) else none) else some (0,0)

def sourceLoopMachine (s : Nat) (hs : 3≤s) (cycle : Machine s) : Machine (sourceLoopCap s) :=
  blockMachine (sourceFamily s hs cycle) (sourcePorts s)

def sourceCfg (s : Nat) (phase : Fin 2) (state : MachineState s) : MachineState (sourceLoopCap s) :=
  blockCfg (s:=s) phase state

def sourceTape (left : List Bool) (n : Nat) (earlier remaining : List Bool)
    (ending : Nat → List Bool) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (PSTRTMRawNat010.leftBlocks earlier.reverse++left)
    (nxStream remaining (false::ending n))

def sourceDoneTape (left : List Bool) (n : Nat) (processed : List Bool)
    (ending : Nat → List Bool) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (pushField left processed) (false::ending n)

/-- The contract must exhibit a run of the same fixed cycle code. It is
not an executable oracle; actual cache navigation/expansion establishes it. -/
def SourceCycleContract (s : Nat) (cycle : Machine s) (k surcharge : Nat)
    (ending : Nat → List Bool) : Prop :=
  ∀ archive later n, BoundedRun (s:=s) cycle
    (Turing.Tape.mk₂ (false::archive) (nxStream later (false::ending n))) (Fin.last s)
    (Turing.Tape.mk₂ (true::archive) (nxStream later (false::ending (n+k))))
    (4*later.length+2*n+4*k+surcharge)

theorem sourceForeach_runsFrom (s : Nat) (hs : 3≤s) (cycle : Machine s)
    (k surcharge : Nat) (ending : Nat → List Bool)
    (cycleBound : SourceCycleContract s cycle k surcharge ending)
    (left : List Bool) (n : Nat) (earlier remaining : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom (sourceLoopMachine s hs cycle)
      (sourceCfg s 0 ⟨0,sourceTape left n earlier remaining ending⟩) trace
      (sourceCfg s 0 (padCfg hs
        ⟨(1 : Fin 4),sourceDoneTape left (n+k*remaining.length) (earlier++remaining) ending⟩)) ∧
      trace.length≤remaining.length*(2*n+(2*k+4)*remaining.length+4*k+surcharge+4)+2 := by
  induction remaining generalizing n earlier with
  | nil =>
    let leftL := PSTRTMRawNat010.leftBlocks earlier.reverse++left
    have hp := pad_runsFrom (hs) probeMachine _ _ _ (probeEnd_runsFrom leftL (ending n))
    have hseg := block_segment (sourceFamily s hs cycle) (sourcePorts s) (0 : Fin 2)
      (padCfg (hs) (probeState 0 leftL (false::false::ending n)))
      (padCfg (hs) (probeState 1 (false::leftL) (false::ending n)))
      ((probeEndTrace leftL (ending n)).map (padCfg (hs))) hp
    let tr : List (MachineState (sourceLoopCap s)) :=
      ((probeEndTrace leftL (ending n)).map (padCfg (hs))).map
        (blockCfg (s:=s) (0 : Fin 2))
    refine ⟨tr,?_,?_⟩
    · refine ⟨?_,hseg.2.1,?_,?_⟩
      · simpa only [tr,sourceCfg,sourceTape,nxStream,PSTRTMIncrement009.blocks,List.flatMap_nil,
          List.nil_append,probeState,PA17TMRatArithmeticBookmark014.pad_zero,leftL] using hseg.1
      · simpa only [tr,sourceCfg,sourceDoneTape,pushField,probeState,leftL,List.append_nil,List.length_nil,
          Nat.mul_zero,Nat.add_zero] using hseg.2.2
      · have hh := block_halt (sourceFamily s hs cycle) (sourcePorts s) (0 : Fin 2)
          (padCfg (hs) (probeState 1 (false::leftL) (false::ending n))) hp.2.2.2 (by rfl)
        simpa only [sourceLoopMachine,sourceCfg,sourceDoneTape,pushField,probeState,leftL,List.append_nil,
          List.length_nil,Nat.mul_zero,Nat.add_zero] using hh
    · change (((probeEndTrace leftL (ending n)).map (padCfg (hs))).map
        (blockCfg (s:=s) (0 : Fin 2))).length≤_
      rw [List.length_map,List.length_map]
      change 2≤_
      simp
  | cons bit later ih =>
    let leftL := PSTRTMRawNat010.leftBlocks earlier.reverse++left
    let right := nxStream later (false::ending n)
    have hp := pad_runsFrom (hs) probeMachine _ _ _ (probe_runsFrom leftL bit right)
    have hps := block_segment (sourceFamily s hs cycle) (sourcePorts s) (0 : Fin 2)
      (padCfg (hs) (probeState 0 leftL (bit::true::right)))
      (padCfg (hs) (probeState 3 (false::bit::leftL) right))
      ((probeTrace leftL bit right).map (padCfg (hs))) hp
    obtain ⟨tc,hc,hlc⟩ := cycleBound (bit::leftL) later n
    have hcs := block_segment (sourceFamily s hs cycle) (sourcePorts s) (1 : Fin 2)
      ⟨0,Turing.Tape.mk₂ (false::bit::leftL) right⟩
      ⟨Fin.last (s),Turing.Tape.mk₂ (true::bit::leftL) (nxStream later (false::ending (n+k)))⟩ tc hc
    have hpc : Turing.TM0.step (sourceLoopMachine s hs cycle)
        (sourceCfg s 0 (padCfg (hs) (probeState 3 (false::bit::leftL) right))) =
        some (sourceCfg s 1 ⟨0,Turing.Tape.mk₂ (false::bit::leftL) right⟩) := by
      apply block_transfer (sourceFamily s hs cycle) (sourcePorts s) (0 : Fin 2)
        (padCfg (hs) (probeState 3 (false::bit::leftL) right)) (1,0) hp.2.2.2
      rfl
    have hstart : sourceTape left (n+k) (earlier++[bit]) later ending =
        Turing.Tape.mk₂ (true::bit::leftL) (nxStream later (false::ending (n+k))) := by
      simp only [sourceTape,leftBlocks_snoc,List.cons_append,leftL]
    have hn : n+k+k*later.length=n+k*(bit::later).length := by
      simp only [List.length_cons]
      ring
    have hend : sourceDoneTape left (n+k+k*later.length) ((earlier++[bit])++later) ending =
        sourceDoneTape left (n+k*(bit::later).length) (earlier++bit::later) ending := by
      rw [hn]
      simp only [List.append_assoc,List.singleton_append]
    obtain ⟨tr,hr,hlr⟩ := ih (n+k) (earlier++[bit])
    rw [hstart,hend] at hr
    have hcr : Turing.TM0.step (sourceLoopMachine s hs cycle)
        (sourceCfg s 1 ⟨Fin.last (s),Turing.Tape.mk₂ (true::bit::leftL)
          (nxStream later (false::ending (n+k)))⟩) =
        some (sourceCfg s 0 ⟨0,Turing.Tape.mk₂ (true::bit::leftL)
          (nxStream later (false::ending (n+k)))⟩) := by
      apply block_transfer (sourceFamily s hs cycle) (sourcePorts s) (1 : Fin 2)
        ⟨Fin.last (s),Turing.Tape.mk₂ (true::bit::leftL) (nxStream later (false::ending (n+k)))⟩
        (0,0) hc.2.2.2
      rfl
    let tp : List (MachineState (sourceLoopCap s)) :=
      ((probeTrace leftL bit right).map (padCfg (hs))).map (blockCfg (s:=s) (0 : Fin 2))
    let tb : List (MachineState (sourceLoopCap s)) := tc.map (blockCfg (s:=s) (1 : Fin 2))
    have hfirst := segment_append (sourceLoopMachine s hs cycle) _ _ _ _ tp tb hps hcs hpc
    have hfull := segment_append (sourceLoopMachine s hs cycle) _ _ _ _ (tp++tb) tr
      hfirst ⟨hr.1,hr.2.1,hr.2.2.1⟩ hcr
    refine ⟨(tp++tb)++tr,?_,?_⟩
    · refine ⟨?_,hfull.2.1,hfull.2.2,hr.2.2.2⟩
      simpa only [sourceCfg,sourceTape,nxStream,probeState,PA17TMRatArithmeticBookmark014.pad_zero,
        PSTRTMIncrement009.blocks,List.flatMap_cons,List.cons_append,List.nil_append,leftL,right] using hfull.1
    · have htp : tp.length=4 := by
        change (((probeTrace leftL bit right).map (padCfg (hs))).map
          (blockCfg (s:=s) (0 : Fin 2))).length=4
        rw [List.length_map,List.length_map]
        rfl
      have htb : tb.length=tc.length := List.length_map _
      rw [List.length_append,List.length_append,htp,htb]
      simp only [List.length_cons]
      nlinarith [Nat.zero_le (k*later.length)]

def sourceExit (s : Nat) (hs : 3≤s) : Fin (sourceLoopCap s+1) :=
  label (p:=1) (s:=s) 0 (padLabel hs (1 : Fin 4))

theorem source_foreach_bounded (s : Nat) (hs : 3≤s) (cycle : Machine s)
    (k surcharge : Nat) (ending : Nat → List Bool)
    (cycleBound : SourceCycleContract s cycle k surcharge ending)
    (left digits : List Bool) (n : Nat) :
    BoundedRun (s:=sourceLoopCap s) (sourceLoopMachine s hs cycle)
      (Turing.Tape.mk₂ left (nxStream digits (false::ending n))) (sourceExit s hs)
      (Turing.Tape.mk₂ (pushField left digits) (false::ending (n+k*digits.length)))
      (digits.length*(2*n+(2*k+4)*digits.length+4*k+surcharge+4)+2) := by
  obtain ⟨trace,hr,hl⟩ := sourceForeach_runsFrom s hs cycle k surcharge ending cycleBound left n [] digits
  change PSTRTMSeq005.RunsFrom (sourceLoopMachine s hs cycle)
    (blockCfg (s:=s) (0 : Fin 2) ⟨0,Turing.Tape.mk₂ left (nxStream digits (false::ending n))⟩) trace
    (blockCfg (s:=s) (0 : Fin 2) (padCfg hs
      ⟨(1 : Fin 4),Turing.Tape.mk₂ (pushField left digits) (false::ending (n+k*digits.length))⟩)) at hr
  rw [blockCfg_zero] at hr
  exact ⟨trace,hr,hl⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
