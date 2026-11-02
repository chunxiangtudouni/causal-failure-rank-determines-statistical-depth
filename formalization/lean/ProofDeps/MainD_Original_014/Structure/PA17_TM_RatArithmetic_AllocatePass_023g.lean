module
public import Structure.PA17_TM_RatArithmetic_AllocatePass_023f

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
open PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018

def fieldCap (k : Nat) : Nat := totalStates 1 (cycleCap k)
attribute [local implicit_reducible] fieldCap
def passFieldFamily (k : Nat) (cycle : Machine (cycleCap k)) (phase : Fin 2) : Machine (cycleCap k) :=
  if phase.val=0 then padMachine (cycleCap_ge k) probeMachine else cycle
def passFieldPorts (k : Nat) (phase : Fin 2) (q : Fin (cycleCap k+1)) :
    Option (Fin 2 × Fin (cycleCap k+1)) :=
  if phase.val=0 then (if q.val=3 then some (1,0) else none) else some (0,0)
def fieldPassMachine (k : Nat) (cycle : Machine (cycleCap k)) : Machine (fieldCap k) :=
  blockMachine (passFieldFamily k cycle) (passFieldPorts k)
def passFieldCfg (k : Nat) (phase : Fin 2) (state : MachineState (cycleCap k)) : MachineState (fieldCap k) :=
  blockCfg (s:=cycleCap k) phase state

def passFieldTape (left : List Bool) (n : Nat) (earlier remaining : List Bool)
    (rest : List Bool → List Bool) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (PSTRTMRawNat010.leftBlocks earlier.reverse++left)
    (nxStream remaining (false::rest (gapTail n)))
def passFieldDoneTape (left : List Bool) (n : Nat) (processed : List Bool)
    (rest : List Bool → List Bool) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (pushField left processed) (false::rest (gapTail n))

/-- Actual source-controlled foreach. Only an observed TRUE flag executes
the expansion cycle. FALSE stops at the real following boundary. No width,
fuel, counter h, gap length or saved-memory tuple is an executable input. -/
theorem fieldPass_runsFrom (k : Nat) (out back : Machine 26) (outPort backPort : Fin 27)
    (rest : List Bool → List Bool) (footer : List Bool → List Bool → List Bool)
    (followingWidth : Nat) (routes : PassRoutes out back outPort backPort rest footer followingWidth)
    (left : List Bool) (n : Nat) (earlier remaining : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom (fieldPassMachine k (passCycleMachine k out back))
      (passFieldCfg k 0 ⟨0,passFieldTape left n earlier remaining rest⟩) trace
      (passFieldCfg k 0 (padCfg (cycleCap_ge k)
        ⟨(1 : Fin 4),passFieldDoneTape left (n+k*remaining.length) (earlier++remaining) rest⟩)) ∧
      trace.length≤remaining.length*(2*n+(2*k+4)*remaining.length+4*followingWidth+4*k+51)+2 := by
  induction remaining generalizing n earlier with
  | nil =>
    let leftL := PSTRTMRawNat010.leftBlocks earlier.reverse++left
    have hp := pad_runsFrom (cycleCap_ge k) probeMachine _ _ _ (probeEnd_runsFrom leftL (rest (gapTail n)))
    have hs := block_segment (passFieldFamily k (passCycleMachine k out back)) (passFieldPorts k) (0 : Fin 2)
      (padCfg (cycleCap_ge k) (probeState 0 leftL (false::false::rest (gapTail n))))
      (padCfg (cycleCap_ge k) (probeState 1 (false::leftL) (false::rest (gapTail n))))
      ((probeEndTrace leftL (rest (gapTail n))).map (padCfg (cycleCap_ge k))) hp
    let tr : List (MachineState (fieldCap k)) :=
      ((probeEndTrace leftL (rest (gapTail n))).map (padCfg (cycleCap_ge k))).map
        (blockCfg (s:=cycleCap k) (0 : Fin 2))
    refine ⟨tr,?_,?_⟩
    · refine ⟨?_,hs.2.1,?_,?_⟩
      · simpa only [tr,passFieldCfg,passFieldTape,nxStream,PSTRTMIncrement009.blocks,List.flatMap_nil,
          List.nil_append,probeState,PA17TMRatArithmeticBookmark014.pad_zero,leftL] using hs.1
      · simpa only [tr,passFieldCfg,passFieldDoneTape,pushField,probeState,leftL,List.append_nil,List.length_nil,
          Nat.mul_zero,Nat.add_zero] using hs.2.2
      · have hh := block_halt (passFieldFamily k (passCycleMachine k out back)) (passFieldPorts k) (0 : Fin 2)
          (padCfg (cycleCap_ge k) (probeState 1 (false::leftL) (false::rest (gapTail n)))) hp.2.2.2 (by rfl)
        simpa only [fieldPassMachine,passFieldCfg,passFieldDoneTape,pushField,probeState,leftL,List.append_nil,
          List.length_nil,Nat.mul_zero,Nat.add_zero] using hh
    · change (((probeEndTrace leftL (rest (gapTail n))).map (padCfg (cycleCap_ge k))).map
        (blockCfg (s:=cycleCap k) (0 : Fin 2))).length≤_
      rw [List.length_map,List.length_map]
      change 2≤_
      simp
  | cons bit later ih =>
    let leftL := PSTRTMRawNat010.leftBlocks earlier.reverse++left
    let right := nxStream later (false::rest (gapTail n))
    have hp := pad_runsFrom (cycleCap_ge k) probeMachine _ _ _ (probe_runsFrom leftL bit right)
    have hps := block_segment (passFieldFamily k (passCycleMachine k out back)) (passFieldPorts k) (0 : Fin 2)
      (padCfg (cycleCap_ge k) (probeState 0 leftL (bit::true::right)))
      (padCfg (cycleCap_ge k) (probeState 3 (false::bit::leftL) right))
      ((probeTrace leftL bit right).map (padCfg (cycleCap_ge k))) hp
    obtain ⟨tc,hc,hlc⟩ := passCycle_bounded k out back outPort backPort rest footer followingWidth routes (bit::leftL) later n
    have hcs := block_segment (passFieldFamily k (passCycleMachine k out back)) (passFieldPorts k) (1 : Fin 2)
      ⟨0,Turing.Tape.mk₂ (false::bit::leftL) right⟩
      ⟨Fin.last (cycleCap k),Turing.Tape.mk₂ (true::bit::leftL) (nxStream later (false::rest (gapTail (n+k))))⟩ tc hc
    have hpc : Turing.TM0.step (fieldPassMachine k (passCycleMachine k out back))
        (passFieldCfg k 0 (padCfg (cycleCap_ge k) (probeState 3 (false::bit::leftL) right))) =
        some (passFieldCfg k 1 ⟨0,Turing.Tape.mk₂ (false::bit::leftL) right⟩) := by
      apply block_transfer (passFieldFamily k (passCycleMachine k out back)) (passFieldPorts k) (0 : Fin 2)
        (padCfg (cycleCap_ge k) (probeState 3 (false::bit::leftL) right)) (1,0) hp.2.2.2
      rfl
    have hstart : passFieldTape left (n+k) (earlier++[bit]) later rest =
        Turing.Tape.mk₂ (true::bit::leftL) (nxStream later (false::rest (gapTail (n+k)))) := by
      simp only [passFieldTape,leftBlocks_snoc,List.cons_append,leftL]
    have hn : n+k+k*later.length=n+k*(bit::later).length := by
      simp only [List.length_cons]
      ring
    have hend : passFieldDoneTape left (n+k+k*later.length) ((earlier++[bit])++later) rest =
        passFieldDoneTape left (n+k*(bit::later).length) (earlier++bit::later) rest := by
      rw [hn]
      simp only [List.append_assoc,List.singleton_append]
    obtain ⟨tr,hr,hlr⟩ := ih (n+k) (earlier++[bit])
    rw [hstart,hend] at hr
    have hcr : Turing.TM0.step (fieldPassMachine k (passCycleMachine k out back))
        (passFieldCfg k 1 ⟨Fin.last (cycleCap k),Turing.Tape.mk₂ (true::bit::leftL)
          (nxStream later (false::rest (gapTail (n+k))))⟩) =
        some (passFieldCfg k 0 ⟨0,Turing.Tape.mk₂ (true::bit::leftL)
          (nxStream later (false::rest (gapTail (n+k))))⟩) := by
      apply block_transfer (passFieldFamily k (passCycleMachine k out back)) (passFieldPorts k) (1 : Fin 2)
        ⟨Fin.last (cycleCap k),Turing.Tape.mk₂ (true::bit::leftL) (nxStream later (false::rest (gapTail (n+k))))⟩
        (0,0) hc.2.2.2
      rfl
    let tp : List (MachineState (fieldCap k)) :=
      ((probeTrace leftL bit right).map (padCfg (cycleCap_ge k))).map (blockCfg (s:=cycleCap k) (0 : Fin 2))
    let tb : List (MachineState (fieldCap k)) := tc.map (blockCfg (s:=cycleCap k) (1 : Fin 2))
    have hfirst := segment_append (fieldPassMachine k (passCycleMachine k out back)) _ _ _ _ tp tb hps hcs hpc
    have hfull := segment_append (fieldPassMachine k (passCycleMachine k out back)) _ _ _ _ (tp++tb) tr
      hfirst ⟨hr.1,hr.2.1,hr.2.2.1⟩ hcr
    refine ⟨(tp++tb)++tr,?_,?_⟩
    · refine ⟨?_,hfull.2.1,hfull.2.2,hr.2.2.2⟩
      simpa only [passFieldCfg,passFieldTape,nxStream,probeState,PA17TMRatArithmeticBookmark014.pad_zero,
        PSTRTMIncrement009.blocks,List.flatMap_cons,List.cons_append,List.nil_append,leftL,right] using hfull.1
    · have htp : tp.length=4 := by
        change (((probeTrace leftL bit right).map (padCfg (cycleCap_ge k))).map
          (blockCfg (s:=cycleCap k) (0 : Fin 2))).length=4
        rw [List.length_map,List.length_map]
        rfl
      have htb : tb.length=tc.length := List.length_map _
      rw [List.length_append,List.length_append,htp,htb]
      simp only [List.length_cons]
      nlinarith [Nat.zero_le (k*later.length)]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
