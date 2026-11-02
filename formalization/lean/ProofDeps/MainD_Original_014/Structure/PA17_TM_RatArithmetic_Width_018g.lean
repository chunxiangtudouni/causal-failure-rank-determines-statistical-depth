module
public import Structure.PA17_TM_RatArithmetic_Width_018f

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
open PA17TMDivisionCompose006

def probeMachine : Machine 3 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => if symbol then some (2,.write false) else none
  | 2 => some (3,.move .right)
  | _ => none

def probeState (q : Fin 4) (left right : List Bool) : MachineState 3 := ⟨q,Turing.Tape.mk₂ left right⟩
def probeTrace (left : List Bool) (bit : Bool) (right : List Bool) : List (MachineState 3) :=
  [probeState 0 left (bit::true::right),probeState 1 (bit::left) (true::right),
   probeState 2 (bit::left) (false::right),probeState 3 (false::bit::left) right]

theorem probe_runsFrom (left : List Bool) (bit : Bool) (right : List Bool) :
    PSTRTMSeq005.RunsFrom probeMachine (probeState 0 left (bit::true::right))
      (probeTrace left bit right) (probeState 3 (false::bit::left) right) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [probeTrace,List.isChain_cons_cons,Turing.TM0.step,probeMachine,probeState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,probeMachine,probeState]

def probeEndTrace (left suffix : List Bool) : List (MachineState 3) :=
  [probeState 0 left (false::false::suffix),probeState 1 (false::left) (false::suffix)]

theorem probeEnd_runsFrom (left suffix : List Bool) :
    PSTRTMSeq005.RunsFrom probeMachine (probeState 0 left (false::false::suffix))
      (probeEndTrace left suffix) (probeState 1 (false::left) (false::suffix)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [probeEndTrace,List.isChain_cons_cons,Turing.TM0.step,probeMachine,probeState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,probeMachine,probeState,Turing.Tape.mk₂]

def fieldFamily (cycle : Machine 75) (phase : Fin 2) : Machine 75 :=
  if phase.val=0 then padMachine (by decide : 3≤75) probeMachine else cycle
def fieldPorts (phase : Fin 2) (q : Fin 76) : Option (Fin 2 × Fin 76) :=
  if phase.val=0 then (if q.val=3 then some (1,0) else none) else some (0,0)
def fieldCounterMachine (cycle : Machine 75) : Machine 151 := blockMachine (fieldFamily cycle) fieldPorts
def fieldCfg (phase : Fin 2) (localState : MachineState 75) : MachineState 151 := blockCfg phase localState

def fieldTape (archive : Nat → List Bool) (n : Nat) (earlier remaining suffix : List Bool) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive n)
    (PSTRTMIncrement009.blocks remaining++false::false::suffix)
def fieldDoneTape (archive : Nat → List Bool) (n : Nat) (processed suffix : List Bool) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks processed.reverse++false::archive n)) (false::suffix)

theorem leftBlocks_snoc (earlier : List Bool) (bit : Bool) :
    PSTRTMRawNat010.leftBlocks (earlier++[bit]).reverse=true::bit::PSTRTMRawNat010.leftBlocks earlier.reverse := by
  simp [PSTRTMRawNat010.leftBlocks,List.reverse_append]

/-- The loop's read symbol selects count/EOF. Its width and unary value
appear only in this trace proof; the executable is the same fixed loop. -/
theorem fieldCounter_runsFrom (back forward : Machine 28) (backPort forwardPort : Fin 29)
    (archive : Nat → List Bool) (home : List Bool → List Bool) (previousWidth : Nat)
    (routes : RouteSpec back forward backPort forwardPort archive home previousWidth)
    (n : Nat) (earlier remaining suffix fieldTail : List Bool)
    (hfield : earlier++remaining=false::fieldTail) :
    ∃ trace, PSTRTMSeq005.RunsFrom (fieldCounterMachine (cycleMachine back forward))
      (fieldCfg 0 ⟨0,fieldTape archive n earlier remaining suffix⟩) trace
      (fieldCfg 0 (padCfg (by decide : 3≤75)
        (probeState 1
          (false::(PSTRTMRawNat010.leftBlocks (earlier++remaining).reverse++false::archive (n+remaining.length)))
          (false::suffix)))) ∧
      trace.length≤remaining.length*(2*n+4*earlier.length+6*remaining.length+4*previousWidth+64)+2 := by
  induction remaining generalizing n earlier with
  | nil =>
    let left := PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive n
    have hr := pad_runsFrom (by decide : 3≤75) probeMachine _ _ _ (probeEnd_runsFrom left suffix)
    have hs := block_segment (fieldFamily (cycleMachine back forward)) fieldPorts (0 : Fin 2)
      (padCfg (by decide : 3≤75) (probeState 0 left (false::false::suffix)))
      (padCfg (by decide : 3≤75) (probeState 1 (false::left) (false::suffix)))
      ((probeEndTrace left suffix).map (padCfg (by decide : 3≤75))) hr
    refine ⟨((probeEndTrace left suffix).map (padCfg (by decide : 3≤75))).map (blockCfg (0 : Fin 2)),?_,?_⟩
    · refine ⟨?_,hs.2.1,?_,?_⟩
      · exact hs.1
      · simpa only [fieldCfg,left,List.append_nil,List.length_nil,Nat.add_zero] using hs.2.2
      · have he := block_halt (fieldFamily (cycleMachine back forward)) fieldPorts (0 : Fin 2)
          (padCfg (by decide : 3≤75) (probeState 1 (false::left) (false::suffix))) hr.2.2.2 (by rfl)
        simpa only [fieldCounterMachine,fieldCfg,left,List.append_nil,List.length_nil,Nat.add_zero] using he
    · rw [List.length_map,List.length_map]
      change 2≤_
      simp
  | cons bit later ih =>
    let left := PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive n
    let right := PSTRTMIncrement009.blocks later++false::false::suffix
    have hp := pad_runsFrom (by decide : 3≤75) probeMachine _ _ _ (probe_runsFrom left bit right)
    have hps := block_segment (fieldFamily (cycleMachine back forward)) fieldPorts (0 : Fin 2)
      (padCfg (by decide : 3≤75) (probeState 0 left (bit::true::right)))
      (padCfg (by decide : 3≤75) (probeState 3 (false::bit::left) right))
      ((probeTrace left bit right).map (padCfg (by decide : 3≤75))) hp
    obtain ⟨tc,hc,hlc⟩ := cycle_runsFrom back forward backPort forwardPort archive home previousWidth
      routes n earlier bit later suffix fieldTail hfield
    have hcs := block_segment (fieldFamily (cycleMachine back forward)) fieldPorts (1 : Fin 2)
      ⟨0,Turing.Tape.mk₂ (false::bit::left) right⟩
      ⟨75,Turing.Tape.mk₂ (true::bit::(PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive (n+1))) right⟩ tc hc
    have hpc : Turing.TM0.step (fieldCounterMachine (cycleMachine back forward))
        (fieldCfg 0 (padCfg (by decide : 3≤75) (probeState 3 (false::bit::left) right))) =
        some (fieldCfg 1 ⟨0,Turing.Tape.mk₂ (false::bit::left) right⟩) := by
      apply block_transfer (fieldFamily (cycleMachine back forward)) fieldPorts (0 : Fin 2)
        (padCfg (by decide : 3≤75) (probeState 3 (false::bit::left) right)) (1,0) hp.2.2.2
      rfl
    have hstart : fieldTape archive (n+1) (earlier++[bit]) later suffix =
        Turing.Tape.mk₂ (true::bit::(PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive (n+1))) right := by
      simp only [fieldTape,leftBlocks_snoc,List.cons_append,right]
    have hn : n+1+later.length=n+(bit::later).length := by simp only [List.length_cons];omega
    have hend : fieldDoneTape archive (n+1+later.length) ((earlier++[bit])++later) suffix =
        fieldDoneTape archive (n+(bit::later).length) (earlier++bit::later) suffix := by
      rw [hn]
      simp only [List.append_assoc,List.singleton_append]
    have hfield' : (earlier++[bit])++later=false::fieldTail := by
      simpa only [List.append_assoc,List.singleton_append] using hfield
    obtain ⟨tr,hr,hlr⟩ := ih (n+1) (earlier++[bit]) hfield'
    change PSTRTMSeq005.RunsFrom (fieldCounterMachine (cycleMachine back forward))
      (fieldCfg 0 ⟨0,fieldTape archive (n+1) (earlier++[bit]) later suffix⟩) tr
      (fieldCfg 0 (padCfg (by decide : 3≤75) ⟨1,fieldDoneTape archive (n+1+later.length) ((earlier++[bit])++later) suffix⟩)) at hr
    rw [hstart,hend] at hr
    have hcr : Turing.TM0.step (fieldCounterMachine (cycleMachine back forward))
        (fieldCfg 1 ⟨75,Turing.Tape.mk₂ (true::bit::(PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive (n+1))) right⟩) =
        some (fieldCfg 0 ⟨0,Turing.Tape.mk₂ (true::bit::(PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive (n+1))) right⟩) := by
      apply block_transfer (fieldFamily (cycleMachine back forward)) fieldPorts (1 : Fin 2)
        ⟨75,Turing.Tape.mk₂ (true::bit::(PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive (n+1))) right⟩ (0,0) hc.2.2.2
      rfl
    let tp : List (MachineState 151) := ((probeTrace left bit right).map (padCfg (by decide : 3≤75))).map (blockCfg (0 : Fin 2))
    let tb : List (MachineState 151) := tc.map (blockCfg (1 : Fin 2))
    have hfirst := segment_append (fieldCounterMachine (cycleMachine back forward)) _ _ _ _ tp tb hps hcs hpc
    have hfull := segment_append (fieldCounterMachine (cycleMachine back forward)) _ _ _ _ (tp++tb) tr
      hfirst ⟨hr.1,hr.2.1,hr.2.2.1⟩ hcr
    refine ⟨(tp++tb)++tr,?_,?_⟩
    · refine ⟨?_,hfull.2.1,hfull.2.2,hr.2.2.2⟩
      exact hfull.1
    · have htp : tp.length=4 := by
        change ((((probeTrace left bit right).map (padCfg (by decide : 3≤75))).map (blockCfg (0 : Fin 2)))).length=4
        rw [List.length_map,List.length_map]
        rfl
      have htb : tb.length=tc.length := List.length_map _
      rw [List.length_append,List.length_append,htp,htb]
      simp only [List.length_append,List.length_cons,List.length_nil] at hlr ⊢
      nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
