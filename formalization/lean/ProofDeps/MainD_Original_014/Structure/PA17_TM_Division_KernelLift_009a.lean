module
public import Structure.PA17_TM_Division_Loop_002h

/-! Actual source/commit ports and overlapping trace composition. Every
HALT-to-port step is present; the next entry configuration is counted once. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionKernelLift009

open PA17TMDivisionLoop002 PA17TMDivisionCompose006

theorem liftTrace_length {a : Nat} (phase : Fin 17) (h : a ≤ 33)
    (trace : List (MachineState a)) : (liftTrace phase h trace).length = trace.length := by
  change (trace.map (fun state => blockCfg phase (padCfg h state))).length = trace.length
  exact List.length_map _

def splice {states : Nat} (xs ys : List (MachineState states)) : List (MachineState states) :=
  xs.dropLast ++ ys

theorem splice_segment {states : Nat} (machine : Machine states)
    (first middle last : MachineState states) (xs ys : List (MachineState states))
    (hx : Segment machine first xs middle) (hy : Segment machine middle ys last) :
    Segment machine first (splice xs ys) last := by
  have ex : xs.dropLast ++ [middle] = xs := List.dropLast_append_getLast? middle hx.2.2
  have ey : middle :: ys.tail = ys := List.cons_head?_tail hy.1
  refine ⟨?_,?_,?_⟩
  · cases xs with
    | nil => simp [Segment] at hx
    | cons a later =>
      cases later with
      | nil =>
        have ha : a = first := Option.some.inj hx.1
        have hm : a = middle := Option.some.inj hx.2.2
        simpa only [splice,List.dropLast_singleton,List.nil_append,← ha,hm] using hy.1
      | cons b later =>
        simpa only [splice,List.dropLast_cons_cons,List.cons_append,List.head?_cons] using hx.1
  · have cx : (xs.dropLast ++ [middle]).IsChain (fun before after => Turing.TM0.step machine before = some after) :=
      ex.symm ▸ hx.2.1
    have cy : ([middle] ++ ys.tail).IsChain (fun before after => Turing.TM0.step machine before = some after) := by
      simpa only [List.singleton_append,ey] using hy.2.1
    have joined := cx.append_overlap cy (by simp)
    simpa only [splice,List.append_assoc,List.singleton_append,ey] using joined
  · simp only [splice,List.getLast?_append,hy.2.2,Option.some_or]

theorem splice_length {states : Nat} (machine : Machine states)
    (first last : MachineState states) (xs ys : List (MachineState states))
    (hx : Segment machine first xs last) :
    (splice xs ys).length+1 = xs.length+ys.length := by
  have hn : xs ≠ [] := by intro he; simp [Segment,he] at hx
  have hp := List.length_pos_iff.mpr hn
  simp only [splice,List.length_append,List.length_dropLast]
  omega

theorem component_hop {a : Nat} (phase : Fin 17) (h : a ≤ 33) (machine : Machine a)
    (heq : loopMachines phase = padMachine h machine)
    (first last : MachineState a) (trace : List (MachineState a))
    (run : PSTRTMSeq005.RunsFrom machine first trace last)
    (targetPhase : Fin 17) (targetLabel : Fin 34)
    (port : loopPorts phase (padLabel h last.q) = some (targetPhase,targetLabel)) :
    Segment loopMachine (liftCfg phase h first)
      (liftTrace phase h trace ++ [phaseCfg targetPhase targetLabel last.Tape])
      (phaseCfg targetPhase targetLabel last.Tape) :=
  prepend_component phase h machine heq first last trace run targetPhase targetLabel port
    (phaseCfg targetPhase targetLabel last.Tape) [phaseCfg targetPhase targetLabel last.Tape]
    ⟨rfl,List.IsChain.singleton _,rfl⟩

def shiftPhase (zeroMode : Bool) : Fin 17 := if zeroMode then 5 else 6

def shiftEntry (bit : Bool) : Fin 34 :=
  padLabel (by decide : 19 ≤ 33) (PSTRTMShiftColumnCode065.readA bit)

theorem source_bit_hop (zeroMode bit : Bool) (remaining quotient context : List Bool)
    (resident : List (Bool × Bool)) (suffix : List Bool) :
    ∃ trace : List (MachineState 577),
      Segment loopMachine
        (phaseCfg (readPhase zeroMode) 0 (loopTape context (archiveFor (bit::remaining) quotient) resident suffix))
        trace
        (phaseCfg (shiftPhase zeroMode) (shiftEntry bit)
          (loopTape context (archiveFor (bit::remaining) quotient) resident suffix)) ∧
      trace.length ≤ 8*(1+remaining.length+quotient.length)+10 := by
  let archive := archiveFor (bit::remaining) quotient
  let first := sourceState 0 (frameLeft context archive) (residentRight resident suffix)
  let last := sourceState (sourceHalt (bitMode bit)) (frameLeft context archive) (residentRight resident suffix)
  let trace := sourceTrace context archive (residentRight resident suffix)
  have run : PSTRTMSeq005.RunsFrom sourceMachine first trace last := by
    dsimp [first,last,trace,archive]
    simpa only [frameLeft,archiveFor_read_bit] using
      source_runsFrom context (archiveFor (bit::remaining) quotient) (residentRight resident suffix)
  have heq : loopMachines (readPhase zeroMode) = padMachine (by decide : 27 ≤ 33) sourceMachine := by
    cases zeroMode <;> rfl
  have port : loopPorts (readPhase zeroMode) (padLabel (by decide : 27 ≤ 33) last.q) =
      some (shiftPhase zeroMode,shiftEntry bit) := by
    cases zeroMode <;> cases bit <;> rfl
  have seg := component_hop (readPhase zeroMode) (by decide : 27 ≤ 33) sourceMachine heq
    first last trace run (shiftPhase zeroMode) (shiftEntry bit) port
  refine ⟨liftTrace (readPhase zeroMode) (by decide : 27 ≤ 33) trace ++
    [phaseCfg (shiftPhase zeroMode) (shiftEntry bit) last.Tape],?_,?_⟩
  · exact seg
  · have ht := source_length_le context archive (residentRight resident suffix)
    simp only [List.length_append,List.length_singleton,liftTrace_length]
    dsimp [trace,archive] at ht ⊢
    rw [archiveFor_length,List.length_cons] at ht
    omega

theorem exhausted_segment (zeroMode : Bool) (quotient context : List Bool)
    (resident : List (Bool × Bool)) (suffix : List Bool) :
    ∃ trace : List (MachineState 577),
      Segment loopMachine
        (phaseCfg (readPhase zeroMode) 0 (loopTape context (archiveFor [] quotient) resident suffix))
        trace (phaseCfg 16 0 (loopTape context (archiveFor [] quotient) resident suffix)) ∧
      trace.length ≤ 8*quotient.length+10 := by
  let archive := archiveFor [] quotient
  let first := sourceState 0 (frameLeft context archive) (residentRight resident suffix)
  let last := sourceState (sourceHalt 0) (frameLeft context archive) (residentRight resident suffix)
  let trace := sourceTrace context archive (residentRight resident suffix)
  have run : PSTRTMSeq005.RunsFrom sourceMachine first trace last := by
    dsimp [first,last,trace,archive]
    simpa only [frameLeft,archiveFor_read_none] using
      source_runsFrom context (archiveFor [] quotient) (residentRight resident suffix)
  have heq : loopMachines (readPhase zeroMode) = padMachine (by decide : 27 ≤ 33) sourceMachine := by
    cases zeroMode <;> rfl
  have port : loopPorts (readPhase zeroMode) (padLabel (by decide : 27 ≤ 33) last.q) = some (16,0) := by
    cases zeroMode <;> rfl
  have seg := component_hop (readPhase zeroMode) (by decide : 27 ≤ 33) sourceMachine heq
    first last trace run 16 0 port
  refine ⟨liftTrace (readPhase zeroMode) (by decide : 27 ≤ 33) trace ++ [phaseCfg 16 0 last.Tape],?_,?_⟩
  · exact seg
  · have ht := source_length_le context archive (residentRight resident suffix)
    simp only [List.length_append,List.length_singleton,liftTrace_length]
    dsimp [trace,archive] at ht ⊢
    rw [archiveFor_length,List.length_nil,Nat.zero_add] at ht
    omega

theorem commit_hop (phase nextRead : Fin 17) (emit : Bool)
    (heq : loopMachines phase = padMachine (by decide : 33 ≤ 33) (commitMachine emit))
    (port : loopPorts phase 26 = some (nextRead,0))
    (bit : Bool) (remaining quotient context : List Bool)
    (resident : List (Bool × Bool)) (suffix : List Bool) :
    ∃ trace : List (MachineState 577),
      Segment loopMachine
        (phaseCfg phase 0 (loopTape context (archiveFor (bit::remaining) quotient) resident suffix))
        trace
        (phaseCfg nextRead 0 (loopTape context (archiveFor remaining (emit::quotient)) resident suffix)) ∧
      trace.length ≤ 8*(1+remaining.length+quotient.length)+16 := by
  let archive := archiveFor (bit::remaining) quotient
  let nextArchive := archiveFor remaining (emit::quotient)
  let first := commitState 0 (frameLeft context archive) (residentRight resident suffix)
  let last := commitState 26 (frameLeft context nextArchive) (residentRight resident suffix)
  let trace := commitTrace emit context archive (residentRight resident suffix)
  have run : PSTRTMSeq005.RunsFrom (commitMachine emit) first trace last := by
    have hr := commit_runsFrom emit context archive (residentRight resident suffix)
    dsimp [archive] at hr
    rw [archiveFor_commit_mode,archiveFor_commit] at hr
    exact hr
  have hp : loopPorts phase (padLabel (by decide : 33 ≤ 33) last.q) = some (nextRead,0) := port
  have seg := component_hop phase (by decide : 33 ≤ 33) (commitMachine emit) heq
    first last trace run nextRead 0 hp
  refine ⟨liftTrace phase (by decide : 33 ≤ 33) trace ++ [phaseCfg nextRead 0 last.Tape],?_,?_⟩
  · exact seg
  · have ht := commit_length_le emit context archive (residentRight resident suffix)
    simp only [List.length_append,List.length_singleton,liftTrace_length]
    dsimp [trace,archive] at ht ⊢
    rw [archiveFor_length,List.length_cons] at ht
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionKernelLift009
