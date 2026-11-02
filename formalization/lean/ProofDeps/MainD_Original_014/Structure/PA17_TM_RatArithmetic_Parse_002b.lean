module
public import Structure.PA17_TM_RatArithmetic_Parse_002a
public import Common.PSTR_TM_ContextRaw_028

/-! The frozen raw-field rotations need no left guard until their final
rewind. Stop by a real right move at the field end instead: arbitrary earlier
data and an arbitrary suffix, including a TRUE next-Rat tag, remain intact. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002

open PSTRTMRawNat010

def streamLabel (q : Fin 17) : Fin 18 := ⟨q.val,by omega⟩

def streamCfg (state : MachineState 16) : MachineState 17 := ⟨streamLabel state.q,state.Tape⟩

/-- Fixed eighteen labels. The original bit-length is consumed by the real
raw rotations. No caller length, numeric value or terminator flag is read. -/
def streamMachine : Machine 17 := fun q symbol =>
  if old : q.val < 17 then
    if q.val = 0 ∧ symbol = false then some (17,.move .right)
    else (rawNatMachine ⟨q.val,old⟩ symbol).map (fun (next,statement) => (streamLabel next,statement))
  else none

def StreamSafe (state : MachineState 16) : Prop := state.q.val ≠ 0 ∨ state.Tape.head = true

theorem stream_lookup (q : Fin 17) (symbol : Bool) (safe : q.val ≠ 0 ∨ symbol = true) :
    streamMachine (streamLabel q) symbol =
      (rawNatMachine q symbol).map (fun (next,statement) => (streamLabel next,statement)) := by
  fin_cases q <;> cases symbol <;> simp_all [streamMachine,streamLabel]

theorem stream_step (state : MachineState 16) (safe : StreamSafe state) :
    Turing.TM0.step streamMachine (streamCfg state) =
      (Turing.TM0.step rawNatMachine state).map streamCfg := by
  cases state with
  | mk q tape =>
    simp only [streamCfg,Turing.TM0.step]
    rw [stream_lookup q tape.head safe]
    cases hm : rawNatMachine q tape.head with
    | none => rfl
    | some result =>
      obtain ⟨next,statement⟩ := result
      cases statement <;> rfl

def processedLeft (base previous : List Bool) : List Bool := leftBlocks previous ++ base

def streamUnit (base : List Bool) (bit : Bool) (previous later suffix : List Bool) : List (MachineState 16) :=
  let k := later.length
  let left := processedLeft base previous
  let tail := later ++ suffix
  [state 0 left (List.replicate (k+1) true ++ false::bit::tail),
   state 1 left (false::(List.replicate k true ++ false::bit::tail))] ++
    scanRight k (false::left) (bit::tail) ++
  [state 3 (false::(List.replicate k true ++ false::left)) (bit::tail),
   state (payloadMode bit) (false::(List.replicate k true ++ false::left)) (false::tail),
   state (markerMode bit) (List.replicate k true ++ false::left) (false::false::tail),
   state (leftStartMode bit) (List.replicate k true ++ false::left) (true::false::tail)] ++
    scanLeft bit k left (true::false::tail) ++
  [state 14 left (bit::(List.replicate (k+1) true ++ false::tail)),
   state 15 (bit::left) (List.replicate (k+1) true ++ false::tail)]

theorem streamUnit_head (base : List Bool) (bit : Bool) (previous later suffix : List Bool) :
    (streamUnit base bit previous later suffix).head? = some
      (state 0 (processedLeft base previous) (List.replicate (later.length+1) true ++ false::bit::(later++suffix))) := rfl

theorem streamUnit_last (base : List Bool) (bit : Bool) (previous later suffix : List Bool) :
    (streamUnit base bit previous later suffix).getLast? = some
      (state 15 (bit::processedLeft base previous) (List.replicate (later.length+1) true ++ false::(later++suffix))) := by
  unfold streamUnit
  rw [List.getLast?_append]
  rfl

theorem streamUnit_length (base : List Bool) (bit : Bool) (previous later suffix : List Bool) :
    (streamUnit base bit previous later suffix).length = 2*later.length+10 := by
  simp only [streamUnit,List.length_append,List.length_cons,List.length_nil,scanRight_length,scanLeft_length]
  omega

private theorem append_link (xs ys : List (MachineState 16)) (last first : MachineState 16)
    (hx : xs.IsChain (fun before after => Turing.TM0.step rawNatMachine before = some after))
    (hy : ys.IsChain (fun before after => Turing.TM0.step rawNatMachine before = some after))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (step : Turing.TM0.step rawNatMachine last = some first) :
    (xs++ys).IsChain (fun before after => Turing.TM0.step rawNatMachine before = some after) := by
  apply hx.append hy
  intro x hx y hy
  simp only [hl,Option.mem_some_iff] at hx
  simp only [hh,Option.mem_some_iff] at hy
  subst x
  subst y
  exact step

theorem streamUnit_chain (base : List Bool) (bit : Bool) (previous later suffix : List Bool) :
    (streamUnit base bit previous later suffix).IsChain (fun before after => Turing.TM0.step rawNatMachine before = some after) := by
  let k := later.length
  let left := processedLeft base previous
  let tail := later++suffix
  let first := [state 0 left (List.replicate (k+1) true ++ false::bit::tail),
    state 1 left (false::(List.replicate k true ++ false::bit::tail))]
  let middle := [state 3 (false::(List.replicate k true ++ false::left)) (bit::tail),
    state (payloadMode bit) (false::(List.replicate k true ++ false::left)) (false::tail),
    state (markerMode bit) (List.replicate k true ++ false::left) (false::false::tail),
    state (leftStartMode bit) (List.replicate k true ++ false::left) (true::false::tail)]
  let last := [state 14 left (bit::(List.replicate (k+1) true ++ false::tail)),
    state 15 (bit::left) (List.replicate (k+1) true ++ false::tail)]
  have hfirst : first.IsChain (fun before after => Turing.TM0.step rawNatMachine before = some after) := by
    simp [first,List.isChain_cons_cons,Turing.TM0.step,rawNatMachine,state,Turing.Tape.mk₂,List.replicate_succ]
  have hmiddle : middle.IsChain (fun before after => Turing.TM0.step rawNatMachine before = some after) := by
    cases bit <;> simp [middle,List.isChain_cons_cons,payloadMode,markerMode,leftStartMode,Turing.TM0.step,rawNatMachine,state,Turing.Tape.mk₂]
  have hlast : last.IsChain (fun before after => Turing.TM0.step rawNatMachine before = some after) := by
    simp [last,List.isChain_cons_cons,Turing.TM0.step,rawNatMachine,state,Turing.Tape.mk₂]
  have hleftLast : Turing.TM0.step rawNatMachine
      (state (leftMode bit) left (false::(List.replicate k true ++ true::false::tail))) =
      some (state 14 left (bit::(List.replicate (k+1) true ++ false::tail))) := by
    cases bit <;> simp [leftMode,Turing.TM0.step,rawNatMachine,state,Turing.Tape.mk₂,PSTRTMHeader003.replicate_push]
  have hleft := append_link (scanLeft bit k left (true::false::tail)) last _ _
    (scanLeft_chain _ _ _ _) hlast (scanLeft_last _ _ _ _) (by rfl) hleftLast
  have hleftHead : (scanLeft bit k left (true::false::tail)++last).head? =
      some (scanLeftInitial bit k left (true::false::tail)) := by
    simp [List.head?_append,scanLeft_head]
  have hboundary : Turing.TM0.step rawNatMachine
      (state (leftStartMode bit) (List.replicate k true ++ false::left) (true::false::tail)) =
      some (scanLeftInitial bit k left (true::false::tail)) := by
    cases k <;> cases bit <;> simp [scanLeftInitial,leftStartMode,leftMode,Turing.TM0.step,rawNatMachine,state,Turing.Tape.mk₂,List.replicate_succ]
  have hmiddleRest := append_link middle (scanLeft bit k left (true::false::tail)++last) _ _
    hmiddle hleft (by rfl) hleftHead hboundary
  have hmiddleHead : (middle++scanLeft bit k left (true::false::tail)++last).head? =
      some (state 3 (false::(List.replicate k true ++ false::left)) (bit::tail)) := by simp [middle]
  have hscanBoundary : Turing.TM0.step rawNatMachine
      (state 2 (List.replicate k true ++ false::left) (false::bit::tail)) =
      some (state 3 (false::(List.replicate k true ++ false::left)) (bit::tail)) := by
    simp [Turing.TM0.step,rawNatMachine,state,Turing.Tape.mk₂]
  have hright := append_link (scanRight k (false::left) (bit::tail))
    (middle++scanLeft bit k left (true::false::tail)++last) _ _
    (scanRight_chain _ _ _) hmiddleRest (scanRight_last _ _ _) hmiddleHead hscanBoundary
  have hrightHead : (scanRight k (false::left) (bit::tail)++middle++scanLeft bit k left (true::false::tail)++last).head? =
      some (state 2 (false::left) (List.replicate k true ++ false::bit::tail)) := by simp [List.head?_append,scanRight_head]
  change (first++scanRight k (false::left) (bit::tail)++middle++scanLeft bit k left (true::false::tail)++last).IsChain _
  have hfinal := append_link first
    (scanRight k (false::left) (bit::tail)++(middle++(scanLeft bit k left (true::false::tail)++last))) _ _
    hfirst (by simpa only [List.append_assoc] using hright) (by rfl)
    (by simpa only [List.append_assoc] using hrightHead)
    (by simp [Turing.TM0.step,rawNatMachine,state,Turing.Tape.mk₂])
  simpa only [List.append_assoc] using hfinal

theorem streamUnit_safe (base : List Bool) (bit : Bool) (previous later suffix : List Bool) :
    ∀ old ∈ streamUnit base bit previous later suffix, StreamSafe old := by
  have hr (old : MachineState 16)
      (mem : old ∈ scanRight later.length (false::processedLeft base previous) (bit::(later++suffix))) : StreamSafe old := by
    left
    have hc := PSTRTMFullRawPadding015.scanRight_control _ _ _ old mem
    omega
  have hl (old : MachineState 16)
      (mem : old ∈ scanLeft bit later.length (processedLeft base previous) (true::false::(later++suffix))) : StreamSafe old := by
    left
    have hc := PSTRTMFullRawPadding015.scanLeft_control bit _ _ _ old mem
    cases bit <;> simp [leftMode] at hc <;> omega
  simp only [streamUnit,List.forall_mem_append,List.forall_mem_cons]
  simp only [StreamSafe] at hr hl
  cases bit <;> simp_all [StreamSafe,state,payloadMode,markerMode,leftStartMode,Turing.Tape.mk₂,List.replicate_succ]

theorem liftedUnit_chain (base : List Bool) (bit : Bool) (previous later suffix : List Bool) :
    ((streamUnit base bit previous later suffix).map streamCfg).IsChain
      (fun before after => Turing.TM0.step streamMachine before = some after) := by
  apply (List.isChain_map _).mpr
  apply (streamUnit_chain base bit previous later suffix).imp_of_mem_imp
  intro before after hb _ step
  rw [stream_step before (streamUnit_safe base bit previous later suffix before hb),step]
  rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002
