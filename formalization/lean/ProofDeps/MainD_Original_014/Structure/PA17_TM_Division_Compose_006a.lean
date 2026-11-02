module
public import Common.PSTR_TM_Seq_005

/-! Fixed finite-phase control. Each local HALT either really halts or takes
one charged write-self transition to a fixed port. Tape and head are retained.
Tables and ports are code chosen before input values, not arithmetic oracles. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006

variable {a p s : Nat}

def padLabel (h : a ≤ s) (q : Fin (a+1)) : Fin (s+1) := ⟨q.val, by omega⟩

def padCfg (h : a ≤ s) (state : MachineState a) : MachineState s :=
  ⟨padLabel h state.q, state.Tape⟩

def padMachine (h : a ≤ s) (machine : Machine a) : Machine s := fun q symbol =>
  if small : q.val < a+1 then
    (machine ⟨q.val,small⟩ symbol).map (fun (next,statement) => (padLabel h next,statement))
  else none

theorem pad_step (h : a ≤ s) (machine : Machine a) (state : MachineState a) :
    Turing.TM0.step (padMachine h machine) (padCfg h state) =
      (Turing.TM0.step machine state).map (padCfg h) := by
  cases state with
  | mk q tape =>
    unfold Turing.TM0.step padMachine padCfg padLabel
    simp only [dite_eq_left q.isLt, Fin.eta]
    cases hm : machine q tape.head with
    | none => simp
    | some result =>
      obtain ⟨next,statement⟩ := result
      cases statement <;> simp

theorem pad_runsFrom (h : a ≤ s) (machine : Machine a)
    (first last : MachineState a) (trace : List (MachineState a))
    (run : PSTRTMSeq005.RunsFrom machine first trace last) :
    PSTRTMSeq005.RunsFrom (padMachine h machine) (padCfg h first)
      (trace.map (padCfg h)) (padCfg h last) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.head?_map, run.1, Option.map_some]
  · apply (List.isChain_map _).mpr
    apply run.2.1.imp
    intro before after step
    simp only [pad_step, step, Option.map_some]
  · simp only [List.getLast?_map, run.2.2.1, Option.map_some]
  · simp only [pad_step, run.2.2.2, Option.map_none]

def totalStates (phases states : Nat) : Nat := phases*(states+1)+states

def label (phase : Fin (p+1)) (localLabel : Fin (s+1)) : Fin (totalStates p s+1) :=
  ⟨phase.val*(s+1)+localLabel.val, by
    have hp : phase.val ≤ p := Nat.le_of_lt_succ phase.isLt
    have hm := Nat.mul_le_mul_right (s+1) hp
    have hq := localLabel.isLt
    unfold totalStates
    omega⟩

def phaseOf (code : Fin (totalStates p s+1)) : Fin (p+1) :=
  ⟨code.val/(s+1), by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < s+1)).mpr
    have hc := code.isLt
    have he : totalStates p s+1 = (p+1)*(s+1) := by simp [totalStates]; ring
    omega⟩

def localOf (code : Fin (totalStates p s+1)) : Fin (s+1) :=
  ⟨code.val%(s+1), Nat.mod_lt _ (by omega)⟩

theorem phaseOf_label (phase : Fin (p+1)) (localLabel : Fin (s+1)) :
    phaseOf (label phase localLabel) = phase := by
  apply Fin.ext
  change (phase.val*(s+1)+localLabel.val)/(s+1) = phase.val
  rw [Nat.mul_comm phase.val, Nat.mul_add_div (by omega), Nat.div_eq_of_lt localLabel.isLt, Nat.add_zero]

theorem localOf_label (phase : Fin (p+1)) (localLabel : Fin (s+1)) :
    localOf (label phase localLabel) = localLabel := by
  apply Fin.ext
  change (phase.val*(s+1)+localLabel.val)%(s+1) = localLabel.val
  rw [Nat.mul_add_mod', Nat.mod_eq_of_lt localLabel.isLt]

def blockCfg (phase : Fin (p+1)) (state : MachineState s) : MachineState (totalStates p s) :=
  ⟨label phase state.q,state.Tape⟩

theorem blockCfg_tape (phase : Fin (p+1)) (state : MachineState s) :
    (blockCfg phase state).Tape = state.Tape := rfl

theorem blockCfg_zero (tape : Turing.Tape Bool) :
    blockCfg (0 : Fin (p+1)) (⟨0,tape⟩ : MachineState s) =
      (⟨0,tape⟩ : MachineState (totalStates p s)) := by
  simp [blockCfg,label]

def blockMachine (machines : Fin (p+1) → Machine s)
    (ports : Fin (p+1) → Fin (s+1) → Option (Fin (p+1) × Fin (s+1))) :
    Machine (totalStates p s) := fun code symbol =>
  let phase := phaseOf code
  let localLabel := localOf code
  match machines phase localLabel symbol with
  | some (next,statement) => some (label phase next,statement)
  | none => (ports phase localLabel).map (fun target => (label target.1 target.2,.write symbol))

theorem block_step (machines : Fin (p+1) → Machine s)
    (ports : Fin (p+1) → Fin (s+1) → Option (Fin (p+1) × Fin (s+1)))
    (phase : Fin (p+1)) (state : MachineState s) :
    Turing.TM0.step (blockMachine machines ports) (blockCfg phase state) =
      match Turing.TM0.step (machines phase) state with
      | some after => some (blockCfg phase after)
      | none => (ports phase state.q).map (fun target => blockCfg target.1 ⟨target.2,state.Tape⟩) := by
  cases state with
  | mk q tape =>
    unfold Turing.TM0.step blockMachine blockCfg
    simp only [phaseOf_label,localOf_label]
    cases hm : machines phase q tape.head with
    | none =>
      cases hp : ports phase q with
      | none => rfl
      | some target => simp [Turing.Tape.write_self]
    | some result =>
      obtain ⟨next,statement⟩ := result
      cases statement <;> simp

def Segment {states : Nat} (machine : Machine states)
    (first : MachineState states) (trace : List (MachineState states)) (last : MachineState states) : Prop :=
  trace.head? = some first ∧
  trace.IsChain (fun before after => Turing.TM0.step machine before = some after) ∧
  trace.getLast? = some last

theorem block_segment (machines : Fin (p+1) → Machine s)
    (ports : Fin (p+1) → Fin (s+1) → Option (Fin (p+1) × Fin (s+1)))
    (phase : Fin (p+1)) (first last : MachineState s) (trace : List (MachineState s))
    (run : PSTRTMSeq005.RunsFrom (machines phase) first trace last) :
    Segment (blockMachine machines ports) (blockCfg phase first)
      (trace.map (blockCfg phase)) (blockCfg phase last) := by
  refine ⟨?_,?_,?_⟩
  · simp only [List.head?_map,run.1,Option.map_some]
  · apply (List.isChain_map _).mpr
    apply run.2.1.imp
    intro before after step
    simp only [block_step,step]
  · simp only [List.getLast?_map,run.2.2.1,Option.map_some]

theorem block_transfer (machines : Fin (p+1) → Machine s)
    (ports : Fin (p+1) → Fin (s+1) → Option (Fin (p+1) × Fin (s+1)))
    (phase : Fin (p+1)) (last : MachineState s) (target : Fin (p+1) × Fin (s+1))
    (halt : Turing.TM0.step (machines phase) last = none)
    (port : ports phase last.q = some target) :
    Turing.TM0.step (blockMachine machines ports) (blockCfg phase last) =
      some (blockCfg target.1 ⟨target.2,last.Tape⟩) := by
  simp only [block_step,halt,port,Option.map_some]

theorem block_halt (machines : Fin (p+1) → Machine s)
    (ports : Fin (p+1) → Fin (s+1) → Option (Fin (p+1) × Fin (s+1)))
    (phase : Fin (p+1)) (last : MachineState s)
    (halt : Turing.TM0.step (machines phase) last = none)
    (port : ports phase last.q = none) :
    Turing.TM0.step (blockMachine machines ports) (blockCfg phase last) = none := by
  simp only [block_step,halt,port,Option.map_none]

theorem segment_append {states : Nat} (machine : Machine states)
    (first middle next last : MachineState states) (xs ys : List (MachineState states))
    (left : Segment machine first xs middle) (right : Segment machine next ys last)
    (transfer : Turing.TM0.step machine middle = some next) :
    Segment machine first (xs++ys) last := by
  refine ⟨?_,?_,?_⟩
  · simp only [List.head?_append,left.1,Option.some_or]
  · apply List.IsChain.append left.2.1 right.2.1
    intro x hx y hy
    simp only [left.2.2,Option.mem_some_iff] at hx
    simp only [right.1,Option.mem_some_iff] at hy
    subst x
    subst y
    exact transfer
  · simp only [List.getLast?_append,right.2.2,Option.some_or]

theorem segment_runsFrom {states : Nat} (machine : Machine states)
    (first last : MachineState states) (trace : List (MachineState states))
    (segment : Segment machine first trace last)
    (halt : Turing.TM0.step machine last = none) :
    PSTRTMSeq005.RunsFrom machine first trace last :=
  ⟨segment.1,segment.2.1,segment.2.2,halt⟩

theorem block_runsFrom (machines : Fin (p+1) → Machine s)
    (ports : Fin (p+1) → Fin (s+1) → Option (Fin (p+1) × Fin (s+1)))
    (phase : Fin (p+1)) (first last : MachineState s) (trace : List (MachineState s))
    (run : PSTRTMSeq005.RunsFrom (machines phase) first trace last)
    (port : ports phase last.q = none) :
    PSTRTMSeq005.RunsFrom (blockMachine machines ports) (blockCfg phase first)
      (trace.map (blockCfg phase)) (blockCfg phase last) :=
  segment_runsFrom _ _ _ _ (block_segment machines ports phase first last trace run)
    (block_halt machines ports phase last run.2.2.2 port)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006
