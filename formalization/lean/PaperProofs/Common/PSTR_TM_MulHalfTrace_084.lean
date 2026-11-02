module
public import PaperProofs.Common.PSTR_TM_MulHalfValue_083
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulHalfTrace084
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulHalfCode082
local notation "Triple" => PSTRTMMulPassCode079.Triple
local notation "cols" => PSTRTMMulPassCode079.columns
local notation "leftCols" => PSTRTMMulPassCode079.leftColumns

def initial (r : Fin 4) (archive : List Bool) : List Triple → List Bool → MachineState 33
  | [],tail => state (backward 5 r) archive (false::tail)
  | (c,a,b)::earlier,tail =>
    state (backward 5 r) (b::true::a::true::c::(leftCols earlier++false::archive)) (true::tail)

private theorem commands (r : Fin 4) (a b : Bool) :
    halfMachine (backward 5 r) true=some (readB r,.move .left) ∧
    halfMachine (readB r) b=some (backward 0 (nextControl r b),.write (higher r)) ∧
    halfMachine (backward 0 (nextControl r b)) (higher r)=some (backward 1 (nextControl r b),.move .left) ∧
    halfMachine (backward 1 (nextControl r b)) true=some (backward 2 (nextControl r b),.move .left) ∧
    halfMachine (backward 2 (nextControl r b)) a=some (backward 3 (nextControl r b),.move .left) ∧
    halfMachine (backward 3 (nextControl r b)) true=some (backward 4 (nextControl r b),.move .left) := by
  fin_cases r <;> cases b <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def unitTrace (r : Fin 4) (archive : List Bool) (c a b : Bool) (earlier : List Triple) (tail : List Bool) : List (MachineState 33) :=
  let left := leftCols earlier++false::archive
  let next := nextControl r b
  [initial r archive ((c,a,b)::earlier) tail,
    state (readB r) (true::a::true::c::left) (b::true::tail),
    state (backward 0 next) (true::a::true::c::left) (higher r::true::tail),
    state (backward 1 next) (a::true::c::left) (true::higher r::true::tail),
    state (backward 2 next) (true::c::left) (a::true::higher r::true::tail),
    state (backward 3 next) (c::left) (true::a::true::higher r::true::tail),
    state (backward 4 next) left (c::true::a::true::higher r::true::tail)]

theorem unit_head (r : Fin 4) (archive : List Bool) (c a b : Bool) (earlier : List Triple) (tail : List Bool) :
    (unitTrace r archive c a b earlier tail).head?=some (initial r archive ((c,a,b)::earlier) tail) := rfl
theorem unit_last (r : Fin 4) (archive : List Bool) (c a b : Bool) (earlier : List Triple) (tail : List Bool) :
    (unitTrace r archive c a b earlier tail).getLast?=some
      (state (backward 4 (nextControl r b)) (leftCols earlier++false::archive) (c::true::a::true::higher r::true::tail)) := rfl
theorem unit_length (r : Fin 4) (archive : List Bool) (c a b : Bool) (earlier : List Triple) (tail : List Bool) :
    (unitTrace r archive c a b earlier tail).length=7 := rfl
theorem unit_chain (r : Fin 4) (archive : List Bool) (c a b : Bool) (earlier : List Triple) (tail : List Bool) :
    (unitTrace r archive c a b earlier tail).IsChain (fun before after => Turing.TM0.step halfMachine before=some after) := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := commands r a b
  simp [unitTrace,initial,List.isChain_cons_cons,Turing.TM0.step,state,Turing.Tape.mk₂,h1,h2,h3,h4,h5,h6]

theorem unit_advance (r : Fin 4) (archive : List Bool) (earlier : List Triple) (tail : List Bool) :
    Turing.TM0.step halfMachine (state (backward 4 r) (leftCols earlier++false::archive) tail)=
      some (initial r archive earlier tail) := by
  have hm (symbol : Bool) : halfMachine (backward 4 r) symbol=some (backward 5 r,.move .left) := by
    fin_cases r <;> rfl
  cases earlier with
  | nil => simp [initial,PSTRTMMulPassCode079.leftColumns,Turing.TM0.step,state,Turing.Tape.mk₂,hm]
  | cons triple earlier =>
    obtain ⟨c,a,b⟩ := triple
    simp [initial,PSTRTMMulPassCode079.leftColumns,Turing.TM0.step,state,Turing.Tape.mk₂,hm]

private theorem empty_command (r : Fin 4) : halfMachine (backward 5 r) false=some (haltLabel r,.move .right) := by
  fin_cases r <;> rfl

def loopTrace (r : Fin 4) (archive : List Bool) : List Triple → List Bool → List (MachineState 33)
  | [],tail => [initial r archive [] tail,state (haltLabel r) (false::archive) tail]
  | (c,a,b)::earlier,tail => unitTrace r archive c a b earlier tail ++
      loopTrace (nextControl r b) archive earlier (c::true::a::true::higher r::true::tail)

theorem loop_head (r : Fin 4) (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (loopTrace r archive previous tail).head?=some (initial r archive previous tail) := by
  cases previous with
  | nil => rfl
  | cons triple earlier => obtain ⟨c,a,b⟩ := triple; simp only [loopTrace,List.head?_append,unit_head,Option.some_or]

theorem loop_last (r : Fin 4) (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (loopTrace r archive previous tail).getLast?=some (state (haltLabel (finalControl r previous)) (false::archive)
      (cols (resultReverse r previous).reverse++tail)) := by
  induction previous generalizing r tail with
  | nil => rfl
  | cons triple earlier ih =>
    obtain ⟨c,a,b⟩ := triple
    simp [loopTrace,List.getLast?_append,ih,resultReverse,finalControl,List.reverse_cons,
      PSTRTMMulPassCode079.columns,List.flatMap_append,List.append_assoc]

theorem loop_length (r : Fin 4) (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (loopTrace r archive previous tail).length=7*previous.length+2 := by
  induction previous generalizing r tail with
  | nil => rfl
  | cons triple earlier ih =>
    obtain ⟨c,a,b⟩ := triple
    simp only [loopTrace,List.length_append,unit_length,ih,List.length_cons]
    omega

theorem loop_chain (r : Fin 4) (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (loopTrace r archive previous tail).IsChain (fun before after => Turing.TM0.step halfMachine before=some after) := by
  induction previous generalizing r tail with
  | nil => simp [loopTrace,initial,List.isChain_cons_cons,Turing.TM0.step,state,Turing.Tape.mk₂,empty_command r]
  | cons triple earlier ih =>
    obtain ⟨c,a,b⟩ := triple
    rw [loopTrace]
    apply (unit_chain r archive c a b earlier tail).append (ih (nextControl r b) _)
    intro before hb after ha
    simp only [unit_last,Option.mem_some_iff] at hb
    simp only [loop_head,Option.mem_some_iff] at ha
    subst before
    subst after
    exact unit_advance (nextControl r b) archive earlier _

def fullTrace (archive : List Bool) (previous : List Triple) (tail : List Bool) : List (MachineState 33) :=
  state 0 (leftCols previous++false::archive) tail :: loopTrace (control false false) archive previous tail

theorem full_head (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (fullTrace archive previous tail).head?=some (state 0 (leftCols previous++false::archive) tail) := rfl
theorem full_length (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (fullTrace archive previous tail).length=7*previous.length+3 := by
  simp only [fullTrace,List.length_cons,loop_length]
theorem full_last (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (fullTrace archive previous tail).getLast?=some (state (haltLabel (finalControl (control false false) previous)) (false::archive)
      (cols (resultReverse (control false false) previous).reverse++tail)) := by
  have hne : loopTrace (control false false) archive previous tail≠[] := by
    intro h
    have hh := loop_head (control false false) archive previous tail
    simp [h] at hh
  rw [fullTrace,List.getLast?_cons_of_ne_nil hne,loop_last]

theorem full_chain (archive : List Bool) (previous : List Triple) (tail : List Bool) :
    (fullTrace archive previous tail).IsChain (fun before after => Turing.TM0.step halfMachine before=some after) := by
  apply List.isChain_cons.mpr
  constructor
  · intro after ha
    rw [loop_head] at ha
    have he := Option.mem_some_iff.mp ha
    subst after
    cases previous with
    | nil => simp [initial,PSTRTMMulPassCode079.leftColumns,Turing.TM0.step,halfMachine,state,Turing.Tape.mk₂]
    | cons triple earlier =>
      obtain ⟨c,a,b⟩ := triple
      simp [initial,PSTRTMMulPassCode079.leftColumns,Turing.TM0.step,halfMachine,state,Turing.Tape.mk₂]
  · exact loop_chain (control false false) archive previous tail

/-- Real EOF-boundary to column-start run, retaining EVERY C/A/flag,
all archive cells past the actually visited false guard and arbitrary tail.
Computed old LOW bit/new nonzero bit are in actual HALT control; no external
parity/stop answer. Exact whole trace length7*N+3 includes final HALT. -/
theorem half_runsFrom (archive : List Bool) (triples : List Triple) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom halfMachine (state 0 (leftCols triples.reverse++false::archive) tail)
      (fullTrace archive triples.reverse tail)
      (state (haltLabel (finalControl (control false false) triples.reverse)) (false::archive) (cols (halfTriples triples)++tail)) := by
  exact ⟨full_head _ _ _,full_chain _ _ _,full_last _ _ _,half_halt _ _ _⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulHalfTrace084
