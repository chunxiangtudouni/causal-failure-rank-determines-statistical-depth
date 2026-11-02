module
public import Common.PSTR_TM_MulPassValue_080
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulPassTrace081
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulPassCode079

private theorem commands (r : Fin 8) (c a b : Bool) :
    passMachine (cState r) c = some (flagC r c,.move .right) ∧
    passMachine (flagC r c) true = some (readA r c,.move .right) ∧
    passMachine (readA r c) a = some (backFlag r c a,.move .left) ∧
    passMachine (backFlag r c a) true = some (writeC r c a,.move .left) ∧
    passMachine (writeC r c a) c = some (towardA 0 (nextHold r c a),.write (sumOutput r c a)) ∧
    passMachine (towardA 0 (nextHold r c a)) (sumOutput r c a) = some (towardA 1 (nextHold r c a),.move .right) ∧
    passMachine (towardA 1 (nextHold r c a)) true = some (towardA 2 (nextHold r c a),.move .right) ∧
    passMachine (towardA 2 (nextHold r c a)) a = some (advance 0 (nextControl r c a),.write (aCarry r)) ∧
    passMachine (advance 0 (nextControl r c a)) (aCarry r) = some (advance 1 (nextControl r c a),.move .right) ∧
    passMachine (advance 1 (nextControl r c a)) true = some (advance 2 (nextControl r c a),.move .right) ∧
    passMachine (advance 2 (nextControl r c a)) b = some (advance 3 (nextControl r c a),.move .right) := by
  fin_cases r <;> cases c <;> cases a <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def unitTrace (r : Fin 8) (c a b : Bool) (left right : List Bool) : List (MachineState 191) :=
  let output := sumOutput r c a
  let oldA := aCarry r
  let saved := nextHold r c a
  let next := nextControl r c a
  [state (cState r) left (c::true::a::true::b::true::right),
    state (flagC r c) (c::left) (true::a::true::b::true::right),
    state (readA r c) (true::c::left) (a::true::b::true::right),
    state (backFlag r c a) (c::left) (true::a::true::b::true::right),
    state (writeC r c a) left (c::true::a::true::b::true::right),
    state (towardA 0 saved) left (output::true::a::true::b::true::right),
    state (towardA 1 saved) (output::left) (true::a::true::b::true::right),
    state (towardA 2 saved) (true::output::left) (a::true::b::true::right),
    state (advance 0 next) (true::output::left) (oldA::true::b::true::right),
    state (advance 1 next) (oldA::true::output::left) (true::b::true::right),
    state (advance 2 next) (true::oldA::true::output::left) (b::true::right),
    state (advance 3 next) (b::true::oldA::true::output::left) (true::right)]

theorem unit_head (r : Fin 8) (c a b : Bool) (left right : List Bool) :
    (unitTrace r c a b left right).head? = some (state (cState r) left (c::true::a::true::b::true::right)) := rfl

theorem unit_last (r : Fin 8) (c a b : Bool) (left right : List Bool) :
    (unitTrace r c a b left right).getLast? = some
      (state (advance 3 (nextControl r c a)) (b::true::aCarry r::true::sumOutput r c a::left) (true::right)) := rfl

theorem unit_length (r : Fin 8) (c a b : Bool) (left right : List Bool) : (unitTrace r c a b left right).length=12 := rfl

theorem unit_chain (r : Fin 8) (c a b : Bool) (left right : List Bool) :
    (unitTrace r c a b left right).IsChain (fun before after => Turing.TM0.step passMachine before = some after) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ := commands r c a b
  simp [unitTrace,List.isChain_cons_cons,Turing.TM0.step,state,Turing.Tape.mk₂,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]

theorem unit_advance (r : Fin 8) (left right : List Bool) :
    Turing.TM0.step passMachine (state (advance 3 r) left (true::right)) = some (state (cState r) (true::left) right) := by
  have hm : passMachine (advance 3 r) true = some (cState r,.move .right) := by
    fin_cases r <;> rfl
  simp [Turing.TM0.step,state,Turing.Tape.mk₂,hm]

private theorem end_commands (r : Fin 8) :
    passMachine (cState r) false = some (flagC r false,.move .right) ∧
    passMachine (flagC r false) false = some (haltLabel r,.move .left) := by
  fin_cases r <;> exact ⟨rfl,rfl⟩

def endTrace (r : Fin 8) (left suffix : List Bool) : List (MachineState 191) :=
  [state (cState r) left (false::false::suffix),state (flagC r false) (false::left) (false::suffix),
    state (haltLabel r) left (false::false::suffix)]

theorem end_head (r : Fin 8) (left suffix : List Bool) :
    (endTrace r left suffix).head? = some (state (cState r) left (false::false::suffix)) := rfl
theorem end_last (r : Fin 8) (left suffix : List Bool) :
    (endTrace r left suffix).getLast? = some (state (haltLabel r) left (false::false::suffix)) := rfl
theorem end_length (r : Fin 8) (left suffix : List Bool) : (endTrace r left suffix).length=3 := rfl
theorem end_chain (r : Fin 8) (left suffix : List Bool) :
    (endTrace r left suffix).IsChain (fun before after => Turing.TM0.step passMachine before = some after) := by
  obtain ⟨h1,h2⟩ := end_commands r
  simp [endTrace,List.isChain_cons_cons,Turing.TM0.step,state,Turing.Tape.mk₂,h1,h2]

def passTrace (r : Fin 8) (context : List Bool) (previous : List Triple) : List Triple → List Bool → List (MachineState 191)
  | [],suffix => endTrace r (leftColumns previous++context) suffix
  | (c,a,b)::later,suffix => unitTrace r c a b (leftColumns previous++context) (columns later++false::false::suffix) ++
      passTrace (nextControl r c a) context ((sumOutput r c a,aCarry r,b)::previous) later suffix

theorem pass_head (r : Fin 8) (context : List Bool) (previous triples : List Triple) (suffix : List Bool) :
    (passTrace r context previous triples suffix).head? = some (state (cState r) (leftColumns previous++context)
      (columns triples++false::false::suffix)) := by
  cases triples with
  | nil => rfl
  | cons triple later => obtain ⟨c,a,b⟩ := triple; simp [passTrace,List.head?_append,unit_head,columns]

theorem pass_last (r : Fin 8) (context : List Bool) (previous triples : List Triple) (suffix : List Bool) :
    (passTrace r context previous triples suffix).getLast? = some (state (haltLabel (finalControl r triples))
      (leftColumns ((resultTriples r triples).reverse++previous)++context) (false::false::suffix)) := by
  induction triples generalizing r previous with
  | nil => simpa only [passTrace,resultTriples,finalControl,List.reverse_nil,List.nil_append] using end_last r _ suffix
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    simp [passTrace,List.getLast?_append,ih,resultTriples,finalControl,List.reverse_cons,List.append_assoc]

theorem pass_length (r : Fin 8) (context : List Bool) (previous triples : List Triple) (suffix : List Bool) :
    (passTrace r context previous triples suffix).length=12*triples.length+3 := by
  induction triples generalizing r previous with
  | nil => rfl
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    simp only [passTrace,List.length_append,unit_length,ih,List.length_cons]
    omega

theorem pass_chain (r : Fin 8) (context : List Bool) (previous triples : List Triple) (suffix : List Bool) :
    (passTrace r context previous triples suffix).IsChain (fun before after => Turing.TM0.step passMachine before = some after) := by
  induction triples generalizing r previous with
  | nil => exact end_chain r _ suffix
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    rw [passTrace]
    apply (unit_chain r c a b _ _).append (ih (nextControl r c a) ((sumOutput r c a,aCarry r,b)::previous))
    intro before hb after ha
    simp only [unit_last,Option.mem_some_iff] at hb
    simp only [pass_head,Option.mem_some_iff] at ha
    subst before
    subst after
    simpa only [leftColumns,List.flatMap_cons,List.cons_append,List.nil_append] using
      unit_advance (nextControl r c a) (b::true::aCarry r::true::sumOutput r c a::(leftColumns previous++context))
        (columns later++false::false::suffix)

/-- Genuine 6-cell multiplication pass on the SAME tape, arbitrary retained
left context and every suffix cell after OWN00. The two overflow bits stay
in the actual HALT label. Actual full trace length is12*N+3, never label count.
The original raw-input triple expansion/loop/projection/trim are NOT assumed. -/
theorem pass_runsFrom (r : Fin 8) (context : List Bool) (triples : List Triple) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom passMachine (state (cState r) context (columns triples++false::false::suffix))
      (passTrace r context [] triples suffix)
      (state (haltLabel (finalControl r triples)) (leftColumns (resultTriples r triples).reverse++context) (false::false::suffix)) := by
  refine ⟨?_,pass_chain r context [] triples suffix,?_,pass_halt _ _ _⟩
  · simpa only [leftColumns,List.flatMap_nil,List.nil_append] using pass_head r context [] triples suffix
  · simpa only [List.append_nil] using pass_last r context [] triples suffix

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulPassTrace081
