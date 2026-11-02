module
public import Common.PSTR_TM_MulLoopIteration_092

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulLoopRun093
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulLoopCode088 PSTRTMMulLoopValue091 PSTRTMMulLoopIteration092
local notation "Triple" => PSTRTMMulPassCode079.Triple
local notation "cols" => PSTRTMMulPassCode079.columns
local notation "CVal" => PSTRTMMulPassCode079.cValue
local notation "AVal" => PSTRTMMulPassCode079.aValue
local notation "BVal" => PSTRTMMulPassCode079.bValue

/-- A finite witness of the actual run. Fuel is ONLY a proof-recursion
index derived from original width. It is absent from the fixed machine and
its tape; stopping is the ACTUAL halver control0 computed from real B. -/
def loopTrace (archive : List Bool) : Nat → List Triple → List (MachineState 263)
  | 0,triples => halfTrace archive triples
  | fuel+1,triples => if halfControl triples=0 then halfTrace archive triples
      else iterationTrace archive triples++loopTrace archive fuel (nextTriples triples)
def endTriples : Nat → List Triple → List Triple
  | 0,triples => half triples
  | fuel+1,triples => if halfControl triples=0 then half triples else endTriples fuel (nextTriples triples)
def loopFinal (archive : List Bool) (fuel : Nat) (triples : List Triple) : MachineState 263 :=
  state 32 (false::archive) (cols (endTriples fuel triples))

theorem loop_head (archive : List Bool) (fuel : Nat) (triples : List Triple) :
    (loopTrace archive fuel triples).head?=some (entry archive triples) := by
  cases fuel with
  | zero => exact half_head archive triples
  | succ fuel =>
    by_cases hz : halfControl triples=0
    · simp only [loopTrace,hz,↓reduceIte,half_head]
    · simp only [loopTrace,hz,↓reduceIte,List.head?_append,iteration_head,Option.some_or]

theorem halfFinal_zero (archive : List Bool) (triples : List Triple) (hz : halfControl triples=0) :
    halfFinal archive triples=state 32 (false::archive) (cols (half triples)) := by
  simp only [halfFinal,liftHalf,PSTRTMMulHalfCode082.state,hz,halfLabel,PSTRTMMulHalfCode082.haltLabel,state]
  rfl

theorem loop_last (archive : List Bool) (fuel : Nat) (triples : List Triple) (hb : BVal triples<2^fuel) :
    (loopTrace archive fuel triples).getLast?=some (loopFinal archive fuel triples) := by
  induction fuel generalizing triples with
  | zero =>
    have hb0 : BVal triples=0 := by simpa using hb
    have hz := (zero_iff triples).mpr hb0
    simp only [loopTrace,half_last,halfFinal_zero archive triples hz,loopFinal,endTriples]
  | succ fuel ih =>
    by_cases hz : halfControl triples=0
    · simp only [loopTrace,hz,↓reduceIte,half_last,halfFinal_zero archive triples hz,loopFinal,endTriples]
    · have hn := next_capacity triples fuel hb
      simp only [loopTrace,hz,↓reduceIte,List.getLast?_append,ih (nextTriples triples) hn,Option.some_or,
        loopFinal,endTriples]

theorem loop_chain (archive : List Bool) (fuel : Nat) (triples : List Triple) (hb : BVal triples<2^fuel) :
    (loopTrace archive fuel triples).IsChain (fun a b => Turing.TM0.step loopMachine a=some b) := by
  induction fuel generalizing triples with
  | zero => exact half_chain archive triples
  | succ fuel ih =>
    by_cases hz : halfControl triples=0
    · simpa only [loopTrace,hz,↓reduceIte] using half_chain archive triples
    · simp only [loopTrace,hz,↓reduceIte]
      apply (iteration_chain archive triples hz).append (ih (nextTriples triples) (next_capacity triples fuel hb))
      intro before hbefore after hafter
      rw [iteration_last] at hbefore
      rw [loop_head] at hafter
      have he := Option.mem_some_iff.mp hbefore
      have hf := Option.mem_some_iff.mp hafter
      subst before
      subst after
      exact iteration_advance archive triples

theorem end_values (fuel : Nat) (triples : List Triple) (hb : BVal triples<2^fuel) :
    CVal (endTriples fuel triples)=CVal triples+AVal triples*BVal triples ∧ BVal (endTriples fuel triples)=0 := by
  induction fuel generalizing triples with
  | zero =>
    have hb0 : BVal triples=0 := by simpa using hb
    have hv := PSTRTMMulHalfValue083.half_values triples
    simpa only [endTriples,half,hb0,Nat.mul_zero,Nat.add_zero,Nat.zero_div] using And.intro hv.1 hv.2.2
  | succ fuel ih =>
    by_cases hz : halfControl triples=0
    · have hb0 := (zero_iff triples).mp hz
      have hv := PSTRTMMulHalfValue083.half_values triples
      simpa only [endTriples,hz,↓reduceIte,half,hb0,Nat.mul_zero,Nat.add_zero,Nat.zero_div] using And.intro hv.1 hv.2.2
    · have hv := ih (nextTriples triples) (next_capacity triples fuel hb)
      rw [accumulator_invariant] at hv
      simpa only [endTriples,hz,↓reduceIte] using hv

theorem loop_length_le (archive : List Bool) (fuel : Nat) (triples : List Triple) :
    (loopTrace archive fuel triples).length ≤ 64*(triples.length+fuel+1)*(fuel+1) := by
  induction fuel generalizing triples with
  | zero =>
    simp only [loopTrace,halfTrace,List.length_map,PSTRTMMulHalfTrace084.full_length,List.length_reverse]
    omega
  | succ fuel ih =>
    by_cases hz : halfControl triples=0
    · simp only [loopTrace,hz,↓reduceIte,halfTrace,List.length_map,PSTRTMMulHalfTrace084.full_length,List.length_reverse]
      nlinarith
    · have hn := ih (nextTriples triples)
      rw [next_length] at hn
      simp only [loopTrace,hz,↓reduceIte,List.length_append,iteration_length]
      nlinarith

/-- Complete actual finite264-label multiplication accumulator loop from
its real EOF entry. C final is exactly original C+A*B, B is actually zero.
All allocation/halving/pass/rewind/branch transitions are in this trace.
Original raw input expansion and C-only canonical output remain owed. -/
theorem loop_runsFrom (archive : List Bool) (fuel : Nat) (triples : List Triple) (hb : BVal triples<2^fuel) :
    PSTRTMSeq005.RunsFrom loopMachine (entry archive triples) (loopTrace archive fuel triples)
      (loopFinal archive fuel triples) :=
  ⟨loop_head archive fuel triples,loop_chain archive fuel triples hb,loop_last archive fuel triples hb,
    loop_halt _ _⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulLoopRun093
