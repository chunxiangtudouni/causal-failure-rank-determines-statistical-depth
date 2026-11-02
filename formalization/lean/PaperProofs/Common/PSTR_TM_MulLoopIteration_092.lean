module
public import PaperProofs.Common.PSTR_TM_MulLoopValue_091
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulLoopIteration092
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulLoopCode088 PSTRTMMulLoopValue091
local notation "Triple" => PSTRTMMulPassCode079.Triple
local notation "cols" => PSTRTMMulPassCode079.columns
local notation "leftCols" => PSTRTMMulPassCode079.leftColumns

theorem half_append_transfer (r : Fin 4) (hr : r≠0) (tape : Turing.Tape Bool) :
    Turing.TM0.step loopMachine ⟨halfLabel (PSTRTMMulHalfCode082.haltLabel r),tape⟩=
      some ⟨appendLabel (PSTRTMMulHalfCode082.higher r) 0,tape⟩ := by
  fin_cases r <;> simp_all [Turing.TM0.step,loopMachine,halfLabel,PSTRTMMulHalfCode082.haltLabel,
    appendLabel,PSTRTMMulHalfCode082.higher,Turing.Tape.write_self]

theorem append_pass_transfer (mode : Bool) (tape : Turing.Tape Bool) :
    Turing.TM0.step loopMachine ⟨appendLabel mode 17,tape⟩=
      some ⟨passLabel (PSTRTMMulPassCode079.cState (PSTRTMMulPassCode079.control mode false false)),tape⟩ := by
  cases mode <;> simp [Turing.TM0.step,loopMachine,appendLabel,passLabel,
    PSTRTMMulPassCode079.cState,PSTRTMMulPassCode079.control,Turing.Tape.write_self]

theorem pass_half_transfer (mode : Bool) (tape : Turing.Tape Bool) :
    Turing.TM0.step loopMachine
      ⟨passLabel (PSTRTMMulPassCode079.haltLabel (PSTRTMMulPassCode079.control mode false false)),tape⟩=
      some ⟨halfLabel 0,tape⟩ := by
  cases mode <;> simp [Turing.TM0.step,loopMachine,passLabel,halfLabel,
    PSTRTMMulPassCode079.haltLabel,PSTRTMMulPassCode079.control,Turing.Tape.write_self]

theorem tape_trailing_zeros (left right : List Bool) :
    Turing.Tape.mk₂ left (right++[false,false])=Turing.Tape.mk₂ left right := by
  have hz : Turing.ListBlank.mk (right++[false,false])=Turing.ListBlank.mk right := by
    calc
      _ = Turing.ListBlank.mk ((right++[false])++[false]) := by rw [List.append_assoc]; rfl
      _ = Turing.ListBlank.mk (right++[false]) := PSTRTMRawNat010.blank_append_false _
      _ = Turing.ListBlank.mk right := PSTRTMRawNat010.blank_append_false _
  simp only [Turing.Tape.mk₂,hz]

theorem tape_empty_zeros (left : List Bool) :
    Turing.Tape.mk₂ left [false,false]=Turing.Tape.mk₂ left [] := tape_trailing_zeros left []

def entry (archive : List Bool) (triples : List Triple) : MachineState 263 :=
  liftHalf (PSTRTMMulHalfCode082.state 0 (leftCols triples.reverse++false::archive) [])
def halfTrace (archive : List Bool) (triples : List Triple) : List (MachineState 263) :=
  (PSTRTMMulHalfTrace084.fullTrace archive triples.reverse []).map liftHalf
def halfFinal (archive : List Bool) (triples : List Triple) : MachineState 263 :=
  liftHalf (PSTRTMMulHalfCode082.state (PSTRTMMulHalfCode082.haltLabel (halfControl triples))
    (false::archive) (cols (half triples)))
def appendTrace (archive : List Bool) (triples : List Triple) : List (MachineState 263) :=
  (PSTRTMMulAppendTrace087.appendTrace archive (half triples)).map (liftAppend (lowBit triples))
def appendFinal (archive : List Bool) (triples : List Triple) : MachineState 263 :=
  liftAppend (lowBit triples) (PSTRTMMulAppendTrace087.appendFinal archive (half triples))
def passTrace (archive : List Bool) (triples : List Triple) : List (MachineState 263) :=
  (PSTRTMMulPassTrace081.passTrace (passControl triples) (false::archive) [] (padded triples) []).map liftPass
def iterationTrace (archive : List Bool) (triples : List Triple) : List (MachineState 263) :=
  halfTrace archive triples++appendTrace archive triples++passTrace archive triples
def iterationFinal (archive : List Bool) (triples : List Triple) : MachineState 263 :=
  liftPass (PSTRTMMulPassCode079.state (PSTRTMMulPassCode079.haltLabel (passControl triples))
    (leftCols (nextTriples triples).reverse++false::archive) [false,false])

theorem half_head (archive : List Bool) (triples : List Triple) :
    (halfTrace archive triples).head?=some (entry archive triples) := by
  simp only [halfTrace,List.head?_map,PSTRTMMulHalfTrace084.full_head,Option.map_some,entry]
theorem half_last (archive : List Bool) (triples : List Triple) :
    (halfTrace archive triples).getLast?=some (halfFinal archive triples) := by
  simp only [halfTrace,List.getLast?_map,PSTRTMMulHalfTrace084.full_last,List.append_nil,Option.map_some]
  rfl
theorem append_head (archive : List Bool) (triples : List Triple) :
    (appendTrace archive triples).head?=some
      (liftAppend (lowBit triples) (PSTRTMMulAppendCode086.state 0 (false::archive) (cols (half triples)))) := by
  simp only [appendTrace,List.head?_map,PSTRTMMulAppendTrace087.append_head,Option.map_some]
theorem append_last (archive : List Bool) (triples : List Triple) :
    (appendTrace archive triples).getLast?=some (appendFinal archive triples) := by
  simp only [appendTrace,List.getLast?_map,PSTRTMMulAppendTrace087.append_last,Option.map_some,appendFinal]
theorem pass_head (archive : List Bool) (triples : List Triple) :
    (passTrace archive triples).head?=some (liftPass (PSTRTMMulPassCode079.state
      (PSTRTMMulPassCode079.cState (passControl triples)) (false::archive) (cols (padded triples)++[false,false]))) := by
  simp only [passTrace,List.head?_map,PSTRTMMulPassTrace081.pass_head,
    PSTRTMMulPassCode079.leftColumns,List.flatMap_nil,List.nil_append,Option.map_some]
theorem pass_last (archive : List Bool) (triples : List Triple) :
    (passTrace archive triples).getLast?=some (iterationFinal archive triples) := by
  simp only [passTrace,List.getLast?_map,PSTRTMMulPassTrace081.pass_last,List.append_nil,Option.map_some,no_overflow]
  rfl

private theorem append_link (xs ys : List (MachineState 263)) (last first : MachineState 263)
    (hx : xs.IsChain (fun a b => Turing.TM0.step loopMachine a=some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step loopMachine a=some b))
    (hl : xs.getLast?=some last) (hh : ys.head?=some first)
    (hs : Turing.TM0.step loopMachine last=some first) :
    (xs++ys).IsChain (fun a b => Turing.TM0.step loopMachine a=some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

theorem half_chain (archive : List Bool) (triples : List Triple) :
    (halfTrace archive triples).IsChain (fun a b => Turing.TM0.step loopMachine a=some b) :=
  PSTRTMMulLoopLift090.half_chain _ (PSTRTMMulHalfTrace084.full_chain archive triples.reverse [])

theorem iteration_chain (archive : List Bool) (triples : List Triple) (hn : halfControl triples≠0) :
    (iterationTrace archive triples).IsChain (fun a b => Turing.TM0.step loopMachine a=some b) := by
  unfold iterationTrace
  refine append_link _ _ (appendFinal archive triples) _ ?_
    (PSTRTMMulLoopLift090.pass_chain _ (PSTRTMMulPassTrace081.pass_chain (passControl triples) (false::archive) [] (padded triples) []))
    ?_ (pass_head archive triples) ?_
  · exact append_link _ _ (halfFinal archive triples) _ (half_chain archive triples)
      (PSTRTMMulLoopLift090.append_chain _ _ (PSTRTMMulAppendTrace087.append_chain archive (half triples)))
      (half_last archive triples) (append_head archive triples)
      (half_append_transfer (halfControl triples) hn (Turing.Tape.mk₂ (false::archive) (cols (half triples))))
  · simp only [List.getLast?_append,append_last,Option.some_or]
  · have hm := append_pass_transfer (lowBit triples) (Turing.Tape.mk₂ (false::archive) (cols (padded triples)))
    simpa only [appendFinal,liftAppend,liftPass,PSTRTMMulAppendTrace087.appendFinal,
      PSTRTMMulAppendCode086.state,PSTRTMMulPassCode079.state,passControl,padded,tape_trailing_zeros] using hm

theorem iteration_head (archive : List Bool) (triples : List Triple) :
    (iterationTrace archive triples).head?=some (entry archive triples) := by
  simp only [iterationTrace,List.head?_append,half_head,Option.some_or]
theorem iteration_last (archive : List Bool) (triples : List Triple) :
    (iterationTrace archive triples).getLast?=some (iterationFinal archive triples) := by
  simp only [iterationTrace,List.getLast?_append,pass_last,Option.some_or]
theorem iteration_length (archive : List Bool) (triples : List Triple) :
    (iterationTrace archive triples).length=31*triples.length+41 := by
  simp only [iterationTrace,halfTrace,appendTrace,passTrace,List.length_append,List.length_map,
    PSTRTMMulHalfTrace084.full_length,List.length_reverse,PSTRTMMulAppendTrace087.append_length,
    PSTRTMMulPassTrace081.pass_length,half_length,padded_length]
  omega

theorem iteration_advance (archive : List Bool) (triples : List Triple) :
    Turing.TM0.step loopMachine (iterationFinal archive triples)=some (entry archive (nextTriples triples)) := by
  have hm := pass_half_transfer (lowBit triples)
    (Turing.Tape.mk₂ (leftCols (nextTriples triples).reverse++false::archive) [])
  simpa only [iterationFinal,entry,liftPass,liftHalf,PSTRTMMulPassCode079.state,
    PSTRTMMulHalfCode082.state,passControl,tape_empty_zeros] using hm

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulLoopIteration092
