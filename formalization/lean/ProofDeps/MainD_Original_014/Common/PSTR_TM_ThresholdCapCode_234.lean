module
public import Common.PSTR_TM_ThresholdBDatum_224
public import Common.PSTR_TM_ReferenceRiskBits_225

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCapCode234
open PaperProofs.Common.Native.RationalControllerComputation

/-! Original cap predicate via the already implemented B(q,1) engine.
This is not a new general Rat comparator. Physical q preservation,
repacking[q,1], calling that engine and later restoring q are still
real caller obligations. The following code merely reads its Nat Datum. -/

theorem B_one_le_two_iff (q : Rat) (hq : 0 < q) :
    PaperProofs.Statistics.controllerB q 1 ≤ 2 ↔ (1/4 : Rat) ≤ q := by
  rw [PaperProofs.Statistics.controllerB_one,Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
  change ⌈1/q⌉₊ ≤ 4 ↔ (1/4 : Rat) ≤ q
  rw [Nat.ceil_le]
  change 1/q ≤ (4 : Rat) ↔ (1/4 : Rat) ≤ q
  rw [div_le_iff₀ hq,div_le_iff₀ (by norm_num : (0 : Rat) < 4)]
  simp only [mul_comm]

theorem bad_product_pos (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    0 < risk*((2*(PaperProofs.Statistics.controllerB risk depth+1) : Nat) : Rat) :=
  mul_pos hr (by positivity)

theorem badRisk_B_branch (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    let product := risk*((2*(PaperProofs.Statistics.controllerB risk depth+1) : Nat) : Rat)
    PaperProofs.Statistics.controllerBadRisk risk (PaperProofs.Statistics.controllerTarget risk depth) =
      if PaperProofs.Statistics.controllerB product 1 ≤ 2 then 1/4 else product := by
  dsimp only
  rw [PaperProofs.Statistics.controllerBadRisk,PSTRTMReferenceRiskBits225.bad_expression_mul_nat]
  simp only [B_one_le_two_iff _ (bad_product_pos risk depth hr)]
  split
  · rename_i h
    exact min_eq_left h
  · rename_i h
    exact min_eq_right (le_of_lt (lt_of_not_ge h))

/-- Fixed7 labels before ALL q/n. Both5(TRUE) and6(FALSE) really HALT;
read/write actions preserve the read bit and every archive/suffix cell. -/
def classifyMachine : Machine 6 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (2,.move .right)
  | 2 => some (if symbol then 3 else 5,if symbol then .move .right else .write false)
  | 3 => some (if symbol then 6 else 4,if symbol then .write true else .move .right)
  | 4 => some (if symbol then 6 else 5,.write symbol)
  | _ => none

def state (q : Fin 7) (left right : List Bool) : MachineState 6 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def rightSteps : Nat → Turing.Tape Bool → Turing.Tape Bool
  | 0,tape => tape
  | k+1,tape => rightSteps k (tape.move .right)

def smallTrace (left tail : List Bool) : List (MachineState 6) :=
  [state 0 left (false::true::false::tail),
   state 1 (false::left) (true::false::tail),
   state 2 (true::false::left) (false::tail),
   state 5 (true::false::left) (false::tail)]

def smallFinal (left tail : List Bool) : MachineState 6 :=
  state 5 (true::false::left) (false::tail)

theorem small_runsFrom (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom classifyMachine (state 0 left (false::true::false::tail))
      (smallTrace left tail) (smallFinal left tail) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [smallTrace,List.isChain_cons_cons,Turing.TM0.step,classifyMachine,state,Turing.Tape.mk₂]
  · simp [smallFinal,Turing.TM0.step,classifyMachine,state]

theorem small_final_tape (left tail : List Bool) :
    (smallFinal left tail).Tape =
      rightSteps 2 (Turing.Tape.mk₂ left (false::true::false::tail)) := by
  simp [smallFinal,state,rightSteps,Turing.Tape.mk₂]

def pairTrace (left : List Bool) (bit : Bool) (tail : List Bool) : List (MachineState 6) :=
  [state 0 left (false::true::true::false::bit::tail),
   state 1 (false::left) (true::true::false::bit::tail),
   state 2 (true::false::left) (true::false::bit::tail),
   state 3 (true::true::false::left) (false::bit::tail),
   state 4 (false::true::true::false::left) (bit::tail),
   state (if bit then 6 else 5) (false::true::true::false::left) (bit::tail)]

def pairFinal (left : List Bool) (bit : Bool) (tail : List Bool) : MachineState 6 :=
  state (if bit then 6 else 5) (false::true::true::false::left) (bit::tail)

theorem pair_runsFrom (left : List Bool) (bit : Bool) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom classifyMachine (state 0 left (false::true::true::false::bit::tail))
      (pairTrace left bit tail) (pairFinal left bit tail) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · cases bit <;> simp [pairTrace,List.isChain_cons_cons,Turing.TM0.step,classifyMachine,state,Turing.Tape.mk₂]
  · cases bit <;> simp [pairFinal,Turing.TM0.step,classifyMachine,state]

theorem pair_final_tape (left : List Bool) (bit : Bool) (tail : List Bool) :
    (pairFinal left bit tail).Tape =
      rightSteps 4 (Turing.Tape.mk₂ left (false::true::true::false::bit::tail)) := by
  simp [pairFinal,state,rightSteps,Turing.Tape.mk₂]

def wideTrace (left tail : List Bool) : List (MachineState 6) :=
  [state 0 left (false::true::true::true::tail),
   state 1 (false::left) (true::true::true::tail),
   state 2 (true::false::left) (true::true::tail),
   state 3 (true::true::false::left) (true::tail),
   state 6 (true::true::false::left) (true::tail)]

def wideFinal (left tail : List Bool) : MachineState 6 :=
  state 6 (true::true::false::left) (true::tail)

theorem wide_runsFrom (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom classifyMachine (state 0 left (false::true::true::true::tail))
      (wideTrace left tail) (wideFinal left tail) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [wideTrace,List.isChain_cons_cons,Turing.TM0.step,classifyMachine,state,Turing.Tape.mk₂]
  · simp [wideFinal,Turing.TM0.step,classifyMachine,state]

theorem wide_final_tape (left tail : List Bool) :
    (wideFinal left tail).Tape =
      rightSteps 3 (Turing.Tape.mk₂ left (false::true::true::true::tail)) := by
  simp [wideFinal,state,rightSteps,Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCapCode234
