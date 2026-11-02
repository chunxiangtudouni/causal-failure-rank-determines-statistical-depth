module

public import Paid.PDCompute_SolverRatSlotMemory_020

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute linearExecute_append)
open PDMenu.ComputeFrame

/-- The same literal scalar code computes good and bad objectives. Fee
and penalty were saved in slots5/2 by the genuine entry prologue. -/
def objectiveSlots (observation repairs risk target : ℕ) : List Instruction :=
  ratBinarySlots .multiply 5 repairs 29 ++ ratBinarySlots .add observation 29 30 ++
    ratBinarySlots .multiply 2 risk 29 ++ ratBinarySlots .add 30 29 target

def objectiveSlotsResult (before : State) (base observation repairs risk target : ℕ)
    (fee penalty obs rep failure : ℚ) : State :=
  let one := ratBinarySlotsResult before base 5 repairs 29 (fee*rep)
  let two := ratBinarySlotsResult one base observation 29 30 (obs+fee*rep)
  let three := ratBinarySlotsResult two base 2 risk 29 (penalty*failure)
  ratBinarySlotsResult three base 30 29 target (obs+fee*rep+penalty*failure)

theorem objectiveSlots_length (observation repairs risk target : ℕ) :
    (objectiveSlots observation repairs risk target).length=40 := rfl

theorem objectiveSlots_straight (observation repairs risk target : ℕ) :
    StraightCode (objectiveSlots observation repairs risk target) := by
  intro instruction member
  simp only [objectiveSlots,List.mem_append] at member
  rcases member with ((hm|hm)|hm)|hm
  · exact ratBinarySlots_straight _ _ _ _ instruction hm
  · exact ratBinarySlots_straight _ _ _ _ instruction hm
  · exact ratBinarySlots_straight _ _ _ _ instruction hm
  · exact ratBinarySlots_straight _ _ _ _ instruction hm

theorem objectiveSlots_execute (input : List Cell) (before : State)
    (base observation repairs risk target : ℕ) (fee penalty obs rep failure : ℚ)
    (hbase : before.register .fresh=.natural base)
    (hfeeLive : base+5 ∈ before.live) (hpenaltyLive : base+2 ∈ before.live)
    (hobsLive : base+observation ∈ before.live) (hrepLive : base+repairs ∈ before.live)
    (hriskLive : base+risk ∈ before.live)
    (hfee : before.heap (base+5)=.rational fee) (hpenalty : before.heap (base+2)=.rational penalty)
    (hobs : before.heap (base+observation)=.rational obs)
    (hrep : before.heap (base+repairs)=.rational rep) (hrisk : before.heap (base+risk)=.rational failure)
    (hobsTemp : observation ≠ 29) (hriskTempA : risk ≠ 29) (hriskTempB : risk ≠ 30) :
    linearExecute input (objectiveSlots observation repairs risk target) before=
      some (objectiveSlotsResult before base observation repairs risk target fee penalty obs rep failure) := by
  let one := ratBinarySlotsResult before base 5 repairs 29 (fee*rep)
  let two := ratBinarySlotsResult one base observation 29 30 (obs+fee*rep)
  let three := ratBinarySlotsResult two base 2 risk 29 (penalty*failure)
  let four := ratBinarySlotsResult three base 30 29 target (obs+fee*rep+penalty*failure)
  have hb1 : one.register .fresh=.natural base := (ratBinarySlotsResult_base ..).trans hbase
  have hb2 : two.register .fresh=.natural base := (ratBinarySlotsResult_base ..).trans hb1
  have hb3 : three.register .fresh=.natural base := (ratBinarySlotsResult_base ..).trans hb2
  have hl1 : before.live ⊆ one.live := ratBinarySlotsResult_live_mono ..
  have hl2 : one.live ⊆ two.live := ratBinarySlotsResult_live_mono ..
  have hl3 : two.live ⊆ three.live := ratBinarySlotsResult_live_mono ..
  have he1 : linearExecute input (ratBinarySlots .multiply 5 repairs 29) before=some one :=
    ratBinarySlots_execute input before base 5 repairs 29 .multiply fee rep (fee*rep)
      hbase hfeeLive hrepLive hfee hrep rfl
  have ho1 : one.heap (base+observation)=.rational obs :=
    (ratBinarySlotsResult_other before base 5 repairs 29 observation (fee*rep) hobsTemp).trans hobs
  have ht1 : one.heap (base+29)=.rational (fee*rep) := ratBinarySlotsResult_value ..
  have he2 : linearExecute input (ratBinarySlots .add observation 29 30) one=some two :=
    ratBinarySlots_execute input one base observation 29 30 .add obs (fee*rep) (obs+fee*rep)
      hb1 (hl1 hobsLive) (ratBinarySlotsResult_target_live ..) ho1 ht1 rfl
  have hp2 : two.heap (base+2)=.rational penalty := by
    rw [ratBinarySlotsResult_other one base observation 29 30 2 (obs+fee*rep) (by omega),
      ratBinarySlotsResult_other before base 5 repairs 29 2 (fee*rep) (by omega)]
    exact hpenalty
  have hr2 : two.heap (base+risk)=.rational failure := by
    rw [ratBinarySlotsResult_other one base observation 29 30 risk (obs+fee*rep) hriskTempB,
      ratBinarySlotsResult_other before base 5 repairs 29 risk (fee*rep) hriskTempA]
    exact hrisk
  have he3 : linearExecute input (ratBinarySlots .multiply 2 risk 29) two=some three :=
    ratBinarySlots_execute input two base 2 risk 29 .multiply penalty failure (penalty*failure)
      hb2 (hl2 (hl1 hpenaltyLive)) (hl2 (hl1 hriskLive)) hp2 hr2 rfl
  have ht3 : three.heap (base+30)=.rational (obs+fee*rep) :=
    (ratBinarySlotsResult_other two base 2 risk 29 30 (penalty*failure) (by omega)).trans
      (ratBinarySlotsResult_value ..)
  have he4 : linearExecute input (ratBinarySlots .add 30 29 target) three=some four :=
    ratBinarySlots_execute input three base 30 29 target .add (obs+fee*rep) (penalty*failure)
      (obs+fee*rep+penalty*failure) hb3 (hl3 (ratBinarySlotsResult_target_live ..))
      (ratBinarySlotsResult_target_live ..) ht3 (ratBinarySlotsResult_value ..) rfl
  change _=some four
  simp only [objectiveSlots,linearExecute_append,he1,Option.bind_some,he2,he3,he4]

theorem objectiveSlotsResult_value (before : State) (base observation repairs risk target : ℕ)
    (fee penalty obs rep failure : ℚ) :
    (objectiveSlotsResult before base observation repairs risk target fee penalty obs rep failure).heap (base+target)=
      .rational (obs+fee*rep+penalty*failure) := ratBinarySlotsResult_value ..

theorem objectiveSlotsResult_base (before : State) (base observation repairs risk target : ℕ)
    (fee penalty obs rep failure : ℚ) :
    (objectiveSlotsResult before base observation repairs risk target fee penalty obs rep failure).register .fresh=
      before.register .fresh := by simp only [objectiveSlotsResult,ratBinarySlotsResult_base]

theorem objectiveSlotsResult_pc (before : State) (base observation repairs risk target : ℕ)
    (fee penalty obs rep failure : ℚ) :
    (objectiveSlotsResult before base observation repairs risk target fee penalty obs rep failure).pc=before.pc+40 := by
  simp only [objectiveSlotsResult,ratBinarySlotsResult_pc]

theorem objectiveSlotsResult_frame (before : State) (base observation repairs risk target : ℕ)
    (fee penalty obs rep failure : ℚ) (n k : ℕ) (htarget : target < headerWords) :
    Frame before (objectiveSlotsResult before base observation repairs risk target fee penalty obs rep failure) base n k := by
  apply Frame.trans (ratBinarySlotsResult_frame before base 5 repairs 29 (fee*rep) n k (by decide))
  apply Frame.trans (ratBinarySlotsResult_frame _ base observation 29 30 (obs+fee*rep) n k (by decide))
  apply Frame.trans (ratBinarySlotsResult_frame _ base 2 risk 29 (penalty*failure) n k (by decide))
  exact ratBinarySlotsResult_frame _ base 30 29 target (obs+fee*rep+penalty*failure) n k htarget

end PDCompute.Solver
