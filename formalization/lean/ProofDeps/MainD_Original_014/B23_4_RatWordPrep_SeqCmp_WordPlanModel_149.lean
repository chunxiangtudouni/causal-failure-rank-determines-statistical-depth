module

public import B23_4_RatWordPrep_SeqCmp_WordPlanScale_148

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

def stageData0 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  initialData target (E.rationalWordOdds word) (Channels.channelValues E)

def stageData1 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  packetData .targetForSub (stageData0 E target word) (target) ([])

def stageData2 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  Function.update (stageData1 E target word) 15 (1::(stageData1 E target word) 15)

def stageData3 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  Function.update (stageData2 E target word) 15 (((1)-(target))::[(E.rationalWordOdds word)])

def stageData4 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  packetData .parkComplement (stageData3 E target word) (1-target) ([(E.rationalWordOdds word)])

def stageData5 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  packetData .targetForHigh (stageData4 E target word) (target) ([])

def stageData6 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  packetData .complementForHigh (stageData5 E target word) (1-target) ([])

def stageData7 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  Function.update (stageData6 E target word) 15 (((1-target)/(target))::[(E.rationalWordOdds word)])

def stageData8 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  packetData .parkHigh (stageData7 E target word) ((1-target)/target) ([(E.rationalWordOdds word)])

def stageData9 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  packetData .complementForLow (stageData8 E target word) (1-target) ([])

def stageData10 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  packetData .targetForLow (stageData9 E target word) (target) ([])

def stageData11 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  Function.update (stageData10 E target word) 15 (((target)/(1-target))::[(E.rationalWordOdds word)])

def stageData12 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  packetData .parkLow (stageData11 E target word) (target/(1-target)) ([(E.rationalWordOdds word)])

def stageData13 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  packetData .cacheOdds (stageData12 E target word) ((E.rationalWordOdds word)) ([])

def stageData14 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  packetData .oddsFirst (stageData13 E target word) ((E.rationalWordOdds word)) ([target])

def stageData15 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  Function.update (stageData14 E target word) 15 (1::(stageData14 E target word) 15)

def stageData16 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  packetData .oddsMiddle (stageData15 E target word) ((E.rationalWordOdds word)) ([target])

def stageData17 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  packetData .high (stageData16 E target word) ((1-target)/target) (Channels.channelValues E)

def stageData18 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  packetData .low (stageData17 E target word) (target/(1-target)) ([1-target])

def stageData19 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Data :=
  packetData .oddsLast (stageData18 E target word) ((E.rationalWordOdds word)) ([target])

theorem stageCapacity0 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData0 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([] : List Rat).length≤7 ∧ ∀ q∈[],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        cases member
    · change ([target] : List Rat).length≤7 ∧ ∀ q∈[target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
  · refine ⟨[],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      cases member

theorem stageCapacity1 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData1 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([] : List Rat).length≤7 ∧ ∀ q∈[],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        cases member
    · change ([target] : List Rat).length≤7 ∧ ∀ q∈[target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([target,(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[target,(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
  · refine ⟨[],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      cases member

theorem stageCapacity2 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData2 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([] : List Rat).length≤7 ∧ ∀ q∈[],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        cases member
    · change ([target] : List Rat).length≤7 ∧ ∀ q∈[target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([1,target,(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[1,target,(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          rcases List.mem_cons.mp rest with rfl | rest
          · simp [operands]
          ·
            have equal := List.mem_singleton.mp rest
            subst q
            simp [operands]
  · refine ⟨[],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      cases member

theorem stageCapacity3 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData3 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([] : List Rat).length≤7 ∧ ∀ q∈[],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        cases member
    · change ([target] : List Rat).length≤7 ∧ ∀ q∈[target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([1-target,(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[1-target,(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
  · refine ⟨[],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      cases member

theorem stageCapacity4 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData4 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([1-target] : List Rat).length≤7 ∧ ∀ q∈[1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([target] : List Rat).length≤7 ∧ ∀ q∈[target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
  · refine ⟨[],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      cases member

theorem stageCapacity5 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData5 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([1-target] : List Rat).length≤7 ∧ ∀ q∈[1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([target] : List Rat).length≤7 ∧ ∀ q∈[target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([target,(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[target,(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
  · refine ⟨[],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      cases member

theorem stageCapacity6 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData6 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([1-target] : List Rat).length≤7 ∧ ∀ q∈[1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([target] : List Rat).length≤7 ∧ ∀ q∈[target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([1-target,target,(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[1-target,target,(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          rcases List.mem_cons.mp rest with rfl | rest
          · simp [operands]
          ·
            have equal := List.mem_singleton.mp rest
            subst q
            simp [operands]
  · refine ⟨[],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      cases member

theorem stageCapacity7 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData7 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([1-target] : List Rat).length≤7 ∧ ∀ q∈[1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([target] : List Rat).length≤7 ∧ ∀ q∈[target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([(1-target)/target,(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[(1-target)/target,(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
  · refine ⟨[],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      cases member

theorem stageCapacity8 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData8 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([1-target] : List Rat).length≤7 ∧ ∀ q∈[1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([target] : List Rat).length≤7 ∧ ∀ q∈[target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
  · refine ⟨[(1-target)/target],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      have equal := List.mem_singleton.mp member
      subst q
      simp [operands]

theorem stageCapacity9 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData9 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([1-target] : List Rat).length≤7 ∧ ∀ q∈[1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([target] : List Rat).length≤7 ∧ ∀ q∈[target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([1-target,(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[1-target,(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
  · refine ⟨[(1-target)/target],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      have equal := List.mem_singleton.mp member
      subst q
      simp [operands]

theorem stageCapacity10 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData10 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([1-target] : List Rat).length≤7 ∧ ∀ q∈[1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([target] : List Rat).length≤7 ∧ ∀ q∈[target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([target,1-target,(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[target,1-target,(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          rcases List.mem_cons.mp rest with rfl | rest
          · simp [operands]
          ·
            have equal := List.mem_singleton.mp rest
            subst q
            simp [operands]
  · refine ⟨[(1-target)/target],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      have equal := List.mem_singleton.mp member
      subst q
      simp [operands]

theorem stageCapacity11 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData11 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([1-target] : List Rat).length≤7 ∧ ∀ q∈[1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([target] : List Rat).length≤7 ∧ ∀ q∈[target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([target/(1-target),(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[target/(1-target),(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
  · refine ⟨[(1-target)/target],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      have equal := List.mem_singleton.mp member
      subst q
      simp [operands]

theorem stageCapacity12 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData12 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([target/(1-target),1-target] : List Rat).length≤7 ∧ ∀ q∈[target/(1-target),1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([target] : List Rat).length≤7 ∧ ∀ q∈[target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
    · change ([(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
  · refine ⟨[(1-target)/target],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      have equal := List.mem_singleton.mp member
      subst q
      simp [operands]

theorem stageCapacity13 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData13 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([target/(1-target),1-target] : List Rat).length≤7 ∧ ∀ q∈[target/(1-target),1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([(E.rationalWordOdds word),target] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word),target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        have equal := List.mem_singleton.mp member
        subst q
        simp [operands]
  · refine ⟨[(1-target)/target],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      have equal := List.mem_singleton.mp member
      subst q
      simp [operands]

theorem stageCapacity14 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData14 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([target/(1-target),1-target] : List Rat).length≤7 ∧ ∀ q∈[target/(1-target),1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([(E.rationalWordOdds word),target] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word),target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([(E.rationalWordOdds word),(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word),(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
  · refine ⟨[(1-target)/target],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      have equal := List.mem_singleton.mp member
      subst q
      simp [operands]

theorem stageCapacity15 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData15 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([target/(1-target),1-target] : List Rat).length≤7 ∧ ∀ q∈[target/(1-target),1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([(E.rationalWordOdds word),target] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word),target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([1,(E.rationalWordOdds word),(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[1,(E.rationalWordOdds word),(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          rcases List.mem_cons.mp rest with rfl | rest
          · simp [operands]
          ·
            have equal := List.mem_singleton.mp rest
            subst q
            simp [operands]
  · refine ⟨[(1-target)/target],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      have equal := List.mem_singleton.mp member
      subst q
      simp [operands]

theorem stageCapacity16 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData16 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([target/(1-target),1-target] : List Rat).length≤7 ∧ ∀ q∈[target/(1-target),1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([(E.rationalWordOdds word),target] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word),target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([(E.rationalWordOdds word),1,(E.rationalWordOdds word),(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word),1,(E.rationalWordOdds word),(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          rcases List.mem_cons.mp rest with rfl | rest
          · simp [operands]
          ·
            rcases List.mem_cons.mp rest with rfl | rest
            · simp [operands]
            ·
              have equal := List.mem_singleton.mp rest
              subst q
              simp [operands]
  · refine ⟨[(1-target)/target],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      have equal := List.mem_singleton.mp member
      subst q
      simp [operands]

theorem stageCapacity17 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData17 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([target/(1-target),1-target] : List Rat).length≤7 ∧ ∀ q∈[target/(1-target),1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([(E.rationalWordOdds word),target] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word),target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([(1-target)/target,(E.rationalWordOdds word),1,(E.rationalWordOdds word),(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[(1-target)/target,(E.rationalWordOdds word),1,(E.rationalWordOdds word),(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          rcases List.mem_cons.mp rest with rfl | rest
          · simp [operands]
          ·
            rcases List.mem_cons.mp rest with rfl | rest
            · simp [operands]
            ·
              rcases List.mem_cons.mp rest with rfl | rest
              · simp [operands]
              ·
                have equal := List.mem_singleton.mp rest
                subst q
                simp [operands]
  · refine ⟨[(1-target)/target],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      have equal := List.mem_singleton.mp member
      subst q
      simp [operands]

theorem stageCapacity18 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData18 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([target/(1-target),1-target] : List Rat).length≤7 ∧ ∀ q∈[target/(1-target),1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([(E.rationalWordOdds word),target] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word),target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([target/(1-target),(1-target)/target,(E.rationalWordOdds word),1,(E.rationalWordOdds word),(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[target/(1-target),(1-target)/target,(E.rationalWordOdds word),1,(E.rationalWordOdds word),(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          rcases List.mem_cons.mp rest with rfl | rest
          · simp [operands]
          ·
            rcases List.mem_cons.mp rest with rfl | rest
            · simp [operands]
            ·
              rcases List.mem_cons.mp rest with rfl | rest
              · simp [operands]
              ·
                rcases List.mem_cons.mp rest with rfl | rest
                · simp [operands]
                ·
                  have equal := List.mem_singleton.mp rest
                  subst q
                  simp [operands]
  · refine ⟨[(1-target)/target],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      have equal := List.mem_singleton.mp member
      subst q
      simp [operands]

theorem stageCapacity19 (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PlanData E target word (stageData19 E target word) := by
  constructor
  · intro slot selected
    rcases selected with rfl | rfl | rfl
    · change ([target/(1-target),1-target] : List Rat).length≤7 ∧ ∀ q∈[target/(1-target),1-target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([(E.rationalWordOdds word),target] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word),target],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          have equal := List.mem_singleton.mp rest
          subst q
          simp [operands]
    · change ([(E.rationalWordOdds word),target/(1-target),(1-target)/target,(E.rationalWordOdds word),1,(E.rationalWordOdds word),(E.rationalWordOdds word)] : List Rat).length≤7 ∧ ∀ q∈[(E.rationalWordOdds word),target/(1-target),(1-target)/target,(E.rationalWordOdds word),1,(E.rationalWordOdds word),(E.rationalWordOdds word)],q∈operands E target word
      constructor
      · norm_num
      ·
        intro q member
        rcases List.mem_cons.mp member with rfl | rest
        · simp [operands]
        ·
          rcases List.mem_cons.mp rest with rfl | rest
          · simp [operands]
          ·
            rcases List.mem_cons.mp rest with rfl | rest
            · simp [operands]
            ·
              rcases List.mem_cons.mp rest with rfl | rest
              · simp [operands]
              ·
                rcases List.mem_cons.mp rest with rfl | rest
                · simp [operands]
                ·
                  rcases List.mem_cons.mp rest with rfl | rest
                  · simp [operands]
                  ·
                    have equal := List.mem_singleton.mp rest
                    subst q
                    simp [operands]
  · refine ⟨[(1-target)/target],?_,by norm_num,?_⟩
    · rfl
    ·
      intro q member
      have equal := List.mem_singleton.mp member
      subst q
      simp [operands]

theorem stageData19_eq (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    stageData19 E target word=operandData target (E.rationalWordOdds word) (Channels.channelValues E) := by
  funext slot
  fin_cases slot <;> rfl

end B23_4_RatWordPrep.WordFinish.Resources
