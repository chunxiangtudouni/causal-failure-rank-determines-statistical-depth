module

public import Structure.PSTR_HD_HeadsAdvanceSafe_072

/-! EVERY-clock actual fetch/access and ORIGINAL-heap physical prefix frame
for first-return writes and ordered-output append. No initialized scratch is
assumed at the first return, and no stage/count/output is an input ROM field. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel

def initialLead (origin : Nat) : List PackingOp := headsInit ++ jumpLead (origin + 40)

def appendLead (origin : Nat) : List PackingOp := headsAppend ++ jumpLead (origin + 56)

theorem initialLead_length (origin : Nat) : (initialLead origin).length = 23 := rfl

theorem appendLead_length (origin : Nat) : (appendLead origin).length = 12 := rfl

theorem initialLead_straight (origin : Nat) : StraightProgram (initialLead origin) := by
  simp [initialLead, headsInit, jumpLead, StraightProgram, StraightOp]

theorem appendLead_straight (origin : Nat) : StraightProgram (appendLead origin) := by
  simp [appendLead, headsAppend, jumpLead, StraightProgram, StraightOp]

theorem initial_prefix_safe {bits q : Nat} (full : List (Finset (Fin q)))
    (origin endpoint heapWords : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (he : Fits bits (endpoint + 8)) (hroom : endpoint + 8 < heapWords)
    (haddr : state.register .address = BitVec.ofNat bits endpoint)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 80))) (ha : state.halted = false)
    (clock : Nat) (hc : clock < 24) :
    AtSafe (callInput q full .query) whole heapWords (packingRun (callInput q full .query) whole clock state) ∧
    HeapFrame (fun physical => physical < endpoint) state.heap
      (packingRun (callInput q full .query) whole clock state).heap := by
  let rom := callInput q full .query
  let region := fun physical => physical < endpoint
  have initSafe : PrefixOK rom heapWords region headsInit state := by
    constructor
    · exact headsInit_prefix_access full .query endpoint heapWords state hb haddr
        ((show endpoint + 3 ≤ endpoint + 8 by omega).trans_lt he) hroom
    · intro count hcount physical hf hphysical
      exact headsInit_prefix_frame rom endpoint state hb haddr he physical hf (Or.inl hphysical) count hcount
  have jumpSafe : PrefixOK rom heapWords region (jumpLead (origin + 40)) (executeOps rom headsInit state) :=
    readOnly_prefixOK rom heapWords region (jumpLead (origin + 40)) _
      (by simp [jumpLead, ReadOnly]) (by
        intro count hcount
        change count < 2 at hcount
        interval_cases count <;> trivial)
  have leadSafe : PrefixOK rom heapWords region (initialLead origin) state :=
    prefixOK_append rom heapWords region headsInit (jumpLead (origin + 40)) state initSafe jumpSafe
  have leadCode := tail_slice whole (initialLead origin) origin 80 hbound hcode
    (by change 80 + 23 ≤ 111; decide) rfl
  exact branch_prefix_safe rom whole (initialLead origin) heapWords (origin + 80) region
    (by have h := tailAt_length origin; rw [initialLead_length]; omega) leadCode
    (hcode 103 (by change 103 < 111; decide)) (initialLead_straight origin) hwords hpcfit state hp ha leadSafe clock
    (by rw [initialLead_length]; omega)

theorem append_prefix_safe {bits : Nat} (rom : PhysicalROM)
    (origin endpoint cursor heapWords : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (he : Fits bits (endpoint + 2)) (hf : Fits bits cursor)
    (hroom : endpoint + 2 < heapWords) (hcursor : cursor < heapWords) (hafter : endpoint ≤ cursor)
    (haddr : state.register .address = BitVec.ofNat bits endpoint)
    (hslot : state.heap (BitVec.ofNat bits (endpoint + 2)) = BitVec.ofNat bits cursor)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 67))) (ha : state.halted = false)
    (clock : Nat) (hc : clock < 13) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) ∧
    HeapFrame (fun physical => physical < endpoint) state.heap (packingRun rom whole clock state).heap := by
  let region := fun physical => physical < endpoint
  have appendSafe : PrefixOK rom heapWords region headsAppend state := by
    constructor
    · exact headsAppend_prefix_access rom endpoint cursor heapWords state haddr hslot hroom hcursor
    · intro count hcount physical hphysical hprotected
      exact headsAppend_prefix_frame rom endpoint cursor state haddr hslot he hf physical hphysical
        (by omega) (by omega) (by omega) count hcount
  have jumpSafe : PrefixOK rom heapWords region (jumpLead (origin + 56)) (executeOps rom headsAppend state) :=
    readOnly_prefixOK rom heapWords region (jumpLead (origin + 56)) _
      (by simp [jumpLead, ReadOnly]) (by
        intro count hcount
        change count < 2 at hcount
        interval_cases count <;> trivial)
  have leadSafe : PrefixOK rom heapWords region (appendLead origin) state :=
    prefixOK_append rom heapWords region headsAppend (jumpLead (origin + 56)) state appendSafe jumpSafe
  have leadCode := tail_slice whole (appendLead origin) origin 67 hbound hcode
    (by change 67 + 12 ≤ 111; decide) rfl
  exact branch_prefix_safe rom whole (appendLead origin) heapWords (origin + 67) region
    (by have h := tailAt_length origin; rw [appendLead_length]; omega) leadCode
    (hcode 79 (by change 79 < 111; decide)) (appendLead_straight origin) hwords hpcfit state hp ha leadSafe clock
    (by rw [appendLead_length]; omega)

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
