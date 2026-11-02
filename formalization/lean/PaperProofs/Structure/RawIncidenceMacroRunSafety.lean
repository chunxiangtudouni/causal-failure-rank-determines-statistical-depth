module

public import PaperProofs.Structure.RawIncidenceMacroSafety

/-! Actual encoded prefix safety of the fixed checker's non-scan macros.
The shared macro bounds are consumed only after their original code words
have been matched with the real checker segment. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawIncidenceMacroSafety

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety

def QuickPC (pc : Nat) : Prop := pc ∈ [0, 50, 85, 100, 135, 195, 230, 460, 480, 500, 520, 540, 585, 630]

instance (pc : Nat) : Decidable (QuickPC pc) :=
  inferInstanceAs (Decidable (pc ∈ [0, 50, 85, 100, 135, 195, 230, 460, 480, 500, 520, 540, 585, 630]))

theorem safePoint_of_quickPC (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hr : RegistersBound full.length q state) (hp : QuickPC state.pc) : SafePoint q full state := by
  simp only [QuickPC, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  · exact safePoint_of_body q full state 0 (by rw [checker_length]; decide) hp hr True.intro
  · exact safePoint_of_body q full state 10 (by rw [checker_length]; decide) hp hr True.intro
  · exact safePoint_of_body q full state 17 (by rw [checker_length]; decide) hp hr True.intro
  · exact safePoint_of_body q full state 20 (by rw [checker_length]; decide) hp hr True.intro
  · exact safePoint_of_body q full state 27 (by rw [checker_length]; decide) hp hr True.intro
  · exact safePoint_of_body q full state 39 (by rw [checker_length]; decide) hp hr True.intro
  · exact safePoint_of_body q full state 46 (by rw [checker_length]; decide) hp hr True.intro
  · exact safePoint_of_body q full state 92 (by rw [checker_length]; decide) hp hr True.intro
  · exact safePoint_of_body q full state 96 (by rw [checker_length]; decide) hp hr True.intro
  · exact safePoint_of_body q full state 100 (by rw [checker_length]; decide) hp hr True.intro
  · exact safePoint_of_body q full state 104 (by rw [checker_length]; decide) hp hr True.intro
  · exact safePoint_of_body q full state 108 (by rw [checker_length]; decide) hp hr True.intro
  · exact safePoint_of_body q full state 117 (by rw [checker_length]; decide) hp hr True.intro
  · exact safePoint_of_halt q full state hp hr

theorem checker_segment_prefix_safe (q : Nat) (full : List (Finset (Fin q)))
    (lead : List PackingOp) (last : PackingOp) (start : Nat)
    (hbound : start + lead.length + 1 ≤ checker.length)
    (hcode : ∀ position (hp : position < (lead ++ [last]).length),
      checker[start + position]'(by simp only [List.length_append, List.length_singleton] at hp; omega) =
        (lead ++ [last])[position])
    (hstraight : ∀ op ∈ lead, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false)
    (hr : ∀ count ≤ lead.length + 1,
      RegistersBound full.length q (runOps (rawIncidenceROM q full) ((lead ++ [last]).take count) state))
    (ha : ∀ count (hc : count < (lead ++ [last]).length),
      NatAccessFits (rawIncidenceROM q full) 8
        (runOps (rawIncidenceROM q full) ((lead ++ [last]).take count) state) (lead ++ [last])[count])
    (hend : QuickPC (runOps (rawIncidenceROM q full) (lead ++ [last]) state).pc) :
    ∀ count ≤ lead.length + 1,
      SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  have hlcode : ∀ position (hp : position < lead.length),
      checker[start + position]'(by omega) = lead[position] := by
    intro position hp
    exact (hcode position (by simp; omega)).trans (List.getElem_append_left hp)
  have hlast : checker[start + lead.length]'(by omega) = last := by
    exact (hcode lead.length (by simp)).trans
      ((List.getElem_append_right (Nat.le_refl _)).trans (by simp only [Nat.sub_self, List.getElem_cons_zero]))
  intro count hc
  rw [natRun_segment_prefix (rawIncidenceROM q full) checker lead last start hbound hlcode hlast
    hstraight state hpc hactive count hc]
  by_cases hfull : count = lead.length + 1
  · have ht : ((lead ++ [last]).take count) = lead ++ [last] := by rw [hfull]; simp
    rw [ht]
    exact safePoint_of_quickPC q full _ (by simpa only [ht] using hr count hc) hend
  · have hle : count ≤ lead.length := by omega
    have hidx : start + count < checker.length := by omega
    have ht : ((lead ++ [last]).take count) = lead.take count := List.take_append_of_le_length hle
    have hprefix : ∀ op ∈ lead.take count, NoJump op :=
      fun op ho => hstraight op (List.mem_of_mem_take ho)
    have hpc' : (runOps (rawIncidenceROM q full) ((lead ++ [last]).take count) state).pc =
        5 * (start + count) := by
      rw [ht, runOps_pc _ _ _ hprefix, List.length_take_of_le hle, hpc]
      omega
    apply safePoint_of_body q full _ (start + count) hidx hpc' (hr count hc)
    rw [hcode count (by simp; omega)]
    exact ha count (by simp; omega)

theorem checker_test_safe (q : Nat) (full : List (Finset (Fin q)))
    (bound counter exit start : Nat) (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false)
    (hr : RegistersBound full.length q state) (hb : bound < 8) (hc : counter < 8) (he : exit ≤ 126)
    (hv : state.heap bound ≤ registerBound full.length q) (hw : state.heap counter ≤ registerBound full.length q)
    (hbound : start + 7 ≤ checker.length)
    (hcode : ∀ position (hp : position < (testCell bound counter exit).length),
      checker[start + position]'(by change position < 7 at hp; omega) = (testCell bound counter exit)[position])
    (hexit : QuickPC (5 * exit)) (hafter : QuickPC (5 * (start + 7))) :
    ∀ count ≤ 7, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  let lead := (testCell bound counter exit).take 6
  have hlen : lead.length = 6 := rfl
  have hblock : lead ++ [.jumpIfZero .flag .index] = testCell bound counter exit := rfl
  have hend : QuickPC (runOps (rawIncidenceROM q full) (testCell bound counter exit) state).pc := by
    rw [(runOps_testCell _ bound counter exit state).2.2.1, hpc]
    split_ifs
    · exact hexit
    · convert hafter using 1
  have h := checker_segment_prefix_safe q full lead (.jumpIfZero .flag .index) start
    (by simpa only [hlen] using hbound) (by simpa only [hblock] using hcode)
    (by simp [lead, testCell, loadCell, NoJump]) state hpc hactive
    (fun count hcount => by
      rw [hblock]
      exact testCell_prefix_registerBound full.length q _ bound counter exit state hr hb hc he hv hw count
        (by simpa only [hlen] using hcount))
    (by
      intro count hcount
      simpa only [hblock] using testCell_prefix_accessFits (rawIncidenceROM q full) bound counter exit
        state hb hc count (by simpa only [hblock] using hcount))
    (by simpa only [hblock] using hend)
  simpa only [hlen] using h

theorem prefix_registerBound_append (N q : Nat) (rom : PhysicalROM) (left right : List PackingOp)
    (state : NatState)
    (hl : ∀ count ≤ left.length, RegistersBound N q (runOps rom (left.take count) state))
    (hr : ∀ count ≤ right.length, RegistersBound N q (runOps rom (right.take count) (runOps rom left state))) :
    ∀ count ≤ (left ++ right).length, RegistersBound N q (runOps rom ((left ++ right).take count) state) := by
  intro count hc
  by_cases hleft : count ≤ left.length
  · rw [List.take_append_of_le_length hleft]
    exact hl count hleft
  · have hsplit : count = left.length + (count - left.length) := by omega
    rw [hsplit, List.take_add, List.take_append_of_le_length (Nat.le_refl _), List.take_length,
      List.drop_left, runOps_append]
    exact hr (count - left.length) (by rw [List.length_append] at hc; omega)

theorem prefix_accessFits_append (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hl : ∀ count (hc : count < left.length),
      NatAccessFits rom 8 (runOps rom (left.take count) state) left[count])
    (hr : ∀ count (hc : count < right.length),
      NatAccessFits rom 8 (runOps rom (right.take count) (runOps rom left state)) right[count]) :
    ∀ count (hc : count < (left ++ right).length),
      NatAccessFits rom 8 (runOps rom ((left ++ right).take count) state) (left ++ right)[count] := by
  intro count hc
  by_cases hleft : count < left.length
  · rw [List.take_append_of_le_length hleft.le, List.getElem_append_left hleft]
    exact hl count hleft
  · have hle : left.length ≤ count := by omega
    have hsplit : count = left.length + (count - left.length) := by omega
    have ht : (left ++ right).take count = left ++ right.take (count - left.length) := by
      conv_lhs => rw [hsplit, List.take_add,
        List.take_append_of_le_length (Nat.le_refl _), List.take_length, List.drop_left]
    rw [ht, runOps_append, List.getElem_append_right hle]
    exact hr (count - left.length) (by rw [List.length_append] at hc; omega)

theorem safe_prefix_add (q : Nat) (full : List (Finset (Fin q))) (state : NatState) (left right : Nat)
    (hl : ∀ count ≤ left, SafePoint q full (natRun (rawIncidenceROM q full) checker count state))
    (hr : ∀ count ≤ right, SafePoint q full
      (natRun (rawIncidenceROM q full) checker count (natRun (rawIncidenceROM q full) checker left state))) :
    ∀ count ≤ left + right, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  intro count hc
  by_cases hleft : count ≤ left
  · exact hl count hleft
  · have hsplit : count = left + (count - left) := by omega
    rw [hsplit, natRun_add]
    exact hr (count - left) (by omega)

theorem checker_incrementJump_safe (q : Nat) (full : List (Finset (Fin q)))
    (cell exit start : Nat) (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false)
    (hr : RegistersBound full.length q state) (hc : cell < 8) (he : exit ≤ 126)
    (hv : state.heap cell + 1 ≤ registerBound full.length q)
    (hbound : start + 9 ≤ checker.length)
    (hcode : ∀ position (hp : position < (incrementCell cell ++ jumpTo exit).length),
      checker[start + position]'(by change position < 6 + 3 at hp; omega) = (incrementCell cell ++ jumpTo exit)[position])
    (hexit : QuickPC (5 * exit)) :
    ∀ count ≤ 9, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  let block := incrementCell cell ++ jumpTo exit
  let lead := block.take 8
  have hlen : lead.length = 8 := rfl
  have hblock : lead ++ [.jumpIfZero .flag .index] = block := rfl
  have hir : RegistersBound full.length q (runOps (rawIncidenceROM q full) (incrementCell cell) state) :=
    (by simpa only [show 6 = (incrementCell cell).length from rfl, List.take_length] using
      incrementCell_prefix_registerBound full.length q _ cell state hr hc hv 6 le_rfl)
  have hreg := prefix_registerBound_append full.length q (rawIncidenceROM q full)
    (incrementCell cell) (jumpTo exit) state
    (fun count hcount => incrementCell_prefix_registerBound full.length q _ cell state hr hc hv count hcount)
    (fun count hcount => jumpTo_prefix_registerBound full.length q _ exit _ hir he count hcount)
  have haccess := prefix_accessFits_append (rawIncidenceROM q full) (incrementCell cell) (jumpTo exit) state
    (fun count hcount => incrementCell_prefix_accessFits _ cell state hc count hcount)
    (fun count hcount => jumpTo_prefix_accessFits _ exit _ count hcount)
  have hend : QuickPC (runOps (rawIncidenceROM q full) block state).pc := by
    have hp : (runOps (rawIncidenceROM q full) block state).pc = 5 * exit := by
      simp [block, runOps_append, runOps, jumpTo, natExecuteOp, Op.execute, Instruction.execute]
    rw [hp]
    exact hexit
  have h := checker_segment_prefix_safe q full lead (.jumpIfZero .flag .index) start
    (by simpa only [hlen] using hbound) (by simpa only [hblock, block] using hcode)
    (by simp [lead, block, incrementCell, loadCell, storeCell, jumpTo, NoJump]) state hpc hactive
    (by simpa only [hblock, block, hlen, show (incrementCell cell ++ jumpTo exit).length = 9 from rfl] using hreg)
    (by simpa only [hblock, block] using haccess)
    (by simpa only [hblock] using hend)
  simpa only [hlen] using h

theorem checker_nextPair_safe (q : Nat) (full : List (Finset (Fin q))) (i j : Nat) (state : NatState)
    (ready : Ready full.length q i j 540 state) (_hi : i < full.length) (hj : j < full.length)
    (hr : RegistersBound full.length q state) :
    ∀ count ≤ 9, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  refine checker_incrementJump_safe q full 3 20 108 state ready.pc ready.active hr (by decide) (by decide)
    ?_ (by rw [checker_length]; decide) ?_ ?_
  · rw [ready.right]
    dsimp [registerBound]
    omega
  · intro position hp
    change position < 9 at hp
    interval_cases position <;> rfl
  · decide

theorem checker_nextRow_safe (q : Nat) (full : List (Finset (Fin q))) (i j : Nat) (state : NatState)
    (ready : Ready full.length q i j 585 state) (hi : i < full.length) (_hj : j ≤ full.length)
    (hr : RegistersBound full.length q state) :
    ∀ count ≤ 9, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  refine checker_incrementJump_safe q full 2 10 117 state ready.pc ready.active hr (by decide) (by decide)
    ?_ (by decide) ?_ ?_
  · rw [ready.left]
    dsimp [registerBound]
    omega
  · intro position hp
    change position < 9 at hp
    interval_cases position <;> rfl
  · decide

theorem checker_outerTest_safe (q : Nat) (full : List (Finset (Fin q))) (i j : Nat) (state : NatState)
    (ready : Ready full.length q i j 50 state) (hi : i ≤ full.length)
    (hr : RegistersBound full.length q state) :
    ∀ count ≤ 7, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  refine checker_test_safe q full 0 2 126 10 state ready.pc ready.active hr (by decide) (by decide) (by decide)
    ?_ ?_ (by rw [checker_length]; decide) ?_ ?_ ?_
  · rw [ready.dimension]; dsimp [registerBound]; omega
  · rw [ready.left]; dsimp [registerBound]; omega
  · intro position hp
    change position < 7 at hp
    interval_cases position <;> rfl
  · decide
  · decide

theorem checker_pairTest_safe (q : Nat) (full : List (Finset (Fin q))) (i j : Nat) (state : NatState)
    (ready : Ready full.length q i j 100 state) (hj : j ≤ full.length)
    (hr : RegistersBound full.length q state) :
    ∀ count ≤ 7, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  refine checker_test_safe q full 0 3 117 20 state ready.pc ready.active hr (by decide) (by decide) (by decide)
    ?_ ?_ (by rw [checker_length]; decide) ?_ ?_ ?_
  · rw [ready.dimension]; dsimp [registerBound]; omega
  · rw [ready.right]; dsimp [registerBound]; omega
  · intro position hp
    change position < 7 at hp
    interval_cases position <;> rfl
  · decide
  · decide

theorem checker_pair_terminal_safe (q : Nat) (full : List (Finset (Fin q))) (i : Nat) (state : NatState)
    (ready : Ready full.length q i full.length 100 state) (_hi : i < full.length)
    (hr : RegistersBound full.length q state) :
    ∀ count ≤ 7, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) :=
  checker_pairTest_safe q full i full.length state ready le_rfl hr

theorem checker_outer_terminal_safe (q : Nat) (full : List (Finset (Fin q))) (j : Nat) (state : NatState)
    (ready : Ready full.length q full.length j 50 state) (_hj : j ≤ full.length)
    (hr : RegistersBound full.length q state) :
    ∀ count ≤ 8, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  have htest := checker_outerTest_safe q full full.length j state ready le_rfl hr
  let tested := natRun (rawIncidenceROM q full) checker 7 state
  have hpc : tested.pc = 630 := by
    rw [show tested = runOps (rawIncidenceROM q full) (testCell 0 2 126) state from
      natRun_checker_outerTest _ state ready.pc ready.active]
    simpa only [ready.dimension, ready.left, Nat.sub_self, ite_true] using
      (runOps_testCell (rawIncidenceROM q full) 0 2 126 state).2.2.1
  have hactive : tested.halted = false := by
    rw [show tested = runOps (rawIncidenceROM q full) (testCell 0 2 126) state from
      natRun_checker_outerTest _ state ready.pc ready.active, runOps_halted, ready.active]
  apply safe_prefix_add q full state 7 1 htest
  intro count hc
  have hrTest : RegistersBound full.length q tested := (htest 7 le_rfl).1
  have hc' : count = 0 ∨ count = 1 := by omega
  rcases hc' with rfl | rfl
  · exact htest 7 le_rfl
  · rw [natRun_checker_halt _ tested hpc hactive]
    exact safePoint_of_halt q full _ hpc hrTest

end PaperProofs.Structure.LaminarTree.RawIncidenceMacroSafety
