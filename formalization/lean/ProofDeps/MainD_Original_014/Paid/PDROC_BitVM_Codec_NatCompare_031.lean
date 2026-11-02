module

public import Paid.PDROC_BitVM_Codec_NatCompare_030

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Codec.NatCompare

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PDROC.BitVM.Codec.FieldOps (Path)

theorem state_at_label (state : State) (label : Label) (position : state.l = some label) :
    state = (⟨some label, state.var, state.stk⟩ : State) := by
  rcases state with ⟨oldLabel, saved, contents⟩
  change oldLabel = some label at position
  subst oldLabel
  rfl

/-- Parentheses specify Bool negation BEFORE equality. This is the exact
actual finite inspector output on the two complete Nat Cell words. -/
theorem read_bool (flag : Bool) :
    (!PDROC.BitVM.Kernel.Branch.zeroFlag
      (PDROC.BitVM.Kernel.Branch.captured (encodeCellBits (.natural (if flag then 1 else 0))))) = flag := by
  cases flag <;> rfl

def coreScalarBudget (left right : Register) (size a b : ℕ) : ℕ :=
  PDROC.BitVM.Kernel.NatInstruction.computeBudget a b +
    32 * (3 * (size + PDROC.BitVM.Kernel.InternalInstruction.computePushCap .lessEqual left right *
      PDROC.BitVM.Kernel.NatInstruction.computeBudget a b) + 1) + 2

def readBudget (left right : Register) (contents : Stack → List Bool) (a b : ℕ) : ℕ :=
  64 * (RatMarshal.globalSize contents + 4) +
    coreScalarBudget left right (RatMarshal.globalSize contents) a b +
    coreScalarBudget right left (32 * (RatMarshal.globalSize contents + 4)) b a

theorem coreBudget_le (left right : Register) (contents : Stack → List Bool) (size a b : ℕ)
    (bounded : RatMarshal.globalSize contents ≤ size) :
    coreBudget left right contents a b ≤ coreScalarBudget left right size a b := by
  change PDROC.BitVM.Kernel.NatInstruction.dataSize contents ≤ size at bounded
  unfold coreBudget coreCeiling coreScalarBudget
  omega

theorem globalSize_le (contents : Stack → List Bool) (size : ℕ)
    (bounded : ∀ role, (contents role).length ≤ size) : RatMarshal.globalSize contents ≤ 32 * size := by
  unfold RatMarshal.globalSize
  calc
    ∑ role : Stack, (contents role).length ≤ ∑ _role : Stack, size :=
      Finset.sum_le_sum (fun role _ => bounded role)
    _ = 32 * size := by simp

theorem bool_cell_length (flag : Bool) :
    (encodeCellBits (.natural (if flag then 1 else 0))).length = 4 := by cases flag <;> rfl

/-- Reset, actual work clears, AB computation, actual AB inspection,
BA computation and actual BA inspection on ONE path. Both original
register operands survive the whole prefix, including source aliases. -/
theorem read_both (comparison : Comparison) (target left right : Register)
    (logical : PaperProofs.Paid.Computation.State) (a b : ℕ)
    (contents : Stack → List Bool) (saved : Store)
    (represented : ∀ reg, contents (registerSlot reg) = encodeCellBits (logical.register reg))
    (leftNat : logical.register left = .natural a) (rightNat : logical.register right = .natural b) :
    ∃ ready : State, ∃ path : Path (program comparison target left right) (before contents saved) ready,
      ready.l = some (control 6) ∧ resultFlag comparison ready.var = comparison.nat a b ∧
      ready.stk 0 = [] ∧ ready.stk 24 = [] ∧
      ready.stk 25 = encodeCellBits (.natural (if decide (a ≤ b) then 1 else 0)) ∧
      ready.stk 26 = encodeCellBits (.natural (if decide (b ≤ a) then 1 else 0)) ∧
      (∀ reg, ready.stk (registerSlot reg) = contents (registerSlot reg)) ∧
      (∀ other, other ≠ 0 → other ≠ 24 → other ≠ 25 → other ≠ 26 → ready.stk other = contents other) ∧
      path.states.length ≤ readBudget left right contents a b := by
  let old0 := Function.update contents 0 []
  let entry := FieldOps.prefixContents contents
  let part0 := Path.single (reset_step comparison target left right contents saved)
  obtain ⟨part1, size1⟩ := clear_call comparison target left right 0 contents clearedStore
  obtain ⟨part2, size2⟩ := clear_call comparison target left right 1 old0 clearedStore
  have entryRep : ∀ reg, entry (registerSlot reg) = encodeCellBits (logical.register reg) :=
    fun reg => (FieldOps.prefix_register contents reg).trans (represented reg)
  obtain ⟨firstEnd, firstPath, firstPos, firstBranch, _firstFlag, first0, first24,
    firstCell, firstFrame, firstTime⟩ :=
    core_call comparison target left right false logical a b entry
      (none, none, none, none, none) false entryRep leftNat rightNat
      (by simp [entry, FieldOps.prefixContents]) (by simp [entry, FieldOps.prefixContents])
  change firstEnd.stk 25 = _ at firstCell
  have firstEq : firstEnd = (⟨some (control 3), firstEnd.var, firstEnd.stk⟩ : State) :=
    state_at_label firstEnd (control 3) firstPos
  let part3 := firstPath.castLast firstEq
  obtain ⟨part4, size4⟩ := branch_call comparison target left right false firstEnd.stk firstEnd.var
  let abCaptured := PDROC.BitVM.Kernel.Branch.captured (firstEnd.stk 25)
  have abFlag : (!PDROC.BitVM.Kernel.Branch.zeroFlag abCaptured) = decide (a ≤ b) := by
    dsimp only [abCaptured]
    rw [firstCell]
    exact read_bool _
  let savedAB : Store := (abCaptured, firstEnd.var.2)
  let savePath := Path.single (save_step comparison target left right firstEnd.stk savedAB)
  have saveEq : (⟨some (coreLabels true (.inl 0)),
      (abCaptured, (coreInitial, !PDROC.BitVM.Kernel.Branch.zeroFlag abCaptured)), firstEnd.stk⟩ : State) =
      (⟨some (coreLabels true (.inl 0)), (abCaptured, (coreInitial, decide (a ≤ b))), firstEnd.stk⟩ : State) := by
    rw [abFlag]
  let part5 := savePath.castLast saveEq
  have firstRegs : ∀ reg, firstEnd.stk (registerSlot reg) = contents (registerSlot reg) := by
    intro reg
    exact (firstFrame _ (RatMarshal.source_not_right reg) (RatMarshal.register_not_left reg)
      (RatMarshal.register_not_temp reg 0)).trans (FieldOps.prefix_register contents reg)
  have firstRep : ∀ reg, firstEnd.stk (registerSlot reg) = encodeCellBits (logical.register reg) :=
    fun reg => (firstRegs reg).trans (represented reg)
  obtain ⟨secondEnd, secondPath, secondPos, _secondBranch, secondFlag, second0, second24,
    secondCell, secondFrame, secondTime⟩ :=
    core_call comparison target left right true logical b a firstEnd.stk abCaptured (decide (a ≤ b))
      firstRep rightNat leftNat first0 first24
  change secondEnd.stk 26 = _ at secondCell
  have secondEq : secondEnd = (⟨some (control 5), secondEnd.var, secondEnd.stk⟩ : State) :=
    state_at_label secondEnd (control 5) secondPos
  let part6 := secondPath.castLast secondEq
  obtain ⟨part7, size7⟩ := branch_call comparison target left right true secondEnd.stk secondEnd.var
  let final : State := ⟨some (control 6),
    (PDROC.BitVM.Kernel.Branch.captured (secondEnd.stk 26), secondEnd.var.2), secondEnd.stk⟩
  let joined := ((((((part0.append part1).append part2).append part3).append part4).append part5).append part6).append part7
  have flagCorrect : resultFlag comparison final.var = comparison.nat a b := by
    change combine comparison secondEnd.var.2.2
      (!PDROC.BitVM.Kernel.Branch.zeroFlag (PDROC.BitVM.Kernel.Branch.captured (secondEnd.stk 26))) = _
    rw [secondFlag, secondCell, read_bool, combine_correct]
  have oldFrame : ∀ other, other ≠ 0 → other ≠ 24 → other ≠ 25 → other ≠ 26 →
      secondEnd.stk other = contents other := by
    intro other not0 not24 not25 not26
    rw [secondFrame other not0 not24 not26, firstFrame other not0 not24 not25]
    dsimp only [entry, FieldOps.prefixContents]
    rw [Function.update_of_ne not24, Function.update_of_ne not0]
  have final25 : secondEnd.stk 25 = encodeCellBits (.natural (if decide (a ≤ b) then 1 else 0)) :=
    (secondFrame 25 (by decide) (by decide) (by decide)).trans firstCell
  let g := RatMarshal.globalSize contents
  have entrySize : RatMarshal.globalSize entry ≤ g := by
    unfold RatMarshal.globalSize
    apply Finset.sum_le_sum
    intro role _
    by_cases is0 : role = 0
    · subst role
      simp [entry, FieldOps.prefixContents]
    by_cases is24 : role = 24
    · subst role
      simp [entry, FieldOps.prefixContents]
    · simp only [entry, FieldOps.prefixContents, Function.update_of_ne is24, Function.update_of_ne is0, le_refl]
  have firstEach : ∀ role, (firstEnd.stk role).length ≤ g + 4 := by
    intro role
    by_cases is0 : role = 0
    · subst role; rw [first0]; simp
    by_cases is24 : role = 24
    · subst role; rw [first24]; simp
    by_cases is25 : role = 25
    · subst role; rw [firstCell, bool_cell_length]; omega
    rw [firstFrame role is0 is24 is25]
    exact (RatMarshal.initial_le_globalSize entry role).trans (entrySize.trans (Nat.le_add_right _ _))
  have firstSize : RatMarshal.globalSize firstEnd.stk ≤ 32 * (g + 4) := globalSize_le _ _ firstEach
  have firstBound : part3.states.length ≤ coreScalarBudget left right g a b :=
    firstTime.trans (coreBudget_le left right entry g a b entrySize)
  have secondBound : part6.states.length ≤ coreScalarBudget right left (32 * (g + 4)) b a :=
    secondTime.trans (coreBudget_le right left firstEnd.stk _ b a firstSize)
  have total : joined.states.length ≤ 2 + part1.states.length + part2.states.length + part3.states.length +
      part4.states.length + 2 + part6.states.length + part7.states.length := by
    have h1 := part0.append_length part1
    have h2 := (part0.append part1).append_length part2
    have h3 := ((part0.append part1).append part2).append_length part3
    have h4 := (((part0.append part1).append part2).append part3).append_length part4
    have h5 := ((((part0.append part1).append part2).append part3).append part4).append_length part5
    have h6 := (((((part0.append part1).append part2).append part3).append part4).append part5).append_length part6
    have h7 := ((((((part0.append part1).append part2).append part3).append part4).append part5).append part6).append_length part7
    dsimp only [part0, part5, savePath, Path.single, Path.castLast] at h1 h2 h3 h4 h5 h6 h7
    simp only [List.length_cons, List.length_nil] at h1 h2 h3 h4 h5 h6 h7
    dsimp only [joined, part0, part5, savePath, Path.single, Path.castLast]
    omega
  have time : joined.states.length ≤ readBudget left right contents a b := by
    change part1.states.length = (contents 0).length + 2 at size1
    change part2.states.length = (old0 24).length + 2 at size2
    have same24 : old0 24 = contents 24 := by simp [old0]
    rw [same24] at size2
    have initial0 := RatMarshal.initial_le_globalSize contents 0
    have initial24 := RatMarshal.initial_le_globalSize contents 24
    change (contents 0).length ≤ g at initial0
    change (contents 24).length ≤ g at initial24
    rw [size1, size2, size4, size7] at total
    change joined.states.length ≤ 64 * (g + 4) + coreScalarBudget left right g a b +
      coreScalarBudget right left (32 * (g + 4)) b a
    omega
  refine ⟨final, joined, rfl, flagCorrect, second0, second24, final25, secondCell, ?_, oldFrame, time⟩
  intro reg
  exact oldFrame _ (RatMarshal.source_not_right reg) (RatMarshal.register_not_left reg)
    (RatMarshal.register_not_temp reg 0) (RatMarshal.register_not_temp reg 1)

end PDROC.BitVM.Codec.NatCompare
