module

public import Common.PSTR_WordBool_TM2Native_040
public import Common.PSTR_TM_Seq_005

/-! The fixed first phase of the raw-output decoder. It actually pops all
fifteen non-output bank, using only a finite label and one Bool flag.
The length sum below measures a real trace; it is never machine input. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Common.Native.PSTRWordBool.RawOutput

open Turing
open scoped BigOperators

abbrev Stacks := Fin 16 → List Bool
abbrev SourceState := TM2.Cfg (fun _ : Fin 16 => Bool) (Fin 16) Bool

def weight (bank : Stacks) : Nat := 1 + ∑ slot : Fin 16, (bank slot).length

def phaseLabel (phase : Nat) (bound : phase ≤ 15) : Fin 16 := ⟨phase, by omega⟩
def phaseSlot (phase : Nat) (bound : phase < 15) : Fin 16 := ⟨phase+1, by omega⟩

def sourceMachine (label : Fin 16) : TM2.Stmt (fun _ : Fin 16 => Bool) (Fin 16) Bool :=
  if before : label.val < 15 then
    .pop ⟨label.val+1, by omega⟩ (fun _ value => value.isSome)
      (.branch id (.goto (fun _ => label))
        (.goto (fun _ => ⟨label.val+1, by omega⟩)))
  else .halt

def sourceCfg (phase : Nat) (bound : phase ≤ 15) (flag : Bool) (bank : Stacks) : SourceState :=
  ⟨some (phaseLabel phase bound), flag, bank⟩

def sourceFinal (bank : Stacks) : SourceState := ⟨none, false, bank⟩

def clearFrom (phase : Nat) (bank : Stacks) : Stacks :=
  fun slot => if phase < slot.val then [] else bank slot

theorem source_closed : TM2.Supports sourceMachine Finset.univ := by
  constructor
  · simp
  · intro label _
    unfold sourceMachine
    split <;> simp [TM2.SupportsStmt]

theorem source_counts (label : Fin 16) :
    ScannerClock.actions (sourceMachine label) ≤ 1 ∧
      AuxWorkspace.pushes (sourceMachine label) = 0 := by
  unfold sourceMachine
  split <;> simp [ScannerClock.actions, AuxWorkspace.pushes]

private theorem updated_lengths (bank : Stacks) (slot : Fin 16) (digits : List Bool)
    (short : digits.length ≤ (bank slot).length) :
    ∀ other, ((Function.update bank slot digits) other).length ≤ (bank other).length := by
  intro other
  by_cases same : other = slot
  · subst other; simpa using short
  · simp [Function.update_of_ne same]

private theorem updated_weight (bank : Stacks) (slot : Fin 16) (digits : List Bool)
    (short : digits.length ≤ (bank slot).length) :
    weight (Function.update bank slot digits) ≤ weight bank := by
  unfold weight
  exact Nat.add_le_add_left (Finset.sum_le_sum (fun other _ => updated_lengths bank slot digits short other)) 1

theorem slot_length_lt_weight (bank : Stacks) (slot : Fin 16) :
    (bank slot).length < weight bank := by
  have part : (bank slot).length ≤ ∑ other : Fin 16, (bank other).length :=
    Finset.single_le_sum (f := fun other : Fin 16 => (bank other).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ slot)
  unfold weight
  omega

private theorem phase_path (phase : Nat) (before : phase < 15) (digits : List Bool)
    (bank : Stacks) (flag : Bool) (actual : bank (phaseSlot phase before) = digits) :
    ∃ rest : List SourceState,
      (sourceCfg phase (by omega) flag bank :: rest).IsChain
        (fun a b => TM2.step sourceMachine a = some b) ∧
      (sourceCfg phase (by omega) flag bank :: rest).getLast? =
        some (sourceCfg (phase+1) (by omega) false
          (Function.update bank (phaseSlot phase before) [])) ∧
      rest.length = digits.length+1 ∧
      (∀ state ∈ sourceCfg phase (by omega) flag bank :: rest, ∀ slot,
        (state.stk slot).length ≤ (bank slot).length) := by
  induction digits generalizing bank flag with
  | nil =>
    have atSlot := actual
    dsimp only [phaseSlot] at atSlot
    let finish := sourceCfg (phase+1) (by omega) false
      (Function.update bank (phaseSlot phase before) [])
    have edge : TM2.step sourceMachine (sourceCfg phase (by omega) flag bank) = some finish := by
      simp [sourceCfg, sourceMachine, phaseLabel, phaseSlot, before, TM2.stepAux, atSlot, finish]
    refine ⟨[finish], ?_, rfl, rfl, ?_⟩
    · simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using edge
    · intro state present slot
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl
      · exact le_rfl
      · exact updated_lengths bank _ [] (by simp) slot
  | cons bit later ih =>
    have atSlot := actual
    dsimp only [phaseSlot] at atSlot
    let changed := Function.update bank (phaseSlot phase before) later
    have changedAt : changed (phaseSlot phase before) = later := by simp [changed]
    obtain ⟨rest, chain, last, clock, bounded⟩ := ih changed true changedAt
    have edge : TM2.step sourceMachine (sourceCfg phase (by omega) flag bank) =
        some (sourceCfg phase (by omega) true changed) := by
      simp [sourceCfg, sourceMachine, phaseLabel, phaseSlot, before, TM2.stepAux, atSlot, changed]
    have final : Function.update changed (phaseSlot phase before) [] =
        Function.update bank (phaseSlot phase before) [] := by simp [changed]
    refine ⟨sourceCfg phase (by omega) true changed :: rest, ?_, ?_, ?_, ?_⟩
    · exact List.isChain_cons_cons.mpr ⟨edge, chain⟩
    · simpa [final] using last
    · simp only [List.length_cons, clock, List.length_cons]
    · intro state present slot
      rcases List.mem_cons.mp present with rfl | present
      · exact le_rfl
      · have short : later.length ≤ (bank (phaseSlot phase before)).length := by
          rw [actual]; simp
        exact (bounded state present slot).trans (updated_lengths bank _ later short slot)

private theorem clearFrom_step (phase : Nat) (before : phase < 15) (bank : Stacks) :
    clearFrom (phase+1) (Function.update bank (phaseSlot phase before) []) = clearFrom phase bank := by
  funext slot
  by_cases same : slot = phaseSlot phase before
  · subst slot
    simp [clearFrom, phaseSlot]
  · have unequal : slot.val ≠ phase+1 := by
      intro equal
      apply same
      exact Fin.ext equal
    have compare : phase+1 < slot.val ↔ phase < slot.val := by omega
    simp only [clearFrom, Function.update_of_ne same, compare]

private theorem clearFrom_end (bank : Stacks) : clearFrom 15 bank = bank := by
  funext slot
  have bound := slot.isLt
  simp [clearFrom, show ¬15 < slot.val by omega]

private theorem source_path_aux (remaining phase : Nat) (total : phase+remaining=15)
    (bank : Stacks) :
    ∃ rest : List SourceState,
      (sourceCfg phase (by omega) false bank :: rest).IsChain
        (fun a b => TM2.step sourceMachine a = some b) ∧
      (sourceCfg phase (by omega) false bank :: rest).getLast? = some (sourceFinal (clearFrom phase bank)) ∧
      rest.length ≤ (remaining+1)*weight bank ∧
      (∀ state ∈ sourceCfg phase (by omega) false bank :: rest, ∀ slot,
        (state.stk slot).length ≤ (bank slot).length) := by
  induction remaining generalizing phase bank with
  | zero =>
    have phaseEq : phase=15 := by omega
    subst phase
    have edge : TM2.step sourceMachine (sourceCfg 15 (by omega) false bank) =
        some (sourceFinal bank) := by
      simp [sourceCfg, sourceMachine, phaseLabel, sourceFinal, TM2.stepAux]
    refine ⟨[sourceFinal bank], ?_, ?_, ?_, ?_⟩
    · simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using edge
    · simp [clearFrom_end]
    · simp [weight]
    · intro state present slot
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> exact le_rfl
  | succ remaining ih =>
    have before : phase < 15 := by omega
    let slot := phaseSlot phase before
    let changed := Function.update bank slot []
    let middle := sourceCfg (phase+1) (by omega) false changed
    obtain ⟨front, frontChain, frontLast, frontClock, frontBound⟩ :=
      phase_path phase before (bank slot) bank false rfl
    obtain ⟨back, backChain, backLast, backClock, backBound⟩ :=
      ih (phase+1) (by omega) changed
    have changedBound := updated_lengths bank slot [] (by simp)
    have changedWeight := updated_weight bank slot [] (by simp)
    have tailBound := Nat.mul_le_mul_left (remaining+1) changedWeight
    have part := slot_length_lt_weight bank slot
    have result : clearFrom (phase+1) changed = clearFrom phase bank :=
      clearFrom_step phase before bank
    refine ⟨front ++ back, ?_, ?_, ?_, ?_⟩
    · exact NativeTrace.join_chain (sourceCfg phase (by omega) false bank :: front)
        middle back frontLast frontChain backChain
    · have last := (NativeTrace.join_last
        (sourceCfg phase (by omega) false bank :: front) middle back frontLast).trans backLast
      simpa only [result, List.cons_append] using last
    · simp only [List.length_append]
      rw [frontClock]
      nlinarith
    · intro state present point
      simp only [List.mem_cons, List.mem_append] at present
      rcases present with rfl | present | present
      · exact le_rfl
      · exact frontBound state (List.mem_cons_of_mem _ present) point
      · exact (backBound state (List.mem_cons_of_mem _ present) point).trans (changedBound point)

/-- A genuine finite source path, all intermediate bank bounded by their
actual original sizes, and a clock in the original sixteen-length sum. -/
theorem source_path (bank : Stacks) :
    ∃ rest : List SourceState,
      (sourceCfg 0 (by omega) false bank :: rest).IsChain
        (fun a b => TM2.step sourceMachine a = some b) ∧
      (sourceCfg 0 (by omega) false bank :: rest).getLast? = some (sourceFinal (clearFrom 0 bank)) ∧
      rest.length ≤ 16*weight bank ∧
      (∀ state ∈ sourceCfg 0 (by omega) false bank :: rest, ∀ slot,
        (state.stk slot).length ≤ (bank slot).length) :=
  source_path_aux 15 0 rfl bank

theorem clear_zero (bank : Stacks) : clearFrom 0 bank (0 : Fin 16) = bank 0 := rfl

theorem clear_other (bank : Stacks) (slot : Fin 16) (nonzero : slot ≠ 0) :
    clearFrom 0 bank slot = [] := by
  have positive : 0 < slot.val := by
    have notZero : slot.val ≠ 0 := by intro equal; exact nonzero (Fin.ext equal)
    omega
  simp [clearFrom, positive]

end PaperProofs.Common.Native.PSTRWordBool.RawOutput
