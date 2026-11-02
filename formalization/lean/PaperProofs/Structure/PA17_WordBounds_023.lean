module

public import PaperProofs.Structure.RawTreeOutputWords
public import PaperProofs.Structure.PA17_WordExecution_021

/-! ROM and encoded-code bounds for the original A17 word model.
Program-specific immediate and prefix bounds remain explicit obligations. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17WordBounds023

open IndexedRAM IndexedClosureRAM AlgorithmClaims

theorem fits_mono_bits {bits larger value : Nat} (hbits : bits ≤ larger) (hfit : Fits bits value) :
    Fits larger value :=
  hfit.trans_le (Nat.pow_le_pow_right (by decide) hbits)

theorem indexWidth_mono_factor (small large N q : Nat) (hf : small ≤ large) :
    indexWidth small N q ≤ indexWidth large N q :=
  Nat.mul_le_mul_right _ hf

theorem cubic_fits (N q value : Nat) (hvalue : value ≤ 65536 * (N + q + 2) ^ 3) :
    Fits (indexWidth 32 N q) value := by
  apply fits_indexWidth_of_lt_power
  let base := N + q + 2
  have hb : 2 ≤ base := by dsimp [base]; omega
  have hp : 65536 < base ^ 29 :=
    lt_of_lt_of_le (by decide : 65536 < 2 ^ 29) (Nat.pow_le_pow_left hb 29)
  have hpos : 0 < base ^ 3 := pow_pos (by omega) _
  calc
    value ≤ 65536 * base ^ 3 := hvalue
    _ < base ^ 3 * base ^ 29 := by nlinarith
    _ = base ^ 32 := by rw [← pow_add]

theorem queryROM_word_le (q : Nat) (full : List (Finset (Fin q)))
    (stage : Fin (full.length + 1)) (used : Finset (Fin q))
    (region : Region) (value : Nat) (hv : value ∈ (queryROM q full stage.val used).words region) :
    value ≤ full.length + q + 1 := by
  cases region with
  | input =>
    change value ∈ ((givenTreeROM q full).input ++ [stage.val]) ++
      (List.finRange q).map (fun tool => bit (decide (tool ∈ used))) at hv
    rw [List.mem_append, List.mem_append] at hv
    rcases hv with (hv | hv) | hv
    · exact RawTreeOutputWords.givenTreeROM_word_le q full .input value hv
    · simp only [List.mem_singleton] at hv
      subst value
      have hs := stage.isLt
      omega
    · obtain ⟨tool, _, rfl⟩ := List.mem_map.mp hv
      simp only [bit]
      split_ifs <;> omega
  | internal => exact RawTreeOutputWords.givenTreeROM_word_le q full .internal value hv
  | children => exact RawTreeOutputWords.givenTreeROM_word_le q full .children value hv

theorem givenTreeROM_wordsFit (q : Nat) (full : List (Finset (Fin q))) :
    ∀ region, WordsFit (indexWidth 32 full.length q) ((givenTreeROM q full).words region) := by
  intro region value hv
  exact fits_mono_bits (indexWidth_mono_factor 16 32 full.length q (by decide))
    (RawTreeOutputWords.givenTreeROM_wordsFit q full region value hv)

theorem queryROM_wordsFit (q : Nat) (full : List (Finset (Fin q)))
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) :
    ∀ region, WordsFit (indexWidth 32 full.length q) ((queryROM q full stage.val used).words region) := by
  intro region value hv
  apply cubic_fits
  have hh := queryROM_word_le q full stage used region value hv
  have hpos : 0 < (full.length + q + 2) ^ 2 := pow_pos (by omega) _
  have hb : full.length + q + 1 ≤ (full.length + q + 2) ^ 3 := by
    calc
      _ ≤ full.length + q + 2 := by omega
      _ = (full.length + q + 2) * 1 := by omega
      _ ≤ (full.length + q + 2) * (full.length + q + 2) ^ 2 :=
        Nat.mul_le_mul_left _ hpos
      _ = (full.length + q + 2) ^ 3 := by ring
  exact hh.trans (hb.trans (by nlinarith))

theorem register_word_le (register : Register) : register.word ≤ 6 := by
  cases register <;> decide

theorem region_word_le (region : Region) : region.word ≤ 2 := by
  cases region <;> decide

def ImmediateFits (bits : Nat) : Op → Prop
  | .base (.constant _ value) => Fits bits value
  | _ => True

theorem op_wordsFit (bits : Nat) (op : Op) (hsmall : Fits bits 8) (himmediate : ImmediateFits bits op) :
    WordsFit bits op.encodeWords.toArray.toList := by
  have hr (register : Register) : Fits bits register.word :=
    lt_of_le_of_lt ((register_word_le register).trans (by decide)) hsmall
  have hregion (region : Region) : Fits bits region.word :=
    lt_of_le_of_lt ((region_word_le region).trans (by decide)) hsmall
  cases op with
  | subtract target left right =>
    intro value hv
    change value ∈ [8, target.word, left.word, right.word, 0] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> first
      | exact hsmall
      | exact hr _
      | exact lt_of_le_of_lt (by decide) hsmall
  | base instruction =>
    cases instruction with
    | constant target number =>
      intro value hv
      change value ∈ [0, target.word, number, 0, 0] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> first
        | exact himmediate
        | exact hr _
        | exact lt_of_le_of_lt (by decide) hsmall
    | add target left right =>
      intro value hv
      change value ∈ [1, target.word, left.word, right.word, 0] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> first
        | exact hr _
        | exact lt_of_le_of_lt (by decide) hsmall
    | minimum target left right =>
      intro value hv
      change value ∈ [2, target.word, left.word, right.word, 0] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> first
        | exact hr _
        | exact lt_of_le_of_lt (by decide) hsmall
    | select target condition whenTrue whenFalse =>
      intro value hv
      change value ∈ [3, target.word, condition.word, whenTrue.word, whenFalse.word] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> first
        | exact hr _
        | exact lt_of_le_of_lt (by decide) hsmall
    | loadROM region target pointer =>
      intro value hv
      change value ∈ [4, region.word, target.word, pointer.word, 0] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> first
        | exact hr _
        | exact hregion _
        | exact lt_of_le_of_lt (by decide) hsmall
    | loadHeap target pointer =>
      intro value hv
      change value ∈ [5, target.word, pointer.word, 0, 0] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> first
        | exact hr _
        | exact lt_of_le_of_lt (by decide) hsmall
    | storeHeap pointer source =>
      intro value hv
      change value ∈ [6, pointer.word, source.word, 0, 0] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> first
        | exact hr _
        | exact lt_of_le_of_lt (by decide) hsmall

theorem haltingWords_fit (bits : Nat) (program : List Op) (hsmall : Fits bits 8)
    (himmediates : ∀ op ∈ program, ImmediateFits bits op) : WordsFit bits (haltingWords program) := by
  intro value hv
  rw [haltingWords, List.mem_append] at hv
  rcases hv with hv | hv
  · obtain ⟨op, ho, hv⟩ := List.mem_flatMap.mp hv
    exact op_wordsFit bits op hsmall (himmediates op ho) value hv
  · change value ∈ [7, 0, 0, 0, 0] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> exact lt_of_le_of_lt (by decide) hsmall

theorem haltingWords_fit_of_prefixRegisters (bits : Nat) (rom : ROM) (program : List Op) (state : State)
    (hsmall : Fits bits 8)
    (hregister : ∀ count ≤ program.length, ∀ register,
      Fits bits ((execute rom (program.take count) state).register register)) :
    WordsFit bits (haltingWords program) := by
  apply haltingWords_fit bits program hsmall
  intro op ho
  obtain ⟨index, hi, heq⟩ := List.getElem_of_mem ho
  cases op with
  | subtract target left right => trivial
  | base instruction =>
    cases instruction with
    | constant target value =>
      have hr := hregister (index + 1) (by omega) target
      rw [PA17WordExecution021.execute_take_succ rom program index hi state, heq] at hr
      simpa only [ImmediateFits, Op.execute, Instruction.execute, Function.update_self] using hr
    | add target left right => trivial
    | minimum target left right => trivial
    | select target condition whenTrue whenFalse => trivial
    | loadROM region target pointer => trivial
    | loadHeap target pointer => trivial
    | storeHeap pointer source => trivial

theorem small_word_fit (N q : Nat) : Fits (indexWidth 32 N q) 8 := by
  apply cubic_fits
  have hp : 0 < (N + q + 2) ^ 3 := pow_pos (by omega) _
  nlinarith

theorem executionClaims_of_numeric_prefix (N q heapWords : Nat) (rom : PhysicalROM)
    (program : List Op) (state : State) (hpc : state.pc = 0)
    (hrom : ∀ region, WordsFit (indexWidth 32 N q) (rom.words region))
    (hfootprint : rom.size + heapWords + (haltingWords program).length ≤ 65536 * (N + q + 2) ^ 3)
    (hinitial : ∀ address < heapWords, Fits (indexWidth 32 N q) (state.heap address))
    (hregister : ∀ count ≤ program.length, ∀ register,
      (execute rom.semantic (program.take count) state).register register ≤ 65536 * (N + q + 2) ^ 3)
    (haccess : ∀ count (hc : count < program.length),
      AccessFits rom heapWords (execute rom.semantic (program.take count) state) program[count]) :
    ExecutionClaims 32 N q heapWords rom program state := by
  have hr (count : Nat) (hc : count ≤ program.length) (register : Register) :
      Fits (indexWidth 32 N q) ((execute rom.semantic (program.take count) state).register register) :=
    cubic_fits N q _ (hregister count hc register)
  exact PA17WordExecution021.executionClaims_of_finiteSafe 32 N q heapWords rom program state hpc
    (PA17WordExecution021.finiteSafe_of_registers_and_access _ heapWords rom program state hpc
      (haltingWords_fit_of_prefixRegisters _ rom.semantic program state (small_word_fit N q) hr)
      hrom (cubic_fits N q _ hfootprint) hinitial hr haccess)

end PaperProofs.Structure.LaminarTree.PA17WordBounds023
