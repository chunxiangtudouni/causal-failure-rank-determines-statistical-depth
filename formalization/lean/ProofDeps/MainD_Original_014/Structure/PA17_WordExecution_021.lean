module

public import PaperProofs.Structure.PackingWordRefinement

/-! Exact refinement for AlgorithmClaims' original nonpacked wordRun.
The hypotheses are actual prefix certificates, not extra paper inputs.
This machine lemma does not supply those certificates for an algorithm. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17WordExecution021

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def natState (state : State) : PackingMachine.NatState :=
  ⟨state.register, state.heap, state.pc, false⟩

theorem op_toWord (bits : Nat) (rom : PhysicalROM) (op : Op) (state : State)
    (hregister : ∀ register, Fits bits (state.register register)) :
    wordOp rom op (wordState bits state) = wordState bits (op.execute rom.semantic state) := by
  exact PackingMachine.natExecuteOp_toWord rom (.base op) (natState state) hregister

theorem wordRun_succ (bits : Nat) (rom : PhysicalROM) (code : List (BitVec bits))
    (count : Nat) (state : WordState bits) :
    wordRun rom code (count + 1) state = wordStep rom code (wordRun rom code count state) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    change wordRun rom code (count + 1) (wordStep rom code state) =
      wordStep rom code (wordRun rom code (count + 1) state)
    rw [ih]
    rfl

theorem wordStep_body (bits : Nat) (rom : PhysicalROM) (program : List Op) (index : Nat)
    (hi : index < program.length) (state : State) (hpc : state.pc = 5 * index)
    (hcode : WordsFit bits (haltingWords program)) (hpcFit : Fits bits state.pc)
    (hregister : ∀ register, Fits bits (state.register register)) :
    wordStep rom ((haltingWords program).map (BitVec.ofNat bits)) (wordState bits state) =
      wordState bits ((program[index]'hi).execute rom.semantic state) := by
  have hp : (BitVec.ofNat bits state.pc).toNat = state.pc := Nat.mod_eq_of_lt hpcFit
  change (match Op.decodeWords (PackingMachine.physicalFetch bits (haltingWords program)
      (BitVec.ofNat bits state.pc).toNat) with
    | none => { wordState bits state with halted := true }
    | some op => wordOp rom op (wordState bits state)) = _
  rw [hp, PackingMachine.physicalFetch_eq bits (haltingWords program) state.pc hcode,
    hpc, fetchWords_halting_body program index hi, Op.decodeWords_encodeWords]
  exact op_toWord bits rom _ state hregister

theorem wordStep_terminal (bits : Nat) (rom : PhysicalROM) (program : List Op) (state : State)
    (hpc : state.pc = 5 * program.length) (hcode : WordsFit bits (haltingWords program))
    (hpcFit : Fits bits state.pc) :
    wordStep rom ((haltingWords program).map (BitVec.ofNat bits)) (wordState bits state) =
      { wordState bits state with halted := true } := by
  have hp : (BitVec.ofNat bits state.pc).toNat = state.pc := Nat.mod_eq_of_lt hpcFit
  change (match Op.decodeWords (PackingMachine.physicalFetch bits (haltingWords program)
      (BitVec.ofNat bits state.pc).toNat) with
    | none => { wordState bits state with halted := true }
    | some op => wordOp rom op (wordState bits state)) = _
  rw [hp, PackingMachine.physicalFetch_eq bits (haltingWords program) state.pc hcode,
    hpc, IndexedClosureRAM.fetchWords_halting_terminal, Op.decodeWords_halt]

theorem execute_take_succ (rom : ROM) (program : List Op) (index : Nat) (hi : index < program.length)
    (state : State) :
    execute rom (program.take (index + 1)) state =
      (program[index]'hi).execute rom (execute rom (program.take index) state) := by
  rw [List.take_succ_eq_append_getElem hi, IndexedClosureRAM.execute_append]
  rfl

theorem wordRefines_of_prefixFits (bits : Nat) (rom : PhysicalROM) (program : List Op) (state : State)
    (hpc : state.pc = 0) (hcode : WordsFit bits (haltingWords program))
    (hprefix : ∀ count ≤ program.length,
      Fits bits (execute rom.semantic (program.take count) state).pc ∧
        ∀ register, Fits bits ((execute rom.semantic (program.take count) state).register register)) :
    WordRefines bits rom program state := by
  have hrun (count : Nat) (hc : count ≤ program.length) :
      wordRun rom ((haltingWords program).map (BitVec.ofNat bits)) count (wordState bits state) =
        wordState bits (execute rom.semantic (program.take count) state) := by
    induction count with
    | zero => rfl
    | succ count ih =>
      have hi : count < program.length := by omega
      rw [wordRun_succ, ih (by omega), execute_take_succ rom.semantic program count hi state]
      have hp : (execute rom.semantic (program.take count) state).pc = 5 * count := by
        rw [IndexedClosureRAM.execute_pc, hpc, List.length_take, Nat.min_eq_left (by omega), Nat.zero_add]
      exact wordStep_body bits rom program count hi _ hp hcode (hprefix count (by omega)).1
        (hprefix count (by omega)).2
  constructor
  · exact hrun
  · rw [wordRun_succ, hrun program.length le_rfl, List.take_length]
    have hp : (execute rom.semantic program state).pc = 5 * program.length := by
      rw [IndexedClosureRAM.execute_pc, hpc, Nat.zero_add]
    have hpFit : Fits bits (execute rom.semantic program state).pc := by
      simpa only [List.take_length] using (hprefix program.length le_rfl).1
    exact wordStep_terminal bits rom program _ hp hcode hpFit

theorem wordRefines_of_finiteSafe (bits heapWords : Nat) (rom : PhysicalROM) (program : List Op)
    (state : State) (hpc : state.pc = 0) (hsafe : FiniteSafe bits heapWords rom program state) :
    WordRefines bits rom program state := by
  apply wordRefines_of_prefixFits bits rom program state hpc hsafe.1
  intro count hc
  have hs := hsafe.2.2.2.1 count hc
  exact ⟨lt_of_le_of_lt (Nat.le_add_right _ 4) hs.1, hs.2.1⟩

theorem op_heapFits (bits heapWords : Nat) (rom : ROM) (op : Op) (state : State)
    (hheap : ∀ address < heapWords, Fits bits (state.heap address))
    (hregister : ∀ register, Fits bits (state.register register)) :
    ∀ address < heapWords, Fits bits ((op.execute rom state).heap address) := by
  intro address ha
  cases op with
  | subtract target left right => exact hheap address ha
  | base instruction =>
    cases instruction with
    | storeHeap pointer source =>
      change Fits bits (Function.update state.heap (state.register pointer) (state.register source) address)
      by_cases heq : address = state.register pointer
      · rw [heq, Function.update_self]
        exact hregister source
      · rw [Function.update_of_ne heq]
        exact hheap address ha
    | constant target value => exact hheap address ha
    | add target left right => exact hheap address ha
    | minimum target left right => exact hheap address ha
    | select target condition whenTrue whenFalse => exact hheap address ha
    | loadROM region target pointer => exact hheap address ha
    | loadHeap target pointer => exact hheap address ha

theorem execute_prefix_heapFits (bits heapWords : Nat) (rom : ROM) (program : List Op) (state : State)
    (hinitial : ∀ address < heapWords, Fits bits (state.heap address))
    (hregister : ∀ count < program.length, ∀ register,
      Fits bits ((execute rom (program.take count) state).register register)) :
    ∀ count ≤ program.length, ∀ address < heapWords,
      Fits bits ((execute rom (program.take count) state).heap address) := by
  intro count hc
  induction count with
  | zero => exact hinitial
  | succ count ih =>
    have hi : count < program.length := by omega
    rw [execute_take_succ rom program count hi state]
    exact op_heapFits bits heapWords rom program[count] _ (ih (by omega)) (hregister count hi)

theorem finiteSafe_of_registers_and_access (bits heapWords : Nat) (rom : PhysicalROM)
    (program : List Op) (state : State) (hpc : state.pc = 0)
    (hcode : WordsFit bits (haltingWords program)) (hrom : ∀ region, WordsFit bits (rom.words region))
    (hfootprint : Fits bits (rom.size + heapWords + (haltingWords program).length))
    (hinitial : ∀ address < heapWords, Fits bits (state.heap address))
    (hregister : ∀ count ≤ program.length, ∀ register,
      Fits bits ((execute rom.semantic (program.take count) state).register register))
    (haccess : ∀ count (hc : count < program.length),
      AccessFits rom heapWords (execute rom.semantic (program.take count) state) program[count]) :
    FiniteSafe bits heapWords rom program state := by
  refine ⟨hcode, hrom, hfootprint, ?_, haccess⟩
  intro count hc
  refine ⟨?_, hregister count hc,
    execute_prefix_heapFits bits heapWords rom.semantic program state hinitial
      (fun k hk => hregister k hk.le) count hc⟩
  rw [IndexedClosureRAM.execute_pc, hpc, List.length_take, Nat.min_eq_left hc, Nat.zero_add]
  apply lt_of_le_of_lt _ hfootprint
  rw [haltingWords_length]
  omega

theorem executionClaims_of_finiteSafe (factor N q heapWords : Nat) (rom : PhysicalROM)
    (program : List Op) (state : State) (hpc : state.pc = 0)
    (hsafe : FiniteSafe (indexWidth factor N q) heapWords rom program state) :
    ExecutionClaims factor N q heapWords rom program state :=
  ⟨hsafe, wordRefines_of_finiteSafe _ _ rom program state hpc hsafe,
    IndexedClosureRAM.execute_halts rom.semantic program state hpc⟩

end PaperProofs.Structure.LaminarTree.PA17WordExecution021
