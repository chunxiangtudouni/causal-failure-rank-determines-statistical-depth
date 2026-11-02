module

public import Structure.PSTR_LiveDispatchData_128
public import Structure.PSTR_HD_HeadsReadBranchSafe_100

/-! Fetched readonly dispatcher blocks and SAME-run prefix composition.
Every branch is the real final instruction of its static containing slice.
No heap representation, business state, safe-prefix or restart is assumed. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRLiveDispatch
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRWordSegments PSTRCountKernel PSTRReplySpill PA17A19RuntimeEntry020

structure ReadonlyRun {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (steps heapWords : Nat) (state : WordState bits) : Prop where
  active : (packingRun rom whole steps state).halted = false
  heap : ∀ clock ≤ steps, (packingRun rom whole clock state).heap = state.heap
  reply : ∀ clock ≤ steps, ReplyRegisters state (packingRun rom whole clock state)
  safe : ∀ clock < steps, AtSafe rom whole heapWords (packingRun rom whole clock state)

theorem branch_prefix {bits : Nat} (rom : PhysicalROM) (whole lead : List PackingOp)
    (start : Nat) (test target : Register)
    (block : PSTROuterCountCode.BlockAt whole start (lead ++ [PackingOp.jumpIfZero test target]))
    (straight : StraightProgram lead) (hw : WordsFit bits (packingCode whole))
    (hpc : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (clock : Nat) (hc : clock ≤ lead.length + 1) :
    packingRun rom whole clock state = executeOps rom ((lead ++ [PackingOp.jumpIfZero test target]).take clock) state := by
  by_cases hlead : clock ≤ lead.length
  · rw [List.take_append_of_le_length hlead]
    apply fetched_prefix rom whole lead start _ _ straight hw hpc state hp ha clock hlead
    · have h := block.bound
      simp only [List.length_append, List.length_singleton] at h
      omega
    · intro index hi
      exact (block.code index (by simp only [List.length_append, List.length_singleton]; omega)).trans
        (List.getElem_append_left hi)
  · have he : clock = lead.length + 1 := by omega
    subst clock
    have ht : (lead ++ [PackingOp.jumpIfZero test target]).take (lead.length + 1) = lead ++ [PackingOp.jumpIfZero test target] :=
      List.take_of_length_le (by simp only [List.length_append, List.length_singleton]; omega)
    rw [ht]
    exact branch_run rom whole lead start test target block straight hw hpc state hp ha

theorem readonly_branch_run {bits : Nat} (rom : PhysicalROM) (whole lead : List PackingOp)
    (start heapWords : Nat) (test target : Register)
    (block : PSTROuterCountCode.BlockAt whole start (lead ++ [PackingOp.jumpIfZero test target]))
    (straight : StraightProgram lead) (readonly : ∀ op ∈ lead, ReadOnly op)
    (hw : WordsFit bits (packingCode whole)) (hpc : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (replies : ∀ clock ≤ lead.length + 1, ReplyRegisters state (executeOps rom ((lead ++ [PackingOp.jumpIfZero test target]).take clock) state))
    (access : ∀ clock (hc : clock < lead.length),
      packingAccessFits rom heapWords (executeOps rom (lead.take clock) state) lead[clock]) :
    ReadonlyRun rom whole (lead.length + 1) heapWords state := by
  have bound : start + lead.length + 1 ≤ whole.length := by
    have h := block.bound
    simpa only [List.length_append, List.length_singleton, Nat.add_assoc] using h
  have code : ∀ index (hi : index < lead.length), whole[start + index]'(by omega) = lead[index] := by
    intro index hi
    exact (block.code index (by simp only [List.length_append, List.length_singleton]; omega)).trans
      (List.getElem_append_left hi)
  have last : whole[start + lead.length]'(by omega) = PackingOp.jumpIfZero test target := by
    have h := block.code lead.length (by simp only [List.length_append, List.length_singleton]; omega)
    exact h.trans (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [branch_run rom whole lead start test target block straight hw hpc state hp ha, executeOps_halted]
    exact ha
  · intro clock hc
    rw [branch_prefix rom whole lead start test target block straight hw hpc state hp ha clock hc]
    exact readOnly_prefix_heap rom _ state
      (by intro op ho; rcases List.mem_append.mp ho with hl | hr
          · exact readonly op hl
          · have he : op = PackingOp.jumpIfZero test target := List.mem_singleton.mp hr
            rw [he]
            trivial) clock
  · intro clock hc
    rw [branch_prefix rom whole lead start test target block straight hw hpc state hp ha clock hc]
    exact replies clock hc
  · intro clock hc
    exact (PSTRHeadsRuntime.readonly_branch_prefix_safe rom whole lead heapWords start test target bound code last straight readonly
      hw hpc state hp ha access clock (by omega)).1

theorem ReadonlyRun.append {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (first second heapWords : Nat) (state : WordState bits)
    (head : ReadonlyRun rom whole first heapWords state)
    (tail : ReadonlyRun rom whole second heapWords (packingRun rom whole first state)) :
    ReadonlyRun rom whole (first + second) heapWords state := by
  have split (clock : Nat) (hc : first ≤ clock) :
      packingRun rom whole clock state = packingRun rom whole (clock - first) (packingRun rom whole first state) := by
    rw [← run_add]
    congr 1
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [run_add]
    exact tail.active
  · intro clock hc
    by_cases h : clock ≤ first
    · exact head.heap clock h
    · rw [split clock (by omega), tail.heap _ (by omega), head.heap first le_rfl]
  · intro clock hc
    by_cases h : clock ≤ first
    · exact head.reply clock h
    · rw [split clock (by omega)]
      have old := head.reply first le_rfl
      have fresh := tail.reply (clock - first) (by omega)
      exact ⟨fresh.1.trans old.1, fresh.2.1.trans old.2.1, fresh.2.2.1.trans old.2.2.1, fresh.2.2.2.trans old.2.2.2⟩
  · intro clock hc
    by_cases h : clock < first
    · exact head.safe clock h
    · rw [split clock (by omega)]
      exact tail.safe (clock - first) (by omega)

theorem zero_prefix_reply {bits : Nat} (rom : PhysicalROM) (done : Nat) (state : WordState bits)
    (clock : Nat) (hc : clock ≤ 4) : ReplyRegisters state (executeOps rom ((zeroBlock done).take clock) state) := by
  interval_cases clock <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem command_prefix_reply {bits : Nat} (rom : PhysicalROM) (done : Nat) (state : WordState bits)
    (clock : Nat) (hc : clock ≤ 8) : ReplyRegisters state (executeOps rom ((commandBlock done).take clock) state) := by
  interval_cases clock <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem correct_prefix_reply {bits : Nat} (rom : PhysicalROM) (correct : Nat) (state : WordState bits)
    (clock : Nat) (hc : clock ≤ 4) : ReplyRegisters state (executeOps rom ((correctBlock correct).take clock) state) := by
  interval_cases clock <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem error_prefix_reply {bits : Nat} (rom : PhysicalROM) (failed : Nat) (state : WordState bits)
    (clock : Nat) (hc : clock ≤ 2) : ReplyRegisters state (executeOps rom ((errorBlock failed).take clock) state) := by
  interval_cases clock <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem zero_run {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (whole : List PackingOp) (start done heapWords : Nat) (state : WordState (wordBits full))
    (block : PSTROuterCountCode.BlockAt whole start (zeroBlock done))
    (hw : WordsFit (wordBits full) (packingCode whole)) (hpc : Fits (wordBits full) (5 * whole.length))
    (hp : state.pc = BitVec.ofNat (wordBits full) (5 * start)) (ha : state.halted = false) :
    ReadonlyRun (callInput q full command) whole 4 heapWords state ∧
      (packingRun (callInput q full command) whole 4 state).pc =
        (if q = 0 then BitVec.ofNat (wordBits full) (5 * done) else BitVec.ofNat (wordBits full) (5 * (start + 4))) ∧
      (packingRun (callInput q full command) whole 4 state).register .flag = BitVec.ofNat (wordBits full) q := by
  have run := branch_run (callInput q full command) whole (zeroLead done) start .flag .total block
    (zeroLead_straight done) hw hpc state hp ha
  change packingRun (callInput q full command) whole 4 state = executeOps (callInput q full command) (zeroBlock done) state at run
  have fields := zero_fields full command start done state hp
  refine ⟨?_, ?_, ?_⟩
  · exact readonly_branch_run (callInput q full command) whole (zeroLead done) start heapWords .flag .total block
      (zeroLead_straight done) (by simp [zeroLead, ReadOnly]) hw hpc state hp ha
      (zero_prefix_reply _ done state) (zeroLead_access full command done heapWords state)
  · rw [run]
    exact fields.1
  · rw [run]
    exact fields.2.1

theorem command_run {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (whole : List PackingOp) (start done heapWords : Nat) (state : WordState (wordBits full))
    (block : PSTROuterCountCode.BlockAt whole start (commandBlock done))
    (hw : WordsFit (wordBits full) (packingCode whole)) (hpc : Fits (wordBits full) (5 * whole.length))
    (hp : state.pc = BitVec.ofNat (wordBits full) (5 * start)) (ha : state.halted = false)
    (hqreg : state.register .flag = BitVec.ofNat (wordBits full) q) :
    ReadonlyRun (callInput q full command) whole 8 heapWords state ∧
      (packingRun (callInput q full command) whole 8 state).pc =
        (if command = .query then BitVec.ofNat (wordBits full) (5 * done) else BitVec.ofNat (wordBits full) (5 * (start + 8))) ∧
      (packingRun (callInput q full command) whole 8 state).register .flag = BitVec.ofNat (wordBits full) command.word := by
  have run := branch_run (callInput q full command) whole (commandLead done) start .flag .total block
    (commandLead_straight done) hw hpc state hp ha
  change packingRun (callInput q full command) whole 8 state = executeOps (callInput q full command) (commandBlock done) state at run
  have fields := command_fields full command start done state hp hqreg
  refine ⟨?_, ?_, ?_⟩
  · exact readonly_branch_run (callInput q full command) whole (commandLead done) start heapWords .flag .total block
      (commandLead_straight done) (by simp [commandLead, ReadOnly]) hw hpc state hp ha
      (command_prefix_reply _ done state) (commandLead_access full command done heapWords state hqreg)
  · rw [run]
    exact fields.1
  · rw [run]
    exact fields.2.1

theorem correct_run {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (whole : List PackingOp) (start correct heapWords : Nat) (state : WordState (wordBits full))
    (block : PSTROuterCountCode.BlockAt whole start (correctBlock correct))
    (hw : WordsFit (wordBits full) (packingCode whole)) (hpc : Fits (wordBits full) (5 * whole.length))
    (hp : state.pc = BitVec.ofNat (wordBits full) (5 * start)) (ha : state.halted = false)
    (hcmd : state.register .flag = BitVec.ofNat (wordBits full) command.word) :
    ReadonlyRun (callInput q full command) whole 4 heapWords state ∧
      (packingRun (callInput q full command) whole 4 state).pc =
        (if command = .error then BitVec.ofNat (wordBits full) (5 * (start + 4)) else BitVec.ofNat (wordBits full) (5 * correct)) := by
  have run := branch_run (callInput q full command) whole (correctLead correct) start .flag .total block
    (correctLead_straight correct) hw hpc state hp ha
  change packingRun (callInput q full command) whole 4 state = executeOps (callInput q full command) (correctBlock correct) state at run
  have fields := correct_fields full command start correct state hp hcmd
  refine ⟨?_, ?_⟩
  · exact readonly_branch_run (callInput q full command) whole (correctLead correct) start heapWords .flag .total block
      (correctLead_straight correct) (by simp [correctLead, ReadOnly]) hw hpc state hp ha
      (correct_prefix_reply _ correct state) (correctLead_access _ correct heapWords state)
  · rw [run]
    exact fields.1

theorem error_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (start failed heapWords : Nat) (state : WordState bits)
    (block : PSTROuterCountCode.BlockAt whole start (errorBlock failed))
    (hw : WordsFit bits (packingCode whole)) (hpc : Fits bits (5 * whole.length))
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    ReadonlyRun rom whole 2 heapWords state ∧
      (packingRun rom whole 2 state).pc =
        (if (state.register .index).toNat = 0 then BitVec.ofNat bits (5 * failed) else BitVec.ofNat bits (5 * (start + 2))) := by
  have run := branch_run rom whole (errorLead failed) start .index .total block
    (errorLead_straight failed) hw hpc state hp ha
  change packingRun rom whole 2 state = executeOps rom (errorBlock failed) state at run
  have fields := error_fields rom start failed state hp
  refine ⟨?_, ?_⟩
  · exact readonly_branch_run rom whole (errorLead failed) start heapWords .index .total block
      (errorLead_straight failed) (by simp [errorLead, ReadOnly]) hw hpc state hp ha
      (error_prefix_reply _ failed state) (errorLead_access _ failed heapWords state)
  · rw [run]
    exact fields.1

end PaperProofs.Structure.LaminarTree.PSTRLiveDispatch

