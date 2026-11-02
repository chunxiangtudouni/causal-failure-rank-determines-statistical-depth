module

public import Structure.PSTR_LiveDispatchRun_130

/-! Whole actual18-op dispatcher from ANY seven registers and ORIGINAL
command ROM. The chosen4/12/16/18 clocks are one containing-program run.
Every prefix preserves the entire heap and all four OLD reply registers. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRLiveDispatch
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRWordSegments PSTRCountKernel PSTRReplySpill PA17A19RuntimeEntry020

def duration (q : Nat) (command : Command) : Nat :=
  if q = 0 then 4 else match command with | .query => 12 | .correct => 16 | .error => 18

def destination (q : Nat) (command : Command) (start correct failed done index : Nat) : Nat :=
  if q = 0 then done else match command with
    | .query => done
    | .correct => correct
    | .error => if index = 0 then failed else start + 18

theorem duration_bound (q : Nat) (command : Command) : duration q command ≤ 18 := by
  unfold duration
  split_ifs <;> cases command <;> decide

structure DispatchPost {q : Nat} (full : List (Finset (Fin q))) (command : Command) (whole : List PackingOp)
    (start correct failed done heapWords : Nat) (state : WordState (wordBits full)) : Prop where
  execution : ReadonlyRun (callInput q full command) whole (duration q command) heapWords state
  pc : (packingRun (callInput q full command) whole (duration q command) state).pc =
    BitVec.ofNat (wordBits full) (5 * destination q command start correct failed done (state.register .index).toNat)
  steps : duration q command ≤ 18
  trace : (packingDynamicTrace (callInput q full command) whole (duration q command) state).length ≤ 216

theorem post_of_run {q : Nat} (full : List (Finset (Fin q))) (command : Command) (whole : List PackingOp)
    (start correct failed done heapWords : Nat) (state : WordState (wordBits full))
    (execution : ReadonlyRun (callInput q full command) whole (duration q command) heapWords state)
    (pc : (packingRun (callInput q full command) whole (duration q command) state).pc =
      BitVec.ofNat (wordBits full) (5 * destination q command start correct failed done (state.register .index).toNat)) :
    DispatchPost full command whole start correct failed done heapWords state := by
  have steps := duration_bound q command
  have trace := packingDynamicTrace_length_le (callInput q full command) whole (duration q command) state
  exact ⟨execution, pc, steps, by omega⟩

theorem positive_dispatch {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (whole : List PackingOp) (start correct failed done heapWords : Nat) (state : WordState (wordBits full))
    (hq : q ≠ 0) (block : PSTROuterCountCode.BlockAt whole start (program correct failed done))
    (hw : WordsFit (wordBits full) (packingCode whole)) (hpc : Fits (wordBits full) (5 * whole.length))
    (hp : state.pc = BitVec.ofNat (wordBits full) (5 * start)) (ha : state.halted = false) :
    DispatchPost full command whole start correct failed done heapWords state := by
  let rom := callInput q full command
  let state4 := packingRun rom whole 4 state
  let state12 := packingRun rom whole 12 state
  let state16 := packingRun rom whole 16 state
  have zblock : PSTROuterCountCode.BlockAt whole start (zeroBlock done) := by
    simpa only [Nat.add_zero] using block_trans whole (program correct failed done) (zeroBlock done) start 0 block (zero_slice correct failed done)
  have first := zero_run full command whole start done heapWords state zblock hw hpc hp ha
  have pc4 : state4.pc = BitVec.ofNat (wordBits full) (5 * (start + 4)) := by
    simpa only [hq, ite_false] using first.2.1
  have cblock := block_trans whole (program correct failed done) (commandBlock done) start 4 block (command_slice correct failed done)
  have second := command_run full command whole (start + 4) done heapWords state4 cblock hw hpc pc4 first.1.active first.2.2
  have readonly12 : ReadonlyRun rom whole 12 heapWords state := ReadonlyRun.append rom whole 4 8 heapWords state first.1 second.1
  have run12 : state12 = packingRun rom whole 8 state4 := by
    change packingRun rom whole 12 state = _
    rw [show 12 = 4 + 8 from rfl, run_add]
  have flag12 : state12.register .flag = BitVec.ofNat (wordBits full) command.word := by rw [run12]; exact second.2.2
  have pc12 (notQuery : command ≠ .query) : state12.pc = BitVec.ofNat (wordBits full) (5 * (start + 12)) := by
    rw [run12]
    simpa only [notQuery, ite_false, show start + 4 + 8 = start + 12 by omega] using second.2.1
  have kblock := block_trans whole (program correct failed done) (correctBlock correct) start 12 block (correct_slice correct failed done)
  have third (notQuery : command ≠ .query) :=
    correct_run full command whole (start + 12) correct heapWords state12 kblock hw hpc (pc12 notQuery) readonly12.active flag12
  have readonly16 (notQuery : command ≠ .query) : ReadonlyRun rom whole 16 heapWords state :=
    ReadonlyRun.append rom whole 12 4 heapWords state readonly12 (third notQuery).1
  have run16 : state16 = packingRun rom whole 4 state12 := by
    change packingRun rom whole 16 state = _
    rw [show 16 = 12 + 4 from rfl, run_add]
  cases command with
  | query =>
    apply post_of_run full .query whole start correct failed done heapWords state
    · simpa only [duration, hq, ite_false] using readonly12
    · simp only [duration, destination, hq, ite_false]
      change state12.pc = BitVec.ofNat (wordBits full) (5 * done)
      rw [run12]
      simpa only [↓reduceIte] using second.2.1
  | correct =>
    apply post_of_run full .correct whole start correct failed done heapWords state
    · simpa only [duration, hq, ite_false] using readonly16 (by decide)
    · simp only [duration, destination, hq, ite_false]
      change state16.pc = BitVec.ofNat (wordBits full) (5 * correct)
      rw [run16]
      simpa only [show Command.correct ≠ Command.error by decide, ite_false] using (third (by decide)).2
  | error =>
    have pc16 : state16.pc = BitVec.ofNat (wordBits full) (5 * (start + 16)) := by
      rw [run16]
      simpa only [↓reduceIte, show start + 12 + 4 = start + 16 by omega] using (third (by decide)).2
    have eblock := block_trans whole (program correct failed done) (errorBlock failed) start 16 block (error_slice correct failed done)
    have fourth := error_run rom whole (start + 16) failed heapWords state16 eblock hw hpc pc16 (readonly16 (by decide)).active
    have readonly18 : ReadonlyRun rom whole 18 heapWords state :=
      ReadonlyRun.append rom whole 16 2 heapWords state (readonly16 (by decide)) fourth.1
    have run18 : packingRun rom whole 18 state = packingRun rom whole 2 state16 := by
      rw [show 18 = 16 + 2 from rfl, run_add]
    have index16 : state16.register .index = state.register .index := ((readonly16 (by decide)).reply 16 le_rfl).2.2.2
    apply post_of_run full .error whole start correct failed done heapWords state
    · simpa only [duration, hq, ite_false] using readonly18
    · simp only [duration, destination, hq, ite_false]
      change (packingRun rom whole 18 state).pc =
        BitVec.ofNat (wordBits full) (5 * (if (state.register .index).toNat = 0 then failed else start + 18))
      rw [run18, fourth.2, index16]
      by_cases hi : (state.register .index).toNat = 0
      · simp only [hi, ite_true]
      · simp only [hi, ite_false, show start + 16 + 2 = start + 18 by omega]

theorem actual_dispatch {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (whole : List PackingOp) (start correct failed done heapWords : Nat) (state : WordState (wordBits full))
    (block : PSTROuterCountCode.BlockAt whole start (program correct failed done))
    (hw : WordsFit (wordBits full) (packingCode whole)) (hpc : Fits (wordBits full) (5 * whole.length))
    (hp : state.pc = BitVec.ofNat (wordBits full) (5 * start)) (ha : state.halted = false) :
    DispatchPost full command whole start correct failed done heapWords state := by
  by_cases hq : q = 0
  · subst q
    have zblock : PSTROuterCountCode.BlockAt whole start (zeroBlock done) := by
      simpa only [Nat.add_zero] using block_trans whole (program correct failed done) (zeroBlock done) start 0 block (zero_slice correct failed done)
    have first := zero_run full command whole start done heapWords state zblock hw hpc hp ha
    apply post_of_run full command whole start correct failed done heapWords state
    · simpa only [duration, ↓reduceIte] using first.1
    · simpa only [duration, destination, ↓reduceIte] using first.2.1
  · exact positive_dispatch full command whole start correct failed done heapWords state hq block hw hpc hp ha

theorem charged_dispatch_cost {q : Nat} (full : List (Finset (Fin q))) (command : Command) (whole : List PackingOp)
    (start correct failed done heapWords : Nat) (state : WordState (wordBits full))
    (post : DispatchPost full command whole start correct failed done heapWords state) :
    1 + (packingCode whole).length + 8 + (packingDynamicTrace (callInput q full command) whole (duration q command) state).length ≤
      5 * whole.length + 230 := by
  have h := post.trace
  rw [packingCode_length]
  omega

end PaperProofs.Structure.LaminarTree.PSTRLiveDispatch
