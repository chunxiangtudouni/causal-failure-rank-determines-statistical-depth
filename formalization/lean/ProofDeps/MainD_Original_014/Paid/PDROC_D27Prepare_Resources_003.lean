module

public import Paid.PDROC_D27Prepare_Resources_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute
open PDROC.DataBits

namespace PDROC.D27Prepare.Resources

/-- The value invariant is about every physical register, live heap cell,
and already emitted cell. The program counter is bounded by actual fetch. -/
structure StateBounds (heapBound valueBits : ℕ) (state : State) : Prop where
  live : state.live ⊆ Finset.range heapBound
  registers : ∀ register, (state.register register).bits ≤ valueBits
  heapValues : ∀ address ∈ state.live, (state.heap address).bits ≤ valueBits
  outputs : ∀ cell ∈ state.output, cell.bits ≤ valueBits

theorem StateBounds.with_pc {H B : ℕ} {state : State} (h : StateBounds H B state) (pc : ℕ) :
    StateBounds H B {state with pc := pc} :=
  ⟨h.live, h.registers, h.heapValues, h.outputs⟩

theorem StateBounds.set {H B : ℕ} {state : State} (h : StateBounds H B state)
    (target : Register) (value : Cell) (hv : value.bits ≤ B) :
    StateBounds H B (state.set target value) := by
  refine ⟨h.live, ?_, h.heapValues, h.outputs⟩
  intro register
  by_cases same : register = target
  · subst register
    simpa only [State.set, Function.update_self] using hv
  · simpa only [State.set, Function.update_of_ne same] using h.registers register

theorem StateBounds.store {H B : ℕ} {state : State} (h : StateBounds H B state)
    (address : ℕ) (value : Cell) (ha : address < H) (hv : value.bits ≤ B) :
    StateBounds H B {state with
      heap := Function.update state.heap address value
      live := insert address state.live} := by
  constructor
  · intro other member
    rcases Finset.mem_insert.mp member with same | old
    · subst other
      exact Finset.mem_range.mpr ha
    · exact h.live old
  · exact h.registers
  · intro other member
    by_cases same : other = address
    · subst other
      simpa only [Function.update_self] using hv
    · have old : other ∈ state.live := (Finset.mem_insert.mp member).resolve_left same
      simpa only [Function.update_of_ne same] using h.heapValues other old
  · exact h.outputs

/-- Every successful literal prefix, including the whole macro. This is
stronger than a final-heap bound and attaches directly to real trace witnesses. -/
def LinearPrefixBounds (input : List Cell) (code : List Instruction) (before : State)
    (heapBound valueBits : ℕ) : Prop :=
  ∀ count after, linearExecute input (code.take count) before = some after →
    StateBounds heapBound valueBits after

theorem LinearPrefixBounds.nil (input : List Cell) {before : State} {H B : ℕ}
    (h : StateBounds H B before) : LinearPrefixBounds input [] before H B := by
  intro count after executed
  have same : before = after := Option.some.inj (by simpa only [List.take_nil, linearExecute] using executed)
  subst after
  exact h

theorem LinearPrefixBounds.cons (input : List Cell) (instruction : Instruction)
    (rest : List Instruction) (before middle : State) (H B : ℕ)
    (hbefore : StateBounds H B before)
    (executed : instruction.execute input before = some middle)
    (later : LinearPrefixBounds input rest middle H B) :
    LinearPrefixBounds input (instruction :: rest) before H B := by
  intro count after hexecPrefix
  cases count with
  | zero =>
      have same : before = after := Option.some.inj hexecPrefix
      subst after
      exact hbefore
  | succ count =>
      simp only [List.take_succ_cons, linearExecute, executed, Option.bind_some] at hexecPrefix
      exact later count after hexecPrefix

theorem LinearPrefixBounds.append (input : List Cell) (first later : List Instruction)
    (before middle : State) (H B : ℕ)
    (executed : linearExecute input first before = some middle)
    (hfirst : LinearPrefixBounds input first before H B)
    (hlater : LinearPrefixBounds input later middle H B) :
    LinearPrefixBounds input (first ++ later) before H B := by
  intro count after hexecPrefix
  by_cases short : count ≤ first.length
  · rw [List.take_append_of_le_length short] at hexecPrefix
    exact hfirst count after hexecPrefix
  · rw [List.take_append, List.take_of_length_le (by omega : first.length ≤ count),
      linearExecute_append, executed, Option.bind_some] at hexecPrefix
    exact hlater (count - first.length) after hexecPrefix

theorem LinearPrefixBounds.final {input : List Cell} {code : List Instruction}
    {before after : State} {H B : ℕ} (h : LinearPrefixBounds input code before H B)
    (executed : linearExecute input code before = some after) : StateBounds H B after := by
  apply h code.length after
  simpa only [List.take_length] using executed

theorem loadSlot_prefix_bounds (input : List Cell) (before : State) (offset : ℕ)
    (target : Register) (H B : ℕ) (hbefore : StateBounds H B before)
    (fresh : before.register .fresh = .natural 0) (live : offset ∈ before.live)
    (addressBits : (Cell.natural offset).bits ≤ B) :
    LinearPrefixBounds input (loadSlot offset target) before H B := by
  let first := ({before with pc := before.pc + 1}).set .address (.natural offset)
  let second := ({first with pc := first.pc + 1}).set .address (.natural offset)
  let last := ({second with pc := second.pc + 1}).set target (before.heap offset)
  have hfirst : StateBounds H B first := (hbefore.with_pc _).set _ _ addressBits
  have hsecond : StateBounds H B second := (hfirst.with_pc _).set _ _ addressBits
  have hlast : StateBounds H B last := (hsecond.with_pc _).set _ _ (hbefore.heapValues offset live)
  unfold loadSlot
  apply LinearPrefixBounds.cons input _ _ before first H B hbefore
  · rfl
  apply LinearPrefixBounds.cons input _ _ first second H B hfirst
  · simp [Instruction.execute, first, second, State.set, fresh, Cell.nat?, NatOp.eval]
  apply LinearPrefixBounds.cons input _ _ second last H B hsecond
  · simp [Instruction.execute, first, second, last, State.set, live, Cell.nat?]
  exact LinearPrefixBounds.nil input hlast

theorem storeSlot_prefix_bounds (input : List Cell) (before : State) (offset : ℕ)
    (source : Register) (H B : ℕ) (hbefore : StateBounds H B before)
    (fresh : before.register .fresh = .natural 0) (inside : offset < H)
    (safe : source ≠ .address) (addressBits : (Cell.natural offset).bits ≤ B) :
    LinearPrefixBounds input (storeSlot offset source) before H B := by
  let first := ({before with pc := before.pc + 1}).set .address (.natural offset)
  let second := ({first with pc := first.pc + 1}).set .address (.natural offset)
  let last : State := {second with
    heap := Function.update second.heap offset (before.register source)
    live := insert offset second.live
    pc := second.pc + 1}
  have hfirst : StateBounds H B first := (hbefore.with_pc _).set _ _ addressBits
  have hsecond : StateBounds H B second := (hfirst.with_pc _).set _ _ addressBits
  have hlast : StateBounds H B last :=
    ((hsecond.store offset (before.register source) inside (hbefore.registers source)).with_pc _)
  unfold storeSlot
  apply LinearPrefixBounds.cons input _ _ before first H B hbefore
  · rfl
  apply LinearPrefixBounds.cons input _ _ first second H B hfirst
  · simp [Instruction.execute, first, second, State.set, fresh, Cell.nat?, NatOp.eval]
  apply LinearPrefixBounds.cons input _ _ second last H B hsecond
  · simp [Instruction.execute, first, second, last, State.set, safe, Cell.nat?]
  exact LinearPrefixBounds.nil input hlast

theorem address_cell_bits (offset H B : ℕ) (inside : offset < H)
    (enough : 1 + natBits H ≤ B) : (Cell.natural offset).bits ≤ B :=
  (Nat.add_le_add_left (natBits_mono inside.le) 1).trans enough

/-- Transfer actual literal prefix executions to every state of the
genuine fetched trace, including its terminal boundary state. -/
theorem LinearPrefixBounds.trace {input : List Cell} {code : List Instruction}
    {before after : State} {H B : ℕ} (h : LinearPrefixBounds input code before H B)
    (executed : linearExecute input code before = some after)
    (trace : List State) (last : trace.getLast? = some after)
    (prefixes : ∀ state ∈ trace.dropLast, ∃ count < code.length,
      linearExecute input (code.take count) before = some state) :
    ∀ state ∈ trace, StateBounds H B state := by
  have decomposed : trace.dropLast ++ [after] = trace :=
    List.dropLast_append_getLast? after (by rw [last]; rfl)
  intro state member
  rw [← decomposed] at member
  rcases List.mem_append.mp member with earlier | terminal
  · obtain ⟨count, _, actual⟩ := prefixes state earlier
    exact h count state actual
  · have same := List.mem_singleton.mp terminal
    subst state
    exact h.final executed

end PDROC.D27Prepare.Resources
