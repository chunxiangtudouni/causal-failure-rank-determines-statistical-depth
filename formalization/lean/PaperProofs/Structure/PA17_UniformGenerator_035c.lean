module

public import PaperProofs.Structure.PA17_UniformGenerator_035b

/-! Real streaming output from compiled expressions. A fixed scratch prefix
holds variables, counters and the output cursor; emitted code starts after
it. The concluding generator copy to address0 is a separate component. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035c

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b

theorem expression_frame (expression : Expr) (rom : PhysicalROM) (stack address : Nat)
    (hf : address < stack ∨ stack + expression.size ≤ address) (state : NatState) :
    (runOps rom (expression.compile stack) state).heap address = state.heap address := by
  induction expression generalizing stack state with
  | constant value => rfl
  | cell source => rfl
  | input source => rfl
  | binary operation left right ihl ihr =>
    have hf' : address < stack ∨ stack + (left.size + right.size + 1) ≤ address := hf
    simp only [Expr.compile, runOps_append, finish_heap]
    rw [ihr (stack + 1) (by omega), spill_heap, Function.update_of_ne (show address ≠ stack by omega),
      ihl stack (by omega)]

def emitTail (cursor outputBase : Nat) : List PackingOp :=
  [.base (.base (.constant .index cursor)), .base (.base (.loadHeap .old .index)),
   .base (.base (.constant .fresh outputBase)), .base (.base (.add .address .fresh .old)),
   .base (.base (.storeHeap .address .value)), .base (.base (.constant .fresh 1)),
   .base (.base (.add .old .old .fresh)), .base (.base (.storeHeap .index .old))]

def emitWord (expression : Expr) (stack cursor outputBase : Nat) : List PackingOp :=
  expression.compile stack ++ emitTail cursor outputBase

theorem emitTail_heap (rom : PhysicalROM) (cursor outputBase : Nat) (state : NatState) :
    (runOps rom (emitTail cursor outputBase) state).heap =
      Function.update (Function.update state.heap (outputBase + state.heap cursor) (state.register .value))
        cursor (state.heap cursor + 1) := rfl

theorem emitWord_heap (expression : Expr) (rom : PhysicalROM) (stack cursor outputBase : Nat)
    (he : expression.Below stack) (hc : cursor < stack) (state : NatState) :
    (runOps rom (emitWord expression stack cursor outputBase) state).heap =
      Function.update
        (Function.update (runOps rom (expression.compile stack) state).heap
          (outputBase + state.heap cursor) (expression.eval rom state.heap)) cursor (state.heap cursor + 1) := by
  have hh := expression.compile_correct rom stack he state
  rw [emitWord, runOps_append, emitTail_heap, hh.1, hh.2.1 cursor hc]

theorem emitWord_cursor (expression : Expr) (rom : PhysicalROM) (stack cursor outputBase : Nat)
    (he : expression.Below stack) (hc : cursor < stack) (state : NatState) :
    (runOps rom (emitWord expression stack cursor outputBase) state).heap cursor = state.heap cursor + 1 := by
  rw [emitWord_heap expression rom stack cursor outputBase he hc state, Function.update_self]

theorem emitWord_value (expression : Expr) (rom : PhysicalROM) (stack cursor outputBase : Nat)
    (he : expression.Below stack) (hc : cursor < stack) (ho : cursor < outputBase) (state : NatState) :
    (runOps rom (emitWord expression stack cursor outputBase) state).heap (outputBase + state.heap cursor) =
      expression.eval rom state.heap := by
  rw [emitWord_heap expression rom stack cursor outputBase he hc state,
    Function.update_of_ne (show outputBase + state.heap cursor ≠ cursor by omega), Function.update_self]

theorem emitWord_frame (expression : Expr) (rom : PhysicalROM) (stack cursor outputBase address : Nat)
    (state : NatState) (he : expression.Below stack) (hc : cursor < stack)
    (hcursor : address ≠ cursor) (houtput : address ≠ outputBase + state.heap cursor)
    (hstack : address < stack ∨ stack + expression.size ≤ address) :
    (runOps rom (emitWord expression stack cursor outputBase) state).heap address = state.heap address := by
  rw [emitWord_heap expression rom stack cursor outputBase he hc state,
    Function.update_of_ne hcursor, Function.update_of_ne houtput]
  exact expression_frame expression rom stack address hstack state

def StreamRep (cursor outputBase : Nat) (words : List Nat) (heap : Nat → Nat) : Prop :=
  heap cursor = words.length ∧ ∀ position (hp : position < words.length), heap (outputBase + position) = words[position]

theorem emitWord_stream (expression : Expr) (rom : PhysicalROM) (stack cursor outputBase : Nat)
    (he : expression.Below stack) (hc : cursor < stack) (hstack : stack + expression.size ≤ outputBase)
    (words : List Nat) (state : NatState) (hr : StreamRep cursor outputBase words state.heap) :
    StreamRep cursor outputBase (words ++ [expression.eval rom state.heap])
      (runOps rom (emitWord expression stack cursor outputBase) state).heap := by
  constructor
  · rw [emitWord_cursor expression rom stack cursor outputBase he hc state, hr.1]
    simp only [List.length_append, List.length_singleton]
  · intro position hp
    simp only [List.length_append, List.length_singleton] at hp
    by_cases hi : position < words.length
    · rw [emitWord_frame expression rom stack cursor outputBase (outputBase + position) state he hc
        (by omega) (by rw [hr.1]; omega) (Or.inr (by omega)),
        List.getElem_append_left hi]
      exact hr.2 position hi
    · have hi' : position = words.length := by omega
      subst position
      have hv := emitWord_value expression rom stack cursor outputBase he hc (by omega) state
      rw [hr.1] at hv
      simpa only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero] using hv

theorem emitWord_counter_frame (expression : Expr) (rom : PhysicalROM) (stack cursor outputBase counter : Nat)
    (he : expression.Below stack) (hc : cursor < stack) (hcounter : counter < stack) (hne : counter ≠ cursor)
    (hstack : stack + expression.size ≤ outputBase) (state : NatState) :
    (runOps rom (emitWord expression stack cursor outputBase) state).heap counter = state.heap counter :=
  emitWord_frame expression rom stack cursor outputBase counter state he hc hne (by omega) (Or.inl hcounter)

theorem emitWord_noJump (expression : Expr) (stack cursor outputBase : Nat) :
    ∀ op ∈ emitWord expression stack cursor outputBase, NoJump op := by
  intro op hm
  rw [emitWord, List.mem_append] at hm
  rcases hm with hm | hm
  · exact expression.compile_noJump stack op hm
  · have hh : ∀ entry ∈ emitTail cursor outputBase, NoJump entry := by simp [emitTail, NoJump]
    exact hh op hm

theorem emitWord_bodyExits (expression : Expr) (rom : PhysicalROM) (stack cursor outputBase counter : Nat)
    (he : expression.Below stack) (hc : cursor < stack) (hcounter : counter < stack) (hne : counter ≠ cursor)
    (hstack : stack + expression.size ≤ outputBase) (left right : List PackingOp) :
    BodyExits rom left (emitWord expression stack cursor outputBase) right counter
      (fun _ => (emitWord expression stack cursor outputBase).length) :=
  straight_body_exits rom left _ right counter (emitWord_noJump expression stack cursor outputBase)
    (emitWord_counter_frame expression rom stack cursor outputBase counter he hc hcounter hne hstack)

theorem emitWord_length (expression : Expr) (stack cursor outputBase : Nat) :
    (emitWord expression stack cursor outputBase).length = (expression.compile stack).length + 8 := by
  simp [emitWord, emitTail]

theorem emitWord_segment_run (expression : Expr) (rom : PhysicalROM) (stack cursor outputBase : Nat)
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ emitWord expression stack cursor outputBase ++ right)
      (emitWord expression stack cursor outputBase).length state =
      runOps rom (emitWord expression stack cursor outputBase) state :=
  natRun_of_straight_segment rom _ _ left.length (by simp only [List.length_append]; omega)
    (segment_index left _ right) (emitWord_noJump expression stack cursor outputBase) state hpc ha

theorem emitWord_word_value (expression : Expr) (rom : PhysicalROM) (stack cursor outputBase bits : Nat)
    (he : expression.Below stack) (hc : cursor < stack) (ho : cursor < outputBase)
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ emitWord expression stack cursor outputBase ++ right)))
    (hsafe : ∀ count < (emitWord expression stack cursor outputBase).length,
      RegistersFit bits (natRun rom (left ++ emitWord expression stack cursor outputBase ++ right) count state) ∧
        Fits bits (natRun rom (left ++ emitWord expression stack cursor outputBase ++ right) count state).pc)
    (haddress : Fits bits (outputBase + state.heap cursor)) (hvalue : Fits bits (expression.eval rom state.heap)) :
    ((packingRun rom (left ++ emitWord expression stack cursor outputBase ++ right)
      (emitWord expression stack cursor outputBase).length (state.toWord bits)).heap
      (BitVec.ofNat bits (outputBase + state.heap cursor))).toNat = expression.eval rom state.heap := by
  rw [natRun_toWord _ _ _ _ hcode hsafe, emitWord_segment_run expression rom stack cursor outputBase left right state hpc ha]
  change (BitVec.ofNat bits ((runOps rom (emitWord expression stack cursor outputBase) state).heap
    (BitVec.ofNat bits (outputBase + state.heap cursor)).toNat)).toNat = _
  have hpNat : (BitVec.ofNat bits (outputBase + state.heap cursor)).toNat = outputBase + state.heap cursor := Nat.mod_eq_of_lt haddress
  rw [hpNat, emitWord_value expression rom stack cursor outputBase he hc ho state,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvalue]

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035c
