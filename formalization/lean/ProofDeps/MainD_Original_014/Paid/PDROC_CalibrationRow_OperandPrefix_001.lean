module

public import Paid.RootD27Bits_SlotPrefix_004
public import Paid.PDROC_CalibrationRow_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid.Computation PDLower.CalibrationCompute RootD27.Bits

/-- Every genuine literal prefix preserves the SAME local caller budget.
Concrete phase proofs supply the actual assigned values. This does not
impose a parameter-only bound on arbitrary callee scratch registers. -/
def PrefixSafe (input : List Cell) (code : List Instruction) (before : State) (budget : ℕ) : Prop :=
  ∀ count after,linearExecute input (code.take count) before=some after → SafeBits after budget

theorem PrefixSafe.nil (input : List Cell) (before : State) (budget : ℕ)
    (safe : SafeBits before budget) : PrefixSafe input [] before budget := by
  intro count after run
  have same : before=after := Option.some.inj (by simpa only [List.take_nil,linearExecute] using run)
  subst after
  exact safe

theorem PrefixSafe.final {input : List Cell} {code : List Instruction} {before after : State}
    {budget : ℕ} (safe : PrefixSafe input code before budget)
    (run : linearExecute input code before=some after) : SafeBits after budget :=
  safe code.length after (by simpa only [List.take_length] using run)

theorem PrefixSafe.of_bounded (input : List Cell) (code : List Instruction) (before : State)
    (budget : ℕ) (safe : ∀ count≤code.length,∀ after,
      linearExecute input (code.take count) before=some after → SafeBits after budget) :
    PrefixSafe input code before budget := by
  intro count after run
  by_cases short : count≤code.length
  · exact safe count short after run
  · apply safe code.length (Nat.le_refl _) after
    simpa only [List.take_length,List.take_of_length_le (by omega : code.length≤count)] using run

theorem PrefixSafe.cons (input : List Cell) (instruction : Instruction) (rest : List Instruction)
    (before middle : State) (budget : ℕ) (run : instruction.execute input before=some middle)
    (safe : SafeBits before budget) (later : PrefixSafe input rest middle budget) :
    PrefixSafe input (instruction::rest) before budget := by
  intro count after executed
  cases count with
  | zero =>
      have same : before=after := Option.some.inj executed
      subst after
      exact safe
  | succ count =>
      change (instruction.execute input before).bind (linearExecute input (rest.take count))=some after at executed
      rw [run,Option.bind_some] at executed
      exact later count after executed

theorem PrefixSafe.append (input : List Cell) (first later : List Instruction)
    (before middle : State) (budget : ℕ)
    (run : linearExecute input first before=some middle)
    (firstSafe : PrefixSafe input first before budget) (laterSafe : PrefixSafe input later middle budget) :
    PrefixSafe input (first++later) before budget := by
  intro count after executed
  by_cases short : count≤first.length
  · rw [List.take_append_of_le_length short] at executed
    exact firstSafe count after executed
  · rw [List.take_append,List.take_of_length_le (by omega : first.length≤count),
      linearExecute_append,run,Option.bind_some] at executed
    exact laterSafe (count-first.length) after executed

theorem PrefixSafe.singleton (input : List Cell) (instruction : Instruction)
    (before after : State) (budget : ℕ) (run : instruction.execute input before=some after)
    (first : SafeBits before budget) (last : SafeBits after budget) :
    PrefixSafe input [instruction] before budget :=
  PrefixSafe.cons input instruction [] before after budget run first (PrefixSafe.nil input after budget last)

theorem PrefixSafe.loadSlot (input : List Cell) (before : State)
    (base slot budget : ℕ) (target : Register) (safe : SafeBits before budget)
    (fresh : before.register .fresh=.natural base) (live : base+slot∈before.live)
    (addressBits : 1+PaperProofs.Paid.Parameters.natBits (base+slot)≤budget)
    (pcBits : PaperProofs.Paid.Parameters.natBits (before.pc+3)≤budget) :
    PrefixSafe input (loadSlot slot target) before budget := by
  apply PrefixSafe.of_bounded
  intro count bound after executed
  exact loadSlot_prefix_safe input before after base slot budget count target safe fresh live addressBits pcBits bound executed

theorem PrefixSafe.storeSlot (input : List Cell) (before : State)
    (base slot budget : ℕ) (source : Register) (safe : SafeBits before budget)
    (fresh : before.register .fresh=.natural base) (different : source≠.address)
    (addressBits : 1+PaperProofs.Paid.Parameters.natBits (base+slot)≤budget)
    (pcBits : PaperProofs.Paid.Parameters.natBits (before.pc+3)≤budget) :
    PrefixSafe input (storeSlot slot source) before budget := by
  apply PrefixSafe.of_bounded
  intro count bound after executed
  exact storeSlot_prefix_safe input before after base slot budget count source safe fresh different addressBits pcBits bound executed

end PDROC.CalibrationRow.Operand
