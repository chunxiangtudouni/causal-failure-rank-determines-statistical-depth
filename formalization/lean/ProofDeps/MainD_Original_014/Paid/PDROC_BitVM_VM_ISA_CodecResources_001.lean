module

public import Paid.PDROC_BitVM_VM_ISA_Specification_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.CodecResources

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Kernel.RegisterGlobal

theorem nat_word_length (value : ℕ) : (encodeNatBits value).length = 2 * natBits value + 1 := by
  simp only [encodeNatBits, List.length_append, List.length_replicate, List.length_singleton, List.length_ofFn]
  omega

theorem nat_cell_length (value : ℕ) : (encodeCellBits (.natural value)).length = 2 * natBits value + 2 := by
  change (false :: encodeNatBits value).length = _
  rw [List.length_cons, nat_word_length]

/-- Operand bit length follows from the actual represented register,
already included in the actual32-stack sum. It is not a numeric oracle. -/
theorem nat_bits_le (logical : PaperProofs.Paid.Computation.State) (contents : Stack → List Bool)
    (reg : Register) (value : ℕ)
    (represented : ∀ r, contents (registerSlot r) = encodeCellBits (logical.register r))
    (natural : logical.register reg = .natural value) : natBits value ≤ Kernel.NatInstruction.dataSize contents := by
  have bound := Kernel.NatInstruction.dataSize_each contents (registerSlot reg)
  rw [represented reg, natural, nat_cell_length] at bound
  omega

theorem compute_quadratic (size a b : ℕ) (ha : natBits a ≤ size) (hb : natBits b ≤ size) :
    Kernel.NatInstruction.computeBudget a b ≤ 200000 * (size + 1)^2 := by
  have positive : 1 ≤ size + 1 := by omega
  have square : size + 1 ≤ (size + 1)^2 := by
    simpa only [Nat.mul_one, ← pow_two] using Nat.mul_le_mul_left (size + 1) positive
  have width : (natBits a + natBits b + 1)^2 ≤ (2 * (size + 1))^2 :=
    Nat.pow_le_pow_left (by omega) 2
  change 2*(encodeNatBits a).length+2*(encodeNatBits b).length+
    32768*(natBits a+natBits b+1)^2+12 ≤ 200000*(size+1)^2
  rw [nat_word_length, nat_word_length]
  nlinarith

/-- Both caps are constants of the old fixed397-LE source code for the
static source-register choices, BEFORE all logical/physical inputs. -/
def comparisonCoefficient (left right : Register) : ℕ :=
  100000000 * (Kernel.InternalInstruction.computePushCap .lessEqual left right +
    Kernel.InternalInstruction.computePushCap .lessEqual right left + 1)

theorem comparisonCoefficient_pos (left right : Register) : 0 < comparisonCoefficient left right := by
  unfold comparisonCoefficient
  omega

theorem comparison_quadratic (left right : Register) (contents : Stack → List Bool) (a b : ℕ)
    (ha : natBits a ≤ Kernel.NatInstruction.dataSize contents)
    (hb : natBits b ≤ Kernel.NatInstruction.dataSize contents) :
    Codec.NatCompare.budget left right contents a b ≤
      comparisonCoefficient left right * (Kernel.NatInstruction.dataSize contents + 1)^2 := by
  let g := Kernel.NatInstruction.dataSize contents
  let p := Kernel.InternalInstruction.computePushCap .lessEqual left right
  let q := Kernel.InternalInstruction.computePushCap .lessEqual right left
  let H := (g + 1)^2
  have ab : Kernel.NatInstruction.computeBudget a b ≤ 200000 * H := compute_quadratic g a b ha hb
  have ba : Kernel.NatInstruction.computeBudget b a ≤ 200000 * H := compute_quadratic g b a hb ha
  have wab := Nat.mul_le_mul_left (96 * p + 1) ab
  have wba := Nat.mul_le_mul_left (96 * q + 1) ba
  have positive : 1 ≤ g + 1 := by omega
  have square : g + 1 ≤ H := by
    simpa only [H, Nat.mul_one, ← pow_two] using Nat.mul_le_mul_left (g + 1) positive
  have linear : 3296 * g + 12868 ≤ 16164 * H := by omega
  have expanded : Codec.NatCompare.budget left right contents a b =
      (96 * p + 1) * Kernel.NatInstruction.computeBudget a b +
      (96 * q + 1) * Kernel.NatInstruction.computeBudget b a + (3296 * g + 12868) := by
    unfold Codec.NatCompare.budget Codec.NatCompare.readBudget Codec.NatCompare.coreScalarBudget
    change 64 * (g + 4) +
      (Kernel.NatInstruction.computeBudget a b + 32 * (3 * (g + p * Kernel.NatInstruction.computeBudget a b) + 1) + 2) +
      (Kernel.NatInstruction.computeBudget b a + 32 * (3 * (32 * (g + 4) + q * Kernel.NatInstruction.computeBudget b a) + 1) + 2) +
      64 * (g + 4) = _
    ring
  have coefficient : (96 * p + 1) * 200000 + (96 * q + 1) * 200000 + 16164 ≤
      100000000 * (p + q + 1) := by omega
  calc
    Codec.NatCompare.budget left right contents a b =
        (96 * p + 1) * Kernel.NatInstruction.computeBudget a b +
        (96 * q + 1) * Kernel.NatInstruction.computeBudget b a + (3296 * g + 12868) := expanded
    _ ≤ (96 * p + 1) * (200000 * H) + (96 * q + 1) * (200000 * H) + 16164 * H :=
      Nat.add_le_add (Nat.add_le_add wab wba) linear
    _ = ((96 * p + 1) * 200000 + (96 * q + 1) * 200000 + 16164) * H := by ring
    _ ≤ 100000000 * (p + q + 1) * H := Nat.mul_le_mul_right H coefficient
    _ = comparisonCoefficient left right * (Kernel.NatInstruction.dataSize contents + 1)^2 := rfl

/-- The old five linear codec bounds admit one uniform positive degree2
base bound. Both constants512 and2 precede every input and caller datum. -/
theorem linear_quadratic (input : List Cell) (contents : Stack → List Bool) (length : ℕ)
    (time : length ≤ 512 * (Kernel.NatInstruction.dataSize contents + 1)) :
    length ≤ 512 * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^2 := by
  have mono : Kernel.NatInstruction.dataSize contents + 1 ≤
      Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1 := by omega
  have positive : 1 ≤ Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1 := by omega
  have square : Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1 ≤
      (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^2 := by
    simpa only [Nat.mul_one, ← pow_two] using Nat.mul_le_mul_left
      (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1) positive
  exact time.trans (Nat.mul_le_mul_left 512 (mono.trans square))

end PDROC.BitVM.VM.ISA.CodecResources
