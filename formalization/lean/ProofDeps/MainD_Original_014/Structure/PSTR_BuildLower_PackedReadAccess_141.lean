module

public import Structure.PSTR_BuildLower_WordDataCongr_140
public import Structure.PSTR_BuildLower_CounterAccess_037

/-! Reuse the frozen A06 reader access proof directly. Only its proof-side
PC0/halted=false state is normalized; executeOps data congruence proves the
actual prefix's identical registers/heap. No fetched runs are equated and
no runtime reset or whole-body Nat-register bound is assumed. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.PackedReadAccess
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open RawTreePreprocessingClaims PA17PackedTranslator034
variable {bits : Nat}

theorem local_safe (q heapWords : Nat) (physical : PhysicalROM) (state : WordState bits)
    (header : PA06A19PrepareRuntimePacked016.Header q state.heap) (hb : 7 ≤ bits)
    (hw : CapacityBits.width q ≤ bits)
    (hs : Fits bits ((state.register .old).toNat * CapacityBits.width q))
    (hf : Fits bits (4 + ((state.register .old).toNat * CapacityBits.width q / bits + 1)))
    (hl : 4 + ((state.register .old).toNat * CapacityBits.width q / bits + 1) < heapWords) :
    PackedAccessSafe heapWords physical PA06A19PrepareBankPacked021.read state := by
  let zero : WordState bits := { state with pc := 0, halted := false }
  intro clock hc
  have existing := PA06A19PrepareBankPacked021.read_accessFits q heapWords physical zero header hb hw hs hf hl
    rfl rfl clock hc
  rw [packingRun_eq_executeOps_take physical PA06A19PrepareBankPacked021.read zero
    PA06A19PrepareBankPacked021.read_straight (PA06A19PrepareBankPacked021.read_code_fit hb)
    (PA06A19PrepareBankPacked021.read_pc_fit hb) rfl rfl clock hc.le] at existing
  have same := WordDataCongr.operations physical (PA06A19PrepareBankPacked021.read.take clock) state zero rfl rfl
  rw [WordDataCongr.access physical heapWords PA06A19PrepareBankPacked021.read[clock]
    (executeOps physical (PA06A19PrepareBankPacked021.read.take clock) state)
    (executeOps physical (PA06A19PrepareBankPacked021.read.take clock) zero) same.1]
  exact existing

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.PackedReadAccess
