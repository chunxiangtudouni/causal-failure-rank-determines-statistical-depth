module

public import Paid.PDROC_D27Prepare_Q_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute
open PDROC.D27Prepare.Program PDROC.D27Prepare.Resources
open PDROC.DataBits

namespace PDROC.D27Prepare.Q

theorem MemoryProgress.of_suffix {R : Finset ℕ} {before middle after : State}
    (whole : MemoryProgress R before after) (suffix : MemoryProgress ∅ middle after) :
    MemoryProgress R before middle := by
  constructor
  · constructor
    · intro address outside
      exact (suffix.1.1 address (Finset.notMem_empty _)).symm.trans (whole.1.1 address outside)
    · intro address outside
      exact (suffix.1.2 address (Finset.notMem_empty _)).symm.trans (whole.1.2 address outside)
  · intro address member
    exact (suffix.1.2 address (Finset.notMem_empty _)).mp (whole.2 member)

/-- Literal positions0..7 precede the sole store. Position9 is a no-write
modulo. These two actual code facts control the pre-store and post-store
prefixes; the final frame alone is not used as an intermediate-state oracle. -/
theorem ceilCore_prefix_memory (R : Finset ℕ) (input : List Cell) (before : State)
    (source target : ℕ) (value : ℚ) (inside : target ∈ R)
    (fresh : before.register .fresh = .natural 0)
    (sourceValue : Search.SlotHas before source (.rational value)) :
    LinearPrefixMemory R input (ceilCore source target) before := by
  let terminal := ceilCoreResult before 0 source target value
  have executed : linearExecute input (ceilCore source target) before = some terminal :=
    ceilCore_execute input before 0 source target value fresh
      (by simpa only [Nat.zero_add] using sourceValue.1)
      (by simpa only [Nat.zero_add] using sourceValue.2)
  have fields := ceilCoreResult_fields before 0 source target value
  have frame : MemoryProgress R before terminal := progress_of_write R before terminal target
    (.natural (value.num.natAbs / value.den)) inside
    (by simpa only [Nat.zero_add] using fields.1) (by simpa only [Nat.zero_add] using fields.2.1)
  intro count after actual
  by_cases complete : 10 ≤ count
  · have length : (ceilCore source target).length = 10 := by simp [ceilCore, loadSlot, storeSlot]
    rw [List.take_of_length_le (by omega : (ceilCore source target).length ≤ count)] at actual
    have same : after = terminal := Option.some.inj (actual.symm.trans executed)
    subst after
    exact frame
  · by_cases early : count < 9
    · apply linearExecute_no_memory_write R input ((ceilCore source target).take count) before after _ actual
      interval_cases count <;> simp [ceilCore, loadSlot, storeSlot, NoMemoryWrite]
    · have same : count = 9 := by omega
      subst count
      have rest : linearExecute input ((ceilCore source target).drop 9) after = some terminal := by
        have full : linearExecute input
            ((ceilCore source target).take 9 ++ (ceilCore source target).drop 9) before = some terminal := by
          rw [List.take_append_drop]
          exact executed
        rw [linearExecute_append, actual, Option.bind_some] at full
        exact full
      apply frame.of_suffix
      apply linearExecute_no_memory_write ∅ input ((ceilCore source target).drop 9) after terminal _ rest
      simp [ceilCore, loadSlot, storeSlot, NoMemoryWrite]

/-- The hypothetical increment is bounded even when remainder=0 and the
actual program skips it. This makes every shared ceiling-prefix disjunct
safe without a numerical loop over the large quotient. -/
theorem quotient_succ_bits (value : ℚ) (B : ℕ) (encoding : ratEncodingBits value + 1 ≤ B) :
    (Cell.natural (value.num.natAbs / value.den + 1)).bits ≤ B := by
  have quotient := Nat.div_le_self value.num.natAbs value.den
  have h := (natBits_mono (Nat.add_le_add_right quotient 1)).trans
    (natBits_add_le value.num.natAbs 1)
  have one : natBits 1 = 1 := by norm_num [natBits]
  have den := natBits_pos value.den
  unfold ratEncodingBits ratNumBits ratDenBits at encoding
  change 1 + natBits (value.num.natAbs / value.den + 1) ≤ B
  omega

end PDROC.D27Prepare.Q
