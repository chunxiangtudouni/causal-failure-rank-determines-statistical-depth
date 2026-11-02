module

public import Paid.PDLower_CalibrationCompute_InputBitScale_089
public import Paid.PDLower_CalibrationCompute_BootstrapStart_060
public import Paid.RootD27Bits_SlotPrefix_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits

namespace PDLower.CalibrationCompute

def standaloneLoaderBudget (P : Parameters) (fee : ℚ) (incoming : ℕ) : ℕ :=
  incoming+16*calibrationBitScale P fee+natBits (mainStart+27)+64

structure LoaderOperandBounds (P : Parameters) (budget : ℕ) : Prop where
  small : 32≤budget
  input : ∀ cell∈calibrationInput P,cell.bits≤budget
  natural : ∀ value≤rowWidth P.certificate.M+3,(Cell.natural value).bits≤budget
  pc : ∀ counter≤mainStart+27,natBits counter≤budget

theorem LoaderOperandBounds.literal (P : Parameters) (budget value : ℕ) (bounds : LoaderOperandBounds P budget)
    (bounded : value≤16) : (Cell.natural value).bits≤budget := by
  have mono := PDROC.DataBits.natBits_mono bounded
  have sixteen : natBits 16=5 := by decide
  have small := bounds.small
  change 1+natBits value≤budget
  rw [sixteen] at mono
  omega

theorem standaloneLoaderBudget_bounds (P : Parameters) (fee : ℚ) (incoming : ℕ) :
    LoaderOperandBounds P (standaloneLoaderBudget P fee incoming) := by
  have qScale := calibrationBitScale_Q P fee
  have mQ := PDROC.DataBits.level_le_original_Q P P.certificate.M (le_refl _)
  refine ⟨?_,?_,?_,?_⟩
  · unfold standaloneLoaderBudget
    omega
  · intro cell member
    have actual := calibrationInput_cell_bits P fee cell member
    unfold standaloneLoaderBudget
    omega
  · intro value bounded
    have bits : natBits value≤value+1 := Nat.add_le_add_right (Nat.log2_le_self _) 1
    change 1+natBits value≤standaloneLoaderBudget P fee incoming
    unfold standaloneLoaderBudget rowWidth at *
    omega
  · intro counter bounded
    have actual := PDROC.DataBits.natBits_mono bounded
    unfold standaloneLoaderBudget
    omega

theorem standaloneLoaderBudget_initial (P : Parameters) (fee : ℚ) (incoming : ℕ) (before : State)
    (safe : SafeBits before incoming) : SafeBits before (standaloneLoaderBudget P fee incoming) := by
  intro bits member
  exact (safe bits member).trans (by unfold standaloneLoaderBudget;omega)

theorem calibration_initial_safe : SafeBits initial 4 := by
  apply SafeBits.of_fields
  · intro target
    norm_num [initial,Cell.bits,natBits]
  · intro address alive
    simp only [initial,Finset.notMem_empty] at alive
  · intro address alive
    simp only [initial,Finset.notMem_empty] at alive
  · intro cell member
    simp only [initial,List.not_mem_nil] at member
  · norm_num [initial,natBits]

end PDLower.CalibrationCompute
