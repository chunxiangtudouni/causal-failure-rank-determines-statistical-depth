module

public import Paid.PDLower_CalibrationCompute_HeadCorrect_049
public import Paid.PDLower_CalibrationCompute_EmitMemory_074

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem headResult_frame (origin : ℕ) (P : Parameters) (base : ℕ) (before : State) :
    Frame before (headResult origin P base before) base P.certificate.M := by
  have avoid (address : ℕ) (outside : address∉workspace base P.certificate.M)
      (offset : ℕ) (inside : offset<16) : address≠base+offset := by
    intro equal
    exact outside (equal.symm ▸ workspace_member base P.certificate.M offset
      (by rw [workspaceSize_linear]; omega))
  have avoidResult (address : ℕ) (outside : address∉workspace base P.certificate.M) :
      address≠resultBase base P.certificate.M := by
    intro equal
    apply outside
    rw [equal]
    simpa only [resultBase,Nat.add_assoc] using
      workspace_member base P.certificate.M (16+2*rowWidth P.certificate.M)
        (by unfold workspaceSize; have positive := rowWidth_positive P.certificate.M; omega)
  constructor
  · intro address outside
    simp only [headResult,enterBiasResult,enterBiasComputed,constantSlotResult,loadSlotResult,
      storeSlotResult,enterCacheResult,writeCell,enterBasesResult,prologueResult,State.set,
      Function.update_apply,avoid address outside 0 (by decide),avoid address outside 1 (by decide),
      avoid address outside 2 (by decide),avoid address outside 3 (by decide),
      avoid address outside 4 (by decide),avoid address outside 5 (by decide),
      avoid address outside 6 (by decide),avoid address outside 7 (by decide),
      avoid address outside 8 (by decide),avoid address outside 9 (by decide),
      avoid address outside 10 (by decide),avoid address outside 11 (by decide),
      avoid address outside 12 (by decide),avoid address outside 13 (by decide),
      avoid address outside 14 (by decide),avoid address outside 15 (by decide),
      avoidResult address outside,ite_false]
  · intro address outside
    simp only [headResult,enterBiasResult,enterBiasComputed,constantSlotResult,loadSlotResult,
      storeSlotResult,enterCacheResult,writeCell,enterBasesResult,prologueResult,State.set,
      Finset.mem_insert,avoid address outside 0 (by decide),avoid address outside 1 (by decide),
      avoid address outside 2 (by decide),avoid address outside 3 (by decide),
      avoid address outside 4 (by decide),avoid address outside 5 (by decide),
      avoid address outside 6 (by decide),avoid address outside 7 (by decide),
      avoid address outside 8 (by decide),avoid address outside 9 (by decide),
      avoid address outside 10 (by decide),avoid address outside 11 (by decide),
      avoid address outside 12 (by decide),avoid address outside 13 (by decide),
      avoid address outside 14 (by decide),avoid address outside 15 (by decide),
      avoidResult address outside,false_or]

theorem headResult_cache (origin : ℕ) (P : Parameters) (base : ℕ) (before : State) :
    HeapList (headResult origin P base before) (resultBase base P.certificate.M)
      [.natural (P.certificate.M+1)] := by
  have avoid (offset : ℕ) (inside : offset<16) :
      resultBase base P.certificate.M≠base+offset := by
    unfold resultBase
    have positive := rowWidth_positive P.certificate.M
    omega
  apply HeapList.of_values
  · intro index inside
    have equal : index=0 := by simp only [List.length_cons,List.length_nil] at inside; omega
    subst index
    simp [headResult,enterBiasResult,enterBiasComputed,constantSlotResult,loadSlotResult,
      storeSlotResult,enterCacheResult,writeCell,enterBasesResult,prologueResult,State.set]
  · intro index inside
    have equal : index=0 := by simp only [List.length_cons,List.length_nil] at inside; omega
    subst index
    simp only [Nat.add_zero,List.getElem_cons_zero,headResult,enterBiasResult,enterBiasComputed,
      constantSlotResult,loadSlotResult,storeSlotResult,enterCacheResult,writeCell,enterBasesResult,
      prologueResult,State.set,Function.update_apply,
      avoid 1 (by decide),avoid 2 (by decide),avoid 3 (by decide),
      avoid 4 (by decide),avoid 5 (by decide),avoid 6 (by decide),avoid 7 (by decide),
      avoid 8 (by decide),avoid 9 (by decide),avoid 10 (by decide),avoid 11 (by decide),
      avoid 12 (by decide),avoid 13 (by decide),avoid 14 (by decide),avoid 15 (by decide),ite_false,ite_true]

end PDLower.CalibrationCompute
