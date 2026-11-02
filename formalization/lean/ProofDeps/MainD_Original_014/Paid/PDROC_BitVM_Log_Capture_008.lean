module

public import Paid.PDROC_BitVM_Log_Capture_007
public import Paid.PDROC_BitVM_Log_Header_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Log.Capture

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-- Input field and returned address buffer use the existing official
canonical bytes. Logical value/width are never machine control data. -/
theorem officialNat_capture_runs (value : ℕ) (suffix archive : List Bool)
    (other : Stack → List Bool) (store : Store) :
    ∃ (run : List State) (after : State),
      run.head? = some (state (some 0) store (encodeNatBits value ++ suffix) [] archive [] other) ∧
      run.IsChain (fun before after => TM2.step program before = some after) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧ after.var = (none, store.2) ∧
      after.stk = slots suffix (encodeNatBits value) ((encodeNatBits value).reverse ++ archive) [] other ∧
      run.length = 4 * natBits value + 6 := by
  simpa only [Header.natWord_digits, Header.digits_length] using
    capture_runs (Header.digits value) suffix archive other store

end PDROC.BitVM.Log.Capture
