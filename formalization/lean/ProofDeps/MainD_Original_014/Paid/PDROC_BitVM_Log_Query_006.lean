module

public import Paid.PDROC_BitVM_Log_Query_005
public import Paid.PDROC_BitVM_Log_003
public import Paid.PDROC_BitVM_Link_Codec_002
public import Common.PSTR_TM_Codec_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Log.Query

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-- The genuine per-Bool comparison is identified with logical Nat equality
by the existing canonical codec injection. No Nat comparison is a machine
operation; `program` was fixed in Query001 before these logical parameters. -/
theorem nat_address_compare_runs (address query : ℕ) (other : Stack → List Bool) (store : Store) :
    ∃ (run : List State) (after : State),
      run.head? = some (state (some 0) store (encodeNatBits address) (encodeNatBits query) [] other) ∧
      run.IsChain (fun before after => TM2.step program before = some after) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧ equality after.var = decide (address = query) ∧
      recordTag after.var = recordTag store ∧ after.stk = slots [] (encodeNatBits query) [] other ∧
      run.length ≤ 4 * natBits address + 7 := by
  have sameAddress : encodeNatBits address = encodeNatBits query ↔ address = query := by
    constructor
    · intro encoded
      apply PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCodec001.encodeNat_injective
      simpa only [Link.CodecCandidate.encodeNatBits_eq_neutral] using encoded
    · intro equal; exact congrArg encodeNatBits equal
  obtain ⟨run, after, head, chain, last, halt, done, matched, tag, frame, length⟩ :=
    word_compare_runs (encodeNatBits address) (encodeNatBits query) other store
  refine ⟨run, after, head, chain, last, halt, done, ?_, tag, frame, ?_⟩
  · simpa only [sameAddress] using matched
  · rw [Log.nat_word_length] at length
    omega

end PDROC.BitVM.Log.Query
