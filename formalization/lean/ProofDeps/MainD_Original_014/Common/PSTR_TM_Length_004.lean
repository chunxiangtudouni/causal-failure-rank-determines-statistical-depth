module
public import Common.PSTR_TM_Codec_001

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMLength004
open PaperProofs.Common.Native.RationalControllerComputation

/-- Exact bit lengths of the ORIGINAL shared sign/magnitude codec. -/
theorem encodeNat_length (value : Nat) :
    (encodeNat value).length = 2 * natBits value + 1 := by
  simp only [encodeNat, List.length_append, List.length_replicate, List.length_singleton,
    List.length_ofFn]
  omega

theorem encodeDatum_natural_length (value : Nat) :
    (encodeDatum (.natural value)).length = 2 * natBits value + 2 := by
  simp only [encodeDatum, List.length_cons, encodeNat_length]

theorem encodeDatum_rational_length (value : Rat) :
    (encodeDatum (.rational value)).length =
      2 * (natBits value.num.natAbs + natBits value.den) + 4 := by
  simp only [encodeDatum, List.length_append, List.length_cons, List.length_nil, encodeNat_length]
  omega

/-- Each datum's actual bit cost, not a count of abstract syntax labels. -/
def datumBits : Datum → Nat
  | .natural value => 2 * natBits value + 2
  | .rational value => 2 * (natBits value.num.natAbs + natBits value.den) + 4

theorem encodeDatum_length (value : Datum) : (encodeDatum value).length = datumBits value := by
  cases value with
  | natural value => exact encodeDatum_natural_length value
  | rational value => exact encodeDatum_rational_length value

theorem encode_length (data : List Datum) :
    (encode data).length = 2 * natBits data.length + 2 + (data.map datumBits).sum := by
  simp only [encode, List.length_append, encodeNat_length, List.length_singleton,
    List.length_flatMap, encodeDatum_length]
  change 2 * natBits data.length + 1 + (data.map datumBits).sum + 1 =
    2 * natBits data.length + 2 + (data.map datumBits).sum
  omega

theorem datumBits_pos (value : Datum) : 0 < datumBits value := by
  cases value <;> simp only [datumBits, natBits] <;> omega

/-- A per-datum bit bound gives the actual encoded-list bound, including
its length header and final true delimiter. -/
theorem encode_length_le (data : List Datum) (bound : Nat)
    (hbound : ∀ value ∈ data, datumBits value ≤ bound) :
    (encode data).length ≤ 2 * natBits data.length + 2 + data.length * bound := by
  rw [encode_length]
  have hs : (data.map datumBits).sum ≤ data.length * bound := by
    revert hbound
    induction data with
    | nil => intro _; simp
    | cons value data ih =>
      intro hbound
      have hv := hbound value (by simp)
      have ht := ih (fun d hd => hbound d (by simp [hd]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        datumBits value + (data.map datumBits).sum ≤ bound + data.length * bound := Nat.add_le_add hv ht
        _ = (data.length + 1) * bound := by simp [Nat.add_mul, Nat.add_comm]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMLength004


