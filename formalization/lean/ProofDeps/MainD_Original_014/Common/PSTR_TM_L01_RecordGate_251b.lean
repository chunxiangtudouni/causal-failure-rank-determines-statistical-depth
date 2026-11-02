module
public import Common.PSTR_TM_L01_RecordGate_251a

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTML01RecordGate251
open PaperProofs.Common.Native.RationalControllerComputation

/-- Reuse the old binary bound; no numeric decoding is performed by code. -/
theorem records_header_width (count : Nat) (large : 4 ≤ count) : 2 ≤ natBits count := by
  by_contra short
  have width : natBits count ≤ 1 := by omega
  have bound := PSTRTMCodec001.natBits_bound count
  have power := Nat.pow_le_pow_right (by decide : 1 ≤ 2) width
  norm_num at power
  omega

theorem records_two_true (data : List Datum) (suffix : List Bool) (large : 4 ≤ data.length) :
    ∃ tail : List Bool, encode data++suffix = true::true::tail := by
  have width := records_header_width data.length large
  refine ⟨List.replicate (natBits data.length-2) true++[false]++
    List.ofFn (fun position : Fin (natBits data.length) => data.length.testBit position.val)++
    data.flatMap encodeDatum++[true]++suffix,?_⟩
  have split : natBits data.length = 2+(natBits data.length-2) := by omega
  have header : List.replicate (natBits data.length) true =
      true::true::List.replicate (natBits data.length-2) true := by
    conv_lhs => rw [split,List.replicate_add]
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  unfold encode encodeNat
  rw [header]
  simp only [List.cons_append,List.append_assoc]

theorem zero_records_runsFrom (left suffix : List Bool) :
    PSTRTMSeq005.RunsFrom gateMachine (state 0 left (encode []++suffix))
      (zeroTrace left suffix) (zeroFinal left suffix) := by
  exact zero_header_runsFrom left suffix

theorem large_records_contract (left : List Bool) (data : List Datum) (suffix : List Bool)
    (large : 4 ≤ data.length) :
    ∃ trace,
      PSTRTMSeq005.RunsFrom gateMachine (state 0 left (encode data++suffix)) trace
        (state 4 left (encode data++suffix)) ∧
      trace.length = 3 ∧ trace.map (displacement gateMachine) = [1,-1,0] := by
  obtain ⟨tail,header⟩ := records_two_true data suffix large
  refine ⟨nonzeroTrace left tail,?_,nonzero_length _ _,nonzero_moves _ _⟩
  rw [header]
  exact nonzero_header_runsFrom left tail

def final (left : List Bool) (data : List Datum) (suffix : List Bool) : MachineState 4 :=
  if data = [] then zeroFinal left suffix else state 4 left (encode data++suffix)

theorem final_control (left : List Bool) (data : List Datum) (suffix : List Bool) :
    (final left data suffix).q = if data = [] then 3 else 4 := by
  unfold final
  split <;> rfl

theorem final_tape (left : List Bool) (data : List Datum) (suffix : List Bool) :
    (final left data suffix).Tape =
      if data = [] then Turing.Tape.mk₂ (false::false::true::left) (true::suffix)
      else Turing.Tape.mk₂ left (encode data++suffix) := by
  unfold final
  split <;> rfl

theorem records_gate_contract (left : List Bool) (data : List Datum) (suffix : List Bool)
    (domain : data = [] ∨ 4 ≤ data.length) :
    ∃ trace,
      PSTRTMSeq005.RunsFrom gateMachine (state 0 left (encode data++suffix)) trace (final left data suffix) ∧
      trace.length = (if data = [] then 4 else 3) ∧
      trace.map (displacement gateMachine) = (if data = [] then [1,1,1,0] else [1,-1,0]) := by
  rcases domain with empty | large
  · subst data
    refine ⟨zeroTrace left suffix,?_,?_,?_⟩
    · exact zero_records_runsFrom left suffix
    · exact zero_length left suffix
    · exact zero_moves left suffix
  · have nonempty : data ≠ [] := by
      intro empty
      rw [empty] at large
      simp only [List.length_nil] at large
      omega
    obtain ⟨trace,actual,length,moves⟩ := large_records_contract left data suffix large
    refine ⟨trace,?_,?_,?_⟩
    · simpa only [final,nonempty,ite_false] using actual
    · simpa only [nonempty,ite_false] using length
    · simpa only [nonempty,ite_false] using moves

theorem encoded_right_length (data : List Datum) (suffix : List Bool) :
    4 ≤ (encode data++suffix).length := by
  have positive : 1 ≤ natBits data.length := by unfold natBits; omega
  simp only [encode,encodeNat,List.length_append,List.length_replicate,List.length_singleton,List.length_ofFn]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTML01RecordGate251
