module

public import Common.PSTR_WordBool_RawInit_CopyComplete008

/-! One actual finite controller reads the original outer count and
physically retains a second copy before any decrement. Every original
Datum byte and the true footer remain unread and unchanged. All caller
quantifiers are the original data list; neither length nor saved header
is a new runtime input. This is still the RawInit header front segment. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMSeq005

def retainedHeaderMachine : Machine 103 := seqMachine headerMachine HeaderCopy.machine

theorem actual_retained_header (data : List Datum) :
    ∃ (trace : List (MachineState 103)) (final : MachineState 103),
      Runs retainedHeaderMachine (encode data) trace final ∧ final.q = 103 ∧
      final.Tape = Tape.mk₂
        (false :: (HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length) ++
          false :: false :: HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length)))
        (rawTail data) ∧
      trace.length ≤ 1024 * ((encode data).length + 1)^2 ∧
      ∀ clock, visitedSpace retainedHeaderMachine (encode data).length (trace.take clock) ≤
        1024 * ((encode data).length + 1)^2 := by
  obtain ⟨firstTrace,firstFinal,firstRun,_firstPort,firstTape,_firstValue,firstTime,_firstSpace⟩ :=
    actual_count_header data
  let digits := PSTRTMNatValue017.rawPayload data.length
  have suffixNonempty : rawTail data ≠ [] := by simp [rawTail]
  obtain ⟨originalHead,tail,suffixEq⟩ := List.exists_cons_of_ne_nil suffixNonempty
  obtain ⟨secondTrace,secondRun,secondTime,_secondSpace⟩ :=
    HeaderCopy.actual digits originalHead tail (encode data).length
  have secondStart : RunsFrom HeaderCopy.machine ⟨0,firstFinal.Tape⟩ secondTrace
      (HeaderCopy.copyFinal digits originalHead tail) := by
    rw [firstTape, suffixEq]
    exact secondRun
  let trace := firstTrace.map (leftCfg (b := 85)) ++ secondTrace.map (rightCfg (a := 17))
  let final := rightCfg (a := 17) (HeaderCopy.copyFinal digits originalHead tail)
  have actualRun : Runs retainedHeaderMachine (encode data) trace final :=
    seq_runs headerMachine HeaderCopy.machine (encode data) firstFinal
      (HeaderCopy.copyFinal digits originalHead tail) firstTrace secondTrace firstRun secondStart
  have width : digits.length = natBits data.length := by
    simp only [digits, PSTRTMNatValue017.rawPayload, List.length_ofFn]
  have room : digits.length + 1 ≤ (encode data).length + 1 := by
    rw [width, PSTRTMLength004.encode_length]
    omega
  have copiedTime : secondTrace.length ≤ 64 * ((encode data).length + 1)^2 :=
    secondTime.trans (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left room 2))
  have time : trace.length ≤ 128 * ((encode data).length + 1)^2 := by
    simp only [trace, List.length_append, List.length_map]
    omega
  refine ⟨trace,final,actualRun,rfl,?_,?_,?_⟩
  · simp only [final, rightCfg, HeaderCopy.copyFinal, HeaderCopy.state, digits, suffixEq]
  · omega
  · intro clock
    have space := PSTRTMTrace002.visitedSpace_le retainedHeaderMachine
      (encode data).length (trace.take clock)
    have short : (trace.take clock).length ≤ trace.length := by
      simp only [List.length_take]
      exact Nat.min_le_right _ _
    have inputRoom : (encode data).length + 1 ≤ ((encode data).length + 1)^2 := by nlinarith
    omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit
