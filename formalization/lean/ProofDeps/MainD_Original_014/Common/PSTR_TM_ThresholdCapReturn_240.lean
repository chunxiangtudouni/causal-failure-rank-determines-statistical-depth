module
public import Common.PSTR_TM_WordNatCriteria_239

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCapReturn240
open PaperProofs.Common.Native.RationalControllerComputation

/-! The cap classifier's head movement is really undone. This fixed
16-label machine reads the same canonical B Datum as234, preserves every
cell, and returns TRUE14/FALSE15 at the ORIGINAL Datum tag. The return
distinguishes the actual width-one/width-two/wide header geometry; it
does not assume that a halt control resets the head. Arbitrary archive
and suffix remain literal frame data. -/

def returnMachine : Machine 15 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (2,.move .right)
  | 2 => some (if symbol then 3 else 5,if symbol then .move .right else .write false)
  | 3 => some (if symbol then 6 else 4,if symbol then .write true else .move .right)
  | 4 => some (if symbol then 6 else 5,.write symbol)
  | 5 => some (7,.move .left)
  | 6 => some (8,.move .left)
  | 7 => some (if symbol then 14 else 9,.move .left)
  | 8 => some (if symbol then 11 else 12,.move .left)
  | 9 => some (10,.move .left)
  | 10 => some (14,.move .left)
  | 11 => some (15,.move .left)
  | 12 => some (13,.move .left)
  | 13 => some (15,.move .left)
  | _ => none

def state (q : Fin 16) (left right : List Bool) : MachineState 15 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def smallTrace (left tail : List Bool) : List (MachineState 15) :=
  [state 0 left (false::true::false::tail),
   state 1 (false::left) (true::false::tail),
   state 2 (true::false::left) (false::tail),
   state 5 (true::false::left) (false::tail),
   state 7 (false::left) (true::false::tail),
   state 14 left (false::true::false::tail)]

theorem small_runsFrom (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom returnMachine (state 0 left (false::true::false::tail))
      (smallTrace left tail) (state 14 left (false::true::false::tail)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [smallTrace,List.isChain_cons_cons,Turing.TM0.step,returnMachine,state,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,returnMachine,state]

def pairTrace (left : List Bool) (bit : Bool) (tail : List Bool) : List (MachineState 15) :=
  [state 0 left (false::true::true::false::bit::tail),
   state 1 (false::left) (true::true::false::bit::tail),
   state 2 (true::false::left) (true::false::bit::tail),
   state 3 (true::true::false::left) (false::bit::tail),
   state 4 (false::true::true::false::left) (bit::tail),
   state (if bit then 6 else 5) (false::true::true::false::left) (bit::tail),
   state (if bit then 8 else 7) (true::true::false::left) (false::bit::tail),
   state (if bit then 12 else 9) (true::false::left) (true::false::bit::tail),
   state (if bit then 13 else 10) (false::left) (true::true::false::bit::tail),
   state (if bit then 15 else 14) left (false::true::true::false::bit::tail)]

theorem pair_runsFrom (left : List Bool) (bit : Bool) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom returnMachine (state 0 left (false::true::true::false::bit::tail))
      (pairTrace left bit tail) (state (if bit then 15 else 14) left (false::true::true::false::bit::tail)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · cases bit <;> simp [pairTrace,List.isChain_cons_cons,Turing.TM0.step,returnMachine,state,Turing.Tape.mk₂]
  · cases bit <;> simp [Turing.TM0.step,returnMachine,state]

def wideTrace (left tail : List Bool) : List (MachineState 15) :=
  [state 0 left (false::true::true::true::tail),
   state 1 (false::left) (true::true::true::tail),
   state 2 (true::false::left) (true::true::tail),
   state 3 (true::true::false::left) (true::tail),
   state 6 (true::true::false::left) (true::tail),
   state 8 (true::false::left) (true::true::tail),
   state 11 (false::left) (true::true::true::tail),
   state 15 left (false::true::true::true::tail)]

theorem wide_runsFrom (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom returnMachine (state 0 left (false::true::true::true::tail))
      (wideTrace left tail) (state 15 left (false::true::true::true::tail)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [wideTrace,List.isChain_cons_cons,Turing.TM0.step,returnMachine,state,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,returnMachine,state]

/-- A real returned control and the ENTIRE original tape at the SAME head.
TRUE14 iff n<=2, FALSE15 otherwise; <=10 configurations for ALL n. -/
theorem datum_return_contract (n : Nat) (left suffix : List Bool) :
    ∃ trace,
      PSTRTMSeq005.RunsFrom returnMachine
        (state 0 left (encodeDatum (.natural n)++suffix)) trace
        (state (if n ≤ 2 then 14 else 15) left (encodeDatum (.natural n)++suffix)) ∧
      trace.length ≤ 10 := by
  rcases Nat.lt_or_ge n 4 with hsmall | hlarge
  · interval_cases n
    · exact ⟨smallTrace left (false::suffix),small_runsFrom _ _,by simp [smallTrace]⟩
    · exact ⟨smallTrace left (true::suffix),small_runsFrom _ _,by simp [smallTrace]⟩
    · exact ⟨pairTrace left false (true::suffix),pair_runsFrom _ _ _,by simp [pairTrace]⟩
    · exact ⟨pairTrace left true (true::suffix),pair_runsFrom _ _ _,by simp [pairTrace]⟩
  · have hfour : natBits 4 = 3 := by decide
    have hwidth := PSTRTMArithmetic008.natBits_mono hlarge
    rw [hfour] at hwidth
    let tail := List.replicate (natBits n-3) true++false::(PSTRTMNatValue017.rawPayload n++suffix)
    have hheader : encodeDatum (.natural n)++suffix = false::true::true::true::tail := by
      dsimp only [tail]
      rw [encodeDatum,PA17TMRatArithmeticParse002.encodeNat_rawField]
      simp only [PA17TMRatArithmeticParse002.rawField]
      have hl : (PSTRTMNatValue017.rawPayload n).length = natBits n := by
        simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
      rw [hl]
      have he : natBits n = 3+(natBits n-3) := by omega
      conv_lhs => rw [he,List.replicate_add]
      simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc]
    have hn : ¬n ≤ 2 := by omega
    refine ⟨wideTrace left tail,?_,by simp [wideTrace]⟩
    simp only [hheader,hn,ite_false]
    exact wide_runsFrom _ _

theorem datum_return_bounded (n : Nat) (left suffix : List Bool) (inputLength : Nat) :
    ∃ trace,
      PSTRTMSeq005.RunsFrom returnMachine
        (state 0 left (encodeDatum (.natural n)++suffix)) trace
        (state (if n ≤ 2 then 14 else 15) left (encodeDatum (.natural n)++suffix)) ∧
      trace.length ≤ 10 ∧
      ∀ clock, visitedSpace returnMachine inputLength (trace.take clock) ≤ inputLength+21 := by
  obtain ⟨trace,actual,time⟩ := datum_return_contract n left suffix
  refine ⟨trace,actual,time,?_⟩
  intro clock
  have hs := PSTRTMTrace002.visitedSpace_le returnMachine inputLength (trace.take clock)
  have hl : (trace.take clock).length ≤ trace.length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCapReturn240
