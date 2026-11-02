module
public import Structure.PA17_TM_RatArithmetic_FlagZero_028a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFlagZero028

open Turing

attribute [local simp] zeroPort nonzeroPort

theorem payload_zero : PSTRTMNatValue017.rawPayload 0 = [false] := by decide

theorem payload_single_false_iff (n : Nat) : PSTRTMNatValue017.rawPayload n = [false] ↔ n=0 := by
  constructor
  · intro hp
    have hv := PSTRTMNatValue017.valueDigits_rawPayload n
    rw [hp] at hv
    simpa [PSTRTMIncrement009.valueDigits] using hv.symm
  · intro hn
    subst n
    exact payload_zero

theorem payload_ne_nil (n : Nat) : PSTRTMNatValue017.rawPayload n ≠ [] := by
  intro hp
  have hv := PSTRTMNatValue017.valueDigits_rawPayload n
  rw [hp] at hv
  have hn : n=0 := by simpa [PSTRTMIncrement009.valueDigits] using hv.symm
  rw [hn,payload_zero] at hp
  cases hp

def cacheWord (n : Nat) (suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n)++false::false::suffix

def chosenPort (n : Nat) : Fin 10 := if n=0 then zeroPort else nonzeroPort

def canonicalInitial (archive : List Bool) (n : Nat) (suffix : List Bool) : MachineState 9 :=
  state 0 archive (cacheWord n suffix)

def canonicalFinal (archive : List Bool) (n : Nat) (suffix : List Bool) : MachineState 9 :=
  state (chosenPort n) archive (cacheWord n suffix)

def canonicalTrace (archive : List Bool) (n : Nat) (suffix : List Bool) : List (MachineState 9) :=
  match PSTRTMNatValue017.rawPayload n with
  | [] => []
  | true::later => firstTrueTrace archive (true::(PSTRTMIncrement009.blocks later++false::false::suffix))
  | false::[] => singleFalseTrace archive suffix
  | false::second::later => laterFalseTrace archive second later suffix

/-- n describes a canonical cached field actually produced by Store019.
No n/width/zero flag is a field of this ONE fixed ten-label code. -/
theorem canonical_runsFrom (archive : List Bool) (n : Nat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom zeroMachine (canonicalInitial archive n suffix)
      (canonicalTrace archive n suffix) (canonicalFinal archive n suffix) := by
  cases hp : PSTRTMNatValue017.rawPayload n with
  | nil => exact False.elim (payload_ne_nil n hp)
  | cons bit later =>
    cases bit with
    | true =>
      have hn : n≠0 := by
        intro he
        have h := hp
        rw [he,payload_zero] at h
        cases h
      simpa [canonicalInitial,canonicalFinal,cacheWord,canonicalTrace,hp,chosenPort,hn,
        PSTRTMIncrement009.blocks] using
        firstTrue_runsFrom archive (true::(PSTRTMIncrement009.blocks later++false::false::suffix))
    | false =>
      cases later with
      | nil =>
        have hn : n=0 := (payload_single_false_iff n).mp hp
        subst n
        simpa [canonicalInitial,canonicalFinal,cacheWord,canonicalTrace,payload_zero,chosenPort,
          PSTRTMIncrement009.blocks] using singleFalse_runsFrom archive suffix
      | cons second later =>
        have hn : n≠0 := by
          intro he
          have h := hp
          rw [he,payload_zero] at h
          have hl := congrArg List.length h
          simp only [List.length_cons,List.length_nil] at hl
          omega
        simpa [canonicalInitial,canonicalFinal,cacheWord,canonicalTrace,hp,chosenPort,hn,
          PSTRTMIncrement009.blocks] using laterFalse_runsFrom archive second later suffix

theorem canonical_same_tape (archive : List Bool) (n : Nat) (suffix : List Bool) :
    (canonicalFinal archive n suffix).Tape = (canonicalInitial archive n suffix).Tape := rfl

theorem canonical_final_tape (archive : List Bool) (n : Nat) (suffix : List Bool) :
    (canonicalFinal archive n suffix).Tape =
      Tape.mk₂ archive (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n)++false::false::suffix) := rfl

theorem canonical_zero_iff (archive : List Bool) (n : Nat) (suffix : List Bool) :
    (canonicalFinal archive n suffix).q = zeroPort ↔ n=0 := by
  by_cases hn : n=0 <;> simp [canonicalFinal,state,chosenPort,hn]

theorem canonical_nonzero_iff (archive : List Bool) (n : Nat) (suffix : List Bool) :
    (canonicalFinal archive n suffix).q = nonzeroPort ↔ n≠0 := by
  by_cases hn : n=0 <;> simp [canonicalFinal,state,chosenPort,hn]

theorem canonical_halt (archive : List Bool) (n : Nat) (suffix : List Bool) :
    TM0.step zeroMachine (canonicalFinal archive n suffix) = none :=
  (canonical_runsFrom archive n suffix).2.2.2

theorem canonicalTrace_length_le (archive : List Bool) (n : Nat) (suffix : List Bool) :
    (canonicalTrace archive n suffix).length ≤ 7 := by
  cases hp : PSTRTMNatValue017.rawPayload n with
  | nil => simp [canonicalTrace,hp]
  | cons bit later =>
    cases bit with
    | true => simp [canonicalTrace,hp,firstTrueTrace_length]
    | false =>
      cases later with
      | nil => simp [canonicalTrace,hp,singleFalseTrace_length]
      | cons second later => simp [canonicalTrace,hp,laterFalseTrace_length]

theorem canonical_prefix_space (archive : List Bool) (n : Nat) (suffix : List Bool)
    (prefixLength chargedLength : Nat) :
    visitedSpace zeroMachine chargedLength ((canonicalTrace archive n suffix).take prefixLength) ≤
      chargedLength+15 := by
  have hs := PSTRTMTrace002.visitedSpace_le zeroMachine chargedLength
    ((canonicalTrace archive n suffix).take prefixLength)
  have ht := canonicalTrace_length_le archive n suffix
  have hp : ((canonicalTrace archive n suffix).take prefixLength).length ≤ (canonicalTrace archive n suffix).length := by
    simp only [List.length_take]
    omega
  omega

/-- Actual run, true HALT, same first-data head and ENTIRE tape, exact zero
port semantics and original prefix cost. No callerzero implementation. -/
theorem canonical_sensor (archive : List Bool) (n : Nat) (suffix : List Bool) :
    ∃ trace final,
      PSTRTMSeq005.RunsFrom zeroMachine
        ⟨0,Tape.mk₂ archive (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n)++false::false::suffix)⟩
        trace final ∧
      final.Tape=Tape.mk₂ archive
        (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n)++false::false::suffix) ∧
      (final.q=zeroPort ↔ n=0) ∧ (final.q=nonzeroPort ↔ n≠0) ∧
      trace.length≤7 ∧
      ∀ prefixLength chargedLength,
        visitedSpace zeroMachine chargedLength (trace.take prefixLength) ≤ chargedLength+15 :=
  ⟨canonicalTrace archive n suffix,canonicalFinal archive n suffix,canonical_runsFrom archive n suffix,
    canonical_final_tape archive n suffix,canonical_zero_iff archive n suffix,
    canonical_nonzero_iff archive n suffix,canonicalTrace_length_le archive n suffix,
    canonical_prefix_space archive n suffix⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFlagZero028
