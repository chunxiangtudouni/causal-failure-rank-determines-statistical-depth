module
public import Common.PSTR_TM_PairRewind_105
public import Common.PSTR_TM_NatValue_017

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCountdownCode164
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMIncrement009

/-- Threshold's fixed-width loop counter. This is not a general binary
subtraction/Rat primitive: it borrows ONE within an existing positive
flagged depth word, retains all flags/width/right context, and actually
rewinds to its first digit. No canonical trimming is performed or needed. -/
def countdownMachine : Machine 8 := fun q symbol =>
  match q.val with
  | 0 => some (if symbol then 1 else 2,if symbol then .write false else .write true)
  | 1 => some (4,.move .right)
  | 2 => some (3,.move .right)
  | 3 => some (0,.move .right)
  | 4 => some (5,.move .right)
  | 5 => some (6,.move .left)
  | 6 => some (if symbol then 7 else 8,if symbol then .move .left else .move .right)
  | 7 => some (6,.move .left)
  | _ => none

def state (q : Fin 9) (left right : List Bool) : MachineState 8 := ⟨q,Turing.Tape.mk₂ left right⟩

def liftRewind (configuration : MachineState 3) : MachineState 8 :=
  ⟨⟨5+configuration.q.val,by have hq := configuration.q.isLt; omega⟩,configuration.Tape⟩

theorem rewind_step (configuration : MachineState 3) :
    Turing.TM0.step countdownMachine (liftRewind configuration)=
      (Turing.TM0.step PSTRTMMulRewind085.rewindMachine configuration).map liftRewind := by
  cases configuration with
  | mk q tape =>
    fin_cases q <;> cases hs : tape.head <;>
      simp_all [liftRewind,Turing.TM0.step,countdownMachine,PSTRTMMulRewind085.rewindMachine]

def predDigits : List Bool → List Bool
  | [] => []
  | false::later => true::predDigits later
  | true::later => false::later

theorem pred_length (digits : List Bool) : (predDigits digits).length=digits.length := by
  induction digits with
  | nil => rfl
  | cons bit later ih => cases bit <;> simp only [predDigits,List.length_cons,ih]

theorem pred_value (digits : List Bool) (hp : true∈digits) :
    valueDigits (predDigits digits)+1=valueDigits digits := by
  induction digits with
  | nil => simp at hp
  | cons bit later ih =>
    cases bit with
    | false =>
      have ht : true∈later := by simpa only [List.mem_cons,Bool.true_eq_false,false_or] using hp
      have h := ih ht
      simp only [predDigits,valueDigits,Nat.bit_false_apply,Nat.bit_true_apply] at h ⊢
      omega
    | true => simp [predDigits,valueDigits,Nat.bit]

theorem has_true_of_value_pos (digits : List Bool) (hp : 0 < valueDigits digits) : true∈digits := by
  induction digits with
  | nil => simp [valueDigits] at hp
  | cons bit later ih =>
    cases bit with
    | false =>
      apply List.mem_cons_of_mem
      apply ih
      simp only [valueDigits,Nat.bit_false_apply] at hp
      omega
    | true => exact List.mem_cons_self

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCountdownCode164
