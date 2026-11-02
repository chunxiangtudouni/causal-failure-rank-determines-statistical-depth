module
public import PaperProofs.Common.PSTR_TM_Header_003

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPayload007
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrace002 PSTRTMHeader003

/-- Two fixed states: scan true length bits, consume exactly the first
false delimiter, then genuinely halt on the first payload bit. -/
def payloadMachine : Machine 1 := fun q symbol =>
  if q.val = 0 then some (if symbol then 0 else 1, .move .right) else none

def payloadState (q : Fin 2) (left right : List Bool) : MachineState 1 :=
  ⟨q, Turing.Tape.mk₂ left right⟩

def payloadTrace : Nat → List Bool → List Bool → List (MachineState 1)
  | 0, left, tail => [payloadState 0 left (false :: tail), payloadState 1 (false :: left) tail]
  | n + 1, left, tail =>
    payloadState 0 left (List.replicate (n + 1) true ++ false :: tail) ::
      payloadTrace n (true :: left) tail

theorem payload_true_step (left right : List Bool) :
    Turing.TM0.step payloadMachine (payloadState 0 left (true :: right)) =
      some (payloadState 0 (true :: left) right) := by
  simp [Turing.TM0.step, payloadMachine, payloadState, Turing.Tape.mk₂,
    Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk, Turing.ListBlank.cons_mk]

theorem payload_false_step (left right : List Bool) :
    Turing.TM0.step payloadMachine (payloadState 0 left (false :: right)) =
      some (payloadState 1 (false :: left) right) := by
  simp [Turing.TM0.step, payloadMachine, payloadState, Turing.Tape.mk₂,
    Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk, Turing.ListBlank.cons_mk]

theorem payload_halt (left right : List Bool) :
    Turing.TM0.step payloadMachine (payloadState 1 left right) = none := by
  simp [Turing.TM0.step, payloadMachine, payloadState]

theorem payloadTrace_head (n : Nat) (left tail : List Bool) :
    (payloadTrace n left tail).head? =
      some (payloadState 0 left (List.replicate n true ++ false :: tail)) := by
  cases n <;> rfl

theorem payloadTrace_length (n : Nat) (left tail : List Bool) :
    (payloadTrace n left tail).length = n + 2 := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih => simp only [payloadTrace, List.length_cons, ih]

theorem payloadTrace_chain (n : Nat) (left tail : List Bool) :
    (payloadTrace n left tail).IsChain (fun a b => Turing.TM0.step payloadMachine a = some b) := by
  induction n generalizing left with
  | zero =>
    simp only [payloadTrace, List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact payload_false_step left tail
  | succ n ih =>
    rw [payloadTrace]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      simp only [payloadTrace_head, Option.mem_some_iff] at ha
      subst after
      simpa only [List.replicate_succ, List.cons_append] using
        payload_true_step left (List.replicate n true ++ false :: tail)
    · exact ih (true :: left)

theorem payloadTrace_last (n : Nat) (left tail : List Bool) :
    (payloadTrace n left tail).getLast? =
      some (payloadState 1 (false :: (List.replicate n true ++ left)) tail) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
    have hne : payloadTrace n (true :: left) tail ≠ [] := by
      have := payloadTrace_length n (true :: left) tail
      intro h
      simp [h] at this
    rw [payloadTrace, List.getLast?_cons_of_ne_nil hne, ih, replicate_push]

theorem payload_runs (n : Nat) (tail : List Bool) :
    Runs payloadMachine (List.replicate n true ++ false :: tail) (payloadTrace n [] tail)
      (payloadState 1 (false :: List.replicate n true) tail) := by
  apply runs_of_chain
  · simpa [Turing.TM0.init, Turing.Tape.mk₁, payloadState] using payloadTrace_head n [] tail
  · exact payloadTrace_chain n [] tail
  · simpa using payloadTrace_last n [] tail
  · exact payload_halt _ _

theorem payload_computes (n : Nat) (tail : List Bool) :
    computes payloadMachine (List.replicate n true ++ false :: tail) tail
      (n + 2) (3 * n + tail.length + 6) := by
  refine ⟨payloadTrace n [] tail, payloadState 1 (false :: List.replicate n true) tail,
    payload_runs n tail, ?_, ?_, ?_⟩
  · simp [payloadState, Turing.Tape.mk₂]
  · exact (payloadTrace_length n [] tail).le
  · have h := visitedSpace_le payloadMachine (List.replicate n true ++ false :: tail).length
      (payloadTrace n [] tail)
    simp only [payloadTrace_length, List.length_append, List.length_replicate, List.length_cons] at h ⊢
    omega

/-- Fixed two-state TM exposes precisely the original number's binary
payload, preserving every arbitrary following bit and charging all steps. -/
theorem encodeNat_payload_computes (value : Nat) (suffix : List Bool) :
    let payload := List.ofFn (fun position : Fin (natBits value) => value.testBit position.val)
    computes payloadMachine (encodeNat value ++ suffix) (payload ++ suffix)
      (natBits value + 2) (4 * natBits value + suffix.length + 6) := by
  dsimp only
  have h := payload_computes (natBits value)
    (List.ofFn (fun position : Fin (natBits value) => value.testBit position.val) ++ suffix)
  convert h using 1
  · simp [encodeNat, List.append_assoc]
  · simp only [List.length_append, List.length_ofFn]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPayload007
