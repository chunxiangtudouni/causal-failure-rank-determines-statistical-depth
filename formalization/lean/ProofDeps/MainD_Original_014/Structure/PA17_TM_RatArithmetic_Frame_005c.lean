module
public import Structure.PA17_TM_RatArithmetic_Frame_005b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFrame005

open Turing

theorem windowPrefix_mk (n : Nat) (word : List Bool) :
    windowPrefix n (ListBlank.mk word) =
      word.take n ++ List.replicate (n-word.length) false := by
  induction n generalizing word with
  | zero => simp [windowPrefix]
  | succ n ih =>
    cases word with
    | nil => simp [windowPrefix, ih, List.replicate_succ]
    | cons bit word => simp [windowPrefix, ih]

theorem windowPrefix_mk_of_length (n : Nat) (word : List Bool) (bound : word.length ≤ n) :
    windowPrefix n (ListBlank.mk word) = word ++ List.replicate (n-word.length) false := by
  rw [windowPrefix_mk, List.take_of_length_le bound]

theorem frameTape_mk₂ (leftWord rightWord : List Bool) (left right : Nat)
    (archive suffix : List Bool) :
    frameTape (Tape.mk₂ leftWord rightWord) left right archive suffix =
      Tape.mk₂ (windowPrefix left (ListBlank.mk leftWord) ++ archive)
        (windowPrefix (right+1) (ListBlank.mk rightWord) ++ suffix) := by
  simp [frameTape, Tape.mk₂, Tape.mk', windowPrefix]

/-- Exact owned padding required by the locality lemma. Merely stating this
equality does not allocate it. A runtime producer must prove these cells really
exist before invoking the unchanged isolated arithmetic machine. -/
theorem frameTape_mk₁ (word : List Bool) (left right : Nat)
    (archive suffix : List Bool) (bound : word.length ≤ right+1) :
    frameTape (Tape.mk₁ word) left right archive suffix =
      Tape.mk₂ (List.replicate left false ++ archive)
        (word ++ List.replicate (right+1-word.length) false ++ suffix) := by
  rw [Tape.mk₁,frameTape_mk₂,windowPrefix_mk_of_length (right+1) word bound]
  simp [windowPrefix_mk,List.append_assoc]

variable {states : Nat}

/-- A checked isolated run becomes a SAME-code framed invocation once the
real blank workspace is supplied. Input width/padding is absent from code;
these hypotheses are discharged by actual caller allocation, not exported as
the original four-Rat theorem's input assumptions. -/
theorem isolated_frame_runs (machine : Machine states) (input output : List Bool)
    (trace : List (MachineState states)) (final : MachineState states)
    (run : Runs machine input trace final) (wholeFinal : final.Tape = Tape.mk₁ output)
    (left right : Nat) (archive suffix : List Bool)
    (hl : trace.length ≤ left) (hr : trace.length ≤ right)
    (inputFits : input.length ≤ right+1) :
    ∃ (finalLeft finalRight : Nat) (framed : List (MachineState states)),
      PSTRTMSeq005.RunsFrom machine
        ⟨0,Tape.mk₂ (List.replicate left false ++ archive)
          (input ++ List.replicate (right+1-input.length) false ++ suffix)⟩
        framed (frameCfg finalLeft finalRight archive suffix final) ∧
      (frameCfg finalLeft finalRight archive suffix final).Tape =
        frameTape (Tape.mk₁ output) finalLeft finalRight archive suffix ∧
      framed.length = trace.length ∧
      (∀ inputLength, visitedSpace machine inputLength framed = visitedSpace machine inputLength trace) ∧
      finalLeft+finalRight = left+right := by
  have runFrom : PSTRTMSeq005.RunsFrom machine (TM0.init input) trace final :=
    ⟨run.1,run.2.1,run.2.2.1,run.2.2.2.1⟩
  obtain ⟨finalLeft,finalRight,framed,hfrun,hlen,hspace,hsum⟩ :=
    frame_run_cost machine archive suffix trace (TM0.init input) final left right runFrom hl hr
  have hi : frameCfg left right archive suffix (TM0.init input) =
      (⟨0,Tape.mk₂ (List.replicate left false ++ archive)
        (input ++ List.replicate (right+1-input.length) false ++ suffix)⟩ : MachineState states) := by
    unfold frameCfg TM0.init
    rw [frameTape_mk₁ input left right archive suffix inputFits]
    simp only [Fin.default_eq_zero]
  rw [hi] at hfrun
  refine ⟨finalLeft,finalRight,framed,hfrun,?_,hlen,hspace,hsum⟩
  change frameTape final.Tape finalLeft finalRight archive suffix = _
  rw [wholeFinal]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFrame005
