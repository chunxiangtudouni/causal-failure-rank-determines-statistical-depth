module

public import Common.PSTR_SYM_CounterRound_031

/-! ONE real Natural-Datum parser, using the frozen raw field parser.
Unlike the older Natural-prefix loop its parser HALT remains a true HALT.
It stops on the next original suffix cell, with no EOF assertion. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDatumParser

open Turing PSTRTMSeq005 PA17TMRatArithmeticParse002
open PSTRSymbolicLocator (embedCfg embedLabel scanState naturalLeft rawPayload_length)

def naturalDatumMachine : Machine 18 := fun label symbol =>
  if initial : label.val = 0 then some (1, .move .right)
  else (streamMachine ⟨label.val - 1, by omega⟩ symbol).map
    (fun (next, op) => (embedLabel next, op))

theorem natural_step_embed (cfg : MachineState 17) :
    TM0.step naturalDatumMachine (embedCfg cfg) = (TM0.step streamMachine cfg).map embedCfg := by
  cases cfg with
  | mk label tape =>
    unfold TM0.step naturalDatumMachine embedCfg embedLabel
    simp only [show ¬label.val + 1 = 0 by omega, ↓reduceDIte, Nat.add_sub_cancel, Fin.eta]
    cases action : streamMachine label tape.head with
    | none => simp
    | some pair =>
      obtain ⟨next, op⟩ := pair
      cases op <;> simp

theorem natural_first_step (left : List Bool) (number : Nat) (suffix : List Bool) :
    TM0.step naturalDatumMachine (scanState 0 left (encodeDatum (.natural number) ++ suffix)) =
      some (embedCfg (streamState 0 (false :: left) (encodeNat number ++ suffix))) := by
  simp [TM0.step, naturalDatumMachine, scanState, embedCfg, embedLabel, streamState,
    Tape.mk₂, encodeDatum, List.cons_append]

def naturalDatumTrace (left : List Bool) (number : Nat) (suffix : List Bool) :
    List (MachineState 18) :=
  [scanState 0 left (encodeDatum (.natural number) ++ suffix)] ++
    (streamTrace (false :: left) [] (PSTRTMNatValue017.rawPayload number) suffix).map embedCfg

def naturalDatumFinal (left : List Bool) (number : Nat) (suffix : List Bool) : MachineState 18 :=
  embedCfg (streamFinal (false :: left) (PSTRTMNatValue017.rawPayload number) suffix)

theorem naturalDatum_runsFrom (left : List Bool) (number : Nat) (suffix : List Bool) :
    RunsFrom naturalDatumMachine ⟨0, Tape.mk₂ left (encodeDatum (.natural number) ++ suffix)⟩
      (naturalDatumTrace left number suffix) (naturalDatumFinal left number suffix) := by
  have parsed := encodeNat_stream_runsFrom (false :: left) suffix number
  refine ⟨rfl, ?_, ?_, ?_⟩
  · apply List.IsChain.append
    · exact .singleton _
    · apply (List.isChain_map _).mpr
      exact parsed.2.1.imp (fun before after step => by simp [natural_step_embed, step])
    · intro before beforeLast after afterHead
      simp only [List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      simp only [List.head?_map, parsed.1, Option.map_some, Option.mem_some_iff] at afterHead
      subst before
      subst after
      exact natural_first_step left number suffix
  · simp only [naturalDatumTrace, naturalDatumFinal, List.getLast?_append, List.getLast?_map, parsed.2.2.1,
      Option.map_some, Option.some_or]
  · simp only [naturalDatumFinal, natural_step_embed, parsed.2.2.2, Option.map_none]

theorem naturalDatum_final_tape (left : List Bool) (number : Nat) (suffix : List Bool) :
    (naturalDatumFinal left number suffix).Tape = Tape.mk₂ (naturalLeft left number) suffix := rfl

theorem naturalDatum_time_le (left : List Bool) (number : Nat) (suffix : List Bool) :
    (naturalDatumTrace left number suffix).length ≤ 17 * (natBits number + 1)^2 := by
  have time := stream_length_le (false :: left) (PSTRTMNatValue017.rawPayload number) suffix
  rw [rawPayload_length] at time
  have one : 1 ≤ (natBits number + 1)^2 := by
    nlinarith [Nat.zero_le (natBits number), Nat.zero_le ((natBits number)^2)]
  simp only [naturalDatumTrace, List.length_append, List.length_cons, List.length_nil, List.length_map]
  calc
    _ ≤ 1 + 16 * (natBits number + 1)^2 := Nat.add_le_add_left time 1
    _ ≤ 17 * (natBits number + 1)^2 := by omega

theorem naturalDatum_prefix_space (left : List Bool) (number : Nat) (suffix : List Bool)
    (inputLength clock : Nat) :
    visitedSpace naturalDatumMachine inputLength ((naturalDatumTrace left number suffix).take clock) ≤
      inputLength + 34 * (natBits number + 1)^2 + 1 := by
  have time := naturalDatum_time_le left number suffix
  have cells := PSTRTMTrace002.visitedSpace_le naturalDatumMachine inputLength
    ((naturalDatumTrace left number suffix).take clock)
  have length : ((naturalDatumTrace left number suffix).take clock).length ≤
      (naturalDatumTrace left number suffix).length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDatumParser
