module

public import Common.PSTR_WordBool_RawOutput_Cleanup002
public import Common.PSTR_WordBool_RawOutput_ExtractNative010
public import Common.PSTR_WordBool_RawOutput_Unflag_Final001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Common.Native.PSTRWordBool.RawOutput

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005

noncomputable def frontStates : Nat := cleanupStates+extractStates+1
noncomputable def frontCode : Machine frontStates := seqMachine cleanupMachine extractMachine
noncomputable def states : Nat := frontStates+21+1
noncomputable def code : Machine states := seqMachine frontCode Unflag.unflagMachine
noncomputable def entryPort : Fin (states+1) := 0
noncomputable def haltPort : Fin (states+1) := rightLabel (a := frontStates) Unflag.unflagHalt
noncomputable def coefficient : Nat := cleanupCoefficient+extractCoefficient+128

theorem coefficient_positive : 0 < coefficient := by unfold coefficient; omega

/- ONE fixed finite native table. All other stacks are really cleared,
all33-bit source rows and the owned guard are really erased, and the final
bare Bool list is produced by the paid inverse and unary-header skip. -/
set_option backward.isDefEq.respectTransparency false in
theorem actual (bank : Stacks) (tracks : Tracks) (rep : represented bank tracks) :
    ∃ trace final, RunsFrom code ⟨entryPort,encodedTape tracks⟩ trace final ∧
      final.q=haltPort ∧ TM0.step code final=none ∧
      final.Tape.right₀=ListBlank.mk (bank 0) ∧
      final.Tape=Tape.mk₂ (false :: (List.replicate (bank 0).length true ++ [false])) (bank 0) ∧
      trace.length ≤ coefficient*(weight bank)^2 ∧
      ∀ inputLen clock, visitedSpace code inputLen (trace.take clock) ≤
        inputLen+2*coefficient*(weight bank)^2+1 := by
  obtain ⟨cleanTrace,cleanFinal,cleanRun,cleanLabel,cleanTape,cleanClock⟩ := cleanup_contract bank tracks rep
  obtain ⟨extractTrace,extractFinal,extractRun,extractLabel,extractTape,extractClock⟩ := extract_contract (bank 0)
  have next : RunsFrom extractMachine ⟨0,cleanFinal.Tape⟩ extractTrace extractFinal := by
    rw [cleanTape]
    exact extractRun
  let frontTrace : List (MachineState frontStates) := cleanTrace.map (leftCfg (b := extractStates)) ++
    extractTrace.map (rightCfg (a := cleanupStates))
  let frontFinal : MachineState frontStates := rightCfg (a := cleanupStates) extractFinal
  have frontRun := seq_runsFrom cleanupMachine extractMachine ⟨0,encodedTape tracks⟩ cleanFinal
    extractFinal cleanTrace extractTrace cleanRun next
  change RunsFrom frontCode ⟨0,encodedTape tracks⟩ frontTrace frontFinal at frontRun
  have lastCall : RunsFrom Unflag.unflagMachine ⟨0,frontFinal.Tape⟩
      (Unflag.unflagTrace (bank 0)) (Unflag.unflagFinal (bank 0)) := by
    change RunsFrom Unflag.unflagMachine ⟨0,extractFinal.Tape⟩ _ _
    rw [extractTape]
    exact Unflag.unflag_runsFrom (bank 0)
  let trace : List (MachineState states) := frontTrace.map (leftCfg (a := frontStates) (b := 21)) ++
    (Unflag.unflagTrace (bank 0)).map (rightCfg (a := frontStates))
  let final : MachineState states := rightCfg (a := frontStates) (Unflag.unflagFinal (bank 0))
  have run := seq_runsFrom frontCode Unflag.unflagMachine ⟨0,encodedTape tracks⟩ frontFinal
    (Unflag.unflagFinal (bank 0)) frontTrace (Unflag.unflagTrace (bank 0)) frontRun lastCall
  change RunsFrom code ⟨entryPort,encodedTape tracks⟩ trace final at run
  have digitsBound : (bank 0).length+1 ≤ weight bank := by
    have bound := slot_length_lt_weight bank 0
    nlinarith
  have squareBound := Nat.pow_le_pow_left digitsBound 2
  have extractBound := extractClock.trans (Nat.mul_le_mul_left extractCoefficient squareBound)
  have unflagBound : (Unflag.unflagTrace (bank 0)).length ≤ 128*(weight bank)^2 := by
    rw [Unflag.unflag_length]
    have enlarged := Nat.mul_le_mul_left 128 squareBound
    nlinarith
  have clock : trace.length ≤ coefficient*(weight bank)^2 := by
    simp only [trace,frontTrace,List.length_append,List.length_map]
    unfold coefficient
    nlinarith
  refine ⟨trace,final,run,?_,run.2.2.2,?_,?_,clock,?_⟩
  · change rightLabel (a := frontStates) (Unflag.unflagFinal (bank 0)).q=haltPort
    rw [Unflag.unflag_final_label]
    rfl
  · exact Unflag.unflag_output (bank 0)
  · exact Unflag.unflag_whole_tape (bank 0)
  · intro inputLen clockIndex
    have cells := PSTRTMTrace002.visitedSpace_le code inputLen (trace.take clockIndex)
    have shortPrefix := (List.length_take_le' clockIndex trace).trans clock
    nlinarith

/-- The literal tape interface returned by frozen040. The representation
is the same per-slot equality already produced by its actual native run. -/
theorem compiled_endpoint {Λ σ : Type*}
    (source : TM2.Cfg (fun _ : Fin 16 => Bool) Λ σ) (tracks : Tracks)
    (rep : ∀ slot, tracks.map (proj slot)=ListBlank.mk ((source.stk slot).map some).reverse) :
    ∃ trace final, RunsFrom code
      ⟨entryPort,TM1to1.trTape (FiniteTrackCodec.encode_default 16) (ScannerRun.compiledCfg source tracks).Tape⟩ trace final ∧
      final.q=haltPort ∧ TM0.step code final=none ∧
      final.Tape.right₀=ListBlank.mk (source.stk 0) ∧
      trace.length ≤ coefficient*(weight source.stk)^2 ∧
      ∀ inputLen clock, visitedSpace code inputLen (trace.take clock) ≤
        inputLen+2*coefficient*(weight source.stk)^2+1 := by
  obtain ⟨trace,final,run,label,halt,output,whole,clock,cells⟩ := actual source.stk tracks rep
  exact ⟨trace,final,run,label,halt,output,clock,cells⟩

/-- Code, ports and positive polynomial constants all precede ALL sixteen
source stacks and ALL valid joint track representations. -/
theorem fixed_decoder : ∃ (m : Nat) (B : Machine m) (entry halt : Fin (m+1)) (c d : Nat),
    0<c ∧ 0<d ∧ ∀ (bank : Stacks) (tracks : Tracks), represented bank tracks →
    ∃ trace final, RunsFrom B ⟨entry,encodedTape tracks⟩ trace final ∧
      final.q=halt ∧ TM0.step B final=none ∧ final.Tape.right₀=ListBlank.mk (bank 0) ∧
      trace.length ≤ c*(weight bank)^d ∧
      ∀ inputLen clock, visitedSpace B inputLen (trace.take clock) ≤
        inputLen+2*c*(weight bank)^d+1 := by
  refine ⟨states,code,entryPort,haltPort,coefficient,2,coefficient_positive,by decide,?_⟩
  intro bank tracks rep
  obtain ⟨trace,final,run,label,halt,output,whole,clock,cells⟩ := actual bank tracks rep
  exact ⟨trace,final,run,label,halt,output,clock,cells⟩

end PaperProofs.Common.Native.PSTRWordBool.RawOutput
