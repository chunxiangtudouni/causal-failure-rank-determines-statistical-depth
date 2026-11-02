module

public import Paid.PDROC_BitVM_Common_IO_Output_Program_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

theorem native_return (saved : Store) (tape : Tape Bool) :
    TM1.step program (cfg (nativeLabel 19) saved tape) = some (cfg 31 saved tape) := by
  change some (TM1.stepAux (program (nativeLabel 19)) saved tape) = _
  rw [native_program]
  cases symbol : tape.head <;>
    simp [nativeStatement, nativeAction, PSTRTMUnblock018.unblockMachine, TM1.stepAux, symbol, cfg]

/-- Reuse the SAME genuine selected inverse-codec trace for arbitrary
Bool digits and arbitrary old left/right archive. The real return from
oldHALT is paid, and the actual whole tape/caller flags are retained. -/
theorem native_blocks_path (saved : Store) (archive digits suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 11 saved (Tape.mk₂ (false :: archive)
        (PSTRTMIncrement009.blocks digits ++ false :: false :: suffix)))
      (cfg 31 saved (Tape.mk₂ (false :: archive)
        (PSTRTMUnblockTrace019.rawWord digits ++ false :: suffix))),
      path.posts.length ≤ 32 * (digits.length + 1)^2 := by
  obtain ⟨trace, final, actual, finalQ, finalTape, bound, _⟩ :=
    PA17TMRatArithmeticUnblock004.framed_encoder archive digits suffix
  cases trace with
  | nil => cases actual.1
  | cons first rest =>
    have initial : first = (⟨0, Tape.mk₂ (false :: archive)
        (PSTRTMIncrement009.blocks digits ++ false :: false :: suffix)⟩ : MachineState 19) :=
      Option.some.inj actual.1
    subst first
    have chain : (((⟨0, Tape.mk₂ (false :: archive)
        (PSTRTMIncrement009.blocks digits ++ false :: false :: suffix)⟩ : MachineState 19) ::
        rest).map (embedNative saved)).IsChain (fun before after => TM1.step program before = some after) :=
      List.isChain_map_of_isChain (embedNative saved)
        (fun before after edge => native_edge saved before after edge) actual.2.1
    have last : (((⟨0, Tape.mk₂ (false :: archive)
        (PSTRTMIncrement009.blocks digits ++ false :: false :: suffix)⟩ : MachineState 19) ::
        rest).map (embedNative saved)).getLast? = some (embedNative saved final) := by
      rw [List.getLast?_map, actual.2.2.1]
      rfl
    let lifted : ActualPath (TM1.step program)
        (cfg 11 saved (Tape.mk₂ (false :: archive)
          (PSTRTMIncrement009.blocks digits ++ false :: false :: suffix)))
        (cfg (nativeLabel 19) saved (Tape.mk₂ (false :: archive)
          (PSTRTMUnblockTrace019.rawWord digits ++ false :: suffix))) :=
      ⟨rest.map (embedNative saved),
        by simpa [embedNative, cfg, nativeLabel] using chain,
        by simpa [embedNative, cfg, nativeLabel, finalQ, finalTape] using last⟩
    let joined := lifted.trans (ActualPath.single (native_return saved _))
    refine ⟨joined, ?_⟩
    simpa only [joined, ActualPath.trans, lifted, ActualPath.single, List.length_append,
      List.length_map, List.length_cons, List.length_nil] using bound

theorem replicate_true_push (count : Nat) (left : List Bool) :
    List.replicate count true ++ true :: left = true :: (List.replicate count true ++ left) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons true) ih

/-- Actual scan, not a host drop of the unary header. All scanned TRUEs
and its FALSE separator are retained on the actual left tape. -/
theorem skip_header_path (saved : Store) (count : Nat) (left right : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 31 saved (Tape.mk₂ left (List.replicate count true ++ false :: right)))
      (cfg 32 saved (Tape.mk₂ (false :: (List.replicate count true ++ left)) right)),
      path.posts.length = count + 1 := by
  induction count generalizing left with
  | zero =>
    have edge : TM1.step program (cfg 31 saved (Tape.mk₂ left (false :: right))) =
        some (cfg 32 saved (Tape.mk₂ (false :: left) right)) := by
      simp [TM1.step, TM1.stepAux, cfg, program, Tape.mk₂]
    exact ⟨ActualPath.single edge, rfl⟩
  | succ count ih =>
    have edge : TM1.step program
        (cfg 31 saved (Tape.mk₂ left (List.replicate (count + 1) true ++ false :: right))) =
        some (cfg 31 saved (Tape.mk₂ (true :: left) (List.replicate count true ++ false :: right))) := by
      simp [TM1.step, TM1.stepAux, cfg, program, Tape.mk₂, List.replicate_succ]
    obtain ⟨⟨posts, chain, last⟩, length⟩ := ih (true :: left)
    have lengthBound : posts.length = count + 1 := length
    let later : ActualPath (TM1.step program)
        (cfg 31 saved (Tape.mk₂ (true :: left) (List.replicate count true ++ false :: right)))
        (cfg 32 saved (Tape.mk₂ (false :: (List.replicate (count + 1) true ++ left)) right)) :=
      ⟨posts, chain, by simpa only [replicate_true_push, List.replicate_succ, List.cons_append] using last⟩
    refine ⟨(ActualPath.single edge).trans later, ?_⟩
    simp only [ActualPath.trans, ActualPath.single, later, List.length_append, List.length_cons, List.length_nil]
    omega

theorem final_halt (saved : Store) (tape : Tape Bool) :
    TM1.step program (cfg 32 saved tape) = some (⟨none, saved, tape⟩ : TM1.Cfg Bool Label Store) := rfl

/-- Inverse block encoding, actual unary removal, real HALT, same full
archive and naked original digits on the right. The footerTRUE property
needed for exact right0 is supplied by encodeBits, not by this machine. -/
theorem decode_blocks_path (saved : Store) (archive digits suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 11 saved (Tape.mk₂ (false :: archive)
        (PSTRTMIncrement009.blocks digits ++ false :: false :: suffix)))
      (⟨none, saved, Tape.mk₂ (false :: (List.replicate digits.length true ++ false :: archive))
        (digits ++ false :: suffix)⟩ : TM1.Cfg Bool Label Store),
      path.posts.length ≤ 64 * (digits.length + 1)^2 := by
  obtain ⟨first, firstBound⟩ := native_blocks_path saved archive digits suffix
  obtain ⟨⟨posts, chain, last⟩, length⟩ :=
    skip_header_path saved digits.length (false :: archive) (digits ++ false :: suffix)
  have headerLength : posts.length = digits.length + 1 := length
  let header : ActualPath (TM1.step program)
      (cfg 31 saved (Tape.mk₂ (false :: archive)
        (PSTRTMUnblockTrace019.rawWord digits ++ false :: suffix)))
      (cfg 32 saved (Tape.mk₂ (false :: (List.replicate digits.length true ++ false :: archive))
        (digits ++ false :: suffix))) :=
    ⟨posts,
      by simpa [PSTRTMUnblockTrace019.rawWord, List.append_assoc] using chain,
      by simpa [PSTRTMUnblockTrace019.rawWord, List.append_assoc] using last⟩
  let joined := (first.trans header).trans (ActualPath.single (final_halt saved _))
  refine ⟨joined, ?_⟩
  have positive : 1 ≤ (digits.length + 1)^2 := Nat.one_le_pow' 2 digits.length
  have linear : digits.length + 1 ≤ (digits.length + 1)^2 := by
    have comparison := Nat.mul_le_mul_left (digits.length + 1) (by omega : 1 ≤ digits.length + 1)
    simpa only [Nat.mul_one, pow_two] using comparison
  simp only [joined, ActualPath.trans, ActualPath.single, header, List.length_append,
    List.length_cons, List.length_nil]
  omega

end PDROC.BitVM.Common.IO.Output
