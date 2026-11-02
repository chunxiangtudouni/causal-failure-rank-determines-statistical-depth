module

public import Paid.PDROC_BitVM_Common_IO_Output_Frames_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

/-- Cells traversed from a flag: each TRUE flag then the NEXT data cell.
This describes physical cells, not a host input to the machine. -/
def nextFlags (values : List Bool) : List Bool := values.flatMap (fun value => [true, value])

theorem nextFlags_length (values : List Bool) : (nextFlags values).length = 2 * values.length := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [nextFlags] at ih ⊢; omega

theorem flag_right_step (saved : Store) (value : Bool) (left suffix : List Bool) :
    TM1.step program (cfg 4 saved (Tape.mk₂ left (true :: value :: suffix))) =
      some (cfg 4 saved (Tape.mk₂ (value :: true :: left) suffix)) := by
  simp [TM1.step, TM1.stepAux, cfg, program, Wide.moveCode, Tape.mk₂]

/-- Find the genuine FALSE end flag by actual two-cell steps, retaining
every previous output datum and every part of the caller archive. -/
theorem flag_right_path (saved : Store) (values : List Bool) (left suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 4 saved (Tape.mk₂ left (nextFlags values ++ false :: suffix)))
      (cfg 4 saved (Tape.mk₂ ((nextFlags values).reverse ++ left) (false :: suffix))),
      path.posts.length = values.length := by
  induction values generalizing left with
  | nil => exact ⟨ActualPath.refl _, rfl⟩
  | cons value values ih =>
    have edge := flag_right_step saved value left (nextFlags values ++ false :: suffix)
    obtain ⟨⟨posts, chain, last⟩, length⟩ := ih (value :: true :: left)
    have lengthBound : posts.length = values.length := length
    let later : ActualPath (TM1.step program)
        (cfg 4 saved (Tape.mk₂ (value :: true :: left) (nextFlags values ++ false :: suffix)))
        (cfg 4 saved (Tape.mk₂ ((nextFlags (value :: values)).reverse ++ left) (false :: suffix))) :=
      ⟨posts, chain, by simpa [nextFlags, List.reverse_append, List.append_assoc] using last⟩
    let joined := (ActualPath.single edge).trans later
    refine ⟨⟨joined.posts, ?_, ?_⟩, ?_⟩
    · simpa [nextFlags] using joined.chain
    · simpa [nextFlags] using joined.last
    · simp only [joined, ActualPath.trans, ActualPath.single, later, List.length_append,
        List.length_cons, List.length_nil]
      omega

/-- Actual flag/data writes. The output datum is the real bit read from
the source row; the whole unrelated archive and future workspace remain. -/
theorem flag_append_step (saved : Store) (previous : Bool) (left suffix : List Bool) :
    TM1.step program (cfg 4 saved (Tape.mk₂ (previous :: left) (false :: suffix))) =
      some (cfg 5 saved (Tape.mk₂ (saved.bit :: left) (true :: suffix))) := by
  simp [TM1.step, TM1.stepAux, cfg, program, Tape.mk₂]

theorem flag_left_step (saved : Store) (value previousFlag : Bool) (left suffix : List Bool) :
    TM1.step program (cfg 5 saved (Tape.mk₂ (value :: previousFlag :: left) (true :: suffix))) =
      some (cfg 5 saved (Tape.mk₂ left (previousFlag :: value :: true :: suffix))) := by
  simp [TM1.step, TM1.stepAux, cfg, program, Wide.moveCode, Tape.mk₂]

/-- Reverse-facing data/previous-flag cells. Only the final predecessor
is the genuine FALSE guard; every earlier predecessor is a TRUE flag. -/
def backData : List Bool → List Bool
  | [] => []
  | value :: rest => value :: (!rest.isEmpty) :: backData rest

def backFrame (saved : Store) (values left suffix : List Bool) : TM1.Cfg Bool Label Store :=
  match values with
  | [] => cfg 5 saved (Tape.mk₂ left (false :: suffix))
  | _ :: _ => cfg 5 saved (Tape.mk₂ (backData values ++ left) (true :: suffix))

theorem back_flag_edge (saved : Store) (value : Bool) (values left suffix : List Bool) :
    TM1.step program (backFrame saved (value :: values) left suffix) =
      some (backFrame saved values left (value :: true :: suffix)) := by
  cases values with
  | nil => simpa [backFrame, backData] using flag_left_step saved value false left suffix
  | cons previous rest =>
    simpa [backFrame, backData, List.cons_append] using
      flag_left_step saved value true (backData (previous :: rest) ++ left) suffix

/-- Entire actual backscan of the written flag blocks. It stops at the
real FALSE guard with ALL output bits in their original chronological
order on the right, and with the caller's unrelated archive untouched. -/
theorem back_flag_path (saved : Store) (values left suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (backFrame saved values left suffix)
      (cfg 5 saved (Tape.mk₂ left (false :: (PSTRTMIncrement009.blocks values.reverse ++ suffix)))),
      path.posts.length = values.length := by
  induction values generalizing suffix with
  | nil => exact ⟨ActualPath.refl _, rfl⟩
  | cons value values ih =>
    have edge := back_flag_edge saved value values left suffix
    obtain ⟨⟨posts, chain, last⟩, length⟩ := ih (value :: true :: suffix)
    have lengthBound : posts.length = values.length := length
    let later : ActualPath (TM1.step program)
        (backFrame saved values left (value :: true :: suffix))
        (cfg 5 saved (Tape.mk₂ left (false :: (PSTRTMIncrement009.blocks (value :: values).reverse ++ suffix)))) :=
      ⟨posts, chain, by
        simpa [PSTRTMIncrement009.blocks, List.reverse_cons, List.flatMap_append, List.append_assoc] using last⟩
    refine ⟨(ActualPath.single edge).trans later, ?_⟩
    simp only [ActualPath.trans, ActualPath.single, later, List.length_append, List.length_cons, List.length_nil]
    omega

/-- The guard is at anchor+2. Its actual67 LEFT moves reach oldrowW-1
at col0: TWO to the anchor and SIXTY-FIVE over the preceding physical row. -/
theorem guard_return_step (saved : Store) (front left suffix : List Bool) (width : front.length = 67) :
    TM1.step program (cfg 5 saved (Tape.mk₂ (front ++ left) (false :: suffix))) =
      some (cfg 6 saved (Tape.mk₂ left (front.reverse ++ false :: suffix))) := by
  have moved := Wide.moveCode_left front left (false :: suffix) saved
    (.goto (fun _ _ => 6) : Statement)
  rw [width] at moved
  change some (TM1.stepAux (Wide.moveCode .left 67 (.goto (fun _ _ => 6))) saved
    (Tape.mk₂ (front ++ left) (false :: suffix))) = _
  rw [moved]
  rfl

/-- The original formal contract compares ListBlank right0. The trailing
FALSE is actual blank data already produced by the checked decoder; its
quotient equality needs no extra footer or numeric canonicality premise.
No TRUE footer or unary header remains on the final right tape. -/
theorem decode_blocks_bare_right (saved : Store) (archive digits : List Bool) :
    ∃ final : TM1.Cfg Bool Label Store, ∃ path : ActualPath (TM1.step program)
      (cfg 11 saved (Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks digits ++ [false, false]))) final,
      final.l = none ∧ final.var = saved ∧ final.Tape.right₀ = ListBlank.mk digits ∧
      path.posts.length ≤ 64 * (digits.length + 1)^2 := by
  obtain ⟨⟨posts, chain, last⟩, bound⟩ := decode_blocks_path saved archive digits []
  let left := false :: (List.replicate digits.length true ++ false :: archive)
  have blank : Tape.mk₂ left (digits ++ [false]) = Tape.mk₂ left digits :=
    Wide.tape_right_blank left digits
  let final : TM1.Cfg Bool Label Store := ⟨none, saved, Tape.mk₂ left digits⟩
  refine ⟨final, ⟨posts, chain, ?_⟩, rfl, rfl, ?_, bound⟩
  · simpa only [final, ← blank] using last
  · exact Tape.mk'_right₀ (ListBlank.mk left) (ListBlank.mk digits)

end PDROC.BitVM.Common.IO.Output
