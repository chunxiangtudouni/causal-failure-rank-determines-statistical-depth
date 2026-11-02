module

public import Paid.PDCompute_SolverPaddingPair_131

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute writeCell)

def paddingPairsCode : ℕ → List Instruction
  | 0 => []
  | copies+1 => paddingPairCode++paddingPairsCode copies

theorem paddingPairsCode_length (copies : ℕ) : (paddingPairsCode copies).length=2*copies := by
  induction copies with
  | zero => rfl
  | succ copies ih => rw [paddingPairsCode,List.length_append,ih]; change 2+2*copies=2*(copies+1); ring

/-- Repeating the literal store/increment pair does not spend extra
bit budget. It writes only the genuine Header portion of the pointer
interval, with arbitrary preexisting live data permitted. -/
theorem paddingPairs_prefix_resources (copies : ℕ) (input : List Cell) (before after : State)
    (base pointer budget count : ℕ) (safe : RootD27.Bits.SafeBits before budget)
    (address : before.register .address=.natural pointer) (one : before.register .flag=.natural 1)
    (lower : base ≤ pointer) (room : pointer+copies ≤ base+headerWords)
    (addressBits : 1+natBits (base+headerWords) ≤ budget) (pcBits : natBits (before.pc+2*copies) ≤ budget)
    (countBound : count ≤ 2*copies)
    (executed : linearExecute input ((paddingPairsCode copies).take count) before=some after) :
    RegionMemory before after (cellRegion base headerWords) ∧ RootD27.Bits.SafeBits after budget := by
  induction copies generalizing before pointer count with
  | zero =>
    have same : before=after := by simpa only [paddingPairsCode,List.take_nil,linearExecute,Option.some.injEq] using executed
    subst after
    exact ⟨RegionMemory.refl before _,safe⟩
  | succ copies ih =>
    have firstRoom : pointer+1 ≤ base+headerWords := by omega
    have firstPC : natBits (before.pc+2) ≤ budget :=
      (natBits_mono (by omega : before.pc+2 ≤ before.pc+2*(copies+1))).trans pcBits
    by_cases short : count ≤ 2
    · have takeEq : (paddingPairsCode (copies+1)).take count=paddingPairCode.take count := List.take_append_of_le_length short
      rw [takeEq] at executed
      exact paddingPair_prefix_resources input before after base pointer budget count safe address one lower firstRoom addressBits firstPC short executed
    · let middle:=paddingPairResult before pointer
      have firstRun:=paddingPair_execute input before pointer address one
      have firstResources:=paddingPair_prefix_resources input before middle base pointer budget 2 safe address one lower firstRoom
        addressBits firstPC (le_refl _) firstRun
      have nextAddress : middle.register .address=.natural (pointer+1) := by simp [middle,paddingPairResult,State.set]
      have different : (.flag : Register) ≠ .address := by decide
      have nextOne : middle.register .flag=.natural 1 := by
        simpa only [middle,paddingPairResult,State.set,writeCell,Function.update_of_ne different] using one
      have nextPC : middle.pc=before.pc+2 := rfl
      have split : (paddingPairsCode (copies+1)).take count=paddingPairCode++(paddingPairsCode copies).take (count-2) := by
        change (paddingPairCode++paddingPairsCode copies).take count=_
        rw [List.take_append,List.take_of_length_le (by change 2 ≤ count; omega)]
        rfl
      rw [split,PDLower.CalibrationCompute.linearExecute_append,firstRun,Option.bind_some] at executed
      have tailPC : natBits (middle.pc+2*copies) ≤ budget := by
        have equality : middle.pc+2*copies=before.pc+2*(copies+1) := by rw [nextPC]; ring
        rw [equality]
        exact pcBits
      have tail:=ih middle (pointer+1) (count-2) firstResources.2 nextAddress nextOne (by omega) (by omega)
        tailPC (by omega) executed
      exact ⟨firstResources.1.trans tail.1,tail.2⟩

end PDCompute.Solver
