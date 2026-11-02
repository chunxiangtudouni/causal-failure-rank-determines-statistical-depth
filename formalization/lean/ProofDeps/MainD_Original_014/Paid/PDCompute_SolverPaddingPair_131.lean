module

public import Paid.PDCompute_SolverInitialStore_125

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute writeCell)

theorem writeCell_region (before : State) (pointer : ℕ) (value : Cell) (region : Finset ℕ) (inside : pointer ∈ region) :
    RegionMemory before (writeCell before pointer value) region := by
  refine ⟨?_,?_,Finset.subset_insert _ _,rfl⟩
  · intro address outside
    have different : address ≠ pointer := by intro same; exact outside (same.symm ▸ inside)
    exact Function.update_of_ne different _ _
  · intro address member
    rcases Finset.mem_insert.mp member with same|old
    · exact Finset.mem_union_right _ (same.symm ▸ inside)
    · exact Finset.mem_union_left _ old

def paddingPairCode : List Instruction := [.store .address .value,.natOp .add .address .address .flag]

def paddingPairResult (before : State) (pointer : ℕ) : State :=
  ({writeCell before pointer (before.register .value) with pc:=before.pc+2}).set .address (.natural (pointer+1))

theorem paddingPair_execute (input : List Cell) (before : State) (pointer : ℕ)
    (address : before.register .address=.natural pointer) (one : before.register .flag=.natural 1) :
    linearExecute input paddingPairCode before=some (paddingPairResult before pointer) := by
  simp [paddingPairCode,paddingPairResult,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,address,one,writeCell,Nat.add_assoc]

theorem paddingPair_prefix_resources (input : List Cell) (before after : State) (base pointer budget count : ℕ)
    (safe : RootD27.Bits.SafeBits before budget)
    (address : before.register .address=.natural pointer) (one : before.register .flag=.natural 1)
    (lower : base ≤ pointer) (room : pointer+1 ≤ base+headerWords)
    (addressBits : 1+natBits (base+headerWords) ≤ budget) (pcBits : natBits (before.pc+2) ≤ budget)
    (countBound : count ≤ 2) (executed : linearExecute input (paddingPairCode.take count) before=some after) :
    RegionMemory before after (cellRegion base headerWords) ∧ RootD27.Bits.SafeBits after budget := by
  have inside : pointer ∈ cellRegion base headerWords := (mem_cellRegion_iff _ _ _).mpr ⟨lower,by omega⟩
  have pointerBits : natBits pointer ≤ budget := by
    have mono:=natBits_mono (by omega : pointer ≤ base+headerWords)
    omega
  have nextBits : (.natural (pointer+1) : Cell).bits ≤ budget := by
    have mono:=natBits_mono room
    change 1+natBits (pointer+1) ≤ budget
    omega
  have storedSafe:=safe.store pointer (before.register .value) pointerBits (safe.register .value)
  interval_cases count
  · have same : before=after := by simpa only [List.take_zero,linearExecute,Option.some.injEq] using executed
    subst after
    exact ⟨RegionMemory.refl before _,safe⟩
  · have direct : Instruction.execute input (.store .address .value) before=
        some (writeCell before pointer (before.register .value)) := by
      simp [Instruction.execute,Cell.nat?,address,writeCell]
    have same : writeCell before pointer (before.register .value)=after := by
      simpa only [paddingPairCode,List.take_succ_cons,List.take_zero,linearExecute,direct,Option.bind_some,Option.some.injEq] using executed
    subst after
    have counted:=storedSafe.withPC (before.pc+1) ((natBits_mono (by omega : before.pc+1 ≤ before.pc+2)).trans pcBits)
    exact ⟨writeCell_region before pointer (before.register .value) _ inside,by simpa only [writeCell] using counted⟩
  · change linearExecute input paddingPairCode before=some after at executed
    rw [paddingPair_execute input before pointer address one] at executed
    have same:=Option.some.inj executed
    subst after
    have counted:=(storedSafe.withPC (before.pc+2) pcBits).set .address (.natural (pointer+1)) nextBits
    exact ⟨writeCell_region before pointer (before.register .value) _ inside,
      by simpa only [paddingPairResult,writeCell,State.set] using counted⟩

end PDCompute.Solver
