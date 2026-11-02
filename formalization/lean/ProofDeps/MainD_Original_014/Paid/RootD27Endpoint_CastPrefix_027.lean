module

public import Paid.RootD27Endpoint_Cast_007
public import Paid.PDCompute_SolverRegionSpace_124

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot storeSlot)

/-- Every actual prefix of the original cast writes only its existing
header cell. Arbitrarily live caller workspace is retained, not cleared. -/
theorem castRow_prefix_region (input : List Cell) (before after : State)
    (base m : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (row : values 8=.natural m)
    (count : ℕ) (bound : count≤7)
    (actual : linearExecute input (castRowCode.take count) before=some after) :
    RegionMemory before after (cellRegion base headerWords) := by
  have live := header.live 8 (by decide)
  have value := (header.value 8 (by decide)).trans row
  by_cases atEnd : count=7
  · have fullCode : castRowCode.take 7=castRowCode := by
      rw [←castRowCode_length,List.take_length]
    rw [atEnd,fullCode,castRow_execute input before base m fresh live value] at actual
    have same := Option.some.inj actual
    subst after
    have memory : HeaderMemory before (castRowResult before base m) base :=
      HeaderMemory.write header 18 (by decide) (.rational (m:ℚ))
        (castRow_heap before base m) (castRow_live before base m) (castRow_output before base m)
    exact memory.region _ (Finset.Subset.refl _)
  · have short : count<7 := by omega
    interval_cases count <;>
      simp [castRowCode,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,
        NatOp.eval,Cell.nat?,fresh,live,value,Nat.add_assoc] at actual <;>
      subst after
    all_goals
      have memory : HeaderMemory before _ base := ⟨fun _ _ => rfl,rfl,rfl⟩
      exact memory.region _ (Finset.Subset.refl _)

/-- Strengthened real cast trace, preserving the original functional
contract and adding every-prefix region memory on the SAME witness. -/
theorem castRow_actual_region (program : Program) (input : List Cell) (before : State)
    (base m : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (row : values 8=.natural m)
    (fetched : FetchesCode program before.pc castRowCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (castRowResult before base m) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤120 ∧
      Header (castRowResult before base m) base (Function.update values 18 (.rational (m:ℚ))) ∧
      (castRowResult before base m).register .fresh=.natural base ∧
      (castRowResult before base m).pc=before.pc+7 ∧
      ∀ state∈trace,RegionMemory before state (cellRegion base headerWords) := by
  have executed := castRow_execute input before base m fresh (header.live 8 (by decide))
    ((header.value 8 (by decide)).trans row)
  obtain ⟨trace,head,last,chain,cost,prefixes⟩ :=
    linearExecute_trace_time program input castRowCode castRow_straight before
      (castRowResult before base m) fetched executed
  refine ⟨trace,head,last,chain,cost,castRow_header before base m values header,
    (castRow_fresh before base m).trans fresh,castRow_pc before base m,?_⟩
  intro state member
  have split := List.dropLast_append_getLast? (castRowResult before base m) (by rw [last];simp)
  rw [←split] at member
  rcases List.mem_append.mp member with proper|terminal
  · obtain ⟨count,bound,actual⟩ := prefixes state proper
    apply castRow_prefix_region input before state base m values header fresh row count
    · simpa only [castRowCode_length] using bound.le
    · exact actual
  · have same : state=castRowResult before base m := List.mem_singleton.mp terminal
    subst state
    apply castRow_prefix_region input before _ base m values header fresh row 7 (by omega)
    simpa only [show castRowCode.take 7=castRowCode by rw [←castRowCode_length,List.take_length]] using executed

theorem cast_region_workingCells (before after : State) (base : ℕ)
    (memory : RegionMemory before after (cellRegion base headerWords)) :
    workingCells after≤workingCells before+48 := by
  have size : (cellRegion base headerWords).card≤headerWords := by
    unfold cellRegion
    exact Finset.card_image_le.trans (by simp)
  exact memory.workingCells_le.trans (Nat.add_le_add_left size _)

end RootD27.Endpoint
