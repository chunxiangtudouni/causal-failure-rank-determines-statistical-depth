module

public import Paid.RootD27Core_HeaderActual_042

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver RootD27.Bits

def coreHeaderCode (origin : ℕ) : List Instruction :=
  [.constant .fresh (.natural 13)]++solverPrologue++RootD27.Endpoint.paddingSetup++
    baseRowCode (origin+20)++[Instruction.constant .fresh (.natural 0)]

theorem coreHeaderCode_length (origin : ℕ) : (coreHeaderCode origin).length=39 := by
  have paddingLength : RootD27.Endpoint.paddingSetup.length=3:=rfl
  simp only [coreHeaderCode,List.length_append,List.length_singleton,solverPrologue_length,paddingLength,baseRowCode_length]

/-- The single actual literal39-opcode block supplies every fetch of
042, including the shared padding flag opcode. No header producer or
instruction-fetch oracle remains at this internal program boundary. -/
theorem core_header_initialize_code_actual (P : Parameters) (fee : ℚ) (input : List Cell)
    (program : Program) (before : State)
    (prepared : HeapList before 0 (preparedInput P fee))
    (fetched : FetchesCode program before.pc (coreHeaderCode before.pc)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤2520 ∧
      Header after 0 (fun slot=>after.heap slot) ∧ HeapList after 0 (preparedInput P fee) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+39 ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+48 ∧
      (∀ state∈trace,RegionMemory before state (cellRegion 13 48) ∧
        SafeBits state (coreHeaderBudget before) ∧ before.pc≤state.pc ∧ state.pc≤before.pc+39) := by
  change FetchesCode program before.pc
    ([.constant .fresh (.natural 13)]++solverPrologue++RootD27.Endpoint.paddingSetup++
      baseRowCode (before.pc+20)++[Instruction.constant .fresh (.natural 0)]) at fetched
  simp only [List.append_assoc] at fetched
  have paddingLength : RootD27.Endpoint.paddingSetup.length=3:=rfl
  have startFetch : program[before.pc]?=some (.constant .fresh (.natural 13)) := by
    simpa only [Nat.add_zero,List.getElem?_cons_zero] using fetched.append_left 0 (by decide)
  have prologueFetch : FetchesCode program (before.pc+1) solverPrologue := by
    simpa only [List.length_singleton] using fetched.append_right.append_left
  have restFetch : FetchesCode program (before.pc+17)
      (RootD27.Endpoint.paddingSetup++baseRowCode (before.pc+20)++[Instruction.constant .fresh (.natural 0)]) := by
    simpa only [List.append_assoc,List.length_singleton,solverPrologue_length,Nat.add_assoc] using fetched.append_right.append_right
  have leadFetch : FetchesCode program (before.pc+17) RootD27.Endpoint.paddingLeadCode := by
    intro offset inside
    have bound : offset<4:=inside
    have actualBound : offset<(RootD27.Endpoint.paddingSetup++baseRowCode (before.pc+20)++
        [Instruction.constant .fresh (.natural 0)]).length := by
      simp only [List.length_append,paddingLength,baseRowCode_length,List.length_singleton]
      omega
    have same : (RootD27.Endpoint.paddingSetup++baseRowCode (before.pc+20)++
        [Instruction.constant .fresh (.natural 0)])[offset]?=RootD27.Endpoint.paddingLeadCode[offset]? := by
      interval_cases offset <;> rfl
    exact (restFetch offset actualBound).trans same
  have loopFetch : FetchesCode program (before.pc+20) (baseRowCode (before.pc+20)) := by
    simpa only [List.length_singleton,solverPrologue_length,paddingLength,Nat.add_assoc] using
      fetched.append_right.append_right.append_right.append_left
  have endCode : FetchesCode program (before.pc+38) [Instruction.constant .fresh (.natural 0)] := by
    simpa only [List.length_singleton,solverPrologue_length,paddingLength,baseRowCode_length,Nat.add_assoc] using
      fetched.append_right.append_right.append_right.append_right
  have endFetch : program[before.pc+38]?=some (.constant .fresh (.natural 0)) := by
    simpa only [Nat.add_zero,List.getElem?_cons_zero] using endCode 0 (by decide)
  exact core_header_initialize_actual P fee input program before prepared startFetch prologueFetch leadFetch loopFetch endFetch

end RootD27.Core
