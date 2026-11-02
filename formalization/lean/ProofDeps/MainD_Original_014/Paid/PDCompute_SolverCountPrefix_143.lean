module

public import Paid.PDCompute_SolverPrefixResources_134
public import Paid.PDCompute_SolverEndpointCount_059

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute)

def endpointCountMiddleCode (mode : ReaderMode) : List Instruction :=
  [mode.read .index .address,.constant .value (.natural 1),.natOp .subtract .index .index .value]

/-- The actual original endpoint-length read, constant and subtraction.
The original ROM/heap source supplies M+1; no answer/run oracle occurs. -/
theorem endpointCountMiddle_prefix_resources (mode : ReaderMode) (input : List Cell) (P : Parameters)
    (before : State) (source budget : ℕ) (hsource : EndpointSource mode input P source before)
    (address : before.register .address=.natural source) (safe : RootD27.Bits.SafeBits before budget)
    (lengthBits : 1+natBits (P.certificate.M+1) ≤ budget) (pcBits : natBits (before.pc+3) ≤ budget)
    (region : Finset ℕ) : CodePrefixResources input (endpointCountMiddleCode mode) before region budget := by
  let read : State:=({before with pc:=before.pc+1}).set .index (.natural (P.certificate.M+1))
  let marked : State:=({read with pc:=read.pc+1}).set .value (.natural 1)
  let final : State:=({marked with pc:=marked.pc+1}).set .index (.natural P.certificate.M)
  have readRun : Instruction.execute input (mode.read .index .address) before=some read :=
    readEndpointCount_execute mode input P source before .index hsource address
  have readPC : natBits (before.pc+1) ≤ budget := (natBits_mono (by omega : before.pc+1 ≤ before.pc+3)).trans pcBits
  have readSafe : RootD27.Bits.SafeBits read budget :=
    (safe.withPC (before.pc+1) readPC).set .index (.natural (P.certificate.M+1)) lengthBits
  have oneBits : (.natural 1 : Cell).bits ≤ budget := by
    have mono:=natBits_mono (by omega : 1 ≤ P.certificate.M+1)
    change 1+natBits 1 ≤ budget
    omega
  have markedPC : natBits (read.pc+1) ≤ budget :=
    (natBits_mono (by change before.pc+1+1 ≤ before.pc+3; omega)).trans pcBits
  have markedSafe : RootD27.Bits.SafeBits marked budget :=
    (readSafe.withPC (read.pc+1) markedPC).set .value (.natural 1) oneBits
  have finalBits : (.natural P.certificate.M : Cell).bits ≤ budget := by
    have mono:=natBits_mono (by omega : P.certificate.M ≤ P.certificate.M+1)
    change 1+natBits P.certificate.M ≤ budget
    omega
  have finalPC : natBits (marked.pc+1) ≤ budget := by simpa only [marked,read,State.set,Nat.add_assoc] using pcBits
  have finalSafe : RootD27.Bits.SafeBits final budget :=
    (markedSafe.withPC (marked.pc+1) finalPC).set .index (.natural P.certificate.M) finalBits
  have firstRun : linearExecute input ((endpointCountMiddleCode mode).take 1) before=some read := by
    simp only [endpointCountMiddleCode,List.take_succ_cons,List.take_zero,linearExecute,readRun,Option.bind_some]
  have secondRun : linearExecute input ((endpointCountMiddleCode mode).take 2) before=some marked := by
    change linearExecute input [mode.read .index .address,.constant .value (.natural 1)] before=some marked
    rw [linearExecute,readRun,Option.bind_some]
    rfl
  have thirdRun : linearExecute input ((endpointCountMiddleCode mode).take 3) before=some final := by
    change linearExecute input (endpointCountMiddleCode mode) before=some final
    rw [endpointCountMiddleCode,linearExecute,readRun,Option.bind_some]
    simp [linearExecute,final,marked,read,Instruction.execute,State.set,NatOp.eval,Cell.nat?]
  intro count bound after executed
  change count ≤ 3 at bound
  interval_cases count
  · have same : before=after := by simpa only [List.take_zero,linearExecute,Option.some.injEq] using executed
    subst after
    exact ⟨RegionMemory.refl before _,safe⟩
  · rw [firstRun] at executed
    have same:=Option.some.inj executed
    subst after
    exact ⟨RegionMemory.of_unchanged _ rfl rfl rfl,readSafe⟩
  · rw [secondRun] at executed
    have same:=Option.some.inj executed
    subst after
    exact ⟨RegionMemory.of_unchanged _ rfl rfl rfl,markedSafe⟩
  · rw [thirdRun] at executed
    have same:=Option.some.inj executed
    subst after
    exact ⟨RegionMemory.of_unchanged _ rfl rfl rfl,finalSafe⟩

end PDCompute.Solver
