module

public import Paid.PDCompute_SolverSequenceMemory_051
public import Paid.PDCompute_SolverRangeCompare_035

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot)

theorem addNatSlot_header_memory (input : List Cell) (before after : State) (base slot value amount : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (inside : slot < headerWords)
    (hbase : before.register .fresh=.natural base) (hvalue : values slot=.natural value)
    (count : ℕ) (hcount : count ≤ 8)
    (hexec : linearExecute input ((addNatSlot slot amount).take count) before=some after) :
    HeaderMemory before after base := by
  have valueAt := (header.value slot inside).trans hvalue
  by_cases short : count < 8
  · have memory := addNatSlot_prefix_memory input before after base slot value amount hbase
      (header.live slot inside) valueAt count short hexec
    exact HeaderMemory.of_unchanged base memory.1 memory.2.1 memory.2.2
  · have exactCount : count=8 := by omega
    subst count
    have run : linearExecute input (addNatSlot slot amount) before=some after := hexec
    rw [addNatSlot_execute input before base slot value amount hbase (header.live slot inside) valueAt] at run
    have eq := Option.some.inj run
    subst after
    have fields := addNatSlotResult_fields before base slot value amount
    exact HeaderMemory.write header slot inside (.natural (value+amount)) fields.1 fields.2.1 fields.2.2.2.2

theorem rangeCompareCode_strict_prefix_memory (input : List Cell) (before after : State) (base index last : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hi : values 25=.natural index) (hlast : values 6=.natural last)
    (count : ℕ) (hcount : count < 7)
    (hexec : linearExecute input (rangeCompareCode.take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  have indexLive := header.live 25 (by decide)
  have lastLive := header.live 6 (by decide)
  have indexAt := (header.value 25 (by decide)).trans hi
  have lastAt := (header.value 6 (by decide)).trans hlast
  interval_cases count <;>
    simp [rangeCompareCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
      hbase,indexLive,lastLive,indexAt,lastAt] at hexec <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

theorem rangeCompareCode_memory (input : List Cell) (before after : State) (base index last : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hi : values 25=.natural index) (hlast : values 6=.natural last)
    (count : ℕ) (hcount : count ≤ 7)
    (hexec : linearExecute input (rangeCompareCode.take count) before=some after) :
    HeaderMemory before after base := by
  by_cases short : count < 7
  · have memory := rangeCompareCode_strict_prefix_memory input before after base index last values header hbase hi hlast count short hexec
    exact HeaderMemory.of_unchanged base memory.1 memory.2.1 memory.2.2
  · have exactCount : count=7 := by omega
    subst count
    have run : linearExecute input rangeCompareCode before=some after := hexec
    rw [rangeCompareCode_execute input before base values index last header hbase hi hlast] at run
    have eq := Option.some.inj run
    subst after
    have fields := rangeCompareResult_fields before base index last
    exact HeaderMemory.of_unchanged base fields.1 fields.2.1 fields.2.2.2.2.2

end PDCompute.Solver
