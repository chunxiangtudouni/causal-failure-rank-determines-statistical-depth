module
public import Paid.PDCompute_Pack_SmallBits_060
public import Paid.PDCompute_Pack_CounterInit_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot)

def incrementComputed (before : State) (base slot value amount : ℕ) : State:=
  let loaded:=loadSlotResult before base slot .index
  ({constantNatFirst loaded .flag amount with pc:=loaded.pc+2}).set .index (.natural (value+amount))

/-- Genuine eight-op counter arithmetic. The result bound is a local
numeric fact; original n+1/k+1 are discharged by054, not new paper inputs. -/
theorem increment_prefix_safe (input : List Cell) (before after : State) (base slot value amount budget count : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (inside : slot<headerWords)
    (hbase : before.register .fresh=.natural base) (hvalue : values slot=.natural value)
    (safe : SafeBits before budget) (addressBits : 1+natBits (base+slot) ≤ budget)
    (literalBits : 1+natBits amount ≤ budget) (resultBits : 1+natBits (value+amount) ≤ budget)
    (pcBits : natBits (before.pc+8) ≤ budget) (bound : count ≤ 8)
    (execute : linearExecute input ((addNatSlot slot amount).take count) before=some after) : SafeBits after budget := by
  let loaded:=loadSlotResult before base slot .index
  let computed:=incrementComputed before base slot value amount
  let pair:=constantNatPair .flag amount .add .index .index .flag
  have loadPC : natBits (before.pc+3) ≤ budget:=(natBits_mono (by omega : before.pc+3 ≤ before.pc+8)).trans pcBits
  have loadedSafe : SafeBits loaded budget:=loadSlotResult_safe before base slot budget .index safe (header.live slot inside) addressBits loadPC
  have loadedIndex : loaded.register .index=.natural value:=(header.loadSlot_execute input slot .index inside hbase).2.trans hvalue
  have pairPC : natBits (loaded.pc+2) ≤ budget := by
    change natBits (before.pc+3+2) ≤ budget
    exact (natBits_mono (by omega : before.pc+3+2 ≤ before.pc+8)).trans pcBits
  have firstValue : (constantNatFirst loaded .flag amount).register .index=.natural value:=by simp [constantNatFirst,State.set,loadedIndex]
  have secondValue : (constantNatFirst loaded .flag amount).register .flag=.natural amount:=by simp [constantNatFirst,State.set]
  have pairRun : linearExecute input pair loaded=some computed := by
    simp [pair,constantNatPair,computed,incrementComputed,constantNatFirst,linearExecute,Instruction.execute,
      State.set,NatOp.eval,Cell.nat?,loadedIndex,Nat.add_assoc]
    simp [loaded]
  have computedSafe : SafeBits computed budget:=constantNatPair_prefix_safe input loaded computed .flag amount .add .index .index .flag
    value amount (value+amount) budget 2 loadedSafe literalBits firstValue secondValue rfl resultBits pairPC (le_refl _) pairRun
  have computedBase : computed.register .fresh=.natural base:=by
    simp [computed,incrementComputed,constantNatFirst,State.set,loadSlotResult,hbase]
  have storePC : natBits (computed.pc+3) ≤ budget:=by
    change natBits (before.pc+3+2+3) ≤ budget
    simpa only [Nat.add_assoc] using pcBits
  have firstRun:=(header.loadSlot_execute input slot .index inside hbase).1
  have firstPrefixes : ∀ take ≤ (loadSlot slot .index).length,∀ state,
      linearExecute input ((loadSlot slot .index).take take) before=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact loadSlot_prefix_safe input before state base slot budget take .index safe hbase (header.live slot inside) addressBits loadPC takeBound run
  have pairPrefixes : ∀ take ≤ pair.length,∀ state,linearExecute input (pair.take take) loaded=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact constantNatPair_prefix_safe input loaded state .flag amount .add .index .index .flag value amount (value+amount) budget take
      loadedSafe literalBits firstValue secondValue rfl resultBits pairPC takeBound run
  have storePrefixes : ∀ take ≤ (storeSlot slot .index).length,∀ state,
      linearExecute input ((storeSlot slot .index).take take) computed=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact storeSlot_prefix_safe input computed state base slot budget take .index computedSafe computedBase (by decide) addressBits storePC takeBound run
  have tail:=invariant_prefix_append input pair (storeSlot slot .index) loaded computed pairRun (fun state=>SafeBits state budget) pairPrefixes storePrefixes
  have combined:=invariant_prefix_append input (loadSlot slot .index) (pair++storeSlot slot .index) before loaded firstRun
    (fun state=>SafeBits state budget) firstPrefixes tail
  have allPrefixes : ∀ take ≤ (addNatSlot slot amount).length,∀ state,
      linearExecute input ((addNatSlot slot amount).take take) before=some state → SafeBits state budget:=by
    simpa only [addNatSlot,pair,constantNatPair,List.append_assoc] using combined
  exact allPrefixes count bound after execute

end PDCompute.Pack
