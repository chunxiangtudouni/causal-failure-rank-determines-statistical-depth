module

public import Paid.PDROC_CalibrationRow_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- The two original letter stores share this literal seven-op body.
It reads the previous partial scatter cell before adding this letter,
so duplicate absorbed targets retain both sequential additions. -/
def scatterStoreCode : List Instruction :=
  loadSlot 10 .old ++ [.natOp .add .address .old .index,.load .old .address,
    .ratOp .add .value .old .value,.store .address .value]

def scatterStoreResult (before : State) (base rowBase target : ℕ) (previous amount : ℚ) : State :=
  let loaded := loadSlotResult before base 10 .old
  let addressed := ({loaded with pc:=loaded.pc+1}).set .address (.natural (rowBase+target))
  let fetched := ({addressed with pc:=addressed.pc+1}).set .old (.rational previous)
  let added := ({fetched with pc:=fetched.pc+1}).set .value (.rational (previous+amount))
  writeCell added (rowBase+target) (.rational (previous+amount))

theorem scatterStore_execute (input : List Cell) (before : State)
    (base rowBase target : ℕ) (previous amount : ℚ)
    (fresh : before.register .fresh=.natural base)
    (pointerLive : base+10 ∈ before.live) (pointer : before.heap (base+10)=.natural rowBase)
    (index : before.register .index=.natural target) (value : before.register .value=.rational amount)
    (cellLive : rowBase+target ∈ before.live) (cell : before.heap (rowBase+target)=.rational previous) :
    linearExecute input scatterStoreCode before=some (scatterStoreResult before base rowBase target previous amount) := by
  simp [scatterStoreCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,RatOp.eval,
    Cell.nat?,Cell.rat?,fresh,pointerLive,pointer,index,value,cellLive,cell,
    scatterStoreResult,loadSlotResult,writeCell,Nat.add_assoc]

theorem scatterStore_fields (before : State) (base rowBase target : ℕ) (previous amount : ℚ) :
    (scatterStoreResult before base rowBase target previous amount).heap=
      Function.update before.heap (rowBase+target) (.rational (previous+amount)) ∧
    (scatterStoreResult before base rowBase target previous amount).live=insert (rowBase+target) before.live ∧
    (scatterStoreResult before base rowBase target previous amount).register .fresh=before.register .fresh ∧
    (scatterStoreResult before base rowBase target previous amount).register .index=before.register .index ∧
    (scatterStoreResult before base rowBase target previous amount).register .value=.rational (previous+amount) ∧
    (scatterStoreResult before base rowBase target previous amount).pc=before.pc+7 ∧
    (scatterStoreResult before base rowBase target previous amount).output=before.output := by
  simp [scatterStoreResult,loadSlotResult,State.set,writeCell,Nat.add_assoc]

def scatterStorePrefixCode : List Instruction :=
  loadSlot 10 .old ++ [.natOp .add .address .old .index,.load .old .address,.ratOp .add .value .old .value]

theorem scatterStore_decompose : scatterStoreCode=scatterStorePrefixCode++[.store .address .value] := rfl
theorem leftStore_body : (basicBlock Label.leftStore).body=scatterStoreCode := rfl
theorem rightStore_body : (basicBlock Label.rightStore).body=scatterStoreCode := rfl

theorem scatterStore_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State)
    (base rowBase target : ℕ) (previous amount : ℚ)
    (fresh : before.register .fresh=.natural base)
    (pointerLive : base+10 ∈ before.live) (pointer : before.heap (base+10)=.natural rowBase)
    (index : before.register .index=.natural target) (value : before.register .value=.rational amount)
    (cellLive : rowBase+target ∈ before.live) (cell : before.heap (rowBase+target)=.rational previous)
    (inside : rowBase+target ∈ region) : LinearFrames region input scatterStoreCode before := by
  rw [scatterStore_decompose]
  apply single_last_frames region input scatterStorePrefixCode (.store .address .value)
    before (scatterStoreResult before base rowBase target previous amount)
  · intro instruction member state
    simp only [scatterStorePrefixCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (h|h|h)|(h|h|h) <;> subst instruction <;> trivial
  · rw [←scatterStore_decompose]
    exact scatterStore_execute input before base rowBase target previous amount fresh pointerLive pointer index value cellLive cell
  · have fields := scatterStore_fields before base rowBase target previous amount
    exact frame_of_one_update region before _ (rowBase+target) (.rational (previous+amount)) inside fields.1 fields.2.1

/-- Exact sequential array bump at this actual letter-store boundary. -/
theorem scatterStore_bump (before : State) (base rowBase target : ℕ) (row : Array ℚ) (amount : ℚ)
    (represented : RowAt before rowBase row) (inside : target < row.size) :
    RowAt (scatterStoreResult before base rowBase target (row.getD target 0) amount) rowBase
      (PDROC.endpointArrayBump row target amount) := by
  have bumped := RowAt.bump before rowBase row represented target inside amount
  have fields := scatterStore_fields before base rowBase target (row.getD target 0) amount
  constructor
  · intro i bound
    simpa only [fields.2.1,writeCell] using bumped.live i bound
  · intro i bound
    simpa only [fields.1,writeCell] using bumped.value i bound

end PDROC.CalibrationRow
