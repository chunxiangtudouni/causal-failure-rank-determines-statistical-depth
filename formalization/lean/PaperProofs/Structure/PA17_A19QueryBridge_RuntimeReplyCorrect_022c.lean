module
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeReplyCorrect_022a
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeReplyCorrect_022b

/-! ORIGINAL ReplyCorrect for the actual32-op Word footer. Stored ranks and
the enabled canonical tool are same-call intermediate data,not caller answers. -/
@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2400000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeReplyCorrect022
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem actual_query_reply_correct {bits q origin : Nat} {containing : List PackingOp}
    (em : PA17A19RuntimeReply016.Embedded bits origin containing) (rom : PhysicalROM)
    (cache : IndexedNodeCache (Fin q)) (leaves : Vector (Option (Fin q)) cache.nodes.size)
    (counts : IndexedCapacity cache) (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId)
    (capWords workspace size : Nat) (state : WordState bits)
    (hroom : Fits bits (PSTRQueryLayout.endpoint workspace size q))
    (hq : (rom.words .input).getD 1 0 = q) (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    let g := PA17QueryRanks011.firstFalseValue q (fun budget => IndexedQuery.accepts cache counts (IndexedQuery.entryAt row budget))
    let b := PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node)
    let active := (state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 2))).toNat
    let enabled := if active = 0 then 0 else if b = 0 then 0 else 1
    let tool := IndexedQuery.selectEntry cache leaves counts node (IndexedQuery.entryAt row (b - 1))
    state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 4)) = BitVec.ofNat bits g →
    state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 5)) = BitVec.ofNat bits b →
    state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 7)) = BitVec.ofNat bits enabled →
    (enabled ≠ 0 → state.heap (BitVec.ofNat bits (PSTRQueryLayout.childBase workspace size q + size + 2)) =
      BitVec.ofNat bits (PA17QueryReply017.encodeTool tool)) →
    FooterRegisters rom containing workspace size q g b (PA17QueryReply017.encodeTool tool) active origin state
      (packingRun rom containing 32 state) ∧
    ReplyCorrect q (if active = 0 then IndexedQuery.terminalReply q else IndexedQuery.query cache leaves counts row node)
      (replyState q capWords (packingRun rom containing 32 state)) := by
  dsimp only
  intro hgood hbad hflag htool
  have result := actual_footer_registers em rom workspace size q _ _ _ state hroom hq hsize hh hgood hbad
    (PA17QueryRanks011.firstFalseValue_le q _) (PA17QueryRanks011.firstFalseValue_le q _)
    (encodeTool_le _) hflag htool hp ha
  refine ⟨result, ?_⟩
  exact registers_reply_correct cache leaves counts row node _
    (replyState q capWords (packingRun rom containing 32 state)) result.old result.fresh result.value result.index

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeReplyCorrect022
