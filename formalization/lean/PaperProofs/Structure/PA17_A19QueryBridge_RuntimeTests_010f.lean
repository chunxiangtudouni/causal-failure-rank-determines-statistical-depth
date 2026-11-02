module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010b
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeRead_007d

/-! Literal fetched prefixes of the fixed355-op tests kernel, including the
real back jumps. The containing program is never restarted or halted. This
module certifies phase fetches; semantic loop invariants are separate. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments

structure Embedded (bits origin : Nat) (containing : List PackingOp) : Prop where
  bound : origin + (programAt origin).length ≤ containing.length
  code : ∀ i (hi : i < (programAt origin).length),
    containing[origin + i]'(by omega) = (programAt origin)[i]
  words : WordsFit bits (packingCode containing)
  pcfit : Fits bits (5 * containing.length)

theorem middle_get (before block after : List PackingOp) (index : Nat) (hi : index < block.length) :
    (before ++ block ++ after)[before.length + index]'(by simp only [List.length_append]; omega) = block[index] := by
  rw [List.getElem_append_left (by simp only [List.length_append]; omega), List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem phase_code {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (before block after : List PackingOp) (heq : programAt origin = before ++ block ++ after) :
    ∀ i (hi : i < block.length), containing[(origin + before.length) + i]'(by
      have hl := congrArg List.length heq
      have hb := em.bound
      simp only [List.length_append] at hl
      omega) = block[i] := by
  intro i hi
  have hl := congrArg List.length heq
  simp only [List.length_append] at hl
  have hc := em.code (before.length + i) (by omega)
  have hm : (programAt origin)[before.length + i]'(by omega) = block[i] := by
    simpa only [heq] using middle_get before block after i hi
  simpa only [Nat.add_assoc] using hc.trans hm

theorem actual_straight_phase_prefix {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM)
    (before block after : List PackingOp) (heq : programAt origin = before ++ block ++ after)
    (hs : StraightProgram block) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + before.length))) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ block.length) :
    packingRun rom containing count state = executeOps rom (block.take count) state := by
  have hl : (block.take count).length = count := List.length_take_of_le hc
  conv_lhs => rw [← hl]
  apply straight_segment rom containing (block.take count) (origin + before.length) ?_ ?_ ?_
    em.words em.pcfit state hp ha
  · have hb := em.bound
    have he := congrArg List.length heq
    simp only [List.length_append] at he
    omega
  · intro i hi
    have hi' : i < block.length := by rw [hl] at hi; omega
    simpa only [List.getElem_take] using phase_code em before block after heq i hi'
  · intro op ho
    exact hs op (List.mem_of_mem_take ho)

theorem actual_branch_phase_prefix {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM)
    (before lead after : List PackingOp) (last : PackingOp)
    (heq : programAt origin = before ++ (lead ++ [last]) ++ after)
    (hs : StraightProgram lead) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + before.length))) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ lead.length + 1) :
    packingRun rom containing count state = executeOps rom ((lead ++ [last]).take count) state := by
  have hcode := phase_code em before (lead ++ [last]) after heq
  apply segment_prefix rom containing lead last (origin + before.length) ?_ ?_ ?_ hs em.words em.pcfit state hp ha count hc
  · have hb := em.bound
    have he := congrArg List.length heq
    simp only [List.length_append, List.length_singleton] at he
    omega
  · intro i hi
    have hh := hcode i (by simp only [List.length_append, List.length_singleton]; omega)
    simpa only [List.getElem_append_left hi] using hh
  · have hh := hcode lead.length (by simp only [List.length_append, List.length_singleton]; omega)
    simpa only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero] using hh

def beforeNode (origin : Nat) : List PackingOp :=
  setup ++ counterTest 8 (5 * (origin + 355)) ++ budgetInit ++ counterTest 9 (5 * (origin + 196))
def afterNode (origin : Nat) : List PackingOp :=
  acceptFinish ++ counterTest 12 (5 * (origin + 339)) ++ ancestorBody origin ++ budgetFooter origin
def beforeAncestor (origin : Nat) : List PackingOp :=
  beforeNode origin ++ nodeBody origin ++ acceptFinish ++ counterTest 12 (5 * (origin + 339))
def beforeFooter (origin : Nat) : List PackingOp := beforeAncestor origin ++ ancestorBody origin

theorem beforeNode_length (origin : Nat) : (beforeNode origin).length = 103 := by
  simp only [beforeNode, List.length_append, setup_length, counterTest_length, budgetInit_length]
theorem beforeAncestor_length (origin : Nat) : (beforeAncestor origin).length = 227 := by
  simp only [beforeAncestor, List.length_append, beforeNode_length, nodeBody_length,
    acceptFinish_length, counterTest_length]
theorem beforeFooter_length (origin : Nat) : (beforeFooter origin).length = 339 := by
  simp only [beforeFooter, List.length_append, beforeAncestor_length, ancestorBody_length]

theorem node_partition (origin : Nat) :
    programAt origin = beforeNode origin ++ nodeBody origin ++ afterNode origin := by
  simp only [programAt, beforeNode, afterNode, budgetInit, nodeBody, nodeBodyLead,
    ancestorBody, ancestorBodyLead, budgetFooter, budgetFooterLead, back, List.append_assoc]

theorem ancestor_partition (origin : Nat) :
    programAt origin = beforeAncestor origin ++ ancestorBody origin ++ budgetFooter origin := by
  simp only [programAt, beforeAncestor, beforeNode, budgetInit, nodeBody, nodeBodyLead,
    ancestorBody, ancestorBodyLead, budgetFooter, budgetFooterLead, back, List.append_assoc]

theorem footer_partition (origin : Nat) :
    programAt origin = beforeFooter origin ++ budgetFooter origin ++ [] := by
  simp only [beforeFooter, ancestor_partition origin, List.append_nil, List.append_assoc]

theorem actual_node_prefix {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 103))) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 93) :
    packingRun rom containing count state = executeOps rom ((nodeBody origin).take count) state := by
  exact actual_branch_phase_prefix em rom (beforeNode origin) (nodeBodyLead origin) (afterNode origin)
    (.jumpIfZero .fresh .old) (node_partition origin) (nodeBodyLead_straight origin) state
    (by simpa only [beforeNode_length] using hp) ha count
    (by simpa only [nodeBodyLead_length] using hc)

theorem actual_ancestor_prefix {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 227))) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 112) :
    packingRun rom containing count state = executeOps rom ((ancestorBody origin).take count) state := by
  exact actual_branch_phase_prefix em rom (beforeAncestor origin) (ancestorBodyLead origin) (budgetFooter origin)
    (.jumpIfZero .fresh .old) (ancestor_partition origin) (ancestorBodyLead_straight origin) state
    (by simpa only [beforeAncestor_length] using hp) ha count
    (by simpa only [ancestorBodyLead_length] using hc)

theorem actual_footer_prefix {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 339))) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 16) :
    packingRun rom containing count state = executeOps rom ((budgetFooter origin).take count) state := by
  exact actual_branch_phase_prefix em rom (beforeFooter origin) (budgetFooterLead origin) []
    (.jumpIfZero .fresh .old) (footer_partition origin) (budgetFooterLead_straight origin) state
    (by simpa only [beforeFooter_length] using hp) ha count
    (by simpa only [budgetFooterLead_length] using hc)

theorem cached_phase {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (before after : List PackingOp)
    (heq : programAt origin = before ++ PA17A19RuntimeRead007.cachedProgram ++ after) :
    PA17A19RuntimeRead007.CachedEmbedded bits (origin + before.length) containing := by
  refine ⟨?_, phase_code em before _ after heq, em.words, em.pcfit⟩
  have hb := em.bound
  have hl := congrArg List.length heq
  simp only [List.length_append] at hl
  omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
