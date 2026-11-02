module

public import Structure.PSTR_BuildLower_SourceRep_048

/-! Actual dynamic-constant instructions refine the original source step.
Expr operands are read from the real dimensions and lexical counter words;
the source finite heap view is preserved at every actual fetched clock. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PA17UniformGenerator035b
variable {bits : Nat}

theorem dynamic (q C0 C indexBase I base : Nat) (source physical : PhysicalROM)
    (target : Register) (expr : Expr) (environment : Nat → Nat)
    (logical : State) (state : WordState bits)
    (hrep : Represents q C0 C indexBase I base logical state)
    (hc : expressionCellLimit expr ≤ 22) (hd : expressionInputLimit expr ≤ 3)
    (hcell : ∀ address < expressionCellLimit expr,
      state.heap (state.register .address + BitVec.ofNat bits (64 + address)) = BitVec.ofNat bits (environment address))
    (hdim : ∀ address < expressionInputLimit expr,
      state.heap (state.register .address + BitVec.ofNat bits address) =
        BitVec.ofNat bits ((source.words .input).getD (BitVec.ofNat bits address).toNat 0))
    (hvalues : ExprBounds.nodesFit bits source environment expr)
    (hend : Fits bits (base + max 39 (128 + expr.size)))
    (hC : C0 ≤ C) (hpacked : 4 + packedCapacityWords q C bits ≤ indexBase)
    (hdisjoint : indexBase + I ≤ base + 32)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ DynamicStep.code target expr ++ right)))
    (hpcfit : Fits bits (5 * (left ++ DynamicStep.code target expr ++ right).length)) :
    let block := DynamicStep.code target expr
    let after := packingRun physical (left ++ block ++ right) block.length state
    Represents q C0 C indexBase I base
      ((Op.base (.constant target (expr.eval source environment))).execute source.semantic logical) after ∧
      after.pc = BitVec.ofNat bits (5 * (left.length + block.length)) ∧ after.halted = false := by
  dsimp only
  have ht : 128 + expr.size ≤ 2 ^ bits := by
    have hh := Nat.le_max_right 39 (128 + expr.size)
    change base + max 39 (128 + expr.size) < 2 ^ bits at hend
    omega
  have hb : 0 < bits := by
    by_contra hn
    have hz : bits = 0 := by omega
    simp only [hz, pow_zero] at ht
    omega
  have hr := DynamicStep.run target expr physical left right state hpc ha hcode hpcfit
  have hf := ViewFrame.dynamic_range (bits := bits) physical target expr
  have haddr : (packingRun physical (left ++ DynamicStep.code target expr ++ right)
      (DynamicStep.code target expr).length state).register .address = state.register .address := by
    rw [hr]
    simpa only [List.take_length] using hf.1 state (DynamicStep.code target expr).length
  refine ⟨⟨haddr.trans hrep.address, ?_, ?_⟩, ?_, ?_⟩
  · have hv := DynamicStep.call_nat_VM target expr hc hd source physical environment state ht hcell hdim hvalues
      left right hpc ha hcode hpcfit
    rw [hrep.address, hrep.registers] at hv
    rw [hv]
    funext reg
    by_cases he : reg = target
    · subst reg
      simp only [Op.execute, Instruction.execute, Function.update_self]
    · simp only [Op.execute, Instruction.execute, Function.update_of_ne he]
  · intro a had
    rw [hr]
    have hh := ViewFrame.bankRange_view physical (DynamicStep.code target expr) 32 (max 39 (128 + expr.size)) hf
      (by have := Nat.le_max_left 39 (128 + expr.size); omega)
      q C0 C indexBase I base state hrep.address hend hb hC hpacked hdisjoint (DynamicStep.code target expr).length a had
    rw [List.take_length] at hh
    exact hh.trans (hrep.heap a had)
  · rw [hr, executeOps_pc physical _ state (DynamicStep.code_straight target expr), hpc, BitVec.ofNat_add_ofNat]
    congr 1
    omega
  · rw [hr, executeOps_halted, ha]

theorem dynamic_prefix_heap (q C0 C indexBase I base : Nat) (physical : PhysicalROM)
    (target : Register) (expr : Expr) (state : WordState bits)
    (hbase : state.register .address = BitVec.ofNat bits base) (hb : 0 < bits)
    (hend : Fits bits (base + max 39 (128 + expr.size)))
    (hC : C0 ≤ C) (hpacked : 4 + packedCapacityWords q C bits ≤ indexBase)
    (hdisjoint : indexBase + I ≤ base + 32)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ DynamicStep.code target expr ++ right)))
    (hpcfit : Fits bits (5 * (left ++ DynamicStep.code target expr ++ right).length))
    (count : Nat) (hc : count ≤ (DynamicStep.code target expr).length) (a : Nat) (had : a < C0 + I) :
    PA06A19PreparePackedView013.view q C0 C indexBase
      (packingRun physical (left ++ DynamicStep.code target expr ++ right) count state).heap a =
      PA06A19PreparePackedView013.view q C0 C indexBase state.heap a := by
  rw [straight_prefix physical left (DynamicStep.code target expr) right state
    (DynamicStep.code_straight target expr) hcode hpcfit hpc ha count hc]
  exact ViewFrame.bankRange_view physical (DynamicStep.code target expr) 32 (max 39 (128 + expr.size))
    (ViewFrame.dynamic_range physical target expr) (by have := Nat.le_max_left 39 (128 + expr.size); omega)
    q C0 C indexBase I base state hbase hend hb hC hpacked hdisjoint count a had

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
