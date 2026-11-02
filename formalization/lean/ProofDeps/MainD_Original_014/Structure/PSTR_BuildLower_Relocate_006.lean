module

public import Structure.PSTR_BuildLower_Dynamic_004
public import Structure.PSTR_BuildLower_Room_005

/-! Both lexical counter cells and dimensions are read from the actual shared
control bank. Absolute source-template cell numbers are never used as physical
target addresses. The representation premises here are internal invariants. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035b

theorem fullBuild_static_bounds :
    (programExpressionSize PA17ProgramTemplates041.fullBuild,
      programRepeatDepth PA17ProgramTemplates041.fullBuild,
      programCellLimit PA17ProgramTemplates041.fullBuild,
      programInputLimit PA17ProgramTemplates041.fullBuild) = (29, 3, 21, 3) := by decide

def relocateExpr (dimensions cellMap : Nat → Nat) : Expr → Expr
  | .constant value => .constant value
  | .cell address => .cell (cellMap address)
  | .input address => .cell (dimensions address)
  | .binary op left right => .binary op
      (relocateExpr dimensions cellMap left) (relocateExpr dimensions cellMap right)

theorem relocateExpr_size (expr : Expr) (dimensions cellMap : Nat → Nat) :
    (relocateExpr dimensions cellMap expr).size = expr.size := by
  induction expr with
  | constant value => rfl
  | cell address => rfl
  | input address => rfl
  | binary op left right ihl ihr => simp only [relocateExpr, Expr.size, ihl, ihr]

theorem relocateExpr_eval (expr : Expr) (dimensions cellMap : Nat → Nat)
    (source physical : PhysicalROM) (environment heap : Nat → Nat)
    (hc : ∀ address < expressionCellLimit expr, heap (cellMap address) = environment address)
    (hd : ∀ address < expressionInputLimit expr,
      heap (dimensions address) = source.semantic.read .input address) :
    (relocateExpr dimensions cellMap expr).eval physical heap = expr.eval source environment := by
  induction expr with
  | constant value => rfl
  | cell address => exact hc address (by simp [expressionCellLimit])
  | input address => exact hd address (by simp [expressionInputLimit])
  | binary op left right ihl ihr =>
    have hcl : ∀ address < expressionCellLimit left, heap (cellMap address) = environment address :=
      fun address ha => hc address (lt_of_lt_of_le ha (Nat.le_max_left _ _))
    have hcr : ∀ address < expressionCellLimit right, heap (cellMap address) = environment address :=
      fun address ha => hc address (lt_of_lt_of_le ha (Nat.le_max_right _ _))
    have hdl : ∀ address < expressionInputLimit left,
        heap (dimensions address) = source.semantic.read .input address :=
      fun address ha => hd address (lt_of_lt_of_le ha (Nat.le_max_left _ _))
    have hdr : ∀ address < expressionInputLimit right,
        heap (dimensions address) = source.semantic.read .input address :=
      fun address ha => hd address (lt_of_lt_of_le ha (Nat.le_max_right _ _))
    simp only [relocateExpr, Expr.eval, ihl hcl hdl, ihr hcr hdr]

theorem relocateExpr_below (expr : Expr) (dimensions cellMap : Nat → Nat) (stack : Nat)
    (hc : ∀ address < expressionCellLimit expr, cellMap address < stack)
    (hd : ∀ address < expressionInputLimit expr, dimensions address < stack) :
    (relocateExpr dimensions cellMap expr).Below stack := by
  induction expr with
  | constant value => trivial
  | cell address => exact hc address (by simp [expressionCellLimit])
  | input address => exact hd address (by simp [expressionInputLimit])
  | binary op left right ihl ihr =>
    refine ⟨ihl ?_ ?_, ihr ?_ ?_⟩
    · exact fun address ha => hc address (lt_of_lt_of_le ha (Nat.le_max_left _ _))
    · exact fun address ha => hd address (lt_of_lt_of_le ha (Nat.le_max_left _ _))
    · exact fun address ha => hc address (lt_of_lt_of_le ha (Nat.le_max_right _ _))
    · exact fun address ha => hd address (lt_of_lt_of_le ha (Nat.le_max_right _ _))

def dimensionBank (base index : Nat) : Nat := base + index
def variableBank (base index : Nat) : Nat := base + 64 + index
def savedCounter (base depth : Nat) : Nat := base + 96 + depth
def expressionStack (base : Nat) : Nat := base + 128
def virtualBank (base : Nat) (reg : Register) : Nat := base + 32 + reg.word

theorem relocated_bank_below (expr : Expr) (base : Nat)
    (hc : expressionCellLimit expr ≤ 22) (hd : expressionInputLimit expr ≤ 3) :
    (relocateExpr (dimensionBank base) (variableBank base) expr).Below
      (expressionStack base) := by
  apply relocateExpr_below
  · intro address ha
    unfold variableBank expressionStack
    omega
  · intro address ha
    unfold dimensionBank expressionStack
    omega

theorem expression_temporary_room (base address size : Nat) (hs : size ≤ 384)
    (ha : expressionStack base ≤ address) (hb : address < expressionStack base + size) :
    base + 128 ≤ address ∧ address < base + 512 := by
  unfold expressionStack at *
  omega

theorem savedCounter_room (base depth : Nat) (hd : depth < 32) :
    base + 96 ≤ savedCounter base depth ∧ savedCounter base depth < expressionStack base := by
  unfold savedCounter expressionStack
  omega

theorem virtualBank_room (base : Nat) (reg : Register) :
    base + 32 ≤ virtualBank base reg ∧ virtualBank base reg < base + 39 := by
  have h := registerSlot_bounds reg
  unfold virtualBank registerSlot at *
  omega

theorem variableBank_room (base index : Nat) (hi : index < 22) :
    base + 64 ≤ variableBank base index ∧ variableBank base index < base + 86 := by
  unfold variableBank
  omega

theorem word_address_ne {bits left right : Nat} (hl : Fits bits left)
    (hr : Fits bits right) (hne : left ≠ right) :
    BitVec.ofNat bits left ≠ BitVec.ofNat bits right := by
  intro hh
  have he := congrArg BitVec.toNat hh
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] at he
  exact hne he

theorem virtualBank_word_injective {bits : Nat} (base : Nat) (hf : Fits bits (base + 39)) :
    Function.Injective (fun reg => BitVec.ofNat bits (virtualBank base reg)) := by
  have hs (reg : Register) : Fits bits (virtualBank base reg) :=
    (virtualBank_room base reg).2.trans hf
  intro left right hh
  have he := congrArg BitVec.toNat hh
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hs left), Nat.mod_eq_of_lt (hs right)] at he
  apply registerSlot_injective
  unfold virtualBank at he
  unfold registerSlot
  omega

/-- The actual compiled dynamic expression preserves every word of the high
cache (and every later allocated address), at all instruction prefixes. -/
theorem relocated_compile_high_frame {bits : Nat} (expr : Expr) (physical : PhysicalROM)
    (base point : Nat) (hs : expr.size ≤ 384) (hp : base + 512 ≤ point)
    (hb : Fits bits (base + 512)) (hf : Fits bits point) :
    WordPrefixFrame physical
      ((relocateExpr (dimensionBank base) (variableBank base) expr).compile (expressionStack base))
      (BitVec.ofNat bits point) := by
  apply expr_compile_word_prefix_frame
  intro address hlo hhi
  rw [relocateExpr_size] at hhi
  have ha := expression_temporary_room base address expr.size hs hlo hhi
  exact word_address_ne hf (ha.2.trans hb) (by omega)

/-- The original expression compiler now executes using physical, relocated
counter/dimension loads, with its original exact dynamic-immediate value. -/
theorem relocated_compile_value (expr : Expr) (base : Nat)
    (hc : expressionCellLimit expr ≤ 22) (hd : expressionInputLimit expr ≤ 3)
    (source physical : PhysicalROM) (environment : Nat → Nat) (state : NatState)
    (hcell : ∀ address < expressionCellLimit expr,
      state.heap (variableBank base address) = environment address)
    (hdim : ∀ address < expressionInputLimit expr,
      state.heap (dimensionBank base address) = source.semantic.read .input address) :
    (runOps physical
      ((relocateExpr (dimensionBank base) (variableBank base) expr).compile (expressionStack base))
      state).register .value = expr.eval source environment := by
  rw [(Expr.compile_correct _ physical (expressionStack base)
    (relocated_bank_below expr base hc hd) state).1]
  exact relocateExpr_eval expr _ _ source physical environment state.heap hcell hdim

end PaperProofs.Structure.LaminarTree.PSTRBuildLower

