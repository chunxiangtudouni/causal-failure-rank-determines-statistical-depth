module

public import Structure.PA06_A19Prepare_CompactParents035Cards

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED control vocabulary for the actual compact body in an
arbitrary containing program.  The three source slices keep their original
absolute labels.  Local offsets are retained, rather than erased to a
whole-program fetch bound. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterGate081

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety

abbrev bits (q : Nat) (full : List (Finset (Fin q))) := indexWidth 32 full.length q
abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit
abbrev retentionStart : Nat := 144
abbrev orderingStart : Nat := 542
abbrev parentStart : Nat := 845
abbrev inputStart : Nat := 1206

def RetentionAt (whole : List PackingOp) : Prop :=
  retentionStart + 398 <= whole.length ∧
    ∀ position < 398,
      whole.getD (retentionStart + position) RawCandidateRetentionRAM.paddingOp =
        (RawCandidateRetentionRAM.programAt retentionStart).getD position
          RawCandidateRetentionRAM.paddingOp

def OrderingAt (whole : List PackingOp) : Prop :=
  orderingStart + 303 <= whole.length ∧
    ∀ position < 303,
      whole.getD (orderingStart + position) RawCandidateOrderingRAM.paddingOp =
        (RawCandidateOrderingRAM.programAt orderingStart).getD position
          RawCandidateOrderingRAM.paddingOp

def ParentsAt (whole : List PackingOp) : Prop :=
  parentStart + 361 <= whole.length ∧
    ∀ position < 361,
      whole.getD (parentStart + position) RawCandidateParentRAM.paddingOp =
        (RawCandidateParentRAM.programAt parentStart).getD position
          RawCandidateParentRAM.paddingOp

/-- These are exactly the compact initializer's current-state outputs.
No retained card, sorted order, parent answer or future execution is a field. -/
structure Initialized (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop where
  registers : RegistersFit (bits q full) state
  pc : state.pc = 5 * retentionStart
  active : state.halted = false
  pointer : state.heap 8 = 16
  header : state.heap 16 = full.length + q + 1
  zero : ∀ address, 8 <= address → address ≠ 8 → address ≠ 16 → state.heap address = 0

def Segment (start width : Nat) : Prop :=
  (start = retentionStart ∧ width = 398) ∨
    (start = orderingStart ∧ width = 303) ∨
    (start = parentStart ∧ width = 361)

def Point (q : Nat) (full : List (Finset (Fin q))) (whole : List PackingOp)
    (state : NatState) : Prop :=
  RegistersFit (bits q full) state ∧ Fits (bits q full) state.pc ∧ state.halted = false ∧
    ∃ start width offset, Segment start width ∧ offset < width ∧ start + offset < whole.length ∧
      state.pc = 5 * (start + offset) ∧
      ∃ op, PackingOp.decode (natFetch whole state.pc) = some op ∧
        NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q) state op

theorem point_of_local (q : Nat) (full : List (Finset (Fin q))) (whole : List PackingOp)
    (start width : Nat) (segment : Segment start width) (bound : start + width <= whole.length)
    (hend : Fits (bits q full) (5 * (start + width))) (state : NatState)
    (registers : RegistersFit (bits q full) state) (active : state.halted = false)
    (offset : Nat) (hoff : offset < width) (pc : state.pc = 5 * (start + offset))
    (op : PackingOp) (decoded : PackingOp.decode (natFetch whole state.pc) = some op)
    (access : NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q) state op) :
    Point q full whole state := by
  refine ⟨registers, ?_, active, start, width, offset, segment, hoff, by omega, pc, op, decoded, access⟩
  rw [pc]
  exact (Nat.mul_le_mul_left 5 (show start + offset <= start + width by omega)).trans_lt hend

theorem Point.pc_window {q : Nat} {full : List (Finset (Fin q))} {whole : List PackingOp}
    {state : NatState} (point : Point q full whole state) :
    5 * retentionStart <= state.pc ∧ state.pc < 5 * inputStart := by
  obtain ⟨_registers, _fit, _active, start, width, offset, segment, hoff, _bound, pc, _op, _decode, _access⟩ := point
  rw [pc]
  rcases segment with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · change 5 * 144 <= 5 * (144 + offset) ∧ 5 * (144 + offset) < 5 * 1206
    omega
  · change 5 * 144 <= 5 * (542 + offset) ∧ 5 * (542 + offset) < 5 * 1206
    omega
  · change 5 * 144 <= 5 * (845 + offset) ∧ 5 * (845 + offset) < 5 * 1206
    omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterGate081
