module

public import Structure.PA06_A19Prepare_InitialUsed037_Prefix
public import Structure.PA06_A19Prepare_RawHeader039Body

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED canonical-Structure ABI bridge for the existing fetched
prefix joins and real HALT. Fetched is the unchanged037 predicate. The
normal141 provider supplies the existing HALT/access lemmas; no new whole
prefix premise, model, room, eligibility or clock is introduced. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompletion060Canonical
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims

theorem fetched_add {bits : Nat} (H : Nat) (rom : PhysicalROM) (code : List PackingOp)
    (before : WordState bits) (first second : Nat)
    (hf : ∀ k < first, PA06A19PrepareInitialUsed037.Fetched H rom code (packingRun rom code k before))
    (hs : ∀ k < second, PA06A19PrepareInitialUsed037.Fetched H rom code
      (packingRun rom code k (packingRun rom code first before))) :
    ∀ k < first + second, PA06A19PrepareInitialUsed037.Fetched H rom code (packingRun rom code k before) := by
  intro k hk
  by_cases hfirst : k < first
  · exact hf k hfirst
  · have hrest : k - first < second := by omega
    have clockEq : k = first + (k - first) := by omega
    rw [clockEq, PA06A19PrepareRawHeader039Body.wordRun_add rom code first (k - first) before]
    exact hs (k - first) hrest

/-- Join the given lower-level proper-prefix facts with the one real
terminal step. This is only a segment lemma on an abstract incoming state;
it does not assume or claim the full original preprocessor prefix. -/
theorem fetched_halt {bits : Nat} (H : Nat) (rom : PhysicalROM) (code : List PackingOp)
    (before : WordState bits) (count : Nat)
    (hprefix : ∀ k < count, PA06A19PrepareInitialUsed037.Fetched H rom code (packingRun rom code k before))
    (hcode : WordsFit bits (packingCode code)) (hpcfit : Fits bits (5 * code.length))
    (hpc : (packingRun rom code count before).pc.toNat = 5 * code.length)
    (active : (packingRun rom code count before).halted = false) :
    packingRun rom code (count + 1) before = { packingRun rom code count before with halted := true } ∧
    (packingRun rom code (count + 1) before).heap = (packingRun rom code count before).heap ∧
    (packingRun rom code (count + 1) before).halted = true ∧
    (∀ k < count + 1,
      let state := packingRun rom code k before
      state.halted = false ∧ state.pc.toNat + 4 < (packingCode code).length ∧
        match PackingOp.decode (fetch code state) with
        | none => fetch code state = haltWords
        | some op => packingAccessFits rom H state op) := by
  let final := packingRun rom code count before
  have oneRun : packingRun rom code 1 final = { final with halted := true } := by
    change packingStep rom ((packingCode code).map (BitVec.ofNat bits)) final = _
    exact packingStep_halt rom code final hcode hpc active
  have pcWord : final.pc = BitVec.ofNat bits (5 * code.length) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpcfit]
    exact hpc
  have fetched : fetch code final = haltWords := by
    change physicalFetch bits (packingCode code) final.pc.toNat = haltWords
    rw [pcWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpcfit,
      physicalFetch_eq bits (packingCode code) (5 * code.length) hcode]
    exact natFetch_halt code
  have terminal : final.halted = false ∧ final.pc.toNat + 4 < (packingCode code).length ∧
      match PackingOp.decode (fetch code final) with
      | none => fetch code final = haltWords
      | some op => packingAccessFits rom H final op := by
    refine ⟨active, ?_, ?_⟩
    · rw [hpc, packingCode_length]
      omega
    · rw [fetched, decode_halt]
  have joined : packingRun rom code (count + 1) before = { final with halted := true } := by
    rw [PA06A19PrepareRawHeader039Body.wordRun_add rom code count 1 before]
    exact oneRun
  have hheap := congrArg (fun next : WordState bits => next.heap) joined
  have hhalted := congrArg (fun next : WordState bits => next.halted) joined
  refine ⟨joined, hheap, hhalted, ?_⟩
  intro k hk
  by_cases hbefore : k < count
  · obtain ⟨ha, pc, op, decoded, access⟩ := hprefix k hbefore
    refine ⟨ha, pc, ?_⟩
    rw [decoded]
    exact access
  · have hkEq : k = count := by omega
    subst k
    exact terminal

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompletion060Canonical
