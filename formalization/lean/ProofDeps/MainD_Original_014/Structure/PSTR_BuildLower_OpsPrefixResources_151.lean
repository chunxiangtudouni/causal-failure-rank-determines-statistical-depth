module

public import Structure.PSTR_BuildLower_OpsRun_076
public import Structure.PSTR_BuildLower_OpExprPrefixResources_150

/-! A source list carries full NEW-C capacity and every high-cache word
at ONE actual endpoint in addition to original source/Data/environment.
Every selected primitive count is shared by all fields; no separate run is
identified by an endpoint PC. Every prefix certificate is composed by actual run_add. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035b PA17ProgramTemplates041

def OpsPrefixRuns (q : Nat) (full : List (Finset (Fin q))) (physical : PhysicalROM)
    (ops : List OpExpr) (environment : Nat → Nat) (logical : State)
    (state : WordState (bits q full)) (left right : List PackingOp) : Prop :=
  ∃ count ≤ 206 * ops.length,
    let block := lowerOps ConcreteAST.ports ops left.length
    let after := packingRun physical (left ++ block ++ right) count state
    Prepared q full (IndexedClosureRAM.execute (givenTreeROM q full).semantic
      (instructions (dimensionROM full.length q (t q full)) environment ops) logical) after ∧
      RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + block.length)) ∧ after.halted = false ∧
      (∀ address < 21, after.heap (after.register .address + BitVec.ofNat _ (64 + address)) =
        BitVec.ofNat _ (environment address)) ∧
      (∀ offset < 128, (offset < 32 ∨ 39 ≤ offset) →
        after.heap (BitVec.ofNat _ (controlBase q full + offset)) =
          state.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
      GlobalCapacity.Bounded q full after.heap ∧ ResourceTrace.CacheFrame q full state.heap after.heap ∧
      ResourceTrace.Keeps q full physical (left ++ block ++ right) state count ∧
      TraceAccess.Safe (allocated q full) physical (left ++ block ++ right) state count

theorem ops_prefix_resources (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (ops : List OpExpr) (environment : Nat → Nat)
    (logical : State)
    (context : SourceContext.Context q full (instructions (dimensionROM full.length q (t q full)) environment ops) logical)
    (state : WordState (bits q full)) (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hshape : ∀ op ∈ ops, OpExprShape op) (hvalues : ∀ op ∈ ops, OpExprFits q full environment op)
    (henv : ∀ address < 21, state.heap (state.register .address + BitVec.ofNat _ (64 + address)) =
      BitVec.ofNat _ (environment address))
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ lowerOps ConcreteAST.ports ops left.length ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ lowerOps ConcreteAST.ports ops left.length ++ right).length)) :
    OpsPrefixRuns q full (CompactControllerClaims.controllerInput q full used) ops environment logical state left right := by
  let runtime := CompactControllerClaims.controllerInput q full used
  induction ops generalizing logical state left with
  | nil =>
    refine ⟨0, by simp, ?_⟩
    dsimp only [lowerOps, packingRun, instructions, List.map_nil, IndexedClosureRAM.execute]
    exact ⟨hrep, data, by simpa only [List.length_nil, Nat.add_zero] using hpc, ha, henv,
      (by intro offset ho hout; rfl), bounded, ResourceTrace.CacheFrame.refl q full state.heap,
      ResourceTrace.keeps_zero q full runtime _ state bounded, TraceAccess.zero (allocated q full) runtime _ state⟩
  | cons op later ih =>
    let current := lowerOpExpr ConcreteAST.ports left.length op
    let suffix := lowerOps ConcreteAST.ports later (left.length + current.length)
    have headContext : SourceContext.Context q full
        (op.eval (dimensionROM full.length q (t q full)) environment ::
          instructions (dimensionROM full.length q (t q full)) environment later) logical := context
    obtain ⟨firstCount, firstBound, firstResult⟩ := opExpr_prefix_resources q full used hq hlaminar op environment _ logical
      headContext state hrep data bounded (hshape op List.mem_cons_self) (hvalues op List.mem_cons_self) henv
      left (suffix ++ right) hpc ha
      (by simpa only [lowerOps, List.append_assoc, current, suffix] using hcode)
      (by simpa only [lowerOps, List.append_assoc, current, suffix] using hpcfit)
    let middle := packingRun runtime (left ++ current ++ suffix ++ right) firstCount state
    have first : Prepared q full ((op.eval (dimensionROM full.length q (t q full)) environment).execute
          (givenTreeROM q full).semantic logical) middle ∧ RuntimeData.Data q full middle.heap ∧
        middle.pc = BitVec.ofNat _ (5 * (left.length + current.length)) ∧ middle.halted = false ∧
        (∀ offset < 128, (offset < 32 ∨ 39 ≤ offset) →
          middle.heap (BitVec.ofNat _ (controlBase q full + offset)) = state.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
        GlobalCapacity.Bounded q full middle.heap ∧ ResourceTrace.CacheFrame q full state.heap middle.heap ∧
        ResourceTrace.Keeps q full runtime (left ++ current ++ suffix ++ right) state firstCount ∧
        TraceAccess.Safe (allocated q full) runtime (left ++ current ++ suffix ++ right) state firstCount := by
      simpa only [List.append_assoc, current, middle] using firstResult
    have middleEnv : ∀ address < 21, middle.heap (middle.register .address + BitVec.ofNat _ (64 + address)) =
        BitVec.ofNat _ (environment address) := by
      intro address had
      rw [first.1.address, BitVec.ofNat_add_ofNat]
      rw [first.2.2.2.2.1 (64 + address) (by omega) (Or.inr (by omega))]
      simpa only [hrep.address, BitVec.ofNat_add_ofNat] using henv address had
    obtain ⟨lastCount, lastBound, lastResult⟩ := ih _ (SourceContext.advance headContext) middle first.1 first.2.1 first.2.2.2.2.2.1
      (by intro other hm; exact hshape other (List.mem_cons_of_mem _ hm))
      (by intro other hm; exact hvalues other (List.mem_cons_of_mem _ hm)) middleEnv (left ++ current)
      (by simpa only [List.length_append] using first.2.2.1) first.2.2.2.1
      (by simpa only [lowerOps, List.append_assoc, List.length_append, current, suffix] using hcode)
      (by simpa only [lowerOps, List.append_assoc, List.length_append, current, suffix] using hpcfit)
    have last := lastResult
    simp only [List.length_append, List.append_assoc] at last
    refine ⟨firstCount + lastCount, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · dsimp only
      simp only [lowerOps, List.append_assoc, PSTRWordSegments.run_add]
      have endpoint := last.1
      have endpointData := last.2.1
      have endpointPC := last.2.2.1
      have endpointActive := last.2.2.2.1
      have endpointEnv := last.2.2.2.2.1
      have endpointFrame := last.2.2.2.2.2.1
      have endpointBounded := last.2.2.2.2.2.2.1
      have endpointCache := last.2.2.2.2.2.2.2.1
      have endpointKeeps := last.2.2.2.2.2.2.2.2.1
      have endpointSafe := last.2.2.2.2.2.2.2.2.2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [instructions, List.map_cons, IndexedClosureRAM.execute, middle, current, suffix,
          List.append_assoc] using endpoint
      · simpa only [middle, current, suffix, List.append_assoc] using endpointData
      · simpa only [List.length_append, Nat.add_assoc, middle, current, suffix, List.append_assoc] using endpointPC
      · simpa only [middle, current, suffix, List.append_assoc] using endpointActive
      · simpa only [middle, current, suffix, List.append_assoc] using endpointEnv
      · intro offset ho hout
        have hf := (endpointFrame offset ho hout).trans (first.2.2.2.2.1 offset ho hout)
        simpa only [middle, current, suffix, List.append_assoc] using hf
      · simpa only [middle, current, suffix, List.append_assoc] using endpointBounded
      · have frame := ResourceTrace.CacheFrame.trans endpointCache first.2.2.2.2.2.2.1
        simpa only [middle, current, suffix, List.append_assoc] using frame
      · have back : ResourceTrace.Keeps q full runtime (left ++ current ++ suffix ++ right) middle lastCount := by
          simpa only [middle, current, suffix, List.append_assoc] using endpointKeeps
        have allKeeps := ResourceTrace.keeps_add q full runtime (left ++ current ++ suffix ++ right) state firstCount lastCount
          first.2.2.2.2.2.2.2.1 back
        simpa only [lowerOps, middle, current, suffix, List.append_assoc] using allKeeps
      · have back : TraceAccess.Safe (allocated q full) runtime (left ++ current ++ suffix ++ right) middle lastCount := by
          simpa only [middle, current, suffix, List.append_assoc] using endpointSafe
        have allSafe := TraceAccess.add (allocated q full) runtime (left ++ current ++ suffix ++ right) state firstCount lastCount
          first.2.2.2.2.2.2.2.2 back
        simpa only [lowerOps, middle, current, suffix, List.append_assoc] using allSafe

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
