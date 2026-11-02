module

public import Paid.PDCompute_Nat_Loop_MatrixGivenB_006
public import Paid.PDCompute_SolverEntryGivenBudget_215
public import Paid.PDCompute_SolverPackBudgetBits_202
public import Paid.PDCompute_SolverDensePreservation_171
public import Paid.PDCompute_Nat_Resources_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame PDCompute.NatControl

attribute [local irreducible] fullCellCode cellFieldsCode matrixCode matrixPackCode solverCalleeCode

/-- COMPLETE original callee at ONE already selected global B. The
fixed natural control caller is independent of current dirty scratch;
actual original entry/matrix/serializer/return all use this SAME budget.
The three numeric rooms are internal caller accounting, not run or answer
oracles. Root's concrete core discharges them from its original inputs. -/
theorem solver_callee_given_budget (mode : ReaderMode) (input : List Cell) (origin : ℕ)
    (P : Parameters) (fee penalty : ℚ) (before : State) (base n k source returnPC : ℕ)
    (hpc : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (old : before.register .old=.natural returnPC) (address : before.register .address=.natural source)
    (total : before.register .total=.rational penalty) (index : before.register .index=.natural n)
    (value : before.register .value=.natural k) (flag : before.register .flag=.rational fee)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (controlCaller : State) (incoming budget : ℕ)
    (context : SolverControlContext controlCaller incoming base n k mode origin budget)
    (safeBefore : RootD27.Bits.SafeBits before budget)
    (scalarRoom : 4194304*solverBitScale P fee penalty n k≤budget)
    (indexBits : 1+natBits (P.certificate.M+1)≤budget)
    (sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step (solverLocatedProgram mode origin) input first=some later) ∧
      time (solverLocatedProgram mode origin) trace≤38000*(P.certificate.M+1)*entryCount n k ∧ Return P fee penalty n k base returnPC before after ∧
      (∀ state∈trace,RegionMemory before state (workspace base n k)) ∧ peakCells trace≤workingCells before+62*entryCount n k ∧
      peakOperandBits trace≤budget ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace.dropLast,origin≤state.pc ∧ state.pc<origin+(solverCalleeCode mode origin).length) ∧
      DenseOriginalTable after P fee penalty base n k ∧ PDLower.CalibrationCompute.HeapList after (cellBase base k n k)
        (denseEncodeEntry (menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty k n) n k)) := by
  let program:=solverLocatedProgram mode origin
  obtain ⟨initial,ready,values,initialHead,initialLast,initialChain,initialTime,initialHeader,v0,v1,v2,v3,v4,v5,v6,readyBase,readyPC,readySource,
    initialFrame,_,_,_,_,initialResources⟩:=solver_entry_given_budget mode origin input P fee penalty before base n k source returnPC hpc fresh old address total index value flag hsource avoids controlCaller incoming budget context safeBefore indexBits
  have matrixFetch : FetchesCode program (origin+46) (matrixPackCode mode (origin+46)) :=
    solverCallee_matrixPack_fetch mode program origin (solverLocated_fetch mode origin)
  obtain ⟨matrix,middle,middleValues,matrixHead,matrixLast,matrixChain,matrixTime,middleHeader,dense,inputs,middleBase,middlePC,_,_,matrixMemory,_,_,matrixSafe⟩:=
    PDCompute.NatLoop.matrix_trace_givenB mode origin input (origin+46) matrixFetch P fee penalty ready base n k source controlCaller incoming budget
      context scalarRoom indexBits sourceBits values readyPC initialHeader readyBase readySource avoids v0 v2 v3 v4 v5 v6
      (initialResources ready (List.mem_of_getLast? initialLast)).2
  let packOrigin:=origin+46+(matrixCode mode (origin+46)).length
  have packFetch : FetchesCode program packOrigin (PDCompute.Pack.serializerCode packOrigin) := by
    have literal:=matrixFetch
    rw [matrixPackCode] at literal
    exact literal.append_right
  have packCounter : natBits (packOrigin+233)≤budget := by
    have actualFetch : FetchesCode program middle.pc (PDCompute.Pack.serializerCode packOrigin) := by rw [middlePC];exact packFetch
    have bound:=SolverControlContext.block (before:=middle) context (PDCompute.Pack.serializerCode packOrigin)
      (by rw [PDCompute.Pack.serializerCode_length];decide) actualFetch
    simpa only [middlePC,PDCompute.Pack.serializerCode_length,packOrigin] using bound
  have middleN : middleValues 3=.natural n := (inputs 3 (by decide)).trans v3
  have middleK : middleValues 4=.natural k := (inputs 4 (by decide)).trans v4
  have middleReturn : middleValues 1=.natural returnPC := (inputs 1 (by decide)).trans v1
  obtain ⟨packed,after,packHead,packLast,packChain,packTime,heap,afterBase,afterOld,afterAddress,afterIndex,afterPC,_,packMemory,packSafe⟩:=
    solver_pack_trace_same_budget program input packOrigin (P.cachedSolveMenuTable P.endpointCache fee penalty k n) middle base n k returnPC budget middleValues
      packFetch middlePC middleHeader middleBase middleN middleK middleReturn (originalTable_rows P fee penalty n k) (originalTable_columns P fee penalty n k)
      (PDCompute.Pack.denseTable_heap middle (P.cachedSolveMenuTable P.endpointCache fee penalty k n) base k
        (originalTable_columns P fee penalty n k) dense.pack_cells)
      (matrixSafe middle (List.mem_of_getLast? matrixLast)) (fun number bound=>context.natural number bound)
      (fun counter bound=>(natBits_mono bound).trans packCounter)
  have initialMemory : ∀ state∈initial,RegionMemory before state (workspace base n k) := fun state member=>(initialResources state member).1
  have initialSafe : ∀ state∈initial,RootD27.Bits.SafeBits state budget := fun state member=>(initialResources state member).2
  have packRegion : ∀ state∈packed,RegionMemory middle state (workspace base n k) :=
    fun state member=>(packMemory state member).enlarge (pack_writeRegion_subset_workspace base n k)
  have firstJoin:=joinTrace_spec program input initial matrix before ready middle 2610 (30000*(P.certificate.M+1)*entryCount n k)
    initialHead initialLast matrixHead matrixLast initialChain matrixChain initialTime matrixTime
  have firstMemory:=RegionMemory.join_trace initial matrix before ready (workspace base n k) initialLast initialMemory matrixMemory
  have firstSafe:=PDCompute.Pack.joinTrace_invariant initial matrix (fun state=>RootD27.Bits.SafeBits state budget) initialSafe matrixSafe
  have joined:=joinTrace_spec program input (joinTrace initial matrix) packed before middle after
    (2610+30000*(P.certificate.M+1)*entryCount n k) (4096*(n+1)*(k+1))
    firstJoin.1 firstJoin.2.1 packHead packLast firstJoin.2.2.1 packChain firstJoin.2.2.2 packTime
  have allMemory:=RegionMemory.join_trace (joinTrace initial matrix) packed before middle (workspace base n k) firstJoin.2.1 firstMemory packRegion
  have allSafe:=PDCompute.Pack.joinTrace_invariant (joinTrace initial matrix) packed (fun state=>RootD27.Bits.SafeBits state budget) firstSafe packSafe
  have finalMemory:=RegionMemory.trace_last allMemory joined.2.1
  have returned : Return P fee penalty n k base returnPC before after :=
    ⟨afterPC,afterBase,afterOld,afterAddress,afterIndex,heap,finalMemory.2.2.2,finalMemory.frame (Finset.Subset.refl _)⟩
  have finalDense:=dense.after_serializer (packMemory after (List.mem_of_getLast? packLast))
  have root:=(finalDense n (le_refl _) k (le_refl _))
  refine ⟨joinTrace (joinTrace initial matrix) packed,after,joined.1,joined.2.1,joined.2.2.1,?_,returned,allMemory,?_,
    PDCompute.Pack.safeBits_peak _ budget allSafe,allSafe,?_,finalDense,root⟩
  · have positive : 1≤(P.certificate.M+1)*entryCount n k := by unfold entryCount;nlinarith
    have entries : entryCount n k≤(P.certificate.M+1)*entryCount n k := by nlinarith
    have cost:=joined.2.2.2
    change time program (joinTrace (joinTrace initial matrix) packed)≤38000*(P.certificate.M+1)*entryCount n k
    unfold entryCount at cost entries positive ⊢
    nlinarith
  · exact PDLower.CalibrationCompute.peakCells_le_of_forall _ _ (fun state member=>(allMemory state member).workspace_workingCells)
  · simpa only [program,solverLocatedProgram,List.size_toArray] using PDLower.CalibrationCompute.located_chain_scope origin (solverCalleeCode mode origin).toArray input
      (joinTrace (joinTrace initial matrix) packed) joined.2.2.1

end PDCompute.Solver
