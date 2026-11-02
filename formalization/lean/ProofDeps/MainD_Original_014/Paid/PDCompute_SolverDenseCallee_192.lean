module

public import Paid.PDCompute_SolverCalleeCode_145
public import Paid.PDCompute_SolverMatrixDense_191

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDMenu.ComputeFrame

attribute [local irreducible] fullCellCode matrixCode matrixPackCode

/-- Complete actual solver callee, from genuine register arguments and
the original endpoint source, with original return/table/time/space.
No live-disjointness, initialized Header, table or run is assumed.
The SAME actual original matrix/serializer095 trace also preserves its
final dense root six. This functional theorem makes NO whole-solver
operand-bit bound claim; that numerical chain continues independently. -/
theorem solver_callee_dense_trace (mode : ReaderMode) (program : Program) (input : List Cell)
    (origin : ℕ) (fetch : FetchesCode program origin (solverCalleeCode mode origin))
    (P : Parameters) (fee penalty : ℚ) (before : State) (base n k source returnPC : ℕ)
    (hpc : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (old : before.register .old=.natural returnPC) (address : before.register .address=.natural source)
    (total : before.register .total=.rational penalty) (index : before.register .index=.natural n)
    (value : before.register .value=.natural k) (flag : before.register .flag=.rational fee)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace ≤ 38000*(P.certificate.M+1)*entryCount n k ∧ Return P fee penalty n k base returnPC before after ∧
      (∀ state∈trace,RegionMemory before state (workspace base n k)) ∧
      peakCells trace ≤ workingCells before+62*entryCount n k ∧
      DenseOriginalTable after P fee penalty base n k ∧
      PDLower.CalibrationCompute.HeapList after (cellBase base k n k)
        (denseEncodeEntry (menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty k n) n k)) := by
  let initialCap:=(stateCellBits before).max?.getD 0
  let budget:=initialCap+(1+natBits (base+headerWords))+(.rational 0 : Cell).bits+natBits (origin+46)+(1+natBits (P.certificate.M+1))
  have initialSafe : RootD27.Bits.SafeBits before budget := by
    intro bits member
    have capped : bits ≤ initialCap := List.le_max?_getD_of_mem member
    dsimp only [budget]
    omega
  have addressBits : 1+natBits (base+headerWords) ≤ budget := by dsimp only [budget]; omega
  have zeroBits : (.rational 0 : Cell).bits ≤ budget := by dsimp only [budget]; omega
  have lengthBits : 1+natBits (P.certificate.M+1) ≤ budget := by dsimp only [budget]; omega
  have pcBits : natBits (origin+46) ≤ budget := by dsimp only [budget]; omega
  have headerPC : natBits (origin+37) ≤ budget := (natBits_mono (by omega : origin+37 ≤ origin+46)).trans pcBits
  have prologueFetch : FetchesCode program before.pc solverPrologue := by rw [hpc]; exact solverCallee_prologue_fetch mode program origin fetch
  obtain ⟨initial,initialized,initialHead,initialLast,initialChain,initialTime,initialHeader,initialBase,initialPC,initialFrame,_,initialResources,_⟩:=
    solver_header_initialization_resources program input origin before base n k budget hpc fresh initialSafe addressBits zeroBits headerPC
      prologueFetch (solverCallee_lead_fetch mode program origin fetch) (solverCallee_loop_fetch mode program origin fetch)
  let values:=initializedHeaderValues (solverPrologueResult before base) base
  have saved0 : values 0=.natural source := by simpa only [savedArguments,List.getElem_cons_zero,address] using initializedHeaderValue_saved before base 0 (by decide)
  have saved1 : values 1=.natural returnPC := by simpa only [savedArguments,List.getElem_cons_succ,List.getElem_cons_zero,old] using initializedHeaderValue_saved before base 1 (by decide)
  have saved2 : values 2=.rational penalty := by simpa only [savedArguments,List.getElem_cons_succ,List.getElem_cons_zero,total] using initializedHeaderValue_saved before base 2 (by decide)
  have saved3 : values 3=.natural n := by simpa only [savedArguments,List.getElem_cons_succ,List.getElem_cons_zero,index] using initializedHeaderValue_saved before base 3 (by decide)
  have saved4 : values 4=.natural k := by simpa only [savedArguments,List.getElem_cons_succ,List.getElem_cons_zero,value] using initializedHeaderValue_saved before base 4 (by decide)
  have saved5 : values 5=.rational fee := by simpa only [savedArguments,List.getElem_cons_succ,List.getElem_cons_zero,flag] using initializedHeaderValue_saved before base 5 (by decide)
  have initializedSource:=EndpointSource.frame_of_avoids mode input P source base n k before initialized hsource avoids initialFrame
  have initializedSafe:=(initialResources initialized (List.mem_of_getLast? initialLast)).2.1
  have countPC : natBits (initialized.pc+9) ≤ budget := by simpa only [initialPC,Nat.add_assoc] using pcBits
  have countFetch : FetchesCode program initialized.pc (endpointCountHeaderCode mode) := by rw [initialPC]; exact solverCallee_count_fetch mode program origin fetch
  obtain ⟨count,middle,countHead,countLast,countChain,countTime,middleHeader,middleBase,middlePC,countResources⟩:=
    endpointCountHeader_trace_resources mode program input P initialized base source budget values initialHeader initialBase initializedSource saved0
      initializedSafe addressBits lengthBits countPC countFetch
  let middleValues:=Function.update values 6 (.natural P.certificate.M)
  have countMemory : ∀ state∈count,RegionMemory initialized state (workspace base n k) :=
    fun state member=>(countResources state member).1.enlarge (headerRegion_subset_workspace base n k)
  have middleFrame:=(RegionMemory.trace_last countMemory countLast).frame (Finset.Subset.refl _)
  have middleSource:=EndpointSource.frame_of_avoids mode input P source base n k initialized middle initializedSource avoids middleFrame
  have atMatrix : middle.pc=origin+46 := by rw [middlePC,initialPC]
  have middle0 : middleValues 0=.natural source := by simpa only [middleValues,Function.update_of_ne (by decide : (0 : ℕ) ≠ 6)] using saved0
  have middle1 : middleValues 1=.natural returnPC := by simpa only [middleValues,Function.update_of_ne (by decide : (1 : ℕ) ≠ 6)] using saved1
  have middle2 : middleValues 2=.rational penalty := by simpa only [middleValues,Function.update_of_ne (by decide : (2 : ℕ) ≠ 6)] using saved2
  have middle3 : middleValues 3=.natural n := by simpa only [middleValues,Function.update_of_ne (by decide : (3 : ℕ) ≠ 6)] using saved3
  have middle4 : middleValues 4=.natural k := by simpa only [middleValues,Function.update_of_ne (by decide : (4 : ℕ) ≠ 6)] using saved4
  have middle5 : middleValues 5=.rational fee := by simpa only [middleValues,Function.update_of_ne (by decide : (5 : ℕ) ≠ 6)] using saved5
  obtain ⟨matrix,after,matrixHead,matrixLast,matrixChain,matrixTime,heap,afterBase,afterOld,afterAddress,afterIndex,afterPC,_,_,matrixMemory,_,finalDense,root⟩:=
    matrix_pack_dense_trace mode program input (origin+46) (solverCallee_matrixPack_fetch mode program origin fetch) P fee penalty middle base n k source returnPC
      middleValues atMatrix middleHeader middleBase middleSource avoids middle0 middle1 middle2 middle3 middle4 middle5 (Function.update_self _ _ _)
  have initialMemory : ∀ state∈initial,RegionMemory before state (workspace base n k) :=
    fun state member=>(initialResources state member).1.enlarge (headerRegion_subset_workspace base n k)
  have firstJoin:=joinTrace_spec program input initial count before initialized middle 2460 150
    initialHead initialLast countHead countLast initialChain countChain initialTime countTime
  have firstMemory:=RegionMemory.join_trace initial count before initialized _ initialLast initialMemory countMemory
  have joined:=joinTrace_spec program input (joinTrace initial count) matrix before middle after 2610
    (35000*(P.certificate.M+1)*entryCount n k) firstJoin.1 firstJoin.2.1 matrixHead matrixLast firstJoin.2.2.1 matrixChain firstJoin.2.2.2 matrixTime
  have allMemory:=RegionMemory.join_trace (joinTrace initial count) matrix before middle _ firstJoin.2.1 firstMemory matrixMemory
  have finalMemory:=RegionMemory.trace_last allMemory joined.2.1
  have returned : Return P fee penalty n k base returnPC before after :=
    ⟨afterPC,afterBase,afterOld,afterAddress,afterIndex,heap,finalMemory.2.2.2,finalMemory.frame (Finset.Subset.refl _)⟩
  refine ⟨joinTrace (joinTrace initial count) matrix,after,joined.1,joined.2.1,joined.2.2.1,?_,returned,allMemory,?_,finalDense,root⟩
  · have productPositive : 1 ≤ (P.certificate.M+1)*entryCount n k := by
      unfold entryCount
      nlinarith [Nat.zero_le (P.certificate.M*((n+1)*(k+1)))]
    calc
      _ ≤ 2610+35000*(P.certificate.M+1)*entryCount n k := joined.2.2.2
      _ ≤ 38000*(P.certificate.M+1)*entryCount n k := by nlinarith
  · exact PDLower.CalibrationCompute.peakCells_le_of_forall _ _
      (fun state member=>(allMemory state member).workspace_workingCells)

end PDCompute.Solver
