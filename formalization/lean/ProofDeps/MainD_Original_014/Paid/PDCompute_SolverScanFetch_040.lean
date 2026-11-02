module

public import Paid.PDCompute_SolverScanCandidate_039

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

theorem scanKernel_candidate_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (hcode : FetchesCode program origin (scanKernel mode origin)) (before : State) (hpc : before.pc=origin+8) :
    FetchesCode program before.pc (scanCandidateCode mode) := by
  have layout : scanKernel mode origin=
      (rangeCompareCode++[.branchZero .flag (origin+112) (origin+8)])++scanCandidateCode mode++
        (minimumUpdateCode (origin+75)++addNatSlot 25 1++addNatSlot 39 2++[.jump origin]) := by
    simp only [scanKernel,scanCandidateCode,scanEndpointCode,List.append_assoc]
  rw [layout] at hcode
  have fetched := hcode.middle
  change FetchesCode program (origin+8) (scanCandidateCode mode) at fetched
  simpa only [hpc] using fetched

theorem scanKernel_minimum_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (hcode : FetchesCode program origin (scanKernel mode origin)) :
    FetchesCode program (origin+75) (minimumUpdateCode (origin+75)) := by
  have layout : scanKernel mode origin=
      ((rangeCompareCode++[.branchZero .flag (origin+112) (origin+8)])++scanCandidateCode mode)++
        minimumUpdateCode (origin+75)++(addNatSlot 25 1++addNatSlot 39 2++[.jump origin]) := by
    simp only [scanKernel,scanCandidateCode,scanEndpointCode,List.append_assoc]
  rw [layout] at hcode
  exact hcode.middle

theorem scanKernel_counter_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (hcode : FetchesCode program origin (scanKernel mode origin)) (before : State) (hpc : before.pc=origin+95) :
    FetchesCode program before.pc (addNatSlot 25 1) := by
  have layout : scanKernel mode origin=
      (((rangeCompareCode++[.branchZero .flag (origin+112) (origin+8)])++scanCandidateCode mode)++
        minimumUpdateCode (origin+75))++addNatSlot 25 1++(addNatSlot 39 2++[.jump origin]) := by
    simp only [scanKernel,scanCandidateCode,scanEndpointCode,List.append_assoc]
  rw [layout] at hcode
  have fetched := hcode.middle
  change FetchesCode program (origin+95) (addNatSlot 25 1) at fetched
  simpa only [hpc] using fetched

theorem scanKernel_pointer_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (hcode : FetchesCode program origin (scanKernel mode origin)) (before : State) (hpc : before.pc=origin+103) :
    FetchesCode program before.pc (addNatSlot 39 2) := by
  have layout : scanKernel mode origin=
      ((((rangeCompareCode++[.branchZero .flag (origin+112) (origin+8)])++scanCandidateCode mode)++
        minimumUpdateCode (origin+75))++addNatSlot 25 1)++addNatSlot 39 2++[.jump origin] := by
    simp only [scanKernel,scanCandidateCode,scanEndpointCode,List.append_assoc]
  rw [layout] at hcode
  have fetched := hcode.middle
  change FetchesCode program (origin+103) (addNatSlot 39 2) at fetched
  simpa only [hpc] using fetched

theorem scanKernel_back_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (hcode : FetchesCode program origin (scanKernel mode origin)) (before : State) (hpc : before.pc=origin+111) :
    program[before.pc]?=some (.jump origin) := by
  rw [hpc]
  have closed : (scanKernel mode origin)[111]?=some (.jump origin) := rfl
  exact (hcode 111 (by rw [scanKernel_length]; omega)).trans closed

end PDCompute.Solver
