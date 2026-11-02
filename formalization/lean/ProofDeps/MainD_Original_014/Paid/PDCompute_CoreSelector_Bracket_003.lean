module
public import Paid.PDCompute_CoreSelector_Decisions_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
@[expose] public section
namespace PDCompute.CoreSelector
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CoreSearch RootD27.Core PDCompute.CoreSearchLoop

/-- The bracket path really executes the current160-op computation,
then the actual instruction at175 jumps to180. No endpoint PC is free. -/
theorem bracket_piece (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (origin : ℕ) (before : State)
    (scale budget : ℕ) (position : before.pc=origin+15) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before (.bracket lower upper))
    (safe : RootD27.Bits.SafeBits before budget) (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (origin+180)≤budget) (belowEntry : origin+180<labels.solveEntry)
    (fetched : FetchesCode program (origin+15) (finalBracketCode (origin+15)))
    (jumpFetched : program[origin+175]?=some (.jump (origin+180))) :
    ∃ after,∃ _piece : Piece program input P fee (.bracket lower upper) budget origin (origin+180) before after 3030,
      after.pc=origin+180 ∧ after.heap 29=.rational (clipRat (P.mixtureWeight lower upper)) := by
  have fetch : FetchesCode program before.pc (finalBracketCode before.pc) := by rw [position];exact fetched
  obtain ⟨trace,written,head,last,chain,cost,pc,fresh,header,rep,prepared,cache,value,counter,output,
    _space,properties,scope,proper,_requests,_count⟩:=
    represented_final_selector_actual P fee lower upper program labels input before scale budget ready.header ready.fresh
      ready.prepared ready.cache represented safe intrinsic room addressBits
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+160≤origin+180)).trans pcBits) (by omega) fetch
  have writtenPC : written.pc=origin+175 := by omega
  let first : Piece program input P fee (.bracket lower upper) budget origin (origin+180) before written 3000:=
    ⟨trace,head,last,chain,cost,⟨header,fresh,prepared,cache⟩,rep,counter,output,properties,
      (fun state member=>by have bounds:=scope state member;omega),
      (fun state member=>by have bounds:=proper state member;omega)⟩
  let after : State:={written with pc:=origin+180}
  have fetchJump : program[written.pc]?=some (.jump (origin+180)) := by rw [writtenPC];exact jumpFetched
  have actualJump : step program input written=some after := by simp only [step,fetchJump];rfl
  have jumpChain : [written,after].IsChain (fun first later=>step program input first=some later) :=
    List.isChain_cons_cons.mpr ⟨actualJump,.singleton after⟩
  have writtenSafe : RootD27.Bits.SafeBits written budget:=(properties written (List.mem_of_getLast? last)).2
  have jumpSafe : RootD27.Bits.SafeBits after budget:=writtenSafe.withPC _ pcBits
  have jumpProperties : ∀ state∈[written,after],RegionMemory written state scalarRegion ∧ RootD27.Bits.SafeBits state budget := by
    intro state member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same
    · subst state
      exact ⟨.refl written _,writtenSafe⟩
    · subst state
      exact ⟨.refl written _,jumpSafe⟩
  have jumpScope : ∀ state∈[written,after],origin≤state.pc ∧ state.pc≤origin+180 := by
    intro state member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same
    · subst state
      omega
    · subst state
      change origin≤origin+180 ∧ origin+180≤origin+180
      omega
  have jumpProper : ∀ state∈[written,after].dropLast,state.pc<origin+180 := by
    intro state member
    have same : state=written:=by simpa using member
    subst state
    omega
  have jumpCost : time program [written,after]≤30 :=
    (time_le_length program [written,after]).trans (by simp only [List.length_cons,List.length_nil];omega)
  let jump : Piece program input P fee (.bracket lower upper) budget origin (origin+180) written after 30:=
    ⟨[written,after],rfl,rfl,jumpChain,jumpCost,⟨header,fresh,prepared,cache⟩,rep,rfl,rfl,
      jumpProperties,jumpScope,jumpProper⟩
  exact ⟨after,first.join jump,rfl,value⟩

end PDCompute.CoreSelector
