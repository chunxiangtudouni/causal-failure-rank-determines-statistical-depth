module
public import RootB236_Controller_DFSDriver_BoundedFull025

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing RootB23.GenericRank PaperProofs.Structure
open PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
open scoped BigOperators
variable {C : Type*}
attribute [local irreducible] pushProfile actionProfile nodeProfile

def mass (before : Stack → List Bool) : Nat := ∑ slot : Stack,(before slot).length
def dataEnvelope (inputMass : Nat) : Nat := 64*(inputMass+1)^2
def workspace (C : Type*) (inputMass : Nat) : Nat :=
  dataEnvelope inputMass+pushProfile C*(4096*(dataEnvelope inputMass+1))
def duration (inputMass : Nat) : Nat := 16*(4096*(dataEnvelope inputMass+1))
def clockEnvelope (C : Type*) (inputMass : Nat) : Nat := 2*actionProfile C*(workspace C inputMass+pushProfile C+1)

theorem point_mass (before : Stack → List Bool) (slot : Stack) : (before slot).length≤mass before :=
  Finset.single_le_sum (fun other _ => Nat.zero_le ((before other).length)) (Finset.mem_univ slot)

theorem mass_fields (before : Stack → List Bool) : FieldsBound before (mass before+1) :=
  fun slot _ => (point_mass before slot).trans (by omega)

def rootCap (inputMass depth : Nat) (tail : List Bool) : Nat := tail.length+depth*(28*(inputMass+1)+30)

theorem mass_data_envelope (inputMass depth : Nat) (tail : List Bool)
    (depthBound : depth≤ inputMass) (tailBound : tail.length≤ inputMass) :
    entryCap (inputMass+1) (rootCap inputMass depth tail)≤dataEnvelope inputMass := by
  have product:=Nat.mul_le_mul_right (28*(inputMass+1)+30) depthBound
  dsimp only [entryCap,rootCap,dataEnvelope]
  nlinarith

theorem peak_envelope (inputMass bound cap : Nat) (entry : entryCap bound cap≤dataEnvelope inputMass) :
    peak C bound cap≤workspace C inputMass :=
  Nat.add_le_add entry (Nat.mul_le_mul_left (pushProfile C) (Nat.mul_le_mul_left 4096 (Nat.add_le_add_right entry 1)))

theorem time_envelope (inputMass bound cap : Nat) (entry : entryCap bound cap≤dataEnvelope inputMass) :
    nodeTime bound cap≤duration inputMass :=
  Nat.mul_le_mul_left 16 (Nat.mul_le_mul_left 4096 (Nat.add_le_add_right entry 1))

def originalPick (q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) : Option (Fin q) :=
  match stages with | [] => none | eligible::later => pickGenericMaxRankTool q eligible later remaining

theorem code_original_pick (limit q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) (depth : stages.length≤limit) :
    (evaluateCode q (limit+1) stages remaining).pick=originalPick q stages remaining := by
  have exactValue:=(evaluate_code_original limit q stages remaining depth).2
  cases stages <;> exact exactValue

/-- A full source run with mass measured at the actual staged entry; workspace contains no DFS visit factor. -/
theorem measured_original (finish : Statement C) (limit q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (depth : stages.length≤limit) (memory : Store C) (before : Stack → List Bool) (flag : Bool) (tail : List Bool)
    (r0 : before 0=rows q stages) (r2 : before 2=unary (limit+1)) (r4 : before 4=EraseSem.mask remaining)
    (r11 : before 11=unary q) (r13 : before 13=flag::tail) :
    ∃ steps final,BoundedRun finish (workspace C (mass before)) (state start memory before) final steps ∧
      StableReply (limit+1) q stages remaining tail (before 1) memory.1 (mass before+1) final ∧
      final.stk 15=unary (rankCode limit (genericRank stages remaining)) ∧
      final.stk 13=(originalPick q stages remaining).isSome::tail ∧
      final.stk 14=pickBits (originalPick q stages remaining) ∧
      steps≤duration (mass before)*structuralFactor stages.length q := by
  let inputMass:=mass before
  let bound:=inputMass+1
  let cap:=rootCap inputMass stages.length tail
  have limitMass : limit+1≤ inputMass := by
    have size:=point_mass before 2
    rw [r2] at size
    simpa only [unary,RankCompare.unary,List.length_replicate] using size
  have widthMass : q≤ inputMass := by
    have size:=point_mass before 11
    rw [r11] at size
    simpa only [unary,RankCompare.unary,List.length_replicate] using size
  have rowsMass : (rows q stages).length≤ inputMass := by rw [←r0];exact point_mass before 0
  have tailMass : tail.length≤ inputMass := by
    have size:=point_mass before 13
    rw [r13,List.length_cons] at size
    omega
  have dataBound : entryCap bound cap≤dataEnvelope inputMass := mass_data_envelope inputMass stages.length tail (by omega) tailMass
  obtain ⟨steps,final,run,reply,time⟩:=bounded_staged finish (limit+1) q bound cap stages remaining memory before flag tail r0 r2 r4 r11 r13
    (mass_fields before) (by omega) (by omega) (rowsMass.trans (by omega)) (Nat.le_refl cap)
  have bounded:=run.mono (peak_envelope inputMass bound cap dataBound)
  have exactRank:=(evaluate_code_original limit q stages remaining depth).1
  have exactPick:=code_original_pick limit q stages remaining depth
  refine ⟨steps,final,bounded,reply,?_,?_,?_,?_⟩
  · rw [reply.rank,exactRank]
  · rw [reply.spool,exactPick]
  · rw [reply.tool,exactPick]
  · have count : steps≤nodeTime bound cap*(evaluate q stages remaining).nodes := by omega
    exact count.trans
      ((Nat.mul_le_mul_right _ (time_envelope inputMass bound cap dataBound)).trans
        (Nat.mul_le_mul_left _ (evaluate_nodes_one_factor q stages remaining)))
end RootB236.Controller.DFSDriver.Machine
