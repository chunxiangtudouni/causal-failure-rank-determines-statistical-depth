module
public import RootPaper_Reference_Rank001
public import RootB236_Controller_DFSDriver_Public027

/-! Cost refinement of a high-level query by the already closed actual DFS.
Only an existing primitive is consumed; no new tape or ISA code is built. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference
open Turing PaperProofs.Common PaperProofs.Structure
open PaperProofs.Common.Native RationalControllerComputation
open PaperProofs.Common.Native.PSTRWordBool
open scoped BigOperators
def queryBank (I : Instance) (stage : Nat) (remaining : Finset I.Tool) :
    RootB236.Controller.DFSDriver.Stack→List Bool := fun slot =>
  if slot=0 then RootB236.Controller.DFSDriver.rows I.toolCount (I.compatibility.drop stage) else
  if slot=2 then RootB236.Controller.DFSDriver.unary (I.stageCount+1) else
  if slot=4 then RootB236.Controller.EraseSem.mask remaining else
  if slot=11 then RootB236.Controller.DFSDriver.unary I.toolCount else
  if slot=13 then [false] else []

theorem query_depth (I : Instance) (stage : Nat) : (I.compatibility.drop stage).length≤I.stageCount := by
  change (I.compatibility.drop stage).length≤I.compatibility.length
  rw [List.length_drop]
  exact Nat.sub_le _ _

theorem query_point_mass (I : Instance) (stage : Nat) (remaining : Finset I.Tool)
    (slot : RootB236.Controller.DFSDriver.Stack) :
    (queryBank I stage remaining slot).length≤(I.stageCount+I.toolCount+2)^2 := by
  have depth:=query_depth I stage
  let S:=I.stageCount+I.toolCount+2
  have positive : 1≤S := by dsimp only [S];omega
  have square : S≤S^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤2)
  unfold queryBank
  split_ifs
  · rw [RootB236.Controller.DFSDriver.rows_length]
    exact (Nat.mul_le_mul (by dsimp only [S];omega : I.toolCount+1≤S)
      (depth.trans (by dsimp only [S];omega))).trans_eq (pow_two S).symm
  · change (List.replicate (I.stageCount+1) true).length≤_
    rw [List.length_replicate]
    exact (by dsimp only [S];omega : I.stageCount+1≤S).trans square
  · change (List.ofFn (fun tool : Fin I.toolCount => decide (tool∈remaining))).length≤_
    rw [List.length_ofFn]
    exact (by dsimp only [S];omega : I.toolCount≤S).trans square
  · change (List.replicate I.toolCount true).length≤_
    rw [List.length_replicate]
    exact (by dsimp only [S];omega : I.toolCount≤S).trans square
  · change 1≤_
    exact positive.trans square
  · exact Nat.zero_le _

theorem query_mass (I : Instance) (stage : Nat) (remaining : Finset I.Tool) :
    RootB236.Controller.DFSDriver.Machine.mass (queryBank I stage remaining)≤
      16*(I.stageCount+I.toolCount+2)^2 := by
  have bound:=Finset.sum_le_sum (s:=(Finset.univ : Finset RootB236.Controller.DFSDriver.Stack))
    (fun slot _ => query_point_mass I stage remaining slot)
  simpa only [RootB236.Controller.DFSDriver.Machine.mass,Finset.sum_const,Finset.card_univ,
    show Fintype.card RootB236.Controller.DFSDriver.Stack=16 from rfl,smul_eq_mul] using bound

def queryCoefficient : Nat := RootB236.Controller.DFSDriver.Machine.chargeCoefficient Unit*17^4

theorem queryCoefficient_positive : 0<queryCoefficient := by
  unfold queryCoefficient RootB236.Controller.DFSDriver.Machine.chargeCoefficient
  positivity

theorem query_cost (I : Instance) (stage : Nat) (remaining : Finset I.Tool) :
    ∃ trace final,
      RootB236.Controller.DFSDriver.Machine.Facts (C:=Unit) .halt I.stageCount I.toolCount
        (I.compatibility.drop stage) remaining default (queryBank I stage remaining) [] trace final ∧
      RootB23.GenericRank.decodeRank I.stageCount (final.stk 15).length=(query I stage remaining).rank ∧
      final.stk 13=[(query I stage remaining).pick.isSome] ∧
      final.stk 14=RootB236.Controller.DFSDriver.Machine.pickBits (query I stage remaining).pick ∧
      trace.length+RootB236.Controller.DFSDriver.Machine.clockSum .halt trace≤
        queryCoefficient*(I.stageCount+I.toolCount+2)^8*generalStructureFactor I := by
  obtain ⟨trace,final,facts,_active⟩:=RootB236.Controller.DFSDriver.Machine.Public.root (C:=Unit) .halt
    I.stageCount I.toolCount (I.compatibility.drop stage) remaining (query_depth I stage) default
    (queryBank I stage remaining) (by simp [queryBank]) (by simp [queryBank])
    (by simp [queryBank]) (by simp [queryBank]) (by simp [queryBank])
  have rank:=facts.decoded_rank (query_depth I stage)
  have selected : RootB236.Controller.DFSDriver.Machine.originalPick I.toolCount (I.compatibility.drop stage) remaining=
      (query I stage remaining).pick := by
    rw [(query_spec I stage remaining).2.1]
    unfold RootB236.Controller.DFSDriver.Machine.originalPick
    cases I.compatibility.drop stage <;> rfl
  have factor : RootB23.GenericRank.structuralFactor (I.compatibility.drop stage).length I.toolCount≤
      generalStructureFactor I := RootB23.GenericRank.structuralFactor_mono (query_depth I stage)
  have polynomial:=(RootB236.Controller.DFSDriver.Machine.resource_polynomials (C:=Unit)
    (RootB236.Controller.DFSDriver.Machine.mass (queryBank I stage remaining))).2.2.2
  have mass:=query_mass I stage remaining
  let S:=I.stageCount+I.toolCount+2
  have positive : 1≤S^2 := Nat.one_le_pow _ _ (by dsimp only [S];omega)
  change RootB236.Controller.DFSDriver.Machine.mass (queryBank I stage remaining)≤16*S^2 at mass
  have plus : RootB236.Controller.DFSDriver.Machine.mass (queryBank I stage remaining)+1≤17*S^2 := by omega
  have power:=Nat.pow_le_pow_left plus 4
  have scaled : RootB236.Controller.DFSDriver.Machine.chargeCoefficient Unit*
      (RootB236.Controller.DFSDriver.Machine.mass (queryBank I stage remaining)+1)^4≤queryCoefficient*S^8 := by
    apply (Nat.mul_le_mul_left _ power).trans
    unfold queryCoefficient
    rw [mul_pow,←pow_mul]
    exact le_of_eq (by ring)
  have paid:=facts.charged.trans (Nat.mul_le_mul polynomial factor)
  refine ⟨trace,final,facts,rank.trans (query_spec I stage remaining).1.symm,?_,?_,?_⟩
  · simpa only [selected] using facts.bestFlag
  · simpa only [selected] using facts.firstTool
  · exact paid.trans (Nat.mul_le_mul_right _ scaled)

end RootPaper.Reference
