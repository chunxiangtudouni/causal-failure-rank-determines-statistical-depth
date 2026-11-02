module
public import RootB236_Controller_DFSDriver_Frames011
public import RootB236_Controller_DFSDriver_Data009

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing RootB23.GenericRank PaperProofs.Structure
open PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*} {q : Nat}

def firstBank (bg : Stack → List Bool) (limit skip : Nat) (best : CodeBest q) (tail : List Bool)
    (eligible remaining : Finset (Fin q)) : Stack → List Bool :=
  SelectErase.bank (dataBank bg limit skip best tail) (EraseSem.mask eligible) (EraseSem.mask remaining)
    [] [] [] [] (unary q) []

/-- The list in this invariant is the actual pending suffix, not a rescanned child mask. -/
def ScanResult (bg : Stack → List Bool) (context : C) (order : Ordering) (limit skip : Nat)
    (best : CodeBest q) (frame : List Bool) (remaining : Finset (Fin q))
    (tools : List (Fin q)) (final : State C) : Prop :=
  (∃ tool later bits,tools=tool::later ∧ ControllerCandidate.pending (tool.val+1) bits=later.map Fin.val ∧
    tool.val+1+bits.length=q ∧
    final=state (.inr (.pushBoot false)) (context,false,false,order)
      (scanBank bg limit skip best frame bits (EraseSem.mask (remaining.erase tool))
        (EraseSem.mask remaining) tool.val (tool.val+1))) ∨
  (tools=[] ∧ final=state (.inl (.merge RankMerge.entry)) (context,true,true,order)
    (scanBank bg limit skip best frame [] (EraseSem.mask remaining) (EraseSem.mask remaining) 0 q))

theorem core_state (point : Core) (memory : Store C) (before : Stack → List Bool) :
    LabelMap.configuration coreMap (DFSDriver.state point memory before)=state (coreMap point) memory before := rfl

theorem select_current (finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (limit skip : Nat) (best : CodeBest q) (frame : List Bool) (eligible remaining : Finset (Fin q)) :
    ∃ steps final,Run finish (state (.inl (.select SelectErase.entry)) memory (firstBank bg limit skip best frame eligible remaining)) final steps ∧
      ScanResult bg memory.1 memory.2.2.2 limit skip best frame remaining (genericRankCandidates q eligible remaining) final ∧
      steps≤32*(q+1) := by
  obtain ⟨trace,final,facts,path⟩:=select_path .halt .halt .halt .halt (dataBank bg limit skip best frame)
    (BestUpdate.storeIso.symm memory) (EraseSem.mask eligible) (EraseSem.mask remaining) []
    (by simp only [EraseSem.mask_length])
  have run:=core_path finish path
  rw [select_initial] at run
  dsimp only [scanState] at run
  rw [core_state] at run
  have first : state (coreMap (.select SelectErase.entry)) memory
      (SelectErase.bank (dataBank bg limit skip best frame) (EraseSem.mask eligible) (EraseSem.mask remaining) [] [] [] []
        (unary (EraseSem.mask eligible).length) [])=
      state (.inl (.select SelectErase.entry)) memory (firstBank bg limit skip best frame eligible remaining) := by
    simp only [EraseSem.mask_length];rfl
  change Run finish (state (coreMap (.select SelectErase.entry)) memory _) _ _ at run
  rw [first] at run
  refine ⟨trace.length-1,_,run,?_,?_⟩
  · have outcome:=facts.outcome.original
    rcases outcome with ⟨tool,bits,head,values,width,ended⟩ | ⟨empty,ended⟩
    · obtain ⟨later,shape⟩:=List.head?_eq_some_iff.mp head
      rw [shape,List.map_cons] at values
      refine Or.inl ⟨tool,later,bits,shape,(List.cons.inj values).2.symm,width,?_⟩
      rw [ended]
      simp only [scanBank,EraseSem.mask_length]
      rfl
    · refine Or.inr ⟨empty,?_⟩
      rw [ended]
      simp only [scanBank,EraseSem.mask_length]
      rfl
  · have bound:=facts.count
    simp only [List.length_nil,EraseSem.mask_length,Nat.zero_add] at bound
    omega

/-- Subsequent calls clear the returned child mask and scan only the saved pending suffix. -/
theorem resume_current (finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (limit skip : Nat) (best : CodeBest q) (frame : List Bool) (remaining : Finset (Fin q))
    (bits current : List Bool) (oldTool k : Nat) (tools : List (Fin q))
    (extent : k+bits.length=q) (pending : ControllerCandidate.pending k bits=tools.map Fin.val) :
    ∃ steps final,Run finish (state (.inl (.resume .clear)) memory
      (scanBank bg limit skip best frame bits current (EraseSem.mask remaining) oldTool k)) final steps ∧
      ScanResult bg memory.1 memory.2.2.2 limit skip best frame remaining tools final ∧
      steps≤32*(current.length+oldTool+q+1) := by
  obtain ⟨trace,final,facts,path⟩:=resume_path .halt .halt .halt .halt (dataBank bg limit skip best frame)
    (BestUpdate.storeIso.symm memory) bits (EraseSem.mask remaining) current (unary oldTool) k
    (by simpa only [EraseSem.mask_length] using extent)
  have run:=core_path finish path
  rw [resume_initial] at run
  dsimp only [scanState] at run
  rw [core_state] at run
  simp only [EraseSem.mask_length] at run
  change Run finish (state (.inl (.resume .clear)) memory _) _ _ at run
  have canonical : SelectErase.bank (dataBank bg limit skip best frame) bits current (unary oldTool) (unary k) []
      (EraseSem.mask remaining).reverse (unary q) []=
      scanBank bg limit skip best frame bits current (EraseSem.mask remaining) oldTool k := by
    unfold scanBank;rw [EraseSem.mask_length]
  rw [canonical] at run
  refine ⟨trace.length-1,_,run,?_,?_⟩
  · rcases facts.outcome with ⟨index,rest,inside,width,selected,ended⟩ | ⟨none,ended⟩
    · have values : tools.map Fin.val=index::ControllerCandidate.pending (index+1) rest := pending.symm.trans selected
      cases tools with
      | nil => cases values
      | cons tool later =>
        obtain ⟨position,other⟩:=List.cons.inj values
        refine Or.inl ⟨tool,later,rest,rfl,?_,?_,?_⟩
        · rw [position];exact other.symm
        · rw [position];simpa only [EraseSem.mask_length] using width
        · rw [←position] at ended
          rw [ended,SelectErase.eraseMask_original]
          simp only [scanBank,EraseSem.mask_length]
          rfl
    · refine Or.inr ⟨List.map_eq_nil_iff.mp (pending.symm.trans none),?_⟩
      rw [ended]
      simp only [scanBank,EraseSem.mask_length]
      rfl
  · have bound:=facts.count
    simp only [unary,RankCompare.unary,List.length_replicate,EraseSem.mask_length] at bound
    omega
end RootB236.Controller.DFSDriver.Machine
