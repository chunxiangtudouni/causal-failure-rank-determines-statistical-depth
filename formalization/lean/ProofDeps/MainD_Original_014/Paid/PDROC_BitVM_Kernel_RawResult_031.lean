module

public import Paid.PDROC_BitVM_Kernel_NatResult_001
public import Paid.PDROC_BitVM_Kernel_Register_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawResult

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

theorem encoded_last_true (cells : List Cell) : (encodeBits cells).getLast?=some true :=
  List.getLast?_append_cons _ true []

/-- The actual native result has a complete physical prefix because the
original list codec ends in TRUE. No FALSE materializer or runtime width
is assumed; any real residual padding will be cleared by caller code. -/
theorem physical_prefix (cells : List Cell) (right : List Bool)
    (represented : ListBlank.mk right=ListBlank.mk (encodeBits cells)) :
    ∃ suffix,right=encodeBits cells++suffix :=
  PDROC.BitVM.Codec.OutputList.physical_prefix_of_last_true right (encodeBits cells)
    (encoded_last_true cells) represented

abbrev State := TM2.Cfg Alphabet Unit Unit

/-- The singleton list header is the literal original count-one word.
Three real pops expose the complete result Cell to the actual Cell parser. -/
def program (_ : Unit) : TM2.Stmt Alphabet Unit Unit :=
  .pop 0 (fun _ _=>()) (.pop 0 (fun _ _=>()) (.pop 0 (fun _ _=>()) .halt))

def before (contents : Stack → List Bool) : State := ⟨some (),(),contents⟩
def after (contents : Stack → List Bool) (word : List Bool) : State :=
  ⟨none,(),Function.update contents 0 word⟩

theorem singleton_word (cell : Cell) (padding : List Bool) :
    encodeBits [cell]++padding=[true,false,true]++(encodeCellBits cell++([true]++padding)) := by
  simp only [encodeBits,List.length_singleton,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]; rfl

theorem actual_step (cell : Cell) (padding : List Bool) (contents : Stack → List Bool)
    (input : contents 0=encodeBits [cell]++padding) :
    TM2.step program (before contents)=some (after contents (encodeCellBits cell++([true]++padding))) := by
  change some (⟨none,(),Function.update (Function.update (Function.update contents 0 (contents 0).tail)
    0 (contents 0).tail.tail) 0 (contents 0).tail.tail.tail⟩ : State)=_
  rw [input,singleton_word]
  simp only [Function.update_idem]; rfl

theorem runs (cell : Cell) (padding : List Bool) (contents : Stack → List Bool)
    (input : contents 0=encodeBits [cell]++padding) :
    ∃ (run : List State) (final : State),
      run.head?=some (before contents) ∧
      run.IsChain (fun x y=>TM2.step program x=some y) ∧
      run.getLast?=some final ∧ TM2.step program final=none ∧
      final.stk 0=encodeCellBits cell++([true]++padding) ∧ run.length=2 ∧
      ∀ other,other ≠ 0 → final.stk other=contents other := by
  let final := after contents (encodeCellBits cell++([true]++padding))
  have word : final.stk 0=encodeCellBits cell++([true]++padding) := by
    change Function.update contents 0 (encodeCellBits cell++([true]++padding)) 0=_
    exact Function.update_self _ _ _
  refine ⟨[before contents,final],final,rfl,?_,rfl,rfl,word,rfl,?_⟩
  · exact List.isChain_cons_cons.mpr ⟨actual_step cell padding contents input,List.isChain_singleton _⟩
  · intro other different
    change Function.update contents 0 (encodeCellBits cell++([true]++padding)) other=contents other
    rw [Function.update_of_ne different]

theorem supports : TM2.Supports program (Finset.univ : Finset Unit) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    cases label
    trivial

end PDROC.BitVM.Kernel.RawResult
