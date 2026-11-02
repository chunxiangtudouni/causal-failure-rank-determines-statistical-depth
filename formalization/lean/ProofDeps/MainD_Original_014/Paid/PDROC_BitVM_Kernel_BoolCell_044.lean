module

public import Paid.PDROC_BitVM_Kernel_Register_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.BoolCell

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

abbrev State := TM2.Cfg Alphabet Unit Bool

/-- The signal is an ACTUAL finite caller store bit, initialized by a
real caller transition from observed flags. Four literal/bit writes form
the original Nat0/Nat1 Cell; no encoded word is supplied as input. -/
def program (_ : Unit) : TM2.Stmt Alphabet Unit Bool :=
  .push 0 (fun signal=>signal) (.push 0 (fun _=>false)
    (.push 0 (fun _=>true) (.push 0 (fun _=>false) .halt)))

def value (signal : Bool) : Cell := .natural (if signal then 1 else 0)

def before (contents : Stack → List Bool) (signal : Bool) : State := ⟨some (),signal,contents⟩
def after (contents : Stack → List Bool) (signal : Bool) : State :=
  ⟨none,signal,Function.update contents 0 (encodeCellBits (value signal)++contents 0)⟩

theorem actual_step (contents : Stack → List Bool) (signal : Bool) :
    TM2.step program (before contents signal)=some (after contents signal) := by
  change some (⟨none,signal,Function.update (Function.update (Function.update
    (Function.update contents 0 (signal::contents 0)) 0 (false::signal::contents 0))
      0 (true::false::signal::contents 0)) 0 (false::true::false::signal::contents 0)⟩ : State)=_
  simp only [Function.update_idem]
  cases signal <;> rfl

theorem runs (contents : Stack → List Bool) (signal : Bool) :
    ∃ (run : List State) (final : State),
      run.head?=some (before contents signal) ∧
      run.IsChain (fun a b=>TM2.step program a=some b) ∧
      run.getLast?=some final ∧ TM2.step program final=none ∧ final.var=signal ∧
      final.stk 0=encodeCellBits (value signal)++contents 0 ∧ run.length=2 ∧
      ∀ role,role ≠ 0 → final.stk role=contents role := by
  have word : (after contents signal).stk 0=encodeCellBits (value signal)++contents 0 := by
    change Function.update contents 0 (encodeCellBits (value signal)++contents 0) 0=_
    exact Function.update_self _ _ _
  refine ⟨[before contents signal,after contents signal],after contents signal,rfl,?_,rfl,rfl,rfl,word,rfl,?_⟩
  · exact List.isChain_cons_cons.mpr ⟨actual_step contents signal,List.isChain_singleton _⟩
  · intro role different
    change Function.update contents 0 (encodeCellBits (value signal)++contents 0) role=contents role
    rw [Function.update_of_ne different]

theorem supports : TM2.Supports program (Finset.univ : Finset Unit) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    cases label
    trivial

end PDROC.BitVM.Kernel.BoolCell
