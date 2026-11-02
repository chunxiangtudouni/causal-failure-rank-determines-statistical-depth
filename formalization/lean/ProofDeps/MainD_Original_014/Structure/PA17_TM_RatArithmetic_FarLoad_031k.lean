module
public import Structure.PA17_TM_RatArithmetic_FarLoad_031j

/-! Uniform all-prefix costs. Width and gap occur solely in these trace
bounds; neither is supplied to any executable field loader. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031

def bankWidth (nxTail dxTail nyTail dyTail : List Bool) : Nat :=
  (false::nxTail).length+(false::dxTail).length+(false::nyTail).length+(false::dyTail).length

def uniformBudget (nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) : Nat :=
  (bankWidth nxTail dxTail nyTail dyTail+1)*(bankWidth nxTail dxTail nyTail dyTail+gap+1)

theorem source_length_le_width (field : SourceField) (nxTail dxTail nyTail dyTail : List Bool) :
    (false::sourceTail field nxTail dxTail nyTail dyTail).length≤ bankWidth nxTail dxTail nyTail dyTail := by
  cases field <;> simp only [sourceTail,bankWidth] <;> omega

theorem source_cost_le_width (field : SourceField) (nxTail dxTail nyTail dyTail : List Bool) :
    sourceCost field dxTail nyTail dyTail≤2*bankWidth nxTail dxTail nyTail dyTail+23 := by
  cases field <;> simp only [sourceCost,bankWidth] <;> omega

theorem navigation_fee_le_width (nxTail dxTail nyTail dyTail : List Bool) :
    navigationFee nxTail dxTail nyTail≤2*bankWidth nxTail dxTail nyTail dyTail+17 := by
  unfold navigationFee bankWidth
  omega

theorem loader_fee_le_uniform (field : SourceField) (nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) :
    navigationFee nxTail dxTail nyTail+
      copyFee (false::sourceTail field nxTail dxTail nyTail dyTail)
        (sourceCost field dxTail nyTail dyTail) gap+2≤128*uniformBudget nxTail dxTail nyTail dyTail gap := by
  let w := bankWidth nxTail dxTail nyTail dyTail
  let m := (false::sourceTail field nxTail dxTail nyTail dyTail).length
  let c := sourceCost field dxTail nyTail dyTail
  have hm : m≤ w := source_length_le_width field nxTail dxTail nyTail dyTail
  have hc : c≤2*w+23 := source_cost_le_width field nxTail dxTail nyTail dyTail
  have hn := navigation_fee_le_width nxTail dxTail nyTail dyTail
  have hsq : m*m≤ w*w := Nat.mul_le_mul hm hm
  have hprod : (2*c+2*gap+41)*m≤(4*w+2*gap+87)*w :=
    Nat.mul_le_mul (by omega) hm
  change navigationFee nxTail dxTail nyTail+(4*m^2+(2*c+2*gap+41)*m+3*c+3*gap+29)+2≤
    128*((w+1)*(w+gap+1))
  nlinarith

theorem original_loader_uniform_contract (p : Nat) (field : SourceField) (memory : Fin (p+1)) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail : List Bool) (gap inputLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (originalLoader p field)
      (PA17TMDivisionCompose006.blockCfg memory
        (⟨0,headerTape sx counter nxTail dxTail nyTail dyTail gap⟩ : MachineState 435)) trace
      (PA17TMDivisionCompose006.blockCfg memory (⟨435,Turing.Tape.mk₂
        (destinationLeft gap (globalSourceLeft sx counter nxTail dxTail nyTail dyTail))
        (PA17TMRatArithmeticCopy006.workspace
          (memory.val.testBit (sourceSlot field)::sourceTail field nxTail dxTail nyTail dyTail))⟩ : MachineState 435)) ∧
      trace.length≤128*uniformBudget nxTail dxTail nyTail dyTail gap ∧
      ∀ k, visitedSpace (originalLoader p field) inputLength (trace.take k) ≤
        inputLength+256*uniformBudget nxTail dxTail nyTail dyTail gap+1 := by
  obtain ⟨trace,hr,hl,hs⟩ := original_loader_contract p field memory sx counter nxTail dxTail nyTail dyTail gap inputLength
  rw [source_finish_global] at hr
  have hb := loader_fee_le_uniform field nxTail dxTail nyTail dyTail gap
  refine ⟨trace,hr,hl.trans hb,?_⟩
  intro k
  have h := hs k
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
