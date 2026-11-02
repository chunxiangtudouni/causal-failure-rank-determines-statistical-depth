module

public import PSTR_WordBool_RatPair_Serialize_Transport_001

/-! One fixed, physical four-field path: y then x. The two constant
prefix removals and both footer/count pushes are actual paid transitions. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

/-- The original list codec has only ONE global terminal TRUE.  The y
footer is pushed once, while boot-X does not push a per-datum footer. -/
def program2 (caller : Statement C) (point : Label) : Statement C :=
  match point with
  | .boot true => .load (setMode true) (.goto (fun _ => .phase true .reverseNum))
  | other => program caller other

def datumBits (negative : Bool) (numerator denominator : List Bool) : List Bool :=
  true :: negative :: (encodeNat (PSTRTMIncrement009.valueDigits numerator) ++
    encodeNat (PSTRTMIncrement009.valueDigits denominator))

def output2 (negativeX negativeY : Bool) (nx dx ny dy : List Bool) : List Bool :=
  encodeNat 2 ++ datumBits negativeX nx dx ++ fields negativeY ny dy

theorem program2_phase (caller : Statement C) (isX : Bool) (point : RatInput.Encoder.Label)
    (proper : point ≠ .done) :
    program2 caller (phaseLabel isX point) = LabelMap.statement (phaseLabel isX)
      (StackIso.statement (roles isX)
        (RatInput.Encoder.program (C := C × Bool × Bool) .halt point)) := by
  simp only [phaseLabel,proper,ite_false,program2,program]

theorem boot_true_step2 (caller : Statement C) (memory : Store C)
    (contents : RatInput.Stack → List Bool) :
    TM2.step (program2 caller) ⟨some (.boot true),memory,contents⟩ =
      some ⟨some (.phase true .reverseNum),setMode true memory,contents⟩ := rfl

theorem phase_path2 (caller : Statement C) (isX : Bool)
    (trace : List (RatInput.Encoder.State (C × Bool × Bool)))
    (before final : RatInput.Encoder.State (C × Bool × Bool))
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun a b => TM2.step (RatInput.Encoder.program .halt) a = some b))
    (last : trace.getLast? = some final) (active : final.l = some .done) :
    (trace.map (phaseConfiguration isX)).head? = some (phaseConfiguration isX before) ∧
    (trace.map (phaseConfiguration isX)).IsChain (fun a b => TM2.step (program2 caller) a = some b) ∧
    (trace.map (phaseConfiguration isX)).getLast? = some (phaseConfiguration isX final) := by
  let isoProgram := fun point => StackIso.statement (roles isX)
    (RatInput.Encoder.program (C := C × Bool × Bool) .halt point)
  have first' : (trace.map (StackIso.configuration (roles isX))).head? =
      some (StackIso.configuration (roles isX) before) := by rw [List.head?_map,first,Option.map_some]
  have last' : (trace.map (StackIso.configuration (roles isX))).getLast? =
      some (StackIso.configuration (roles isX) final) := by rw [List.getLast?_map,last,Option.map_some]
  have chain' := StackIso.chain_configuration_on (roles isX) (RatInput.Encoder.program .halt)
    isoProgram trace chain (by intro current member point selected;rfl)
  have proper := NativeMulLink.no_early_halt_port isoProgram .done rfl _ _ chain' last' active
  have mapped := LabelMap.actual_path_on (phaseLabel isX) isoProgram (program2 caller) _ _ _
    first' chain' last' (by
      intro current member point selected
      exact program2_phase caller isX point (by intro same;subst point;exact proper current member selected))
  have maps : (trace.map (StackIso.configuration (roles isX))).map
      (LabelMap.configuration (phaseLabel isX)) = trace.map (phaseConfiguration isX) := by
    rw [List.map_map]
    rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩


theorem actual_phase2 (caller : Statement C) (isX : Bool) (contents : RatInput.Stack → List Bool)
    (context : C × Bool × Bool) (bit flag negative : Bool) (formatter : WordNatIO.Store)
    (num den raw : List Bool) :
    ∃ trace : List (State C),
      trace.head? = some ⟨some (.phase isX .reverseNum),((context,(bit,flag,negative)),formatter),
        phaseBank isX contents num.reverse den.reverse [] [] raw [] []⟩ ∧
      trace.IsChain (fun a b => TM2.step (program2 caller) a = some b) ∧
      trace.getLast? = some ⟨some (.trim isX),((context,(bit,flag,negative)),(false,false)),
        phaseBank isX contents [] [] [] []
          (RatInput.Encoder.prefixBits ++ true :: negative ::
            (encodeNat (PSTRTMIncrement009.valueDigits num) ++
              encodeNat (PSTRTMIncrement009.valueDigits den) ++ raw)) [] []⟩ ∧
      trace.length ≤ 5*(num.length+den.length)+24 := by
  obtain ⟨trace,first,chain,last,count⟩ := old_suffix
    (StackIso.slots (roles isX).symm contents) context bit flag negative formatter
    num den (contents 15) (contents 7) raw
  have path := phase_path2 caller isX trace _ _ first chain last rfl
  refine ⟨trace.map (phaseConfiguration isX),?_,path.2.1,?_,?_⟩
  · rw [path.1,phase_configuration]
    rfl
  · rw [path.2.2,phase_configuration]
    rfl
  · simpa only [List.length_map] using count



structure Path2 (caller : Statement C) (before final : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head? = some before
  chain : trace.IsChain (fun a b => TM2.step (program2 caller) a = some b)
  last : trace.getLast? = some final
  count : trace.length ≤ budget

def Path2.append {caller : Statement C} {before middle final : State C} {frontBudget backBudget : Nat}
    (front : Path2 caller before middle frontBudget) (back : Path2 caller middle final backBudget) :
    Path2 caller before final (frontBudget+backBudget-1) := by
  have shape : middle :: back.trace.tail = back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.head
    rw [same]
    rfl
  have size := congrArg List.length shape
  simp only [List.length_cons] at size
  refine ⟨front.trace ++ back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.head]
    rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have first := front.count
    have second := back.count
    simp only [List.length_append]
    omega

theorem actual_fields2 (caller : Statement C) (background : RatInput.Stack → List Bool)
    (context : C) (negativeX negativeY : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (nx dx ny dy : List Bool) :
    ∃ trace : List (State C),
      trace.head? = some (entry background context negativeX negativeY memory formatter nx dx ny dy) ∧
      trace.IsChain (fun a b => TM2.step (program2 caller) a = some b) ∧
      trace.getLast? = some ⟨some .done,
        (((context,negativeX,negativeY),(memory.1,memory.2.1,negativeX)),(false,false)),
        bank background [] [] [] [] [] [] (output2 negativeX negativeY nx dx ny dy) [] []⟩ ∧
      trace.length ≤ 5*(nx.length+dx.length+ny.length+dy.length)+60 := by
  let ctx := (context,negativeX,negativeY)
  let yMemory : Store C := ((ctx,(memory.1,memory.2.1,negativeY)),formatter)
  let yDone : Store C := ((ctx,(memory.1,memory.2.1,negativeY)),(false,false))
  let xMemory : Store C := ((ctx,(memory.1,memory.2.1,negativeX)),(false,false))
  let fy := fields negativeY ny dy
  let fx := datumBits negativeX nx dx
  let b0 := bank background nx.reverse dx.reverse ny.reverse dy.reverse [] [] [] [] []
  let b1 := bank background nx.reverse dx.reverse ny.reverse dy.reverse [] [] [true] [] []
  let b2 := bank background nx.reverse dx.reverse [] [] [] [] (RatInput.Encoder.prefixBits++fy) [] []
  let b3 := bank background nx.reverse dx.reverse [] [] [] [] fy [] []
  let b4 := bank background nx.reverse dx.reverse [] [] [] [] fy [] []
  let b5 := bank background [] [] [] [] [] [] (RatInput.Encoder.prefixBits++fx++fy) [] []
  let b6 := bank background [] [] [] [] [] [] (output2 negativeX negativeY nx dx ny dy) [] []
  let s0 : State C := entry background context negativeX negativeY memory formatter nx dx ny dy
  let s1 : State C := ⟨some (.phase false .reverseNum),yMemory,b1⟩
  let s2 : State C := ⟨some (.trim false),yDone,b2⟩
  let s3 : State C := ⟨some (.boot true),yDone,b3⟩
  let s4 : State C := ⟨some (.phase true .reverseNum),xMemory,b4⟩
  let s5 : State C := ⟨some (.trim true),xMemory,b5⟩
  let s6 : State C := ⟨some .done,xMemory,b6⟩
  have start : TM2.step (program2 caller) s0 = some s1 := by
    simpa [program2,s0,s1,entry,yMemory,ctx,setMode,b0,b1,bank_update_raw,bank] using
      boot_step caller false (((context,negativeX,negativeY),memory),formatter) b0
  let p0 : Path2 caller s0 s1 2 :=
    ⟨[s0,s1],rfl,List.isChain_cons_cons.mpr ⟨start,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  obtain ⟨ty,hy,cy,ly,nyBound⟩ := actual_phase2 caller false b1 ctx
    memory.1 memory.2.1 negativeY formatter ny dy [true]
  have firstY : ty.head? = some s1 := by
    simpa [s1,yMemory,b1,phaseBank_bank] using hy
  have lastY : ty.getLast? = some s2 := by
    simpa [s2,yDone,b1,b2,phaseBank_bank,fy,fields] using ly
  let p1 : Path2 caller s1 s2 (5*(ny.length+dy.length)+24) := ⟨ty,firstY,cy,lastY,nyBound⟩
  have trimY : TM2.step (program2 caller) s2 = some s3 := by
    simpa [program2,s2,s3,b2,b3,bank_update_raw] using trim_y_step caller yDone b3 fy
  let p2 : Path2 caller s2 s3 2 :=
    ⟨[s2,s3],rfl,List.isChain_cons_cons.mpr ⟨trimY,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  have bootX : TM2.step (program2 caller) s3 = some s4 := by
    simpa [s3,s4,yDone,xMemory,ctx,setMode,b3,b4,bank_update_raw,bank] using boot_true_step2 caller yDone b3
  let p3 : Path2 caller s3 s4 2 :=
    ⟨[s3,s4],rfl,List.isChain_cons_cons.mpr ⟨bootX,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  obtain ⟨tx,hx,cx,lx,nxBound⟩ := actual_phase2 caller true b4 ctx
    memory.1 memory.2.1 negativeX (false,false) nx dx fy
  have firstX : tx.head? = some s4 := by
    simpa [s4,xMemory,b4,phaseBank_bank] using hx
  have lastX : tx.getLast? = some s5 := by
    simpa [s5,xMemory,b4,b5,phaseBank_bank,fx,datumBits,List.cons_append,List.append_assoc] using lx
  let p4 : Path2 caller s4 s5 (5*(nx.length+dx.length)+24) := ⟨tx,firstX,cx,lastX,nxBound⟩
  have trimX : TM2.step (program2 caller) s5 = some s6 := by
    simpa [program2,s5,s6,b5,b6,bank_update_raw,output2,fx,fy,List.append_assoc] using
      trim_x_step caller xMemory (bank background [] [] [] [] [] [] (fx++fy) [] []) (fx++fy)
  let p5 : Path2 caller s5 s6 2 :=
    ⟨[s5,s6],rfl,List.isChain_cons_cons.mpr ⟨trimX,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  let whole := ((((p0.append p1).append p2).append p3).append p4).append p5
  refine ⟨whole.trace,whole.head,whole.chain,whole.last,?_⟩
  have count := whole.count
  omega

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer
