module

public import PSTR_WordBool_RatPair_Serialize_Code_001

/-! The unchanged frozen reverse/format/finish suffix and its static
transport to either cache pair. Its genuine .done halt port is unexecuted. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

theorem old_suffix {D : Type*} (background : RatInput.Stack → List Bool)
    (context : D) (bit flag negative : Bool) (formatter : WordNatIO.Store)
    (num den source scratch raw : List Bool) :
    ∃ trace : List (RatInput.Encoder.State D),
      trace.head? = some ⟨some .reverseNum,((context,(bit,flag,negative)),formatter),
        RatInput.Encoder.bank background source scratch num.reverse den.reverse [] [] raw [] []⟩ ∧
      trace.IsChain (fun a b => TM2.step (RatInput.Encoder.program .halt) a = some b) ∧
      trace.getLast? = some ⟨some .done,((context,(bit,flag,negative)),(false,false)),
        RatInput.Encoder.bank background source scratch [] [] [] []
          (RatInput.Encoder.prefixBits ++ true :: negative ::
            (encodeNat (PSTRTMIncrement009.valueDigits num) ++
              encodeNat (PSTRTMIncrement009.valueDigits den) ++ raw)) [] []⟩ ∧
      trace.length ≤ 5*(num.length+den.length)+24 := by
  let rat : RatInput.Store := (bit,flag,negative)
  let encN := encodeNat (PSTRTMIncrement009.valueDigits num)
  let encD := encodeNat (PSTRTMIncrement009.valueDigits den)
  let b1 := RatInput.Encoder.bank background source scratch num.reverse den.reverse [] [] raw [] []
  let b2 := RatInput.Encoder.bank background source scratch [] den.reverse num [] raw [] []
  let b3 := RatInput.Encoder.bank background source scratch [] [] num den raw [] []
  let b4 := RatInput.Encoder.bank background source scratch [] [] num [] (encD++raw) [] []
  let b5 := RatInput.Encoder.bank background source scratch [] [] [] [] (encN++encD++raw) [] []
  let b6 := RatInput.Encoder.bank background source scratch [] [] [] []
    (RatInput.Encoder.prefixBits++true::negative::(encN++encD++raw)) [] []
  let s1 : RatInput.Encoder.State D := ⟨some .reverseNum,((context,rat),formatter),b1⟩
  let s2 : RatInput.Encoder.State D := ⟨some .reverseDen,((context,rat),(false,false)),b2⟩
  let s3 : RatInput.Encoder.State D := ⟨some (.den 0),((context,rat),(false,false)),b3⟩
  let s4 : RatInput.Encoder.State D := ⟨some (.num 0),((context,rat),(false,false)),b4⟩
  let s5 : RatInput.Encoder.State D := ⟨some .finish,((context,rat),(false,false)),b5⟩
  let s6 : RatInput.Encoder.State D := ⟨some .done,((context,rat),(false,false)),b6⟩
  obtain ⟨t1,h1,c1,l1,n1⟩ := RatInput.Encoder.actual_reverse .halt false b1 ((context,rat),formatter)
  have last1 : t1.getLast? = some s2 := by
    simpa [b1,s2,b2,RatInput.Encoder.reverse_num_bank,RatInput.Encoder.reverseSource,
      RatInput.Encoder.reverseTarget,RatInput.Encoder.reverseReturn,RatInput.Encoder.bank,
      List.reverse_reverse,List.append_nil] using l1
  let p1 : RatInput.Encoder.Path .halt s1 s2 (num.length+2) :=
    ⟨t1,h1,c1,last1,by simpa [b1,RatInput.Encoder.reverseSource,RatInput.Encoder.bank] using n1.le⟩
  obtain ⟨t2,h2,c2,l2,n2⟩ := RatInput.Encoder.actual_reverse .halt true b2 ((context,rat),(false,false))
  have last2 : t2.getLast? = some s3 := by
    simpa [b2,s3,b3,RatInput.Encoder.reverse_den_bank,RatInput.Encoder.reverseSource,
      RatInput.Encoder.reverseTarget,RatInput.Encoder.reverseReturn,RatInput.Encoder.bank,
      List.reverse_reverse,List.append_nil] using l2
  let p2 : RatInput.Encoder.Path .halt s2 s3 (den.length+2) :=
    ⟨t2,h2,c2,last2,by simpa [b2,RatInput.Encoder.reverseSource,RatInput.Encoder.bank] using n2.le⟩
  obtain ⟨t3,h3,c3,l3,n3⟩ := RatInput.Encoder.actual_format .halt true b3 ((context,rat),(false,false)) rfl rfl
  have last3 : t3.getLast? = some s4 := by
    simpa [b3,s4,b4,encD,RatInput.Encoder.format_den_bank,RatInput.Encoder.reverseTarget,
      RatInput.Encoder.formatReturn,RatInput.Encoder.bank] using l3
  let p3 : RatInput.Encoder.Path .halt s3 s4 (4*den.length+11) :=
    ⟨t3,h3,c3,last3,by simpa [b3,RatInput.Encoder.reverseTarget,RatInput.Encoder.bank] using n3⟩
  obtain ⟨t4,h4,c4,l4,n4⟩ := RatInput.Encoder.actual_format .halt false b4 ((context,rat),(false,false)) rfl rfl
  have last4 : t4.getLast? = some s5 := by
    simpa [b4,s5,b5,encN,RatInput.Encoder.format_num_bank,RatInput.Encoder.reverseTarget,
      RatInput.Encoder.formatReturn,RatInput.Encoder.bank,List.append_assoc] using l4
  let p4 : RatInput.Encoder.Path .halt s4 s5 (4*num.length+11) :=
    ⟨t4,h4,c4,last4,by simpa [b4,RatInput.Encoder.reverseTarget,RatInput.Encoder.bank] using n4⟩
  have finish : TM2.step (RatInput.Encoder.program .halt) s5 = some s6 := by
    simpa [s5,s6,b5,b6,RatInput.Encoder.bank_update_raw,RatInput.Encoder.bank,
      PSTRSymbolicNaturalExport.positive,rat] using
      RatInput.Encoder.finish_step .halt ((context,rat),(false,false)) b5
  let p5 : RatInput.Encoder.Path .halt s5 s6 2 :=
    ⟨[s5,s6],rfl,List.isChain_cons_cons.mpr ⟨finish,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  let whole := (((p1.append p2).append p3).append p4).append p5
  refine ⟨whole.trace,whole.head,whole.chain,whole.last,?_⟩
  have count := whole.count
  omega

theorem phase_path (caller : Statement C) (isX : Bool)
    (trace : List (RatInput.Encoder.State (C × Bool × Bool)))
    (before final : RatInput.Encoder.State (C × Bool × Bool))
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun a b => TM2.step (RatInput.Encoder.program .halt) a = some b))
    (last : trace.getLast? = some final) (active : final.l = some .done) :
    (trace.map (phaseConfiguration isX)).head? = some (phaseConfiguration isX before) ∧
    (trace.map (phaseConfiguration isX)).IsChain (fun a b => TM2.step (program caller) a = some b) ∧
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
  have mapped := LabelMap.actual_path_on (phaseLabel isX) isoProgram (program caller) _ _ _
    first' chain' last' (by
      intro current member point selected
      exact program_phase caller isX point (by intro same;subst point;exact proper current member selected))
  have maps : (trace.map (StackIso.configuration (roles isX))).map
      (LabelMap.configuration (phaseLabel isX)) = trace.map (phaseConfiguration isX) := by
    rw [List.map_map]
    rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer
