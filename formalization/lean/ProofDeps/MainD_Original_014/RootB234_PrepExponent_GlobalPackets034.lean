module

public import RootB234_PrepExponent_GlobalPaths033

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.Global
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

def bank (background : Stack → List Bool) (cache exponent input left right result : List Bool) : Stack → List Bool :=
  fun slot => if slot=7 then cache else if slot=11 then exponent else if slot=15 then input
    else if slot=12 then left else if slot=13 then right else if slot=3 then result
    else if slot=2 ∨ slot=4 ∨ slot=5 ∨ slot=6 ∨ slot=10 ∨ slot=14 then [] else background slot

theorem bank_empty (background : Stack → List Bool) (cache exponent input : List Bool) :
    bank background cache exponent input [] [] []=QLoop.bank background cache exponent input [] := by
  funext slot
  fin_cases slot <;> rfl

theorem atBank_self (roles : Stack ≃ Stack) (contents : Stack → List Bool) (input : List Bool)
    (source : contents (roles 15)=input) (temporary : contents (roles 4)=[]) :
    RatPacketTransport.atBank roles contents input [] (contents (roles 2))=contents := by
  funext slot
  unfold RatPacketTransport.atBank
  split_ifs with hs ht hd
  · subst slot;exact source.symm
  · subst slot;exact temporary.symm
  · subst slot;rfl
  · rfl

/-- A real packet call in the full exponent graph. The exact physical
bank is the caller's bank; only the three statically selected roles change. -/
theorem packet_from_state (caller : Statement C) (before : State C) (site : PacketSite)
    (value : Rat) (tail : List Bool) (active : before.l=some (.packet site 0))
    (source : before.stk (packetRoles site 15)=RatInput.Encoder.packet value tail)
    (temporary : before.stk (packetRoles site 4)=[]) :
    ∃ part : Segment caller before
      (state (packetNext site) (before.var.1,false,false)
        (RatPacketTransport.atBank (packetRoles site) before.stk
          (if packetCopy site then RatInput.Encoder.packet value tail else tail) []
          (RatInput.Encoder.packet value (before.stk (packetRoles site 2))))),
      part.trace.length ≤ 3*RatInput.Encoder.fieldSize value+14 := by
  obtain ⟨run,facts⟩ := RatPacketTransport.at_actual (packetRoles site) (packetCopy site)
    before.stk before.var.1 before.var.2 value tail (before.stk (packetRoles site 2))
  have path := label_path (packetLabel site) (RatPacketTransport.atProgram (packetRoles site) (packetCopy site)) caller
    4 rfl run _ _ facts.first facts.chain facts.last rfl
    (by intro point different;simp only [packetLabel,different,ite_false,program])
  have firstState : LabelMap.configuration (packetLabel site)
      (RatPacketTransport.atState (packetRoles site) before.stk 0 before.var.1 before.var.2
        (RatInput.Encoder.packet value tail) [] (before.stk (packetRoles site 2)))=before := by
    cases before with
    | mk position memory contents =>
      change position=some (.packet site 0) at active
      subst position
      unfold LabelMap.configuration RatPacketTransport.atState
      change (⟨some (.packet site 0),memory,_⟩ : State C)=_
      rw [atBank_self _ _ _ source temporary]
  have lastState : LabelMap.configuration (packetLabel site)
      (RatPacketTransport.atState (packetRoles site) before.stk 4 before.var.1 (false,false)
        (if packetCopy site then RatInput.Encoder.packet value tail else tail) []
        (RatInput.Encoder.packet value (before.stk (packetRoles site 2))))=
      state (packetNext site) (before.var.1,false,false)
        (RatPacketTransport.atBank (packetRoles site) before.stk
          (if packetCopy site then RatInput.Encoder.packet value tail else tail) []
          (RatInput.Encoder.packet value (before.stk (packetRoles site 2)))) := rfl
  exact ⟨⟨run.map (LabelMap.configuration (packetLabel site)),path.1.trans (congrArg some firstState),
    path.2.1,path.2.2.trans (congrArg some lastState)⟩,by simpa only [List.length_map] using facts.count⟩

theorem copyQ_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cacheTail exponent : List Bool) (value : Rat) :
    ∃ part : Segment caller
      (state (.packet .copyQ 0) memory (bank background (RatInput.Encoder.packet value cacheTail) exponent [] [] [] []))
      (state (.nat default) (memory.1,false,false)
        (bank background (RatInput.Encoder.packet value cacheTail) exponent (RatInput.Encoder.packet value []) [] [] [])),
      part.trace.length ≤ 3*RatInput.Encoder.fieldSize value+14 := by
  let before := state (.packet .copyQ 0) memory (bank background (RatInput.Encoder.packet value cacheTail) exponent [] [] [] [])
  obtain ⟨part,count⟩ := packet_from_state caller before .copyQ value cacheTail rfl rfl rfl
  have endpoint : state (packetNext .copyQ) (before.var.1,false,false)
      (RatPacketTransport.atBank (packetRoles .copyQ) before.stk
        (if packetCopy .copyQ then RatInput.Encoder.packet value cacheTail else cacheTail) []
        (RatInput.Encoder.packet value (before.stk (packetRoles .copyQ 2))))=
      state (.nat default) (memory.1,false,false)
        (bank background (RatInput.Encoder.packet value cacheTail) exponent (RatInput.Encoder.packet value []) [] [] []) := by
    unfold state
    congr 1
    funext slot
    fin_cases slot <;> rfl
  exact ⟨⟨part.trace,part.first,part.chain,part.last.trans (congrArg some endpoint)⟩,count⟩

theorem nat_bank (background : Stack → List Bool) (cache exponent tail : List Bool) (number : Nat)
    (source : background 8=B23_4_RatWordPrep.NatField.packet number []) :
    NatToRat.bank (bank background cache exponent [] [] [] [])
      (B23_4_RatWordPrep.NatField.packet number []) [] [] tail=bank background cache exponent tail [] [] [] := by
  funext slot
  fin_cases slot <;> try rfl
  exact source.symm

theorem nat_state (background : Stack → List Bool) (cache exponent tail : List Bool) (number : Nat)
    (source : background 8=B23_4_RatWordPrep.NatField.packet number []) (point : NatToRat.Label) (memory : Store C) :
    LabelMap.configuration natLabel
      (NatToRat.state (bank background cache exponent [] [] [] []) point memory
        (B23_4_RatWordPrep.NatField.packet number []) [] [] tail)=
      state (natLabel point) memory (bank background cache exponent tail [] [] []) := by
  unfold LabelMap.configuration NatToRat.state state
  rw [nat_bank background cache exponent tail number source]
  rfl

theorem nat_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cache exponent tail : List Bool) (number : Nat)
    (source : background 8=B23_4_RatWordPrep.NatField.packet number []) :
    ∃ part : Segment caller
      (state (.nat default) memory (bank background cache exponent tail [] [] []))
      (state (.literal .twiceN) (memory.1,false,false)
        (bank background cache exponent (RatInput.Encoder.packet (number : Rat) tail) [] [] [])),
      part.trace.length ≤ 13*NatToRat.scale (bank background cache exponent [] [] [] []) number tail := by
  obtain ⟨run,facts⟩ := NatToRat.actual_bounded (bank background cache exponent [] [] [] []) memory number tail
  have path := label_path natLabel (NatToRat.program .halt) caller .done rfl run _ _ facts.first facts.chain facts.last rfl
    (by intro point different;simp only [natLabel,different,ite_false,program])
  have firstState := nat_state background cache exponent tail number source default memory
  have lastState := nat_state background cache exponent (RatInput.Encoder.packet (number : Rat) tail) number source .done (memory.1,false,false)
  exact ⟨⟨run.map (LabelMap.configuration natLabel),path.1.trans (congrArg some firstState),
    path.2.1,path.2.2.trans (congrArg some lastState)⟩,by simpa only [List.length_map] using facts.time⟩

theorem bank_update15 (background : Stack → List Bool) (cache exponent input left right result next : List Bool) :
    Function.update (bank background cache exponent input left right result) 15 next=
      bank background cache exponent next left right result := by
  funext slot
  fin_cases slot <;> rfl

theorem literal_step (caller : Statement C) (site : MulSite) (memory : Store C) (before : Stack → List Bool) :
    TM2.step (program caller) (state (.literal site) memory before)=
      some (state (.mul site default) memory (Function.update before 15 (RatInput.Encoder.packet (2 : Rat) []++before 15))) := by
  change some (TM2.stepAux (prepend 15 _ _) memory before)=_
  rw [prepend_step]
  rfl

end RootB234.PrepExponent.Global
