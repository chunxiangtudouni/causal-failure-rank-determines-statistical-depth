module

public import B23_4_RatWordPrep_SeqCmp_WordFinishPackets_128
public import B23_4_RatWordPrep_SeqCmp_WordFinishBinary_129

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

abbrev Data := RatInput.Stack → List Rat
def DataSlot (slot : RatInput.Stack) : Prop := slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=15
instance dataSlotDecidable (slot : RatInput.Stack) : Decidable (DataSlot slot) := by unfold DataSlot; infer_instance

/-- Proof-side packet lists describe the actual four non-work banks.
The source does not read this model or a supplied computed answer. -/
def layout (frame : RatInput.Stack → List Bool) (data : Data) : RatInput.Stack → List Bool :=
  fun slot => if DataSlot slot then PacketLists.rats (data slot) [] else
    if Owned slot then [] else frame slot

theorem layout_owned (frame : RatInput.Stack → List Bool) (data : Data) :
    ∀ slot,Owned slot→layout frame data slot=[] := by
  intro slot selected
  fin_cases slot <;> first | rfl | simp [Owned] at selected

def packetData (job : Job) (data : Data) (x : Rat) (tail : List Rat) : Data :=
  Function.update (if copy job then data else Function.update data (source job) tail)
    (destination job) (x::data (destination job))

theorem packetBank_layout (job : Job) (frame : RatInput.Stack → List Bool) (data : Data)
    (x : Rat) (tail : List Rat) (head : data (source job)=x::tail) :
    RootB234.RatPacketTransport.atBank (roles job) (layout frame data)
      (if copy job then RatInput.Encoder.packet x (PacketLists.rats tail []) else PacketLists.rats tail []) []
      (RatInput.Encoder.packet x (layout frame data (destination job)))=
      layout frame (packetData job data x tail) := by
  unfold RootB234.RatPacketTransport.atBank
  rw [roles_source,roles_scratch,roles_destination]
  cases job <;>
    (dsimp only [source] at head
     funext slot
     fin_cases slot <;>
       simp [source,destination,copy,
         layout,DataSlot,Owned,packetData,Function.update,head,PacketLists.rats])

theorem actual_packet_data (caller : Statement C) (job : Job) (before : State C)
    (frame : RatInput.Stack → List Bool) (data : Data) (x : Rat) (tail : List Rat)
    (active : before.l=some (.packet job 0)) (shape : before.stk=layout frame data)
    (head : data (source job)=x::tail) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (next job) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=layout frame (packetData job data x tail) ∧
      run.trace.length≤3*RatInput.Encoder.fieldSize x+14 := by
  have sourcePacket : before.stk (roles job 15)=RatInput.Encoder.packet x (PacketLists.rats tail []) := by
    rw [shape,roles_source]
    cases job <;> change PacketLists.rats (data _) []=_ <;> rw [head] <;> rfl
  have scratch : before.stk (roles job 4)=[] := by rw [shape,roles_scratch]; rfl
  obtain ⟨final,run,port,context,contents,time⟩ := actual_packet caller (packetLabel job) (roles job)
    (copy job) before x (PacketLists.rats tail []) active sourcePacket scratch
      (by intro point different; simp only [packetLabel,different,ite_false,program])
  refine ⟨final,run,port,context,?_,time⟩
  rw [contents,shape,roles_destination]
  exact packetBank_layout job frame data x tail head

theorem binaryBank_layout (frame : RatInput.Stack → List Bool) (data : Data)
    (result : Rat) (tail : List Rat) :
    binaryBank (layout frame data) result (PacketLists.rats tail [])=
      layout frame (Function.update data 15 (result::tail)) := by
  funext slot
  fin_cases slot <;> simp [binaryBank,layout,DataSlot,Owned,Function.update,PacketLists.rats]

theorem pair_layout (before : State C) (frame : RatInput.Stack → List Bool) (data : Data)
    (x y : Rat) (tail : List Rat) (shape : before.stk=layout frame data) (head : data 15=x::y::tail) :
    before.stk 15=RatPair.input x y (PacketLists.rats tail []) := by
  rw [shape]
  change PacketLists.rats (data 15) []=_
  rw [head]
  exact RatPair.two_packet_format x y (PacketLists.rats tail [])

theorem actual_division_data (caller : Statement C) (high : Bool) (before : State C)
    (frame : RatInput.Stack → List Bool) (data : Data) (x y : Rat) (tail : List Rat)
    (active : before.l=some (.divide high default)) (shape : before.stk=layout frame data)
    (head : data 15=x::y::tail) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.packet (if high then .parkHigh else .parkLow) 0) ∧
      final.var.2.2.2=before.var.2.2.2 ∧ final.stk=layout frame (Function.update data 15 ((x/y)::tail)) ∧
      run.trace.length≤RatBinary.time RatMulDiv.divCoefficient before.stk x y (PacketLists.rats tail []) (before.stk 7) := by
  have clean : ∀ slot,Owned slot→before.stk slot=[] := by rw [shape]; exact layout_owned frame data
  obtain ⟨final,run,port,context,contents,time⟩ := actual_division caller high before x y
    (PacketLists.rats tail []) active (pair_layout before frame data x y tail shape head) clean
  refine ⟨final,run,port,context,?_,time⟩
  rw [contents,shape,binaryBank_layout]

theorem actual_subtraction_data (caller : Statement C) (before : State C)
    (frame : RatInput.Stack → List Bool) (data : Data) (x y : Rat) (tail : List Rat)
    (active : before.l=some (.subtract default)) (shape : before.stk=layout frame data)
    (head : data 15=x::y::tail) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.packet .parkComplement 0) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=layout frame (Function.update data 15 ((x-y)::tail)) ∧
      run.trace.length≤RatBinary.time RatAddSub.addSubCoefficient before.stk x y (PacketLists.rats tail []) (before.stk 7) := by
  have clean : ∀ slot,Owned slot→before.stk slot=[] := by rw [shape]; exact layout_owned frame data
  obtain ⟨final,run,port,context,contents,time⟩ := actual_subtraction caller before x y
    (PacketLists.rats tail []) active (pair_layout before frame data x y tail shape head) clean
  refine ⟨final,run,port,context,?_,time⟩
  rw [contents,shape,binaryBank_layout]

theorem oneBank_layout (frame : RatInput.Stack → List Bool) (data : Data) :
    Function.update (layout frame data) 15 (RatInput.Encoder.packet (1:Rat) []++layout frame data 15)=
      layout frame (Function.update data 15 (1::data 15)) := by
  funext slot
  fin_cases slot <;> rfl

theorem actual_one_data (caller : Statement C) (job : OneJob) (before : State C)
    (frame : RatInput.Stack → List Bool) (data : Data)
    (active : before.l=some (.one job)) (shape : before.stk=layout frame data) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (oneNext job) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=layout frame (Function.update data 15 (1::data 15)) ∧ run.trace.length=2 := by
  refine ⟨oneResult job before,actual_one caller job before active,rfl,rfl,?_,rfl⟩
  change Function.update before.stk 15 (RatInput.Encoder.packet (1:Rat) []++before.stk 15)=_
  rw [shape,oneBank_layout]

end B23_4_RatWordPrep.WordFinish
