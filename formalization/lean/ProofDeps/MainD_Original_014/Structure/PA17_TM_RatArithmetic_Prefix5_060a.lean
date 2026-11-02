module
public import Structure.PA17_TM_Division_Compose_006a
public import Common.PSTR_TM_RawNat_010
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! Fixed five-Bool FIFO transport. It scans real DATA/TRUE-FLAG pairs,
recognizes the actual END/OWN00 pair, and really flushes five cells. No
width, value, archive, or fragment is supplied to executable control. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPrefix5060
open Turing PA17TMDivisionCompose006

def front (queue : Fin 32) : Bool := queue.val.testBit 0
def push (queue : Fin 32) (bit : Bool) : Fin 32 :=
  ⟨queue.val/2+(if bit then 16 else 0),by
    have h:=queue.isLt
    cases bit <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega⟩
def queueWord (queue : Fin 32) : List Bool :=
  [queue.val.testBit 0,queue.val.testBit 1,queue.val.testBit 2,queue.val.testBit 3,queue.val.testBit 4]

def lane (mode : Fin 15) (queue : Fin 32) : Fin 481 :=
  ⟨32*mode.val+queue.val,by have hm:=mode.isLt;have hq:=queue.isLt;omega⟩
def queueOf (q : Fin 481) : Fin 32 := ⟨q.val%32,Nat.mod_lt _ (by decide)⟩
theorem lane_mode (mode : Fin 15) (queue : Fin 32) : (lane mode queue).val/32=mode.val := by
  have hq:=queue.isLt
  simp only [lane]
  omega
theorem lane_queue (mode : Fin 15) (queue : Fin 32) : queueOf (lane mode queue)=queue := by
  apply Fin.ext
  have hq:=queue.isLt
  simp only [queueOf,lane]
  omega

def rd (q : Fin 32) : Fin 481 := lane 0 q
def rf (q : Fin 32) : Fin 481 := lane 1 q
def md (q : Fin 32) : Fin 481 := lane 2 q
def mf (q : Fin 32) : Fin 481 := lane 3 q
def me (q : Fin 32) : Fin 481 := lane 4 q
def fw (k : Nat) (q : Fin 32) : Fin 481 :=
  if h:k<5 then lane ⟨5+k,by omega⟩ q else 480
def fm (k : Nat) (q : Fin 32) : Fin 481 :=
  if h:k<5 then lane ⟨10+k,by omega⟩ q else 480

def shiftMachine : Machine 480 := fun q symbol =>
  let fifo:=queueOf q
  match q.val/32 with
  | 0 => some (md (push fifo symbol),.write (front fifo))
  | 1 => some ((if symbol then mf (push fifo true) else me (push fifo false)),.write (front fifo))
  | 2 => some (rf fifo,.move .right)
  | 3 => some (rd fifo,.move .right)
  | 4 => some (fw 0 fifo,.move .right)
  | 5 => some (fm 0 (push fifo false),.write (front fifo))
  | 6 => some (fm 1 (push fifo false),.write (front fifo))
  | 7 => some (fm 2 (push fifo false),.write (front fifo))
  | 8 => some (fm 3 (push fifo false),.write (front fifo))
  | 9 => some (fm 4 (push fifo false),.write (front fifo))
  | 10 => some (fw 1 fifo,.move .right)
  | 11 => some (fw 2 fifo,.move .right)
  | 12 => some (fw 3 fifo,.move .right)
  | 13 => some (fw 4 fifo,.move .right)
  | 14 => some (480,.move .right)
  | _ => none

def cfg (q : Fin 481) (left right : List Bool) : MachineState 480 := ⟨q,Tape.mk₂ left right⟩
theorem lookup_rd (q : Fin 32) (symbol : Bool) :
    shiftMachine (rd q) symbol=some (md (push q symbol),.write (front q)) := by
  simp [shiftMachine,rd,lane_mode,lane_queue]
theorem lookup_rf_true (q : Fin 32) :
    shiftMachine (rf q) true=some (mf (push q true),.write (front q)) := by
  simp [shiftMachine,rf,lane_mode,lane_queue]
theorem lookup_rf_false (q : Fin 32) :
    shiftMachine (rf q) false=some (me (push q false),.write (front q)) := by
  simp [shiftMachine,rf,lane_mode,lane_queue]
theorem lookup_md (q : Fin 32) (symbol : Bool) : shiftMachine (md q) symbol=some (rf q,.move .right) := by
  simp [shiftMachine,md,lane_mode,lane_queue]
theorem lookup_mf (q : Fin 32) (symbol : Bool) : shiftMachine (mf q) symbol=some (rd q,.move .right) := by
  simp [shiftMachine,mf,lane_mode,lane_queue]
theorem lookup_me (q : Fin 32) (symbol : Bool) : shiftMachine (me q) symbol=some (fw 0 q,.move .right) := by
  simp [shiftMachine,me,lane_mode,lane_queue]
theorem lookup_fw (k : Nat) (q : Fin 32) (symbol : Bool) (hk : k<5) :
    shiftMachine (fw k q) symbol=some (fm k (push q false),.write (front q)) := by
  interval_cases k <;> simp [fw,fm,shiftMachine,lane_mode,lane_queue]
theorem lookup_fm (k : Nat) (q : Fin 32) (symbol : Bool) (hk : k<5) :
    shiftMachine (fm k q) symbol=some (fw (k+1) q,.move .right) := by
  interval_cases k <;> simp [fw,fm,shiftMachine,lane_mode,lane_queue]
theorem halt (left right : List Bool) : TM0.step shiftMachine (cfg 480 left right)=none := by
  simp [TM0.step,shiftMachine,cfg]

def flushLeft : Nat → Fin 32 → List Bool → List Bool
  | 0,_,left => left
  | r+1,q,left => flushLeft r (push q false) (front q::left)
def flushPrefix (k : Nat) (q : Fin 32) (left : List Bool) : List (MachineState 480) :=
  [cfg (fw k q) left [],cfg (fm k (push q false)) left [front q]]
def flushTrace : Nat → Nat → Fin 32 → List Bool → List (MachineState 480)
  | _,0,_,left => [cfg 480 left []]
  | k,r+1,q,left => flushPrefix k q left++flushTrace (k+1) r (push q false) (front q::left)

theorem flush_prefix_segment (k : Nat) (q : Fin 32) (left : List Bool) (hk : k<5) :
    Segment shiftMachine (cfg (fw k q) left []) (flushPrefix k q left)
      (cfg (fm k (push q false)) left [front q]) := by
  refine ⟨rfl,?_,rfl⟩
  simp [flushPrefix,List.isChain_cons_cons,TM0.step,cfg,Tape.mk₂,lookup_fw k q false hk]
theorem flush_advance (k : Nat) (q : Fin 32) (left : List Bool) (hk : k<5) :
    TM0.step shiftMachine (cfg (fm k (push q false)) left [front q])=
      some (cfg (fw (k+1) (push q false)) (front q::left) []) := by
  simp [TM0.step,cfg,Tape.mk₂,lookup_fm k (push q false) (front q) hk]

theorem flush_runs (r k : Nat) (q : Fin 32) (left : List Bool) (h : k+r=5) :
    PSTRTMSeq005.RunsFrom shiftMachine (cfg (fw k q) left []) (flushTrace k r q left)
      (cfg 480 (flushLeft r q left) []) := by
  induction r generalizing k q left with
  | zero =>
    have hk : k=5 := by omega
    subst k
    exact ⟨rfl,.singleton _,rfl,halt _ _⟩
  | succ r ih =>
    have hk : k<5 := by omega
    have tail := ih (k+1) (push q false) (front q::left) (by omega)
    have seg := segment_append shiftMachine _ _ _ _ _ _
      (flush_prefix_segment k q left hk) ⟨tail.1,tail.2.1,tail.2.2.1⟩ (flush_advance k q left hk)
    exact segment_runsFrom _ _ _ _ seg tail.2.2.2

theorem flush_length (k r : Nat) (q : Fin 32) (left : List Bool) :
    (flushTrace k r q left).length=2*r+1 := by
  induction r generalizing k q left with
  | zero => rfl
  | succ r ih => simp only [flushTrace,List.length_append,flushPrefix,List.length_cons,List.length_nil,ih];omega
theorem flush_five_left (q : Fin 32) (left : List Bool) :
    flushLeft 5 q left=(queueWord q).reverse++left := by
  fin_cases q <;> rfl

def pairQueue (q : Fin 32) (bit flag : Bool) : Fin 32 := push (push q bit) flag
def pairLeft (q : Fin 32) (bit : Bool) (left : List Bool) : List Bool := front (push q bit)::front q::left
def pairPrefix (q : Fin 32) (left : List Bool) (bit : Bool) (right : List Bool) : List (MachineState 480) :=
  [cfg (rd q) left (bit::true::right),
   cfg (md (push q bit)) left (front q::true::right),
   cfg (rf (push q bit)) (front q::left) (true::right),
   cfg (mf (pairQueue q bit true)) (front q::left) (front (push q bit)::right)]
def eofPrefix (q : Fin 32) (left : List Bool) : List (MachineState 480) :=
  [cfg (rd q) left [false,false],
   cfg (md (push q false)) left [front q,false],
   cfg (rf (push q false)) (front q::left) [false],
   cfg (me (pairQueue q false false)) (front q::left) [front (push q false)]]

theorem pair_segment (q : Fin 32) (left : List Bool) (bit : Bool) (right : List Bool) :
    Segment shiftMachine (cfg (rd q) left (bit::true::right)) (pairPrefix q left bit right)
      (cfg (mf (pairQueue q bit true)) (front q::left) (front (push q bit)::right)) := by
  refine ⟨rfl,?_,rfl⟩
  simp [pairPrefix,List.isChain_cons_cons,TM0.step,cfg,Tape.mk₂,pairQueue,lookup_rd,lookup_md,lookup_rf_true]
theorem pair_advance (q : Fin 32) (left : List Bool) (bit : Bool) (right : List Bool) :
    TM0.step shiftMachine (cfg (mf (pairQueue q bit true)) (front q::left) (front (push q bit)::right))=
      some (cfg (rd (pairQueue q bit true)) (pairLeft q bit left) right) := by
  simp [TM0.step,cfg,Tape.mk₂,pairLeft,lookup_mf]
theorem eof_segment (q : Fin 32) (left : List Bool) :
    Segment shiftMachine (cfg (rd q) left [false,false]) (eofPrefix q left)
      (cfg (me (pairQueue q false false)) (front q::left) [front (push q false)]) := by
  refine ⟨rfl,?_,rfl⟩
  simp [eofPrefix,List.isChain_cons_cons,TM0.step,cfg,Tape.mk₂,pairQueue,lookup_rd,lookup_md,lookup_rf_false]
theorem eof_advance (q : Fin 32) (left : List Bool) :
    TM0.step shiftMachine (cfg (me (pairQueue q false false)) (front q::left) [front (push q false)])=
      some (cfg (fw 0 (pairQueue q false false)) (pairLeft q false left) []) := by
  simp [TM0.step,cfg,Tape.mk₂,pairLeft,lookup_me]

def shiftLeft : Fin 32 → List Bool → List Bool → List Bool
  | q,left,[] => flushLeft 5 (pairQueue q false false) (pairLeft q false left)
  | q,left,bit::later => shiftLeft (pairQueue q bit true) (pairLeft q bit left) later
def shiftTrace : Fin 32 → List Bool → List Bool → List (MachineState 480)
  | q,left,[] => eofPrefix q left++flushTrace 0 5 (pairQueue q false false) (pairLeft q false left)
  | q,left,bit::later => pairPrefix q left bit (PSTRTMIncrement009.blocks later++[false,false])++
      shiftTrace (pairQueue q bit true) (pairLeft q bit left) later

theorem blocks_cons (bit : Bool) (later : List Bool) :
    PSTRTMIncrement009.blocks (bit::later)=bit::true::PSTRTMIncrement009.blocks later := by
  simp only [PSTRTMIncrement009.blocks,List.flatMap_cons,List.cons_append,List.nil_append]
theorem blocks_nil : PSTRTMIncrement009.blocks ([] : List Bool)=[] := rfl
theorem shift_runs (digits : List Bool) (q : Fin 32) (left : List Bool) :
    PSTRTMSeq005.RunsFrom shiftMachine (cfg (rd q) left (PSTRTMIncrement009.blocks digits++[false,false]))
      (shiftTrace q left digits) (cfg 480 (shiftLeft q left digits) []) := by
  induction digits generalizing q left with
  | nil =>
    have tail := flush_runs 5 0 (pairQueue q false false) (pairLeft q false left) rfl
    have seg := segment_append shiftMachine _ _ _ _ _ _ (eof_segment q left)
      ⟨tail.1,tail.2.1,tail.2.2.1⟩ (eof_advance q left)
    simpa only [shiftTrace,shiftLeft,blocks_nil,List.nil_append] using
      segment_runsFrom _ _ _ _ seg tail.2.2.2
  | cons bit later ih =>
    have tail := ih (pairQueue q bit true) (pairLeft q bit left)
    have seg := segment_append shiftMachine _ _ _ _ _ _
      (pair_segment q left bit (PSTRTMIncrement009.blocks later++[false,false]))
      ⟨tail.1,tail.2.1,tail.2.2.1⟩ (pair_advance q left bit _)
    simpa only [shiftTrace,shiftLeft,blocks_cons,List.cons_append] using
      segment_runsFrom _ _ _ _ seg tail.2.2.2

theorem shift_length (digits : List Bool) (q : Fin 32) (left : List Bool) :
    (shiftTrace q left digits).length=4*digits.length+15 := by
  induction digits generalizing q left with
  | nil => simp only [shiftTrace,List.length_append,eofPrefix,List.length_cons,List.length_nil,flush_length]
  | cons bit later ih =>
    simp only [shiftTrace,List.length_append,pairPrefix,List.length_cons,List.length_nil,ih]
    omega

theorem pair_balance (q : Fin 32) (bit flag : Bool) :
    [front q,front (push q bit)]++queueWord (pairQueue q bit flag)=queueWord q++[bit,flag] := by
  fin_cases q <;> cases bit <;> cases flag <;> rfl

theorem shift_left_exact (digits : List Bool) (q : Fin 32) (left : List Bool) :
    shiftLeft q left digits=(queueWord q++PSTRTMIncrement009.blocks digits++[false,false]).reverse++left := by
  induction digits generalizing q left with
  | nil =>
    have h := congrArg List.reverse (pair_balance q false false)
    simp only [List.reverse_append] at h
    simp only [shiftLeft,flush_five_left,pairLeft,PSTRTMIncrement009.blocks,List.flatMap_nil,List.append_nil]
    simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.append_assoc,List.cons_append,List.nil_append] using
      congrArg (fun xs : List Bool => xs++left) h
  | cons bit later ih =>
    rw [shiftLeft,ih]
    have h := pair_balance q bit true
    have hw : queueWord q++PSTRTMIncrement009.blocks (bit::later)++[false,false]=
        [front q,front (push q bit)]++(queueWord (pairQueue q bit true)++PSTRTMIncrement009.blocks later++[false,false]) := by
      rw [blocks_cons]
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using
        congrArg (fun xs : List Bool => xs++PSTRTMIncrement009.blocks later++[false,false]) h.symm
    rw [hw,List.reverse_append]
    simp only [pairLeft,List.reverse_append,List.reverse_cons,List.reverse_nil,List.append_assoc,List.cons_append,List.nil_append]

theorem blocks_reverse (digits : List Bool) :
    (PSTRTMIncrement009.blocks digits).reverse=PSTRTMRawNat010.leftBlocks digits.reverse := by
  induction digits with
  | nil => rfl
  | cons bit later ih =>
    simp only [blocks_cons,List.reverse_cons,
      PSTRTMRawNat010.leftBlocks,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_assoc] at *
    exact congrArg (fun xs => xs++[true,bit]) ih

/-- Real five-cell reserve; the original guard/archive remain in left.
Every old symbol was read before overwrite and every new cell was written. -/
theorem shift5_runsFrom (digits archive : List Bool) :
    PSTRTMSeq005.RunsFrom shiftMachine
      ⟨0,Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++[false,false])⟩
      (shiftTrace 0 (false::archive) digits)
      ⟨480,Tape.mk₂ (false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++
        List.replicate 5 false++false::archive)) []⟩ := by
  have hr := shift_runs digits 0 (false::archive)
  rw [shift_left_exact] at hr
  have h0 : rd 0=(0 : Fin 481) := by apply Fin.ext;rfl
  rw [h0] at hr
  have hq : queueWord 0=List.replicate 5 false := rfl
  simpa only [cfg,hq,List.reverse_append,
    blocks_reverse,List.reverse_replicate,List.reverse_cons,List.reverse_nil,
    List.append_assoc,List.cons_append,List.nil_append] using hr

theorem shift5_prefix_space (digits archive : List Bool) (inputLength k : Nat) :
    visitedSpace shiftMachine inputLength ((shiftTrace 0 (false::archive) digits).take k) ≤
      inputLength+8*digits.length+31 := by
  have hs := PSTRTMTrace002.visitedSpace_le shiftMachine inputLength ((shiftTrace 0 (false::archive) digits).take k)
  have hl := shift_length digits 0 (false::archive)
  have hk : ((shiftTrace 0 (false::archive) digits).take k).length≤(shiftTrace 0 (false::archive) digits).length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPrefix5060
