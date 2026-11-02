module

public import RootPaper_Table_Main001

/-! A specific callback archive, not a VM or a second TABLE execution.
`packets` is the erased readout of the already charged Word calls: online,
each query return supplies its four physical registers exactly once.
Saving uses a flat immutable list: append copies the old list and packet;
lookup scans from the front and copies at most four words. The debits below
pay those traversals and binary length/control bookkeeping conservatively.
No historical query is issued to the mutated live TABLE heap. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootPaper.TableCost

open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Structure PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRQueryRecords

def packets {bits : Nat} (q : Nat) (full : List (Finset (Fin q))) (program : List PackingOp) :
    List Command → List Nat → (BitVec bits → BitVec bits) → List (List Nat)
  | [],_,_ => []
  | _,[],_ => []
  | command::later,steps::counts,heap =>
      let result:=packingRun (callInput q full command) program steps (packingInitial heap)
      let tail:=packets q full program later counts result.heap
      if command=.query then registerWords result::tail else tail

theorem packets_words {bits q : Nat} (full : List (Finset (Fin q))) (program : List PackingOp)
    (commands : List Command) (counts : List Nat) (heap : BitVec bits → BitVec bits) :
    (packets q full program commands counts heap).flatMap id=
      CompactPrice.queryRecords q full program commands counts heap := by
  induction commands generalizing counts heap with
  | nil => rfl
  | cons command later ih =>
      cases counts with
      | nil => rfl
      | cons steps counts =>
          by_cases query:command=.query <;>
            simp only [packets,CompactPrice.queryRecords,query,ite_true,ite_false,
              List.flatMap_cons,id_eq,List.nil_append,registerWords,ih]

theorem packets_four {bits q : Nat} (full : List (Finset (Fin q))) (program : List PackingOp)
    (commands : List Command) (counts : List Nat) (heap : BitVec bits → BitVec bits) :
    ∀ packet∈packets q full program commands counts heap,packet.length=4 := by
  induction commands generalizing counts heap with
  | nil => simp [packets]
  | cons command later ih =>
      cases counts with
      | nil => simp [packets]
      | cons steps counts =>
          by_cases query:command=.query
          · simp only [packets,query,ite_true,List.mem_cons]
            intro packet present
            rcases present with rfl | present
            · rfl
            · exact ih counts _ packet present
          · simpa only [packets,query,ite_false] using ih counts
              (packingRun (callInput q full command) program steps (packingInitial heap)).heap

theorem packets_count {bits q : Nat} (full : List (Finset (Fin q))) (program : List PackingOp)
    (commands : List Command) (counts : List Nat) (heap : BitVec bits → BitVec bits) :
    (packets q full program commands counts heap).length≤commands.length := by
  induction commands generalizing counts heap with
  | nil => exact Nat.le_refl _
  | cons command later ih =>
      cases counts with
      | nil => exact Nat.zero_le _
      | cons steps counts =>
          have tail:=ih counts (packingRun (callInput q full command) program steps (packingInitial heap)).heap
          by_cases query:command=.query
          · rw [query] at tail
            simp only [packets,query,ite_true,List.length_cons]
            omega
          · simp only [packets,query,ite_false,List.length_cons]
            omega

theorem packets_take {bits q : Nat} (full : List (Finset (Fin q))) (program : List PackingOp)
    (commands : List Command) (counts : List Nat) (heap : BitVec bits → BitVec bits) (n : Nat) :
    (packets q full program (commands.take n) (counts.take n) heap).IsPrefix
      (packets q full program commands counts heap) := by
  induction n generalizing commands counts heap with
  | zero => exact List.nil_prefix
  | succ n ih =>
      cases commands with
      | nil => exact List.prefix_refl _
      | cons command later =>
          cases counts with
          | nil => exact List.prefix_refl _
          | cons steps counts =>
              obtain ⟨suffix,same⟩:=ih later counts
                (packingRun (callInput q full command) program steps (packingInitial heap)).heap
              by_cases query:command=.query
              · refine ⟨suffix,?_⟩
                simpa only [List.take_succ_cons,packets,query,ite_true,List.cons_append] using congrArg
                  (List.cons (registerWords (packingRun (callInput q full command) program steps (packingInitial heap)))) same
              · simpa only [List.take_succ_cons,packets,query,ite_false] using (show
                  (packets q full program (later.take n) (counts.take n)
                    (packingRun (callInput q full command) program steps (packingInitial heap)).heap).IsPrefix
                  (packets q full program later counts
                    (packingRun (callInput q full command) program steps (packingInitial heap)).heap) from ⟨suffix,same⟩)

theorem packets_prefix {bits q : Nat} (full : List (Finset (Fin q))) (program : List PackingOp)
    (commands current : List Command) (counts : List Nat) (heap : BitVec bits → BitVec bits)
    (before : current.IsPrefix commands) :
    (packets q full program current (counts.take current.length) heap).IsPrefix
      (packets q full program commands counts heap) := by
  obtain ⟨later,rfl⟩:=before
  simpa only [List.take_append_length] using packets_take full program (current++later) counts heap current.length

/-- Each copied data word has `wordBits` bits. The additional numeric
length bound pays length/index increments and the append-loop controls;
natBits(length) is at most length+1, so these are conservative bit debits. -/
def appendDebit (wordBits : Nat) (old packet : List Nat) : Nat :=
  (old.length+packet.length+2)*(wordBits+old.length+packet.length+2)

def saveDebit (wordBits : Nat) (old : List Nat) : List (List Nat) → Nat
  | [] => 0
  | packet::later => appendDebit wordBits old packet+saveDebit wordBits (old++packet) later

def saved (old : List Nat) : List (List Nat) → List Nat
  | [] => old
  | packet::later => saved (old++packet) later

theorem saved_words (old : List Nat) (stream : List (List Nat)) :
    saved old stream=old++stream.flatMap id := by
  induction stream generalizing old with
  | nil => simp [saved]
  | cons packet later ih => simp only [saved,ih,List.flatMap_cons,id_eq,List.append_assoc]

theorem saved_prefix (old : List Nat) (before later : List (List Nat)) (prefixOf : before.IsPrefix later) :
    (saved old before).IsPrefix (saved old later) := by
  obtain ⟨rest,rfl⟩:=prefixOf
  refine ⟨rest.flatMap id,?_⟩
  simp only [saved_words,List.flatMap_append,List.append_assoc]

theorem saveDebit_bound (wordBits : Nat) (old : List Nat) (stream : List (List Nat))
    (four : ∀ packet∈stream,packet.length=4) :
    saveDebit wordBits old stream≤
      stream.length*(old.length+4*stream.length+2)*(wordBits+old.length+4*stream.length+2) := by
  induction stream generalizing old with
  | nil => simp [saveDebit]
  | cons packet later ih =>
      have length:=four packet List.mem_cons_self
      have tail:=ih (old++packet) (fun item present=>four item (List.mem_cons_of_mem _ present))
      simp only [List.length_append,length] at tail
      have first : appendDebit wordBits old packet≤
          (old.length+4*(later.length+1)+2)*(wordBits+old.length+4*(later.length+1)+2) := by
        unfold appendDebit
        rw [length]
        exact Nat.mul_le_mul (by omega) (by omega)
      have aligned : old.length+4+4*later.length+2=old.length+4*(later.length+1)+2 := by omega
      have aligned' : wordBits+(old.length+4)+4*later.length+2=wordBits+old.length+4*(later.length+1)+2 := by omega
      rw [aligned,aligned'] at tail
      change appendDebit wordBits old packet+saveDebit wordBits (old++packet) later≤_
      simp only [List.length_cons]
      exact (Nat.add_le_add first tail).trans_eq (by ring)

def readRecord (archive : List Nat) (index : Nat) : List Nat := (archive.drop (4*index)).take 4

/-- A front scan followed by a four-word copy, with paid length/control
bookkeeping. The scan stops at the physical archive's end. -/
def readDebit (wordBits : Nat) (archive : List Nat) (index : Nat) : Nat :=
  ((archive.take (4*index)).length+2*(readRecord archive index).length+2)*(wordBits+archive.length+2)

theorem readDebit_bound (wordBits : Nat) (archive : List Nat) (index : Nat) :
    readDebit wordBits archive index≤(archive.length+10)*(wordBits+archive.length+2) := by
  have scan : (archive.take (4*index)).length≤archive.length:=by
    simp only [List.length_take]
    omega
  have output : (readRecord archive index).length≤4:=List.length_take_le _ _
  exact Nat.mul_le_mul_right _ (by omega)

theorem physical_archive {bits q : Nat} (full : List (Finset (Fin q))) (program : List PackingOp)
    (commands : List Command) (counts : List Nat) (heap : BitVec bits → BitVec bits) :
    saved [] (packets q full program commands counts heap)=CompactPrice.queryRecords q full program commands counts heap ∧
    saveDebit bits [] (packets q full program commands counts heap)≤
      commands.length*(4*commands.length+2)*(bits+4*commands.length+2) := by
  constructor
  · simpa only [saved_words,List.nil_append] using packets_words full program commands counts heap
  · have bounded:=saveDebit_bound bits [] _ (packets_four full program commands counts heap)
    simp only [List.length_nil,Nat.zero_add] at bounded
    have count:=packets_count full program commands counts heap
    exact bounded.trans (Nat.mul_le_mul
      (Nat.mul_le_mul count (by omega)) (by omega))

end RootPaper.TableCost
