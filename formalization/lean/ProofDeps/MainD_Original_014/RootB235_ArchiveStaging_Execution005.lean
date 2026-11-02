module
public import RootB235_ArchiveStaging_PrependCopy002

/-! Kernel-checked execution witnesses for bounded physical control paths
and finite stuttering refinements. These functions build traces only; they
are never used to define a runtime transition or a tape answer. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
open Turing RationalControllerComputation

def follow {L : Type} [Inhabited L] (code : TM0.Machine Bool L) : Nat → TM0.Cfg Bool L → Option (TM0.Cfg Bool L)
  | 0,cfg => some cfg
  | n+1,cfg => (TM0.step code cfg).bind (follow code n)

def follow_actual {L : Type} [Inhabited L] (code : TM0.Machine Bool L) (n : Nat)
    (first last : TM0.Cfg Bool L) (done : follow code n first=some last) :
    Segment code first last (2*n+1) := by
  induction n generalizing first with
  | zero =>
    simp only [follow,Option.some.injEq] at done
    subst last
    exact Segment.point _ _
  | succ n ih =>
    cases edge : TM0.step code first with
    | none => simp only [follow,edge,Option.bind_none,reduceCtorEq] at done
    | some next =>
      have rest : follow code n next=some last := by simpa only [follow,edge,Option.bind_some] using done
      exact ((Segment.edge edge).trans (ih next rest)).weaken (by omega)

def map_segment {A B : Type} [Inhabited A] [Inhabited B]
    (source : TM0.Machine Bool A) (whole : TM0.Machine Bool B) (map : TM0.Cfg Bool A → TM0.Cfg Bool B)
    (steps : ∀ a b,TM0.step source a=some b → TM0.step whole (map a)=some (map b))
    {first last : TM0.Cfg Bool A} {budget : Nat} (path : Segment source first last budget) :
    Segment whole (map first) (map last) budget :=
  ⟨path.trace.map map,by simp only [List.head?_map,path.head,Option.map_some],
    (List.isChain_map _).mpr (path.chain.imp (fun a b edge => steps a b edge)),
    by simp only [List.getLast?_map,path.tail,Option.map_some],
    by simpa only [List.length_map] using path.time⟩

def call_map_segment {A B : Type} [Inhabited A] [Inhabited B]
    (whole : TM0.Machine Bool B) (source : TM0.Machine Bool A) (tag finish : A → B)
    (lookup : ∀ q bit,whole (tag q) bit=call source tag finish q bit)
    {first last : TM0.Cfg Bool A} {budget : Nat} (path : Segment source first last budget) :
    Segment whole (embed tag first) (embed tag last) budget :=
  map_segment source whole (embed tag) (fun a b edge => by
    simp only [call_step whole source tag finish lookup,edge]) path

def refine_chain {A B : Type} [Inhabited A] [Inhabited B]
    (source : TM0.Machine Bool A) (whole : TM0.Machine Bool B) (map : TM0.Cfg Bool A → TM0.Cfg Bool B)
    (cost : Nat) (positive : 1≤cost)
    (steps : ∀ a b,TM0.step source a=some b → Segment whole (map a) (map b) cost)
    (path : List (TM0.Cfg Bool A)) (first last : TM0.Cfg Bool A)
    (head : path.head?=some first)
    (chain : path.IsChain (fun a b => TM0.step source a=some b))
    (tail : path.getLast?=some last) : Segment whole (map first) (map last) (cost*path.length) := by
  induction path generalizing first with
  | nil => simp only [List.head?_nil,reduceCtorEq] at head
  | cons current rest ih =>
    simp only [List.head?_cons,Option.some.injEq] at head
    subst first
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton,Option.some.injEq] at tail
      subst last
      exact (Segment.point _ _).weaken (by simpa only [List.length_singleton,Nat.mul_one] using positive)
    | cons next later =>
      obtain ⟨edge,chain'⟩ := List.isChain_cons_cons.mp chain
      have rest := ih next rfl chain' (by simpa only [List.getLast?_cons_cons] using tail)
      exact ((steps current next edge).trans rest).weaken (by
        simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
        omega)

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
