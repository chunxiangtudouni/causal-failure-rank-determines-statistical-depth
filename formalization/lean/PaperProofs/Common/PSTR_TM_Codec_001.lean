module
public import PaperProofs.Common.RationalControllerComputation
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Log

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCodec001
open PaperProofs.Common.Native.RationalControllerComputation

/-- Unary length headers stop at their first false bit, before any payload. -/
theorem header_injective (m n : Nat) (xs ys : List Bool)
    (h : List.replicate m true ++ false :: xs = List.replicate n true ++ false :: ys) :
    m = n ∧ xs = ys := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => simpa using h
    | succ n => simp [List.replicate_succ] at h
  | succ m ih =>
    cases n with
    | zero => simp [List.replicate_succ] at h
    | succ n =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨hm, ht⟩ := ih n h
      exact ⟨congrArg Nat.succ hm, ht⟩

theorem natBits_bound (n : Nat) : n < 2 ^ natBits n := by
  simpa [natBits, Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) n

/-- Prefix decoding consumes exactly one number and preserves any tail. -/
theorem encodeNat_prefix (m n : Nat) (xs ys : List Bool)
    (h : encodeNat m ++ xs = encodeNat n ++ ys) : m = n ∧ xs = ys := by
  simp only [encodeNat, List.append_assoc, List.singleton_append] at h
  obtain ⟨hw, hp⟩ := header_injective (natBits m) (natBits n) _ _ h
  have hbits := List.append_inj hp (by simpa using hw)
  have hm : m = n := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < natBits m
    · have hn : k < natBits n := by omega
      have hh := congrArg (fun l : List Bool => l[k]?) hbits.1
      simpa [List.getElem?_eq_getElem, hk, hn] using hh
    · have hkm : natBits m ≤ k := by omega
      have hkn : natBits n ≤ k := by omega
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (natBits_bound m) (Nat.pow_le_pow_right (by decide) hkm)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (natBits_bound n) (Nat.pow_le_pow_right (by decide) hkn))]
  exact ⟨hm, hbits.2⟩

theorem encodeNat_injective : Function.Injective encodeNat := by
  intro m n h
  exact (encodeNat_prefix m n [] [] (by simpa using h)).1

/-- Sign and reduced numerator/denominator identify the original rational. -/
theorem rat_eq_of_sign_abs_den (r s : Rat)
    (hs : decide (r < 0) = decide (s < 0))
    (hn : r.num.natAbs = s.num.natAbs) (hd : r.den = s.den) : r = s := by
  apply Rat.ext _ hd
  rcases Int.natAbs_eq_natAbs_iff.mp hn with h | h
  · exact h
  · have hsign : r.num < 0 ↔ s.num < 0 := by
      simpa only [Rat.num_neg, decide_eq_decide] using hs
    omega

/-- Tagging and exact numeric payloads make a Datum prefix self-delimiting. -/
theorem encodeDatum_prefix (a b : Datum) (xs ys : List Bool)
    (h : encodeDatum a ++ xs = encodeDatum b ++ ys) : a = b ∧ xs = ys := by
  cases a with
  | natural m =>
    cases b with
    | natural n =>
      simp only [encodeDatum, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, ht⟩ := encodeNat_prefix m n xs ys h
      exact ⟨rfl, ht⟩
    | rational s => simp [encodeDatum] at h
  | rational r =>
    cases b with
    | natural n => simp [encodeDatum] at h
    | rational s =>
      simp only [encodeDatum, List.cons_append, List.nil_append, List.append_assoc,
        List.cons.injEq, true_and] at h
      obtain ⟨hs, hp⟩ := h
      obtain ⟨hn, hp⟩ := encodeNat_prefix r.num.natAbs s.num.natAbs _ _ hp
      obtain ⟨hd, ht⟩ := encodeNat_prefix r.den s.den _ _ hp
      exact ⟨congrArg Datum.rational (rat_eq_of_sign_abs_den r s hs hn hd), ht⟩

theorem datumList_prefix (a b : List Datum) (xs ys : List Bool)
    (hl : a.length = b.length)
    (h : a.flatMap encodeDatum ++ xs = b.flatMap encodeDatum ++ ys) : a = b ∧ xs = ys := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact ⟨rfl, h⟩
    | cons b bs => simp at hl
  | cons a as ih =>
    cases b with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨rfl, hp⟩ := encodeDatum_prefix a b _ _ h
      obtain ⟨rfl, ht⟩ := ih bs (by simpa using hl) hp
      exact ⟨rfl, ht⟩

theorem encode_injective : Function.Injective encode := by
  intro a b h
  simp only [encode, List.append_assoc] at h
  obtain ⟨hl, hp⟩ := encodeNat_prefix a.length b.length _ _ h
  exact (datumList_prefix a b _ _ hl hp).1

theorem boolDatum_injective : Function.Injective boolDatum := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolDatum]

theorem handle_ext (I : Instance) (a b : MismatchHandle I)
    (hs : a.stage.val = b.stage.val) (hw : a.writeSerial = b.writeSerial) : a = b := by
  cases a
  cases b
  simp_all only [Fin.val_inj]

theorem encodeAction_injective (I : Instance) : Function.Injective (encodeAction (I := I)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [encodeAction, encodeHandle, boolDatum] <;> grind [handle_ext]

theorem encodeEvent_prefix (I : Instance) (a b : VisibleEvent I) (xs ys : List Datum)
    (h : encodeEvent a ++ xs = encodeEvent b ++ ys) : a = b ∧ xs = ys := by
  cases a <;> cases b <;> simp_all [encodeEvent, encodeHandle, boolDatum] <;> grind [handle_ext]

theorem eventList_prefix (I : Instance) (a b : List (VisibleEvent I)) (xs ys : List Datum)
    (hl : a.length = b.length)
    (h : a.flatMap encodeEvent ++ xs = b.flatMap encodeEvent ++ ys) : a = b ∧ xs = ys := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact ⟨rfl, h⟩
    | cons b bs => simp at hl
  | cons a as ih =>
    cases b with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨rfl, hp⟩ := encodeEvent_prefix I a b _ _ h
      obtain ⟨rfl, ht⟩ := ih bs (by simpa using hl) hp
      exact ⟨rfl, ht⟩

theorem encodeHistory_injective (I : Instance) : Function.Injective (encodeHistory (I := I)) := by
  intro a b h
  simp only [encodeHistory, List.cons.injEq, Datum.natural.injEq] at h
  exact (eventList_prefix I a b [] [] h.1 (by simpa using h.2)).1

/-- Exactly the original first conjunct of B23, with no implementation assumptions. -/
theorem encodingClaims : EncodingClaims :=
  ⟨encode_injective, encodeAction_injective, encodeHistory_injective⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCodec001


