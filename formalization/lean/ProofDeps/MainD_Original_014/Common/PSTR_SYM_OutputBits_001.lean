module

public import Common.PSTR_HD_Heads_001
public import Common.PSTR_TM_Arithmetic_008

/-! ORIGINAL tree serialization only: actual Bool codec mass identities.
No TM run, computed heads, parser, or symbolic compilation is asserted.
This source is prepared while Stage141 owns the sole compiler admission.
Its coherent product view and strict/public/private checks are still pending. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.CompactPrice.PSTRSymbolicBits

open PaperProofs.Common.SymbolicPrice
open PaperProofs.Statistics
open RationalControllerComputation
open RationalControllerComputation.PSTRTMLength004
open RationalControllerComputation.PSTRTMArithmetic008

def datumMass (data : List Datum) : Nat := (data.map datumBits).sum

def ratBits (value : Rat) : Nat := datumBits (.rational value)

def exprBits (expression : Expr) : Nat := datumMass (encodeExpr expression)

theorem datumMass_append (first second : List Datum) :
    datumMass (first ++ second) = datumMass first + datumMass second := by
  simp only [datumMass, List.map_append, List.sum_append]

theorem datumMass_cons (datum : Datum) (later : List Datum) :
    datumMass (datum :: later) = datumBits datum + datumMass later := rfl

theorem ratBits_ge_eight (value : Rat) : 8 ≤ ratBits value := by
  simp only [ratBits, datumBits, natBits]
  omega

theorem natBits_le_self_add_one (value : Nat) : natBits value ≤ value + 1 := by
  simp only [natBits, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_le_self 2 value) 1

theorem natural_bits_le (value bound : Nat) (hvalue : value ≤ bound) :
    datumBits (.natural value) ≤ 2 * bound + 4 := by
  have hb := natBits_le_self_add_one value
  simp only [datumBits]
  omega

theorem length_le_datumMass (data : List Datum) : data.length ≤ datumMass data := by
  induction data with
  | nil => rfl
  | cons datum later ih =>
    have positive := datumBits_pos datum
    simp only [List.length_cons, datumMass_cons]
    omega

theorem datumMass_le_encoded_length (data : List Datum) :
    datumMass data ≤ (encode data).length := by
  rw [encode_length]
  change datumMass data ≤ 2 * natBits data.length + 2 + datumMass data
  omega

/-- Includes the dynamic list's actual binary length header and final TRUE. -/
theorem encoded_length_le_three_mass (data : List Datum) :
    (encode data).length ≤ 3 * datumMass data + 4 := by
  have hb := natBits_le_self_add_one data.length
  have hd := length_le_datumMass data
  rw [encode_length]
  change 2 * natBits data.length + 2 + datumMass data ≤ 3 * datumMass data + 4
  omega

theorem exprBits_rational (value : Rat) : exprBits (.rational value) = 4 + ratBits value := by
  simp [exprBits, datumMass, encodeExpr, ratBits, datumBits, natBits]

theorem exprBits_add (left right : Expr) :
    exprBits (.add left right) = 4 + exprBits left + exprBits right := by
  simp [exprBits, datumMass, encodeExpr, datumBits, natBits, Nat.add_assoc]

theorem exprBits_multiply (left right : Expr) :
    exprBits (.multiply left right) = 6 + exprBits left + exprBits right := by
  simp [exprBits, datumMass, encodeExpr, datumBits, natBits, Nat.add_assoc]

theorem exprBits_divide (left right : Expr) :
    exprBits (.divide left right) = 6 + exprBits left + exprBits right := by
  simp [exprBits, datumMass, encodeExpr, datumBits, natBits, Nat.add_assoc]

theorem exprBits_log (argument : Expr) : exprBits (.log argument) = 8 + exprBits argument := by
  simp [exprBits, datumMass, encodeExpr, datumBits, natBits]

theorem exprBits_zero : exprBits (.rational 0) = 12 := by
  norm_num [exprBits_rational, ratBits, datumBits, natBits]

/-- This is the ORIGINAL Expr tree: every add and every copied leaf is charged. -/
theorem exprBits_sumExpr (expressions : List Expr) :
    exprBits (sumExpr expressions) =
      12 + (expressions.map (fun expression => 4 + exprBits expression)).sum := by
  induction expressions with
  | nil => simp only [sumExpr, exprBits_zero, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons first later ih =>
    simp only [sumExpr, exprBits_add, List.map_cons, List.sum_cons, ih]
    omega

/-- Reuse the frozen original tree-node and token-count bounds as well.
No expression is replaced by a shared DAG or by its evaluated coefficient. -/
theorem original_expression_data_count {I : Instance}
    (input : StatisticalInput I) (available : Finset I.Tool) :
    (encodeExpr (inputExpression input available)).length ≤
      2 * ((List.ofFn (fun stage : I.Stage =>
        14 * (input.experiment stage).alphabetSize + 10)).sum + 1) :=
  (PSTRHeads.encodeExpr_length_le _).trans
    (Nat.mul_le_mul_left 2 (inputExpression_nodes_le input available))

theorem datumMass_naturals_le (values : List Nat) (bound : Nat)
    (hvalues : ∀ value ∈ values, value ≤ bound) :
    datumMass (values.map Datum.natural) ≤ values.length * (2 * bound + 4) := by
  revert hvalues
  induction values with
  | nil => intro _; simp [datumMass]
  | cons value later ih =>
    intro hvalues
    have head := natural_bits_le value bound (hvalues value List.mem_cons_self)
    have tail := ih (by intro x hx; exact hvalues x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.length_cons, datumMass_cons]
    calc
      _ ≤ (2 * bound + 4) + later.length * (2 * bound + 4) := Nat.add_le_add head tail
      _ = (later.length + 1) * (2 * bound + 4) := by ring

end PaperProofs.Common.Native.CompactPrice.PSTRSymbolicBits
