/-
# Kernel-checked cleared-denominator rational sums

Deep addition in the project's deliberately unnormalized rational carrier
`Q'` can create enormous intermediate denominators.  This module supplies an
equivalent proof-producing check: choose one positive common denominator,
verify that it is divisible by every input denominator, and compare the
cleared integer numerators.

The common denominator may be proposed by an external exact-arithmetic
program, but divisibility and the final integer identity are rechecked by
Lean.  This is finite arithmetic infrastructure only.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.FiniteClearedRationalSumCertificate

set_option maxRecDepth 300000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- A rational with an explicitly selected positive denominator. -/
def commonQ (common : Nat) (hcommon : 0 < common)
    (numerator : Int) : Q' :=
  Q'.mkPos numerator common hcommon

/-- The numerator obtained by lifting `q` to `common`, provided divisibility
is checked separately. -/
def scaledNumerator (common : Nat) (q : Q') : Int :=
  q.num * (common / q.den : Nat)

/-- Exact integer sum, kept separate from `Q'` addition. -/
def intSum : List Int → Int
  | [] => 0
  | head :: tail => head + intSum tail

theorem eqv_commonQ
    (common : Nat) (hcommon : 0 < common) (q : Q')
    (hdiv : q.den ∣ common) :
    q ≈ commonQ common hcommon (scaledNumerator common q) := by
  unfold commonQ scaledNumerator Q'.eqv
  rw [Q'.mkPos_den]
  change q.num * Int.ofNat common =
    (q.num * Int.ofNat (common / q.den)) * Int.ofNat q.den
  rw [Int.mul_assoc]
  have hnat := Nat.div_mul_cancel hdiv
  simpa using
    congrArg (fun value : Nat => q.num * Int.ofNat value) hnat.symm

theorem eqv_commonQ_of_zero_or_dvd
    (common : Nat) (hcommon : 0 < common) (q : Q')
    (husable : q.num = 0 ∨ q.den ∣ common) :
    q ≈ commonQ common hcommon (scaledNumerator common q) := by
  rcases husable with hzero | hdiv
  · unfold commonQ scaledNumerator Q'.eqv
    rw [Q'.mkPos_den, hzero, Q'.mkPos_num]
    simp
  · exact eqv_commonQ common hcommon q hdiv

theorem commonQ_add
    (common : Nat) (hcommon : 0 < common) (a b : Int) :
    commonQ common hcommon a + commonQ common hcommon b ≈
      commonQ common hcommon (a + b) := by
  unfold commonQ Q'.eqv
  simp only [Q'.add_num_cast, Q'.add_den_cast,
    Q'.mkPos_num, Q'.mkPos_den]
  change (a * Int.ofNat common + b * Int.ofNat common) *
      Int.ofNat common =
    (a + b) * (Int.ofNat common * Int.ofNat common)
  rw [← Int.add_mul, Int.mul_assoc]

theorem commonQ_sum (common : Nat) (hcommon : 0 < common) :
    ∀ values : List Int,
    listQSum (commonQ common hcommon) values ≈
      commonQ common hcommon (intSum values)
  | [] => by
      unfold listQSum intSum commonQ Q'.eqv
      simp only [Q'.mkPos_num, Q'.mkPos_den]
      change (0 : Int) * Int.ofNat common =
        (0 : Int) * Int.ofNat (0 : Q').den
      simp
  | head :: tail => by
      unfold listQSum intSum
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (commonQ_sum common hcommon tail))
        (commonQ_add common hcommon head (intSum tail))

theorem listQSum_eqv_commonQ
    (common : Nat) (hcommon : 0 < common) :
    ∀ terms : List Q',
    (∀ term, term ∈ terms → term.num = 0 ∨ term.den ∣ common) →
    listQSum id terms ≈
      commonQ common hcommon
        (intSum (terms.map (scaledNumerator common)))
  | [], _ => commonQ_sum common hcommon []
  | head :: tail, hdiv => by
      unfold listQSum List.map intSum
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (eqv_commonQ_of_zero_or_dvd common hcommon head
            (hdiv head List.mem_cons_self))
          (listQSum_eqv_commonQ common hcommon tail
            (fun term hterm =>
              hdiv term (List.mem_cons_of_mem head hterm))))
        (commonQ_add common hcommon
          (scaledNumerator common head)
          (intSum (List.map (scaledNumerator common) tail)))

/-- A finite cleared-denominator certificate.  The list-wide divisibility
fact is Boolean so the concrete certificate remains directly decidable. -/
def ClearedSumValid (target : Q') (terms : List Q')
    (common : Nat) : Prop :=
  0 < common ∧
    (target.num = 0 ∨ target.den ∣ common) ∧
    (terms.all (fun term =>
      decide (term.num = 0 ∨ term.den ∣ common)) = true) ∧
    scaledNumerator common target =
      intSum (terms.map (scaledNumerator common))

instance (target : Q') (terms : List Q') (common : Nat) :
    Decidable (ClearedSumValid target terms common) := by
  unfold ClearedSumValid
  infer_instance

/-- Soundness of one cleared-denominator certificate. -/
theorem ClearedSumValid.sound
    {target : Q'} {terms : List Q'} {common : Nat}
    (hvalid : ClearedSumValid target terms common) :
    target ≈ listQSum id terms := by
  rcases hvalid with ⟨hcommon, htarget, hterms, hscaled⟩
  have htargetRep :=
    eqv_commonQ_of_zero_or_dvd common hcommon target htarget
  have hsumRep := listQSum_eqv_commonQ common hcommon terms
    (fun term hterm =>
      of_decide_eq_true (List.all_eq_true.mp hterms term hterm))
  exact Q'.eqv_trans _ _ _ htargetRep
    (Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (congrArg (commonQ common hcommon) hscaled))
      (Q'.eqv_symm hsumRep))

end YMGap.Continuum.FiniteClearedRationalSumCertificate

#print axioms
  YMGap.Continuum.FiniteClearedRationalSumCertificate.eqv_commonQ
#print axioms
  YMGap.Continuum.FiniteClearedRationalSumCertificate.ClearedSumValid.sound
