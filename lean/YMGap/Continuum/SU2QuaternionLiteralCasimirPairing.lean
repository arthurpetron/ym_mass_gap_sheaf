/-
# Literal differential representative of the diagonal cyclic Casimir

The computed full-cycle Casimir pairing is identified with the original
product-Haar pairing against the literal sum of negative angular Laplacians.
The proof is blockwise integration by parts and does not use a joint harmonic
eigenaction or a commuting-projector premise.
-/

import YMGap.Continuum.SU2QuaternionChannelCasimirLocality
import YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear
import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt

namespace YMGap.Continuum.SU2QuaternionLiteralCasimirPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.SU2QuaternionChannelAngularContraction
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicCasimirSweep
open YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem sixValue_neg_local (f : Nat → Nat → Q') :
    sixValue (fun i j => -(f i j)) ≈ -(sixValue f) := by
  have h (a b c : Q') (hbc : b ≈ -c) : -a+b ≈ -(a+c) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hbc)
      (Q'.eqv_symm (Q'.neg_add_eqv a c))
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _
    (Q'.eqv_symm (Q'.neg_add_eqv (f 1 3) (f 2 3))))))

private theorem haar_mul_neg (n : Nat) (p q : RatPoly) :
    H n (polyMul p (polyNeg q)) ≈ -(H n (polyMul p q)) := by
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (((QuaternionHaarAngularCarrier.neg_smul q).mul_left p).trans
      (RatPolyCoeffEqv.polyMul_smul_right (-1) p q)))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) _)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
        (.neg (.var 0)) (by decide) (fun _ => H n (polyMul p q))))

/-- The six-plane bilinear angular pairing at one original block. -/
def blockAngularPairValue (n block : Nat) (test p : RatPoly) : Q' :=
  sixValue (fun i j => H n (polyMul
    (blockAngularDerivative block i j test)
    (blockAngularDerivative block i j p)))

/-- Arbitrary-test blockwise integration by parts.  This is the literal
bilinear identity needed before any diagonal or square specialization. -/
theorem blockAngularLaplacian_pair (n block : Nat) (hblock : block < n)
    (test p : RatPoly) :
    H n (polyMul test (polyNeg (blockAngularLaplacian block p))) ≈
      blockAngularPairValue n block test p := by
  let second := fun i j => H n (polyMul test
    (blockAngularDerivative block i j
      (blockAngularDerivative block i j p)))
  have hplane (i j : Nat) (hi : i < 4) (hj : j < 4) :
      second i j ≈ -(H n (polyMul
        (blockAngularDerivative block i j test)
        (blockAngularDerivative block i j p))) :=
    angular_pair_at hblock hi hj test
      (blockAngularDerivative block i j p)
  have hlap : H n (polyMul test (blockAngularLaplacian block p)) ≈
      -(blockAngularPairValue n block test p) := by
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff ((blockAngularLaplacian_eq_six block p).mul_left test))
      (Q'.eqv_trans _ _ _ (haar_six n test _)
        (Q'.eqv_trans _ _ _
          (sixValue_congr _ _ (fun i j hi hj => hplane i j hi hj))
          (sixValue_neg_local _)))
  exact Q'.eqv_trans _ _ _ (haar_mul_neg n test _)
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hlap)
      (poly_identity_of_normal_eq (.neg (.neg (.var 0))) (.var 0)
        (by decide) (fun _ => blockAngularPairValue n block test p)))

/-- Blockwise integration by parts identifies one literal negative angular
Laplacian with its six-plane angular square. -/
theorem blockAngularLaplacian_self_pair (n block : Nat) (hblock : block < n)
    (p : RatPoly) :
    H n (polyMul p (polyNeg (blockAngularLaplacian block p))) ≈
      H n (blockAngularSquare block p) := by
  have hbilinear := blockAngularLaplacian_pair n block hblock p p
  exact Q'.eqv_trans _ _ _ hbilinear
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul _)))
        (Q'.eqv_trans _ _ _
          (haar_six n polyOne (fun i j => polyMul
            (blockAngularDerivative block i j p)
            (blockAngularDerivative block i j p)))
          (sixValue_congr _ _ (fun i j _ _ =>
            haar_of_coeff (RatPolyCoeffEqv.one_mul
              (polyMul (blockAngularDerivative block i j p)
                (blockAngularDerivative block i j p))))))))
      (Q'.eqv_refl _))
/-- Pairing against a finite literal Casimir list is the sum of its blockwise
bilinear angular pairings. -/
theorem activeCasimirPolynomial_pair (n : Nat) : ∀ (active : List Nat),
    (∀ i, i ∈ active → i < n) → ∀ test p : RatPoly,
    H n (polyMul test (activeCasimirPolynomial active p)) ≈
      qListSum (active.map fun block => blockAngularPairValue n block test p)
  | [], _, test, _ => haar_of_coeff (RatPolyCoeffEqv.mul_zero_right test)
  | block::active, hactive, test, p => by
      change H n (polyMul test (polyAdd _ _)) ≈
        blockAngularPairValue n block test p +
          qListSum (active.map fun i => blockAngularPairValue n i test p)
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_trans _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.mul_add_right test _ _))
          (quaternionHaar_append n _ _))
        (Q'.add_eqv_congr'
          (blockAngularLaplacian_pair n block
            (hactive block List.mem_cons_self) test p)
          (activeCasimirPolynomial_pair n active
            (fun i hi => hactive i (List.mem_cons_of_mem block hi)) test p))

private theorem blockAngularPairValue_symm (n block : Nat) (p q : RatPoly) :
    blockAngularPairValue n block p q ≈ blockAngularPairValue n block q p :=
  sixValue_congr _ _ (fun _ _ _ _ =>
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))

private theorem qsum_blockPair_symm (n : Nat) : ∀ (ids : List Nat) p q,
    qListSum (ids.map fun block => blockAngularPairValue n block p q) ≈
      qListSum (ids.map fun block => blockAngularPairValue n block q p)
  | [], _, _ => Q'.eqv_refl _
  | block::ids, p, q => Q'.add_eqv_congr'
      (blockAngularPairValue_symm n block p q)
      (qsum_blockPair_symm n ids p q)

private theorem literalPair_symm (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (p q : RatPoly) :
    H n (polyMul q (activeCasimirPolynomial active p)) ≈
      H n (polyMul p (activeCasimirPolynomial active q)) := by
  exact Q'.eqv_trans _ _ _ (activeCasimirPolynomial_pair n active hactive q p)
    (Q'.eqv_trans _ _ _ (qsum_blockPair_symm n active q p)
      (Q'.eqv_symm (activeCasimirPolynomial_pair n active hactive p q)))

private theorem literalPair_add_test (n : Nat) (active : List Nat)
    (p q r : RatPoly) :
    H n (polyMul (polyAdd q r) (activeCasimirPolynomial active p)) ≈
      H n (polyMul q (activeCasimirPolynomial active p)) +
        H n (polyMul r (activeCasimirPolynomial active p)) := by
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans
      ((RatPolyCoeffEqv.mul_add_right _ q r).trans
        ((RatPolyCoeffEqv.mul_comm _ q).add
          (RatPolyCoeffEqv.mul_comm _ r)))))
    (quaternionHaar_append n _ _)

private theorem literalPair_add_source (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (p q r : RatPoly) :
    H n (polyMul r (activeCasimirPolynomial active (polyAdd p q))) ≈
      H n (polyMul r (activeCasimirPolynomial active p)) +
        H n (polyMul r (activeCasimirPolynomial active q)) := by
  exact Q'.eqv_trans _ _ _ (literalPair_symm n active hactive (polyAdd p q) r)
    (Q'.eqv_trans _ _ _ (literalPair_add_test n active r p q)
      (Q'.add_eqv_congr'
        (Q'.eqv_symm (literalPair_symm n active hactive p r))
        (Q'.eqv_symm (literalPair_symm n active hactive q r))))

private theorem haar_activeCasimir_self (n : Nat) : ∀ (active : List Nat),
    (∀ i, i ∈ active → i < n) → ∀ p : RatPoly,
    H n (polyMul p (activeCasimirPolynomial active p)) ≈
      angularListSum n active p
  | [], _, p => haar_of_coeff (RatPolyCoeffEqv.mul_zero_right p)
  | block::active, hactive, p => by
      change H n (polyMul p (polyAdd _ _)) ≈
        H n (blockAngularSquare block p) + angularListSum n active p
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_trans _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.mul_add_right p _ _))
          (quaternionHaar_append n _ _))
        (Q'.add_eqv_congr'
          (blockAngularLaplacian_self_pair n block
            (hactive block List.mem_cons_self) p)
          (haar_activeCasimir_self n active
            (fun i hi => hactive i (List.mem_cons_of_mem block hi)) p))

/-- The diagonal computed Casimir is pairing with the literal positive
Casimir polynomial over every original block. -/
theorem pairCasimir_diagonal_eq_literal (n : Nat) (hn : 0 < n)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    pairCasimir (n-1) p p ≈
      H n (polyMul p (activeCasimirPolynomial (List.range n) p)) := by
  exact Q'.eqv_trans _ _ _
    (pairCasimir_diagonal_eq_angularListSum n hn p hp)
    (Q'.eqv_symm (haar_activeCasimir_self n (List.range n)
      (fun i hi => List.mem_range.mp hi) p))

/-- The computed cyclic Casimir pairing is the original Haar pairing against
the literal full positive-Casimir polynomial, for an arbitrary signed test. -/
theorem pairCasimir_eq_literal (tail : Nat)
    (p test : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (ht : SupportedQuaternionBlocks (tail+1) test) :
    pairCasimir tail p test ≈
      H (tail+1) (polyMul test
        (activeCasimirPolynomial (List.range (tail+1)) p)) := by
  let C := fun p q : RatPoly => H (tail+1)
    (polyMul q (activeCasimirPolynomial (List.range (tail+1)) p))
  let z := polyAdd p test
  have hz : SupportedQuaternionBlocks (tail+1) z := supported_add hp ht
  have haddA_left (a b c : RatPoly)
      (ha : SupportedQuaternionBlocks (tail+1) a)
      (hb : SupportedQuaternionBlocks (tail+1) b)
      (hc : SupportedQuaternionBlocks (tail+1) c) :
      pairCasimir tail (polyAdd a b) c ≈
        pairCasimir tail a c + pairCasimir tail b c := by
    exact Q'.eqv_trans _ _ _
      (pairCasimir_symm tail (polyAdd a b) c (supported_add ha hb) hc)
      (Q'.eqv_trans _ _ _ (pairCasimir_add_right tail c a b hc)
        (Q'.add_eqv_congr'
          (pairCasimir_symm tail c a hc ha)
          (pairCasimir_symm tail c b hc hb)))
  have hAexpand : pairCasimir tail z z ≈
      (pairCasimir tail p p + pairCasimir tail p test) +
        (pairCasimir tail test p + pairCasimir tail test test) := by
    exact Q'.eqv_trans _ _ _ (haddA_left p test z hp ht hz)
      (Q'.add_eqv_congr'
        (pairCasimir_add_right tail p p test hp)
        (pairCasimir_add_right tail test p test ht))
  have hBexpand : C z z ≈
      (C p p + C p test) + (C test p + C test test) := by
    exact Q'.eqv_trans _ _ _
      (literalPair_add_source (tail+1) (List.range (tail+1))
        (fun i hi => List.mem_range.mp hi) p test z)
      (Q'.add_eqv_congr'
        (literalPair_add_test (tail+1) (List.range (tail+1)) p p test)
        (literalPair_add_test (tail+1) (List.range (tail+1)) test p test))
  have hdiagZ : pairCasimir tail z z ≈ C z z :=
    pairCasimir_diagonal_eq_literal (tail+1) (by omega) z hz
  have hdiagP : pairCasimir tail p p ≈ C p p :=
    pairCasimir_diagonal_eq_literal (tail+1) (by omega) p hp
  have hdiagT : pairCasimir tail test test ≈ C test test :=
    pairCasimir_diagonal_eq_literal (tail+1) (by omega) test ht
  have hsymA : pairCasimir tail test p ≈ pairCasimir tail p test :=
    pairCasimir_symm tail test p ht hp
  have hsymB : C test p ≈ C p test :=
    literalPair_symm (tail+1) (List.range (tail+1))
      (fun i hi => List.mem_range.mp hi) test p
  let XA := (pairCasimir tail p p + pairCasimir tail p test) +
    (pairCasimir tail p test + pairCasimir tail test test)
  let XB := (C p p + C p test) + (C p test + C test test)
  have hXA : pairCasimir tail z z ≈ XA :=
    Q'.eqv_trans _ _ _ hAexpand
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.add_eqv_congr' hsymA (Q'.eqv_refl _)))
  have hXB : C z z ≈ XB :=
    Q'.eqv_trans _ _ _ hBexpand
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.add_eqv_congr' hsymB (Q'.eqv_refl _)))
  have hcommon : XA ≈ XB :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hXA)
      (Q'.eqv_trans _ _ _ hdiagZ hXB)
  have htwo : (Q'.ofNat 2) * pairCasimir tail p test ≈
      (Q'.ofNat 2) * C p test := by
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.const 2) (.var 1))
        (.add (.add
          (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 2)))
          (.neg (.var 0))) (.neg (.var 2)))
        (by decide)
        (fun | 0 => pairCasimir tail p p
             | 1 => pairCasimir tail p test
             | _ => pairCasimir tail test test))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' hcommon
            (Q'.neg_eqv_congr _ _ hdiagP))
          (Q'.neg_eqv_congr _ _ hdiagT))
        (poly_identity_of_normal_eq
          (.add (.add
            (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 2)))
            (.neg (.var 0))) (.neg (.var 2)))
          (.mul (.const 2) (.var 1))
          (by decide) (fun | 0 => C p p | 1 => C p test | _ => C test test)))
  exact Q'.mul_left_cancel_of_pos (Q'.ofNat_succ_pos 1) htwo

/-- The literal full Casimir has the same original Haar square as the cyclic
differential sweep.  No pointwise polynomial identity is asserted. -/
theorem casimirSweep_square_eq_literal (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    H (tail+1) (polyMul (casimirSweep tail (tail+1) p)
      (casimirSweep tail (tail+1) p)) ≈
    H (tail+1) (polyMul
      (activeCasimirPolynomial (List.range (tail+1)) p)
      (activeCasimirPolynomial (List.range (tail+1)) p)) := by
  let S := casimirSweep tail (tail+1) p
  let C := activeCasimirPolynomial (List.range (tail+1)) p
  have hS : SupportedQuaternionBlocks (tail+1) S :=
    casimirSweep_supported tail (tail+1) hp
  have hC : SupportedQuaternionBlocks (tail+1) C :=
    activeCasimirPolynomial_supported (List.range (tail+1))
      (fun i hi => List.mem_range.mp hi) hp
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (pairCasimir_sweep tail p S hp))
    (Q'.eqv_trans _ _ _ (pairCasimir_eq_literal tail p S hp hS)
      (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm S C))
        (Q'.eqv_trans _ _ _
          (Q'.eqv_symm (pairCasimir_sweep tail p C hp))
          (pairCasimir_eq_literal tail p C hp hC))))

/-- If the source is independent of every passive block in a covering
partition, the full cyclic Casimir square is exactly the active-only literal
Casimir square. -/
theorem casimirSweep_square_eq_active (tail : Nat)
    (passive active : List Nat)
    (hcover : (passive ++ active).Perm (List.range (tail+1)))
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hpassive : ∀ block, block ∈ passive → QuaternionBlockIndependent block p) :
    H (tail+1) (polyMul (casimirSweep tail (tail+1) p)
      (casimirSweep tail (tail+1) p)) ≈
    H (tail+1) (polyMul (activeCasimirPolynomial active p)
      (activeCasimirPolynomial active p)) := by
  have hrange := activeCasimirPolynomial_range_eq_active (tail+1)
    passive active hcover p hpassive
  exact Q'.eqv_trans _ _ _ (casimirSweep_square_eq_literal tail p hp)
    (haar_of_coeff (hrange.mul hrange))

end YMGap.Continuum.SU2QuaternionLiteralCasimirPairing

#print axioms YMGap.Continuum.SU2QuaternionLiteralCasimirPairing.blockAngularLaplacian_self_pair
#print axioms YMGap.Continuum.SU2QuaternionLiteralCasimirPairing.blockAngularLaplacian_pair
#print axioms YMGap.Continuum.SU2QuaternionLiteralCasimirPairing.activeCasimirPolynomial_pair
#print axioms YMGap.Continuum.SU2QuaternionLiteralCasimirPairing.pairCasimir_diagonal_eq_literal
#print axioms YMGap.Continuum.SU2QuaternionLiteralCasimirPairing.pairCasimir_eq_literal
#print axioms YMGap.Continuum.SU2QuaternionLiteralCasimirPairing.casimirSweep_square_eq_literal
#print axioms YMGap.Continuum.SU2QuaternionLiteralCasimirPairing.casimirSweep_square_eq_active
