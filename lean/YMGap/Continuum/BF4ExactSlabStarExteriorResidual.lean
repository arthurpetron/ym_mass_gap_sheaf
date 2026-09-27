/-
# Supported exterior multipliers of original slab polynomials

An exterior polynomial is lifted through the selected-link head swap and
multiplied by an original full-action polynomial. This file records the exact
supported seed, the literal lifted multiplication law, and commutation with
the true residual in the SAME completed full-action carrier. Numerator
transport is proved through the original form, not assumed coefficientwise.
No inverse, coarse comparison, or global coercivity is asserted.
-/

import YMGap.Continuum.BF4ExactSlabStarPolynomialResidual

namespace YMGap.Continuum.BF4ExactSlabStarExteriorResidual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabStarPolynomialResidual
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (i : PhysicalLink extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => exteriorData hw0 hw1 K extent hK i.val i.property
local notation "J" => probeMap hw0 hw1 K extent hK i.val i.property
local notation "N" => numeratorMap hw0 hw1 K extent hK i.val i.property

/-- A literal supported original-action polynomial with an exterior factor. -/
def exteriorSeed (r : (G).V) (p : (F).V) : (F).V :=
  ⟨polyMul (J r).val p.val, supported_polyMul (J r).property p.property⟩

/-- Exterior multiplication is performed before integration on the original
full-action carrier; the head-probe product is an exact polynomial identity. -/
theorem exteriorSeed_probe_mul (r s : (G).V) (p : (F).V) :
    (F).veq
      (exteriorSeed hw0 hw1 K extent hK i
        ⟨polyMul r.val s.val, supported_polyMul r.property s.property⟩ p)
      (exteriorSeed hw0 hw1 K extent hK i r
        (exteriorSeed hw0 hw1 K extent hK i s p)) := by
  change RatPolyCoeffEqv
    (polyMul (headProbe (linkHeadSwap extent i.val i.property)
      (polyMul r.val s.val)) p.val)
    (polyMul (headProbe (linkHeadSwap extent i.val i.property) r.val)
      (polyMul (headProbe (linkHeadSwap extent i.val i.property) s.val) p.val))
  rw [headProbe_mul]
  exact RatPolyCoeffEqv.mul_assoc _ _ _

private def exteriorProduct (r s : (G).V) : (G).V :=
  ⟨polyMul r.val s.val, supported_polyMul r.property s.property⟩

private theorem probe_seed_pair (r s : (G).V) (p : (F).V) :
    (F).B (J s) (exteriorSeed hw0 hw1 K extent hK i r p) ≈
      (F).B (J (exteriorProduct hw0 hw1 K extent hK i s r)) p := by
  have hp : RatPolyCoeffEqv
      (polyMul (J s).val (exteriorSeed hw0 hw1 K extent hK i r p).val)
      (polyMul (J (exteriorProduct hw0 hw1 K extent hK i s r)).val p.val) := by
    change RatPolyCoeffEqv
      (polyMul (headProbe (linkHeadSwap extent i.val i.property) s.val)
        (polyMul (headProbe (linkHeadSwap extent i.val i.property) r.val) p.val))
      (polyMul (headProbe (linkHeadSwap extent i.val i.property)
        (polyMul s.val r.val)) p.val)
    rw [headProbe_mul]
    exact (RatPolyCoeffEqv.mul_assoc _ _ _).symm
  change weightedPair _ _ _ _ ≈ weightedPair _ _ _ _
  exact haar_of_coeff (hp.mul_right _)

/-- The inserted numerator obeys exterior multiplication in the original
exterior form, including its untouched complementary action. -/
theorem numerator_exterior_pair (r s : (G).V) (p : (F).V) :
    (G).B s (N (exteriorSeed hw0 hw1 K extent hK i r p)) ≈
      (G).B s (exteriorProduct hw0 hw1 K extent hK i r (N p)) := by
  have hleft := probeMap_test hw0 hw1 K extent hK i.val i.property s
    (exteriorSeed hw0 hw1 K extent hK i r p)
  have hmiddle := probe_seed_pair hw0 hw1 K extent hK i r s p
  have hright := probeMap_test hw0 hw1 K extent hK i.val i.property
    (exteriorProduct hw0 hw1 K extent hK i s r) p
  have hproduct :
      (G).B (exteriorProduct hw0 hw1 K extent hK i s r) (N p) ≈
        (G).B s (exteriorProduct hw0 hw1 K extent hK i r (N p)) := by
    change weightedPair _ _ _ _ ≈ weightedPair _ _ _ _
    exact haar_of_coeff ((RatPolyCoeffEqv.mul_assoc s.val r.val (N p).val).mul_right _)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hmiddle (Q'.eqv_trans _ _ _ hright hproduct))

private theorem rad_of_pair_eq (D : GNSData) (a b : D.V)
    (h : ∀ s : D.V, (D.B s a).eqv (D.B s b)) : D.rad a b := by
  let d := D.sub a b
  have hd : (D.B d d).eqv (D.B d a + -(D.B d b)) :=
    Q'.eqv_trans _ _ _ (D.B_add_right d a (D.neg b))
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (D.B_neg_right d b))
  exact Q'.eqv_trans _ _ _ hd
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (h d) (Q'.eqv_refl _))
      (Q'.add_neg_self_eqv _))

theorem numerator_exterior_rad (r : (G).V) (p : (F).V) :
    (G).rad (N (exteriorSeed hw0 hw1 K extent hK i r p))
      (exteriorProduct hw0 hw1 K extent hK i r (N p)) :=
  rad_of_pair_eq _ _ _ (fun s => numerator_exterior_pair hw0 hw1 K extent hK i r s p)

private theorem probe_numerator_exterior_pair (r : (G).V) (p f : (F).V) :
    (F).B f (J (N (exteriorSeed hw0 hw1 K extent hK i r p))) ≈
      (F).B f (J (exteriorProduct hw0 hw1 K extent hK i r (N p))) := by
  let a := N (exteriorSeed hw0 hw1 K extent hK i r p)
  let b := exteriorProduct hw0 hw1 K extent hK i r (N p)
  have ha := probeMap_test hw0 hw1 K extent hK i.val i.property a f
  have hb := probeMap_test hw0 hw1 K extent hK i.val i.property b f
  have hpair := numerator_exterior_pair hw0 hw1 K extent hK i r (N f) p
  exact Q'.eqv_trans _ _ _ ((F).B_symm f (J a))
    (Q'.eqv_trans _ _ _ ha
      (Q'.eqv_trans _ _ _ ((G).B_symm a (N f))
        (Q'.eqv_trans _ _ _ hpair
          (Q'.eqv_trans _ _ _ ((G).B_symm (N f) b)
            (Q'.eqv_trans _ _ _ (Q'.eqv_symm hb)
              ((F).B_symm (J b) f))))))

theorem probe_numerator_exterior_rad (r : (G).V) (p : (F).V) :
    (F).rad (J (N (exteriorSeed hw0 hw1 K extent hK i r p)))
      (J (exteriorProduct hw0 hw1 K extent hK i r (N p))) :=
  rad_of_pair_eq _ _ _
    (fun f => probe_numerator_exterior_pair hw0 hw1 K extent hK i r p f)

private theorem rad_of_veq (D : GNSData) {a b : D.V} (h : D.veq a b) :
    D.rad a b := by
  have hd : D.veq (D.sub a b) D.zero :=
    D.veq_trans (D.add_congr h (D.veq_refl (D.neg b)))
      (D.veq_trans (D.add_comm b (D.neg b)) (D.neg_add b))
  exact Q'.eqv_trans _ _ _ (D.B_diag_congr hd) (D.B_zero_left D.zero)

private theorem exteriorSeed_sub (r : (G).V) (a b : (F).V) :
    (F).veq (exteriorSeed hw0 hw1 K extent hK i r ((F).sub a b))
      ((F).sub (exteriorSeed hw0 hw1 K extent hK i r a)
        (exteriorSeed hw0 hw1 K extent hK i r b)) := by
  change RatPolyCoeffEqv
    (polyMul (J r).val (polyAdd a.val (polySmul (-1) b.val)))
    (polyAdd (polyMul (J r).val a.val)
      (polySmul (-1) (polyMul (J r).val b.val)))
  exact (RatPolyCoeffEqv.mul_add_right _ _ _).trans
    ((RatPolyCoeffEqv.refl _).add
      (RatPolyCoeffEqv.polyMul_smul_right (-1) _ _))

private def density : (G).V :=
  ⟨normalizer w K extent i.val i.property,
    normalizer_supported w K extent i.val i.property⟩

private theorem residual_as_sub (p : (F).V) :
    (F).veq (polynomialResidual hw0 hw1 K extent hK i p)
      ((F).sub (exteriorSeed hw0 hw1 K extent hK i
        (density hw0 hw1 K extent hK i) p) (J (N p))) := by
  change RatPolyCoeffEqv _ _
  exact RatPolyCoeffEqv.refl _

private theorem density_seed_comm (r : (G).V) (p : (F).V) :
    (F).veq
      (exteriorSeed hw0 hw1 K extent hK i (density hw0 hw1 K extent hK i)
        (exteriorSeed hw0 hw1 K extent hK i r p))
      (exteriorSeed hw0 hw1 K extent hK i r
        (exteriorSeed hw0 hw1 K extent hK i
          (density hw0 hw1 K extent hK i) p)) := by
  change RatPolyCoeffEqv
    (polyMul (J (density hw0 hw1 K extent hK i)).val
      (polyMul (J r).val p.val))
    (polyMul (J r).val
      (polyMul (J (density hw0 hw1 K extent hK i)).val p.val))
  exact (RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans
    (((RatPolyCoeffEqv.mul_comm _ _).mul_right _).trans
      (RatPolyCoeffEqv.mul_assoc _ _ _))

private theorem probe_exterior_product (r s : (G).V) :
    (F).veq (J (exteriorProduct hw0 hw1 K extent hK i r s))
      (exteriorSeed hw0 hw1 K extent hK i r (J s)) := by
  change RatPolyCoeffEqv
    (headProbe (linkHeadSwap extent i.val i.property) (polyMul r.val s.val))
    (polyMul (headProbe (linkHeadSwap extent i.val i.property) r.val)
      (headProbe (linkHeadSwap extent i.val i.property) s.val))
  rw [headProbe_mul]
  exact RatPolyCoeffEqv.refl _

/-- Exterior scaling commutes with the true polynomial residual modulo the
original full-action radical. No coefficient equality of bare numerators is
assumed: their equality is proved against every exterior test above. -/
theorem polynomialResidual_exteriorSeed_rad (r : (G).V) (p : (F).V) :
    (F).rad
      (polynomialResidual hw0 hw1 K extent hK i
        (exteriorSeed hw0 hw1 K extent hK i r p))
      (exteriorSeed hw0 hw1 K extent hK i r
        (polynomialResidual hw0 hw1 K extent hK i p)) := by
  let d := density hw0 hw1 K extent hK i
  let x := exteriorSeed hw0 hw1 K extent hK i r p
  have hleft := rad_of_veq F (residual_as_sub hw0 hw1 K extent hK i x)
  have hdensity := rad_of_veq F (density_seed_comm hw0 hw1 K extent hK i r p)
  have hn1 := probe_numerator_exterior_rad hw0 hw1 K extent hK i r p
  have hn2 := rad_of_veq F
    (probe_exterior_product hw0 hw1 K extent hK i r (N p))
  have hn := (F).rad_trans hn1 hn2
  have hsub := (F).rad_add hdensity ((F).rad_neg hn)
  have hright0 := rad_of_veq F
    (exteriorSeed_sub hw0 hw1 K extent hK i r
      (exteriorSeed hw0 hw1 K extent hK i d p) (J (N p)))
  have hright1 :
      (F).veq
        (exteriorSeed hw0 hw1 K extent hK i r
          (polynomialResidual hw0 hw1 K extent hK i p))
        (exteriorSeed hw0 hw1 K extent hK i r
          ((F).sub (exteriorSeed hw0 hw1 K extent hK i d p) (J (N p)))) := by
    change RatPolyCoeffEqv _ _
    exact RatPolyCoeffEqv.mul_left (J r).val
      (residual_as_sub hw0 hw1 K extent hK i p)
  have hright := (F).rad_trans ((F).rad_symm hright0)
    ((F).rad_symm (rad_of_veq F hright1))
  exact (F).rad_trans hleft ((F).rad_trans hsub hright)

/-- The equality used by the completed original-action residual energy. -/
theorem polynomialResidual_exteriorSeed_completed (r : (G).V) (p : (F).V) :
    embedV F (polynomialResidual hw0 hw1 K extent hK i
      (exteriorSeed hw0 hw1 K extent hK i r p)) =
    embedV F (exteriorSeed hw0 hw1 K extent hK i r
      (polynomialResidual hw0 hw1 K extent hK i p)) :=
  Quotient.sound (embed_null_of_rad F
    (polynomialResidual_exteriorSeed_rad hw0 hw1 K extent hK i r p))

#print axioms exteriorSeed
#print axioms exteriorSeed_probe_mul
#print axioms numerator_exterior_pair
#print axioms numerator_exterior_rad
#print axioms probe_numerator_exterior_rad
#print axioms polynomialResidual_exteriorSeed_rad
#print axioms polynomialResidual_exteriorSeed_completed

end YMGap.Continuum.BF4ExactSlabStarExteriorResidual
