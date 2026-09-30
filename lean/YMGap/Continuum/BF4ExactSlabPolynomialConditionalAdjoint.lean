/-
# Exact adjoint of the pure finite block conditional polynomial

The finite inverse iteration is a polynomial in multiplication by the actual
block normalizer.  Its symmetry in the detached original background form
passes through the exact inserted-numerator pairing to the complete original
finite-slab action.  This is a source-level equality at fixed finite cutoff;
no completed inverse, gap, or degree truncation is used.
-/

import YMGap.Continuum.BF4ExactSlabBlockInverseAlgebra
import YMGap.Continuum.BF4ExactSlabBlockConditionalApproximation
import YMGap.Continuum.BF4ExactSlabBlockInsertedNorm
import YMGap.Continuum.BF4ExactSlabStarFullActionProbe

namespace YMGap.Continuum.BF4ExactSlabPolynomialConditionalAdjoint

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockInverseApproximation
open YMGap.Continuum.BF4ExactSlabBlockInverseAlgebra
open YMGap.Continuum.BF4ExactSlabBlockConditionalApproximation
open YMGap.Continuum.BF4ExactSlabBlockInsertedNorm
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)

local notation "G" => backgroundData hw0 hw1 K extent hK links
local notation "F" => fullData hw0 hw1 K extent hK
local notation "M" => normalizerMap hw0 hw1 K extent hK links
local notation "A" => approximateInverse hw0 hw1 K extent hK links
local notation "s" => HKConv.divPos 1 (blockUpper w links.length)

/-- The existing right-factor law, specialized to the actual normalizer,
commutes every finite inverse iterate with its multiplier. -/
theorem approximateInverse_commutes_normalizer (r : (G).V) (n : Nat) :
    (G).veq (A (M r) n) (M (A r n)) := by
  let d : (G).V := ⟨normalizer w K extent links,
    normalizer_supported w K extent links⟩
  have h := approximateInverse_mul_right hw0 hw1 K extent hK links r d n
  change (G).veq (A (M r) n) (M (A r n)) at h
  exact h

private theorem pair_sub_left (a b c : (G).V) :
    (G).B ((G).sub a b) c ≈ (G).B a c + -((G).B b c) :=
  Q'.eqv_trans _ _ _ ((G).B_add_left a ((G).neg b) c)
    (Q'.add_eqv_congr_left _ _ _ ((G).B_neg_left b c))

private theorem pair_sub_right (a b c : (G).V) :
    (G).B a ((G).sub b c) ≈ (G).B a b + -((G).B a c) :=
  Q'.eqv_trans _ _ _ ((G).B_add_right a b ((G).neg c))
    (Q'.add_eqv_congr_left _ _ _ ((G).B_neg_right a c))

private theorem pair_zero_right (a : (G).V) :
    (G).B a (G).zero ≈ 0 :=
  Q'.eqv_trans _ _ _ ((G).B_symm a (G).zero) ((G).B_zero_left a)

/-- Every finite inverse iterate is symmetric in the actual detached
background pairing, for arbitrary supported source polynomials. -/
theorem approximateInverse_symmetric (r t : (G).V) :
    ∀ n : Nat, (G).B (A r n) t ≈ (G).B r (A t n)
  | 0 => Q'.eqv_trans _ _ _ ((G).B_zero_left t)
      (Q'.eqv_symm (pair_zero_right hw0 hw1 K extent hK links r))
  | n+1 => by
      let ar := A r n
      let ta := A t n
      have hmain : (G).B ar t ≈ (G).B r ta :=
        approximateInverse_symmetric r t n
      have hcomm : (G).veq (A (M t) n) (M ta) :=
        approximateInverse_commutes_normalizer hw0 hw1 K extent hK links t n
      have hcross : (G).B (M ar) t ≈ (G).B r (M ta) :=
        Q'.eqv_trans _ _ _
          (Q'.eqv_symm (normalizerMap_symmetric hw0 hw1 K extent hK links ar t))
          (Q'.eqv_trans _ _ _
            (approximateInverse_symmetric r (M t) n)
            ((G).B_congr_right r hcomm))
      have hsub :
          (G).B r t + -((G).B (M ar) t) ≈
            (G).B r t + -((G).B r (M ta)) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hcross)
      have hleft :
          (G).B ((G).add ar ((G).smul s ((G).sub r (M ar)))) t ≈
            (G).B ar t + s * ((G).B r t + -((G).B (M ar) t)) :=
        Q'.eqv_trans _ _ _ ((G).B_add_left ar _ t)
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_trans _ _ _ ((G).B_smul_left s _ t)
              (Q'.mul_eqv_congr_left s _ _ (pair_sub_left hw0 hw1 K extent hK links r (M ar) t))))
      have hright :
          (G).B r ((G).add ta ((G).smul s ((G).sub t (M ta)))) ≈
            (G).B r ta + s * ((G).B r t + -((G).B r (M ta))) :=
        Q'.eqv_trans _ _ _ ((G).B_add_right r ta _)
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_trans _ _ _ ((G).B_smul_right s r _)
              (Q'.mul_eqv_congr_left s _ _ (pair_sub_right hw0 hw1 K extent hK links r t (M ta)))))
      change (G).B ((G).add ar ((G).smul s ((G).sub r (M ar)))) t ≈
        (G).B r ((G).add ta ((G).smul s ((G).sub t (M ta))))
      exact Q'.eqv_trans _ _ _ hleft
        (Q'.eqv_trans _ _ _
          (QPoly.q_add_congr hmain (Q'.mul_eqv_congr_left s _ _ hsub))
          (Q'.eqv_symm hright))

variable (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)

include hl in
/-- Exact original-action self-adjointness of the PURE polynomial conditional
approximant.  Both inserted numerators and all spectator factors are retained. -/
theorem conditionalApproximation_symmetric (p q : (F).V) (n : Nat) :
    let ap := conditionalApproximation hw0 hw1 K extent hK links p.val p.property n
    let aq := conditionalApproximation hw0 hw1 K extent hK links q.val q.property n
    (F).B ap q ≈ (F).B p aq := by
  let rp := numeratorVector hw0 hw1 K extent hK links p.val p.property
  let rq := numeratorVector hw0 hw1 K extent hK links q.val q.property
  let ap := conditionalApproximation hw0 hw1 K extent hK links p.val p.property n
  let aq := conditionalApproximation hw0 hw1 K extent hK links q.val q.property n
  have hp : (F).B ap q ≈ (G).B ap rq :=
    insertedNormalizer_pair_pin w K extent links hl ap.val q.val
      (fun i hi => conditionalApproximation_independent hw0 hw1 K extent hK links
        p.val p.property n i hi)
  have hq : (F).B aq p ≈ (G).B aq rp :=
    insertedNormalizer_pair_pin w K extent links hl aq.val p.val
      (fun i hi => conditionalApproximation_independent hw0 hw1 K extent hK links
        q.val q.property n i hi)
  have hs : (G).B ap rq ≈ (G).B rp aq :=
    approximateInverse_symmetric hw0 hw1 K extent hK links rp rq n
  exact Q'.eqv_trans _ _ _ hp
    (Q'.eqv_trans _ _ _ hs
      (Q'.eqv_trans _ _ _ ((G).B_symm rp aq)
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm hq)
          ((F).B_symm aq p))))

#print axioms approximateInverse_commutes_normalizer
#print axioms approximateInverse_symmetric
#print axioms conditionalApproximation_symmetric

end YMGap.Continuum.BF4ExactSlabPolynomialConditionalAdjoint
