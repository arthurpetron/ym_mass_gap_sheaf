/-
# Upper Casimir eigenaction on the actual character product

The negative block Laplacians over the upper endpoints act diagonally on the
literal product of normalized relative characters.  Cross terms disappear
because every other factor is independent of the differentiated block.
-/

import YMGap.Continuum.SU2QuaternionCharacterCasimirLocality
import YMGap.Continuum.SU2QuaternionCharacterEndpointSymmetry
import YMGap.Continuum.SU2QuaternionCyclicCharacterPositive

namespace YMGap.Continuum.SU2QuaternionCharacterProductCasimir

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionCharacterProductPositive
open YMGap.Continuum.SU2QuaternionCyclicCharacterPositive
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionCharacterCasimirLocality
open YMGap.Continuum.SU2QuaternionCharacterEndpointSymmetry
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.QuaternionHaarAngularCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem tailProduct_independent (n origin : Nat) : ∀ (ds : List Nat)
    (start : Nat), origin < start → start + ds.length ≤ n →
    QuaternionBlockIndependent (n+origin)
      (characterProduct n (pathSlots start ds))
  | [], _, _, _ => quaternionBlockIndependent_polyOne _
  | d::ds, start, hlt, hbound => by
      simp only [List.length_cons] at hbound
      change QuaternionBlockIndependent (n+origin)
        (polyMul (normalizedCharacterAt start (n+start) d)
          (characterProduct n (pathSlots (start+1) ds)))
      apply quaternionBlockIndependent_polyMul
      · apply normalizedCharacterAt_independent
        · omega
        · omega
      · exact tailProduct_independent n origin ds (start+1) (by omega) (by
          omega)

private theorem activeTail_shift (n start : Nat) (ds : List Nat) :
    ((List.range ds.length).map fun i => n + (start+1) + i) =
      ((List.range ds.length).map fun i => n + start + (i+1)) := by
  apply List.map_congr_left
  intro i hi
  omega

private theorem upperRange_cons (n start len : Nat) :
    ((List.range (len+1)).map fun i => n+start+i) =
      (n+start) :: ((List.range len).map fun i => n+start+(i+1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1

private theorem ofNat_mul_eqv_local (a b : Nat) :
    Q'.ofNat (a*b) ≈ Q'.ofNat a * Q'.ofNat b := by
  show (a*b : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int) =
    (Q'.ofNat a * Q'.ofNat b).num * (1 : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Int.mul_one]

private theorem activeCasimirPolynomial_mul_independent : ∀ (active : List Nat)
    (p q : RatPoly),
    (∀ block, block ∈ active → QuaternionBlockIndependent block q) →
    RatPolyCoeffEqv (activeCasimirPolynomial active (polyMul p q))
      (polyMul (activeCasimirPolynomial active p) q)
  | [], p, q, _ => (RatPolyCoeffEqv.mul_zero_left q).symm
  | block::active, p, q, hq => by
      change RatPolyCoeffEqv (polyAdd _ _)
        (polyMul (polyAdd _ _) q)
      rw [polyMul_add_left_exact]
      have hhead : RatPolyCoeffEqv
          (polyNeg (blockAngularLaplacian block (polyMul p q)))
          (polyMul (polyNeg (blockAngularLaplacian block p)) q) :=
        (RatPolyCoeffEqv.neg
          (blockAngularLaplacian_mul_independent block p q
            (hq block List.mem_cons_self))).trans
          ((QuaternionHaarAngularCarrier.neg_smul _).trans
            ((RatPolyCoeffEqv.polyMul_smul_left (-1) _ q).symm.trans
              ((QuaternionHaarAngularCarrier.neg_smul
                (blockAngularLaplacian block p)).symm.mul_right q)))
      exact hhead.add
        (activeCasimirPolynomial_mul_independent active p q
          (fun i hi => hq i (List.mem_cons_of_mem block hi)))

private theorem blockAngularLaplacian_congr (block : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (blockAngularLaplacian block p)
      (blockAngularLaplacian block q) := by
  refine (blockAngularLaplacian_eq_six block p).trans ?_
  refine (RatPolyCoeffEqv.add
    (angularDerivative_congr _ _ (angularDerivative_congr _ _ h))
    ((angularDerivative_congr _ _ (angularDerivative_congr _ _ h)).add
      ((angularDerivative_congr _ _ (angularDerivative_congr _ _ h)).add
        ((angularDerivative_congr _ _ (angularDerivative_congr _ _ h)).add
          ((angularDerivative_congr _ _ (angularDerivative_congr _ _ h)).add
            (angularDerivative_congr _ _ (angularDerivative_congr _ _ h))))))).trans ?_
  exact (blockAngularLaplacian_eq_six block q).symm

private theorem activeCasimirPolynomial_mul_independent_left
    (active : List Nat) (p q : RatPoly)
    (hp : ∀ block, block ∈ active → QuaternionBlockIndependent block p) :
    RatPolyCoeffEqv (activeCasimirPolynomial active (polyMul p q))
      (polyMul p (activeCasimirPolynomial active q)) := by
  have hcomm : RatPolyCoeffEqv
      (activeCasimirPolynomial active (polyMul p q))
      (activeCasimirPolynomial active (polyMul q p)) := by
    induction active with
    | nil => exact RatPolyCoeffEqv.refl polyZero
    | cons block active ih =>
        exact (RatPolyCoeffEqv.neg
          (blockAngularLaplacian_congr block (RatPolyCoeffEqv.mul_comm p q))).add
            (ih (fun i hi => hp i (List.mem_cons_of_mem block hi)))
  exact hcomm.trans
    ((activeCasimirPolynomial_mul_independent active q p hp).trans
      (RatPolyCoeffEqv.mul_comm _ p))

/-- The upper-endpoint Casimir on a consecutive actual character product has
eigenvalue equal to the sum of the literal representation Casimirs. -/
theorem characterProduct_upperCasimir (n start : Nat) : ∀ (ds : List Nat),
    start + ds.length ≤ n →
    HaarCarrierEqv (n+n)
      (activeCasimirPolynomial
        ((List.range ds.length).map fun i => n+start+i)
        (characterProduct n (pathSlots start ds)))
      (polySmul (totalCasimir ds)
        (characterProduct n (pathSlots start ds)))
  | [], _ => RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.zero_smul polyOne).symm
  | d::ds, hbound => by
      let f := normalizedCharacterAt start (n+start) d
      let r := characterProduct n (pathSlots (start+1) ds)
      let c := Q'.ofNat (d*(d+2))
      let e := Q'.ofNat d * (Q'.ofNat d + Q'.ofNat 2)
      have hce : c ≈ e :=
        Q'.eqv_trans _ _ _ (ofNat_mul_eqv_local d (d+2))
          (Q'.mul_eqv_congr_left (Q'.ofNat d) _ _
            (Q'.ofNat_add_eqv d 2))
      have hs : start < n := by
        simp only [List.length_cons] at hbound
        omega
      have hu : n+start < n+n := by omega
      have hne : start ≠ n+start := by omega
      have hrind : QuaternionBlockIndependent (n+start) r :=
        tailProduct_independent n start ds (start+1) (by omega) (by
          simp only [List.length_cons] at hbound
          omega)
      have hlapCoeff := blockAngularLaplacian_mul_independent (n+start) f r hrind
      have heigen := normalizedCharacterAt_blockAngularLaplacian_right
        (blocks := n+n) (by omega) ⟨start, by omega⟩
        ⟨n+start, hu⟩ hne d
      have heigen' : HaarCarrierEqv (n+n)
          (blockAngularLaplacian (n+start) f) (polySmul (-c) f) :=
        heigen.trans (RatPolyCoeffEqv.haarCarrier
          (RatPolyCoeffEqv.smul_coefficient
            (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hce)) f))
      have hheadLap : HaarCarrierEqv (n+n)
          (blockAngularLaplacian (n+start) (polyMul f r))
          (polySmul (-c) (polyMul f r)) :=
        (RatPolyCoeffEqv.haarCarrier hlapCoeff).trans
          ((HaarCarrierEqv.mul_right r heigen').trans
            (RatPolyCoeffEqv.haarCarrier
              (RatPolyCoeffEqv.polyMul_smul_left (-c) f r)))
      have htail := characterProduct_upperCasimir n (start+1) ds (by
        simp only [List.length_cons] at hbound
        omega)
      rw [activeTail_shift n start ds] at htail
      let activeTail := (List.range ds.length).map fun i => n+start+(i+1)
      have hfind : ∀ block, block ∈ activeTail →
          QuaternionBlockIndependent block f := by
        intro block hb
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
        have hirange := List.mem_range.mp hi
        apply normalizedCharacterAt_independent
        · omega
        · omega
      have htailCoeff : RatPolyCoeffEqv
          (activeCasimirPolynomial activeTail (polyMul f r))
          (polyMul f (activeCasimirPolynomial activeTail r)) := by
        exact activeCasimirPolynomial_mul_independent_left activeTail f r hfind
      have htailFull : HaarCarrierEqv (n+n)
          (activeCasimirPolynomial activeTail (polyMul f r))
          (polySmul (totalCasimir ds) (polyMul f r)) :=
        (RatPolyCoeffEqv.haarCarrier htailCoeff).trans
          ((HaarCarrierEqv.mul_left f htail).trans
            (RatPolyCoeffEqv.haarCarrier
              (RatPolyCoeffEqv.polyMul_smul_right
                (totalCasimir ds) f r)))
      simp only [List.length_cons]
      rw [upperRange_cons n start ds.length]
      change HaarCarrierEqv (n+n)
        (polyAdd (polyNeg (blockAngularLaplacian (n+start) (polyMul f r)))
          (activeCasimirPolynomial
            ((List.range ds.length).map fun i => n+start+(i+1)) (polyMul f r)))
        (polySmul (c + totalCasimir ds) (polyMul f r))
      have hhead : HaarCarrierEqv (n+n)
          (polyNeg (blockAngularLaplacian (n+start) (polyMul f r)))
          (polySmul c (polyMul f r)) :=
        (HaarCarrierEqv.neg hheadLap).trans
          (RatPolyCoeffEqv.haarCarrier
            ((QuaternionHaarAngularCarrier.neg_smul _).trans
              ((RatPolyCoeffEqv.smul_assoc (-1) (-c) (polyMul f r)).trans
                (RatPolyCoeffEqv.smul_coefficient
                  (poly_identity_of_normal_eq
                    (.mul (.const (-1)) (.neg (.var 0))) (.var 0)
                    (by decide) (fun _ => c)) (polyMul f r)))))
      exact (HaarCarrierEqv.add hhead htailFull).trans
        (RatPolyCoeffEqv.haarCarrier
          (RatPolyCoeffEqv.add_smul_same c (totalCasimir ds) (polyMul f r)))

/-- Full-length specialization used by cyclic path reassembly. -/
theorem characterProduct_full_upperCasimir (n : Nat) (ds : List Nat)
    (hlen : ds.length = n) :
    HaarCarrierEqv (n+n)
      (activeCasimirPolynomial ((List.range n).map fun i => n+i)
        (characterProduct n (pathSlots 0 ds)))
      (polySmul (totalCasimir ds)
        (characterProduct n (pathSlots 0 ds))) := by
  simpa only [hlen, Nat.zero_add, Nat.add_zero] using
    characterProduct_upperCasimir n 0 ds (by omega)

end YMGap.Continuum.SU2QuaternionCharacterProductCasimir

#print axioms YMGap.Continuum.SU2QuaternionCharacterProductCasimir.characterProduct_upperCasimir
#print axioms YMGap.Continuum.SU2QuaternionCharacterProductCasimir.characterProduct_full_upperCasimir
