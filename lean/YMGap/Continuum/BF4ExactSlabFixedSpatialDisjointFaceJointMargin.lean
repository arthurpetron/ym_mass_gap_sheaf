/-
# Joint covariance/commutator control on the ORIGINAL disjoint-face plane

Source commutators are Haar-orthogonal to the source-weighted OTHER
observable whenever the literal mixed angular polynomial vanishes. This
remains true when both observables use their ORIGINAL interacting means.
Subtracting scaled centered source vectors therefore JOINS covariance and
mixed temporal energy in one residual Gram pairing. The exact signed heat
weight defect and cubic/cutoff debt remain; the source square is NEVER
substituted for the original marginal. No positive scaling margin is claimed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceSecondOrder
import YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedWard
import YMGap.Continuum.QuaternionHaarPredictionCovariance
import YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondFloor
import YMGap.Continuum.BF4WilsonAllNomeFiniteReferenceMargin

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceJointMargin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport (angularDerivative_smul)
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionSecondOrderCancellation
open YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarPredictionCovariance
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
open YMGap.Continuum.QuaternionHaarNormalizedMomentLinear
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource oddMoment_projected_source)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (marginalMass_pin marginalMass_positive marginalVariance_pin oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
  (spatialSpan_fringe_independent_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence
open YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceSecondOrder
  (sourceCommutator commutatorCross mixedDebt mixedEnergy mixedEnergy_mass_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondFloor
  (finite_family_energy_pin finite_family_variance_pin)
open YMGap.Continuum.BF4WilsonAllNomeFiniteReferenceMargin (referenceMargin)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin (familyExpression)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource marginalWeight

private theorem pair_add_right (n : Nat) (p q r : RatPoly) :
    finiteHaarPair n p (polyAdd q r) ≈ finiteHaarPair n p q + finiteHaarPair n p r :=
  Q'.eqv_trans _ _ _ (finiteHaarPair_symm n _ _)
    (Q'.eqv_trans _ _ _ (finiteHaarPair_add_left n _ _ _)
      (Q'.add_eqv_congr' (finiteHaarPair_symm n _ _) (finiteHaarPair_symm n _ _)))

private theorem pair_smul_right (n : Nat) (p q : RatPoly) (c : Q') :
    finiteHaarPair n p (polySmul c q) ≈ c*finiteHaarPair n p q :=
  Q'.eqv_trans _ _ _ (finiteHaarPair_symm n _ _)
    (Q'.eqv_trans _ _ _ (finiteHaarPair_smul_left n c _ _)
      (Q'.mul_eqv_congr_left c _ _ (finiteHaarPair_symm n _ _)))

/-- Exact commutator pairing from Haar IBP, for arbitrary source and tests.
No Casimir eigenmode, positivity, source independence or heat premise. -/
theorem commutator_pair (n : Nat) (active : List Nat)
    (ha : ∀ i, i ∈ active → i < n) (a f g : RatPoly) :
    H n (polyMul (polyMul a g) (commutatorPolynomial active a f)) ≈
      H n (polyMul (polyMul a a) (activeGamma active g f)) := by
  let A := activeGamma active a f
  let G := activeGamma active g f
  let F := H n (polyMul (polyMul a g) A)
  have hs := activeGamma_symm active f a
  have hprod := (activeGamma_symm active (polyMul (polyMul a a) g) f).trans
    ((activeGamma_mul_right active f (polyMul a a) g).trans
      (((activeGamma_mul_right active f a a).trans
        ((hs.mul_right a).add (hs.mul_left a))).mul_right g |>.add
        ((activeGamma_symm active f g).mul_left (polyMul a a))))
  have hshuffle : RatPolyCoeffEqv
      (polyAdd (polyMul (polyAdd (polyMul A a) (polyMul a A)) g)
        (polyMul (polyMul a a) G))
      (polyAdd (polyAdd (polyMul (polyMul a g) A) (polyMul (polyMul a g) A))
        (polyMul (polyMul a a) G)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.mul (.var 2) (.var 0)) (.mul (.var 0) (.var 2))) (.var 1))
        (.mul (.mul (.var 0) (.var 0)) (.var 3)))
      (.add (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 1)) (.var 2)))
        (.mul (.mul (.var 0) (.var 0)) (.var 3)))
      (by decide) (fun | 0 => a | 1 => g | 2 => A | _ => G)
  have hibp : H n (polyMul (polyMul (polyMul a a) g)
      (activeCasimirPolynomial active f)) ≈ F+F+H n (polyMul (polyMul a a) G) :=
    Q'.eqv_trans _ _ _ (casimir_pair_gamma n active ha _ f)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (hprod.trans hshuffle))
        (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
          (Q'.add_eqv_congr' (quaternionHaar_append n _ _) (Q'.eqv_refl _))))
  have hexpand : RatPolyCoeffEqv
      (polyMul (polyMul a g) (commutatorPolynomial active a f))
      (polyAdd (polyMul (polyMul (polyMul a a) g) (activeCasimirPolynomial active f))
        (polySmul (-2) (polyMul (polyMul a g) A))) :=
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
        (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 2))
        (by decide) (fun | 0 => a | 1 => g | _ => activeCasimirPolynomial active f)).add
        (RatPolyCoeffEqv.polyMul_smul_right (-2) _ A))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hexpand)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hibp (quaternionHaar_polySmul n (-2) _))
        (poly_identity_of_normal_eq (.add (.add (.add (.var 0) (.var 0)) (.var 1))
          (.mul (.const (-2)) (.var 0))) (.var 1) (by decide)
          (fun | 0 => F | _ => H n (polyMul (polyMul a a) G)))))

/-- The source itself is orthogonal to its commutator. -/
theorem commutator_source_zero (n : Nat) (active : List Nat)
    (ha : ∀ i, i ∈ active → i < n) (a f : RatPoly) :
    H n (polyMul a (commutatorPolynomial active a f)) ≈ 0 := by
  have h := gradientFlux_ibp n active ha a f
  have he : RatPolyCoeffEqv (polyMul a (commutatorPolynomial active a f))
      (polyAdd (polyMul (polyMul a a) (activeCasimirPolynomial active f))
        (polySmul (-2) (polyMul a (activeGamma active a f)))) :=
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      (((RatPolyCoeffEqv.mul_assoc a a _).symm).add
        (RatPolyCoeffEqv.polyMul_smul_right (-2) a _))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' h (quaternionHaar_polySmul n (-2) _))
        (poly_identity_of_normal_eq
          (.add (.mul (.const 2) (.var 0)) (.mul (.const (-2)) (.var 0)))
          (.const 0) (by decide) (fun _ => H n (polyMul a (activeGamma active a f))))))

/-- The other centered source vector is orthogonal too; the center may be
the original interacting mean, not a mean under the source square. -/
theorem centered_commutator_zero (n : Nat) (active : List Nat)
    (ha : ∀ i, i ∈ active → i < n) (a f g : RatPoly) (center : Q')
    (hz : RatPolyCoeffEqv (activeGamma active g f) polyZero) :
    H n (polyMul (polyMul a (shifted g center))
      (commutatorPolynomial active a f)) ≈ 0 := by
  have hcoeff : RatPolyCoeffEqv (polyMul a (shifted g center))
      (polyAdd (polyMul a g) (polySmul (-center) a)) := by
    unfold shifted
    exact (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right 1 a g).trans (RatPolyCoeffEqv.one_smul _)).add
        ((RatPolyCoeffEqv.polyMul_smul_right (-center) a polyOne).trans
          ((RatPolyCoeffEqv.mul_one a).smul (-center))))
  have hp := commutator_pair n active ha a f g
  have hp0 := Q'.eqv_trans _ _ _ hp (Q'.eqv_trans _ _ _
    (haar_of_coeff ((hz.mul_left _).trans (RatPolyCoeffEqv.mul_zero_right _)))
    (Q'.eqv_refl 0))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (hcoeff.mul_right _))
    (Q'.eqv_trans _ _ _ (finiteHaarPair_add_left n _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hp0
        (Q'.eqv_trans _ _ _ (finiteHaarPair_smul_left n (-center) _ _)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (commutator_source_zero n active ha a f))
            (Q'.mul_zero_eqv _)))) (Q'.eqv_refl _)))

private theorem six_congr {a b : Nat → Nat → RatPoly}
    (h : ∀ i j, i < 4 → j < 4 → RatPolyCoeffEqv (a i j) (b i j)) :
    RatPolyCoeffEqv (six a) (six b) := by
  unfold six
  exact (h 0 1 (by decide) (by decide)).add
    ((h 0 2 (by decide) (by decide)).add
      ((h 0 3 (by decide) (by decide)).add
        ((h 1 2 (by decide) (by decide)).add
          ((h 1 3 (by decide) (by decide)).add (h 2 3 (by decide) (by decide))))))

private theorem singleton_derivative_zero (width b : Nat) (c : Z4Plaq → Q')
    (p : Z4Plaq) (hb : b < N width) (hoff : blockRow width b p = false)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RatPolyCoeffEqv (blockAngularDerivative b i j (spatialSpan width c [p])) polyZero :=
  (angularDerivative_congr _ _ (RatPolyCoeffEqv.add_zero _)).trans
    ((angularDerivative_smul _ _ _ _).trans
      (((blockRow_derivative_zero width b p hb hoff hi hj).smul (c p)).trans
        (RatPolyCoeffEqv.smul_zero _)))

/-- Literal disjointness, with arbitrary signed singleton coefficients,
annihilates the FULL mixed angular polynomial before any source weighting. -/
theorem disjoint_gamma_zero (width : Nat) (c : Z4Plaq → Q')
    {p q : Z4Plaq} (hd : LinkDisjoint p q) :
    RatPolyCoeffEqv (activeGamma (List.range (N width))
      (spatialSpan width c [p]) (spatialSpan width c [q])) polyZero := by
  have hb (b : Nat) (h : b < N width) : RatPolyCoeffEqv
      (blockGamma b (spatialSpan width c [p]) (spatialSpan width c [q])) polyZero := by
    unfold blockGamma
    apply six_congr (b := fun _ _ => polyZero)
    intro i j hi hj
    rcases blockRow_separate width b hd with hp | hq
    · exact ((singleton_derivative_zero width b c p h hp hi hj).mul_right _).trans
        (RatPolyCoeffEqv.mul_zero_left _)
    · exact ((singleton_derivative_zero width b c q h hq hi hj).mul_left _).trans
        (RatPolyCoeffEqv.mul_zero_right _)
  have hs (ids : List Nat) (hi : ∀ b, b ∈ ids → b < N width) :
      RatPolyCoeffEqv (activeGamma ids (spatialSpan width c [p]) (spatialSpan width c [q]))
        polyZero := by
    induction ids with
    | nil => exact RatPolyCoeffEqv.refl _
    | cons b ids ih =>
        exact ((hb b (hi b List.mem_cons_self)).add
          (ih (fun j hj => hi j (List.mem_cons_of_mem b hj)))).trans
          (RatPolyCoeffEqv.zero_add _)
  exact hs _ (fun _ hi => List.mem_range.mp hi)

/-- The center is computed from the COMPLETE original odd marginal. -/
def originalCenter {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  normalizedMoment (N width) (marginalWeight w K width n) f
    (marginalMass_positive hw0 hw1 K width hK n)

def ownCovariance {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (coeff : Z4Plaq → Q') (p q : Z4Plaq) : Q' :=
  normalizedCovariance (N width) (marginalWeight w K width n)
    (spatialSpan width coeff [p]) (spatialSpan width coeff [q])
    (marginalMass_positive hw0 hw1 K width hK n)

/-- An auxiliary Haar vector, not asserted to be a physical OS state. -/
def centeredSource {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : RatPoly :=
  polyMul (projectedEndpointSource w K width (terminalMessage w K width n))
    (shifted f (originalCenter hw0 hw1 K width hK n f))

/-- The actual source commutator with its original-centered source component
subtracted. No approximation or source-weight substitution. -/
def residual {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) (scale : Q') : RatPoly :=
  polyAdd (sourceCommutator w K width n f)
    (polySmul (-scale) (centeredSource hw0 hw1 K width hK n f))

def residualSquare {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (coeff : Z4Plaq → Q')
    (p : Z4Plaq) (scale : Q') : Q' :=
  let r := residual hw0 hw1 K width hK n (spatialSpan width coeff [p]) scale
  H (N width) (polyMul r r)

/-- The SIGNED difference between the actual heat-paired source density and
its square, tested at BOTH original means. It is not dropped or signed. -/
def heatCovarianceDefect {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (coeff : Z4Plaq → Q') (p q : Z4Plaq) : Q' :=
  let a := projectedEndpointSource w K width (terminalMessage w K width n)
  let x := shifted (spatialSpan width coeff [p])
    (originalCenter hw0 hw1 K width hK n (spatialSpan width coeff [p]))
  let y := shifted (spatialSpan width coeff [q])
    (originalCenter hw0 hw1 K width hK n (spatialSpan width coeff [q]))
  H (N width) (polyMul
    (polyMul a (polyAdd (productMap (N width) w K (List.range (N width)) a) (polyNeg a)))
    (polyMul x y))

/-- The actual mixed contribution to c*OWN variance minus temporal energy,
cleared by the SAME original odd partition. -/
def jointMargin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (coeff : Z4Plaq → Q') (p q : Z4Plaq) (c : Q') : Q' :=
  (2*c*ownCovariance hw0 hw1 K width hK n coeff p q -
    mixedEnergy hw0 hw1 K width hK n coeff p q) * oddMass w K width n

private theorem support_smul {blocks : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks blocks f) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c f) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hf s hs

private theorem source_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width n)) := by
  unfold projectedEndpointSource
  exact SU2QuaternionHaarFamilyProjection.familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n))

private theorem residual_supported {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (scale : Q') :
    SupportedQuaternionBlocks (N width) (residual hw0 hw1 K width hK n f scale) := by
  have ha := source_supported w K width n
  have hi : ∀ i, i ∈ List.range (N width) → i < N width := fun _ hi => List.mem_range.mp hi
  have hB : SupportedQuaternionBlocks (N width) (sourceCommutator w K width n f) :=
    supported_add (supported_polyMul ha (activeCasimirPolynomial_supported _ hi hf))
      (support_smul (activeGamma_supported _ hi ha hf) (-2))
  exact supported_add hB (support_smul
    (supported_polyMul ha (shifted_supported hf _)) (-scale))

private theorem raw_centered_covariance (blocks : Nat) (W f g : RatPoly)
    (hZ : (0 : Q') < H blocks W) :
    H blocks (polyMul W (polyMul
      (shifted f (normalizedMoment blocks W f hZ))
      (shifted g (normalizedMoment blocks W g hZ)))) ≈
      normalizedCovariance blocks W f g hZ * H blocks W := by
  let Z := H blocks W
  let r := Q'.recipPos Z hZ
  have hr : Z*r ≈ 1 := Q'.mul_recipPos_eqv Z hZ
  have hn := Q'.mul_eqv_congr_right _ _ Z (centered_cross_pin (p := f) (q := g) hZ)
  change (_*r)*Z ≈ normalizedCovariance blocks W f g hZ * Z at hn
  have raw (x : Q') : (x*r)*Z ≈ x :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
      (fun | 0 => x | 1 => r | _ => Z))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x _ _ hr) (Q'.mul_one_eqv x))
  exact Q'.eqv_trans _ _ _ (raw _).symm hn

/-- The covariance is the original two-mean centered insertion, with its
original mass; no mean under a*a is introduced. -/
theorem own_covariance_mass_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (coeff : Z4Plaq → Q') (p q : Z4Plaq) :
    H (N width) (polyMul (marginalWeight w K width n)
      (polyMul
        (shifted (spatialSpan width coeff [p])
          (originalCenter hw0 hw1 K width hK n (spatialSpan width coeff [p])))
        (shifted (spatialSpan width coeff [q])
          (originalCenter hw0 hw1 K width hK n (spatialSpan width coeff [q]))))) ≈
      ownCovariance hw0 hw1 K width hK n coeff p q * oddMass w K width n :=
  Q'.eqv_trans _ _ _ (raw_centered_covariance (N width) (marginalWeight w K width n)
    (spatialSpan width coeff [p]) (spatialSpan width coeff [q])
    (marginalMass_positive hw0 hw1 K width hK n))
    (Q'.mul_eqv_congr_left (ownCovariance hw0 hw1 K width hK n coeff p q) _ _
      (marginalMass_pin w K width n))

/-- Exact transport of the centered product through inactive-source
projection; the difference from a*a remains as the signed heat defect. -/
theorem source_covariance_defect_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (n : Nat)
    (coeff : Z4Plaq → Q') {p q : Z4Plaq}
    (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base) :
    H (N width) (polyMul
      (centeredSource hw0 hw1 K width hK n (spatialSpan width coeff [p]))
      (centeredSource hw0 hw1 K width hK n (spatialSpan width coeff [q]))) +
      heatCovarianceDefect hw0 hw1 K width hK n coeff p q ≈
      ownCovariance hw0 hw1 K width hK n coeff p q * oddMass w K width n := by
  let a := projectedEndpointSource w K width (terminalMessage w K width n)
  let x := shifted (spatialSpan width coeff [p])
    (originalCenter hw0 hw1 K width hK n (spatialSpan width coeff [p]))
  let y := shifted (spatialSpan width coeff [q])
    (originalCenter hw0 hw1 K width hK n (spatialSpan width coeff [q]))
  have independent (r : Z4Plaq) (hr : r ∈ spatialFaces base) :
      ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i
        (shifted (spatialSpan width coeff [r])
          (originalCenter hw0 hw1 K width hK n (spatialSpan width coeff [r]))) := by
    intro i hi
    apply quaternionBlockIndependent_polyAdd
    · exact quaternionBlockIndependent_polySmul 1
        (spatialSpan_fringe_independent_after_padding hwidth coeff [r]
          (fun s hs => (List.mem_singleton.mp hs) ▸ hr) i hi)
    · exact quaternionBlockIndependent_polySmul _ (quaternionBlockIndependent_polyOne i)
  have ht := oddMoment_projected_source w K width n (polyMul x y)
    (supported_polyMul (shifted_supported (spatialSpan_supported width coeff [p]) _)
      (shifted_supported (spatialSpan_supported width coeff [q]) _))
    (fun i hi => quaternionBlockIndependent_polyMul (independent p hp i hi) (independent q hq i hi))
  have hcoeff : RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul a x) (polyMul a y))
        (polyMul (polyMul a (polyAdd (productMap (N width) w K (List.range (N width)) a)
          (polyNeg a))) (polyMul x y)))
      (polyMul (polyMul a (polyMul x y))
        (productMap (N width) w K (List.range (N width)) a)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
        (.mul (.mul (.var 0) (.add (.var 3) (.neg (.var 0)))) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3)) (by decide)
      (fun | 0 => a | 1 => x | 2 => y | _ => productMap (N width) w K (List.range (N width)) a)
  exact Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _).symm
    (Q'.eqv_trans _ _ _ (haar_of_coeff hcoeff)
      (Q'.eqv_trans _ _ _ ht.symm (own_covariance_mass_pin hw0 hw1 K width hK n coeff p q)))

private theorem residual_cross_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (n : Nat) (coeff : Z4Plaq → Q')
    {p q : Z4Plaq} (hd : LinkDisjoint p q) (lambda mu : Q') :
    H (N width) (polyMul
      (residual hw0 hw1 K width hK n (spatialSpan width coeff [p]) lambda)
      (residual hw0 hw1 K width hK n (spatialSpan width coeff [q]) mu)) ≈
      commutatorCross w K width n coeff p q + lambda*mu*
        H (N width) (polyMul
          (centeredSource hw0 hw1 K width hK n (spatialSpan width coeff [p]))
          (centeredSource hw0 hw1 K width hK n (spatialSpan width coeff [q]))) := by
  let B := sourceCommutator w K width n (spatialSpan width coeff [p])
  let D := sourceCommutator w K width n (spatialSpan width coeff [q])
  let u := centeredSource hw0 hw1 K width hK n (spatialSpan width coeff [p])
  let v := centeredSource hw0 hw1 K width hK n (spatialSpan width coeff [q])
  have hi : ∀ i, i ∈ List.range (N width) → i < N width := fun _ h => List.mem_range.mp h
  have hud : finiteHaarPair (N width) u D ≈ 0 := centered_commutator_zero (N width) _ hi
    _ _ _ _ (disjoint_gamma_zero width coeff hd)
  have hvb : finiteHaarPair (N width) v B ≈ 0 := centered_commutator_zero (N width) _ hi
    _ _ _ _ ((activeGamma_symm _ _ _).trans (disjoint_gamma_zero width coeff hd))
  have hbv := Q'.eqv_trans _ _ _ (finiteHaarPair_symm (N width) B v) hvb
  have hB : finiteHaarPair (N width) B (polyAdd D (polySmul (-mu) v)) ≈
      finiteHaarPair (N width) B D + (-mu)*0 :=
    Q'.eqv_trans _ _ _ (pair_add_right _ _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (pair_smul_right _ _ _ _)
          (Q'.mul_eqv_congr_left _ _ _ hbv)))
  have hu : finiteHaarPair (N width) u (polyAdd D (polySmul (-mu) v)) ≈
      0 + (-mu)*finiteHaarPair (N width) u v :=
    Q'.eqv_trans _ _ _ (pair_add_right _ _ _ _)
      (Q'.add_eqv_congr' hud (pair_smul_right _ _ _ _))
  exact Q'.eqv_trans _ _ _ (finiteHaarPair_add_left _ _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hB
      (Q'.eqv_trans _ _ _ (finiteHaarPair_smul_left _ _ _ _)
        (Q'.mul_eqv_congr_left _ _ _ hu)))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.mul (.neg (.var 3)) (.const 0)))
          (.mul (.neg (.var 2)) (.add (.const 0) (.mul (.neg (.var 3)) (.var 1)))))
        (.add (.var 0) (.mul (.mul (.var 2) (.var 3)) (.var 1))) (by decide)
        (fun | 0 => finiteHaarPair (N width) B D | 1 => finiteHaarPair (N width) u v
             | 2 => lambda | _ => mu)))

private theorem joint_algebra (c h2 B R F D V X E Z L : Q')
    (hV : F+D ≈ V*Z) (hE : E*Z ≈ -(h2*B)+R)
    (hX : X ≈ B+L*F) (hm : h2*L ≈ 2*c) :
    (2*c*V-E)*Z ≈ h2*X+(2*c)*D-R := by
  have hleft : (2*c*V-E)*Z ≈ (2*c)*(V*Z) - (-(h2*B)+R) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.add (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.neg (.var 2))) (.var 3))
      (.add (.mul (.mul (.const 2) (.var 0)) (.mul (.var 1) (.var 3)))
        (.neg (.mul (.var 2) (.var 3)))) (by decide)
      (fun | 0 => c | 1 => V | 2 => E | _ => Z))
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hE))
  have hright := Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left h2 _ _ hX) (Q'.eqv_refl ((2*c)*D)))
    (Q'.eqv_refl (-R))
  have hfactor : h2*(B+L*F)+(2*c)*D-R ≈ (2*c)*(F+D)-(-(h2*B)+R) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.add (.var 1) (.mul (.var 2) (.var 3))))
        (.mul (.var 4) (.var 5))) (.neg (.var 6)))
      (.add (.add (.mul (.var 0) (.var 1)) (.mul (.mul (.var 0) (.var 2)) (.var 3)))
        (.add (.mul (.var 4) (.var 5)) (.neg (.var 6)))) (by decide)
      (fun | 0 => h2 | 1 => B | 2 => L | 3 => F | 4 => 2*c | 5 => D | _ => R))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.mul_eqv_congr_right _ _ F hm)) (Q'.eqv_refl _))
        (poly_identity_of_normal_eq
          (.add (.add (.mul (.var 0) (.var 1)) (.mul (.var 4) (.var 3)))
            (.add (.mul (.var 4) (.var 5)) (.neg (.var 6))))
          (.add (.mul (.var 4) (.add (.var 3) (.var 5)))
            (.neg (.add (.neg (.mul (.var 0) (.var 1))) (.var 6)))) (by decide)
          (fun | 0 => h2 | 1 => B | 3 => F | 4 => 2*c | 5 => D | _ => R)))
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left (2*c) _ _ hV.symm) (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _ hfactor.symm hright.symm))

/-- ONE signed original covariance/energy join. The scalar matching guard is
algebraic; it imposes no analytic estimate or favorable sign. Both residuals
and the signed heat/debt corrections use the SAME actual source and means. -/
theorem joint_margin_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (n : Nat)
    (coeff : Z4Plaq → Q') {p q : Z4Plaq} (hd : LinkDisjoint p q)
    (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base) (c lambda mu : Q')
    (hmatch : (((1 : Q')-w)*((1 : Q')-w))*(lambda*mu) ≈ 2*c) :
    jointMargin hw0 hw1 K width hK n coeff p q c ≈
      (((1 : Q')-w)*((1 : Q')-w))*
        H (N width) (polyMul
          (residual hw0 hw1 K width hK n (spatialSpan width coeff [p]) lambda)
          (residual hw0 hw1 K width hK n (spatialSpan width coeff [q]) mu)) +
      (2*c)*heatCovarianceDefect hw0 hw1 K width hK n coeff p q - mixedDebt w K width n coeff p q :=
  joint_algebra _ _ _ _ _ _ _ _ _ _ _
    (source_covariance_defect_pin hw0 hw1 K hwidth hK n coeff hp hq)
    (mixedEnergy_mass_pin hw0 hw1 K hwidth hK n coeff hd hp hq)
    (residual_cross_pin hw0 hw1 K width hK n coeff hd lambda mu) hmatch

/-- Sharp CS for the JOINT original margin after its exact signed heat/debt
corrections. No variance-relative residual bound or positive margin is assumed. -/
theorem corrected_joint_margin_square_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (n : Nat)
    (coeff : Z4Plaq → Q') {p q : Z4Plaq} (hd : LinkDisjoint p q)
    (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base) (c lambda mu : Q')
    (hmatch : (((1 : Q')-w)*((1 : Q')-w))*(lambda*mu) ≈ 2*c) :
    let d := jointMargin hw0 hw1 K width hK n coeff p q c + mixedDebt w K width n coeff p q -
      (2*c)*heatCovarianceDefect hw0 hw1 K width hK n coeff p q
    let h2 := ((1 : Q')-w)*((1 : Q')-w)
    d*d ≤ (h2*h2)*(residualSquare hw0 hw1 K width hK n coeff p lambda *
      residualSquare hw0 hw1 K width hK n coeff q mu) := by
  dsimp only
  let r := residual hw0 hw1 K width hK n (spatialSpan width coeff [p]) lambda
  let s := residual hw0 hw1 K width hK n (spatialSpan width coeff [q]) mu
  let X := H (N width) (polyMul r s)
  let h2 := ((1 : Q')-w)*((1 : Q')-w)
  let D := (2*c)*heatCovarianceDefect hw0 hw1 K width hK n coeff p q
  let R := mixedDebt w K width n coeff p q
  have he := Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (joint_margin_pin hw0 hw1 K hwidth hK n coeff hd hp hq c lambda mu hmatch)
      (Q'.eqv_refl R)) (Q'.eqv_refl (-D))
  have he' := Q'.eqv_trans _ _ _ he (poly_identity_of_normal_eq
    (.add (.add (.add (.add (.mul (.var 0) (.var 1)) (.var 2)) (.neg (.var 3))) (.var 3))
      (.neg (.var 2))) (.mul (.var 0) (.var 1)) (by decide)
    (fun | 0 => h2 | 1 => X | 2 => D | _ => R))
  have hs := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ he')
    (Q'.mul_eqv_congr_left _ _ _ he')
  have ht := poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
    (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
    (fun | 0 => h2 | _ => X)
  have hcs := finiteHaar_cauchySchwarz (N width) r s
    (residual_supported hw0 hw1 K width hK n (spatialSpan_supported width coeff [p]) lambda)
    (residual_supported hw0 hw1 K width hK n (spatialSpan_supported width coeff [q]) mu)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hs ht))
    (Q'.mul_le_mul_of_nonneg_left _ _ (h2*h2) hcs (SumOfSquares.q_mul_self_nonneg h2))

/-- A COMPUTED matching right scale for EVERY coefficient c at w<1.
There is no square-root, located eigenvalue or analytic matching input. -/
def matchingRightScale {w : Q'} (hw1 : w < (1 : Q')) (c : Q') : Q' :=
  (2*c)*Q'.recipPos (((1 : Q')-w)*((1 : Q')-w))
    (Q'.mul_pos (HKPos.one_sub_pos hw1) (HKPos.one_sub_pos hw1))

theorem matchingRightScale_pin {w : Q'} (hw1 : w < (1 : Q')) (c : Q') :
    (((1 : Q')-w)*((1 : Q')-w))*(1*matchingRightScale hw1 c) ≈ 2*c := by
  let h2 := ((1 : Q')-w)*((1 : Q')-w)
  let hr := Q'.mul_pos (HKPos.one_sub_pos hw1) (HKPos.one_sub_pos hw1)
  exact Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.const 1) (.mul (.var 1) (.var 2))))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun | 0 => h2 | 1 => 2*c | _ => Q'.recipPos h2 hr))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (2*c) _ _ (Q'.mul_recipPos_eqv h2 hr))
      (Q'.mul_one_eqv (2*c)))

private theorem variance_add_cross (blocks : Nat) (W f g : RatPoly)
    (hZ : (0 : Q') < H blocks W) :
    normalizedVariance blocks W (polyAdd f g) hZ -
      normalizedVariance blocks W f hZ - normalizedVariance blocks W g hZ ≈
      2*normalizedCovariance blocks W f g hZ := by
  let M := fun p => normalizedMoment blocks W p hZ
  have hc : RatPolyCoeffEqv (polyMul (polyAdd f g) (polyAdd f g))
      (polyAdd (polyAdd (polyMul f f) (polyMul g g))
        (polyAdd (polyMul f g) (polyMul f g))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))
      (by decide) (fun | 0 => f | _ => g)
  have hs : M (polyMul (polyAdd f g) (polyAdd f g)) ≈
      (M (polyMul f f)+M (polyMul g g))+(M (polyMul f g)+M (polyMul f g)) :=
    Q'.eqv_trans _ _ _ (normalizedMoment_congr hZ hZ (RatPolyCoeffEqv.refl W) hc)
      (Q'.eqv_trans _ _ _ (normalizedMoment_add hZ)
        (Q'.add_eqv_congr' (normalizedMoment_add hZ) (normalizedMoment_add hZ)))
  have hm : M (polyAdd f g) ≈ M f+M g := normalizedMoment_add hZ
  have he := Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hs (Q'.neg_eqv_congr _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hm) (Q'.mul_eqv_congr_left _ _ _ hm))))
      (Q'.eqv_refl (-normalizedVariance blocks W f hZ)))
    (Q'.eqv_refl (-normalizedVariance blocks W g hZ))
  exact Q'.eqv_trans _ _ _ he (poly_identity_of_normal_eq
    (.add (.add
      (.add (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 2)))
        (.neg (.mul (.add (.var 3) (.var 4)) (.add (.var 3) (.var 4)))))
      (.neg (.add (.var 0) (.neg (.mul (.var 3) (.var 3))))))
      (.neg (.add (.var 1) (.neg (.mul (.var 4) (.var 4))))))
    (.mul (.const 2) (.add (.var 2) (.neg (.mul (.var 3) (.var 4)))))
    (by decide) (fun
      | 0 => M (polyMul f f)
      | 1 => M (polyMul g g)
      | 2 => M (polyMul f g)
      | 3 => M f
      | _ => M g))

private theorem variance_coeff_congr (blocks : Nat) (W f g : RatPoly)
    (hZ : (0 : Q') < H blocks W) (h : RatPolyCoeffEqv f g) :
    normalizedVariance blocks W f hZ ≈ normalizedVariance blocks W g hZ := by
  have hm := normalizedMoment_congr hZ hZ (RatPolyCoeffEqv.refl W) h
  exact Q'.add_eqv_congr'
    (normalizedMoment_congr hZ hZ (RatPolyCoeffEqv.refl W) (h.mul h))
    (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hm) (Q'.mul_eqv_congr_left _ _ _ hm)))

private theorem odd_variance_pair {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (coeff : Z4Plaq → Q') (p q : Z4Plaq) :
    oddVariance hw0 hw1 K width hK n (spatialSpan width coeff [p,q]) -
      oddVariance hw0 hw1 K width hK n (spatialSpan width coeff [p]) -
      oddVariance hw0 hw1 K width hK n (spatialSpan width coeff [q]) ≈
      2*ownCovariance hw0 hw1 K width hK n coeff p q := by
  have hp : RatPolyCoeffEqv (spatialSpan width coeff [p,q])
      (polyAdd (spatialSpan width coeff [p]) (spatialSpan width coeff [q])) :=
    (RatPolyCoeffEqv.add_zero _).symm.add (RatPolyCoeffEqv.refl _)
  have hm (qs : List Z4Plaq) := marginalVariance_pin hw0 hw1 K width hK n
    (spatialSpan width coeff qs)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (hm [p,q]).symm (Q'.neg_eqv_congr _ _ (hm [p]).symm))
      (Q'.neg_eqv_congr _ _ (hm [q]).symm))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (variance_coeff_congr _ _ _ _
          (marginalMass_positive hw0 hw1 K width hK n) hp) (Q'.eqv_refl _)) (Q'.eqv_refl _))
      (variance_add_cross _ _ _ _ (marginalMass_positive hw0 hw1 K width hK n)))

/-- The EXISTING original reference margin on the supplied spatial list. -/
def familyReferenceMargin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base width : Nat} (hwidth : base < width) (coeff : Z4Plaq → Q')
    (qs : List Z4Plaq) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)
    (c : Q') (stage depth : Nat) : Q' :=
  referenceMargin hw0 hw1 (familyExpression width qs coeff
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))) c stage depth

private theorem family_reference_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base width : Nat} (hwidth : base < width) (coeff : Z4Plaq → Q')
    (qs : List Z4Plaq) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)
    (c : Q') (stage depth : Nat) :
    familyReferenceMargin hw0 hw1 hwidth coeff qs hqs c stage depth ≈
      c*oddVariance hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        depth (spatialSpan width coeff qs) -
      BF4ExactSlabFixedSpatialDirichletWindow.normalizedEnergy hw0 hw1 (headCutoff w+stage)
        width (Nat.le_add_right _ _) depth (spatialSpan width coeff qs) :=
  Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left c _ _ (finite_family_variance_pin hw0 hw1 hwidth qs coeff hqs stage depth))
    (Q'.neg_eqv_congr _ _ (finite_family_energy_pin hw0 hw1 hwidth qs coeff hqs stage depth))

private theorem margin_difference (c v₁ v₂ v₃ e₁ e₂ e₃ cov : Q')
    (hv : (v₁-v₂)-v₃ ≈ 2*cov) :
    ((c*v₁-e₁)-(c*v₂-e₂))-(c*v₃-e₃) ≈ 2*c*cov-((e₁-e₂)-e₃) :=
  Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.add (.add (.add (.mul (.var 0) (.var 1)) (.neg (.var 4)))
      (.neg (.add (.mul (.var 0) (.var 2)) (.neg (.var 5)))))
      (.neg (.add (.mul (.var 0) (.var 3)) (.neg (.var 6)))))
    (.add (.mul (.var 0) (.add (.add (.var 1) (.neg (.var 2))) (.neg (.var 3))))
      (.neg (.add (.add (.var 4) (.neg (.var 5))) (.neg (.var 6)))))
    (by decide) (fun | 0 => c | 1 => v₁ | 2 => v₂ | 3 => v₃ | 4 => e₁ | 5 => e₂ | _ => e₃))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left c _ _ hv) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.const 2) (.var 1))) (.neg (.var 2)))
        (.add (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.neg (.var 2)))
        (by decide) (fun | 0 => c | 1 => cov | _ => (e₁-e₂)-e₃)))

private theorem two_faces {base : Nat} {p q : Z4Plaq}
    (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base) :
    ∀ r, r ∈ [p,q] → r ∈ spatialFaces base := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hp
  · exact (List.mem_singleton.mp hr) ▸ hq

/-- Direct SAME-cutoff/depth join to the current original certificate path.
No positivity or successful checker input is assumed. Disjointness is needed
only to apply the preceding signed residual bound, not for polarization. -/
theorem reference_margin_difference_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {base width : Nat}
    (hwidth : base < width) (coeff : Z4Plaq → Q') {p q : Z4Plaq}
    (hp : p ∈ spatialFaces base) (hq : q ∈ spatialFaces base)
    (c : Q') (stage depth : Nat) :
    ((familyReferenceMargin hw0 hw1 hwidth coeff [p,q]
        (two_faces hp hq)
        c stage depth -
      familyReferenceMargin hw0 hw1 hwidth coeff [p]
        (fun _ hr => (List.mem_singleton.mp hr) ▸ hp) c stage depth) -
      familyReferenceMargin hw0 hw1 hwidth coeff [q]
        (fun _ hr => (List.mem_singleton.mp hr) ▸ hq) c stage depth) *
      oddMass w (headCutoff w+stage) width depth ≈
      jointMargin hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        depth coeff p q c := by
  apply Q'.mul_eqv_congr_right
  have hpair : ∀ r, r ∈ [p,q] → r ∈ spatialFaces base := two_faces hp hq
  have hsinglep : ∀ r, r ∈ [p] → r ∈ spatialFaces base := fun r hr => (List.mem_singleton.mp hr) ▸ hp
  have hsingleq : ∀ r, r ∈ [q] → r ∈ spatialFaces base := fun r hr => (List.mem_singleton.mp hr) ▸ hq
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (family_reference_pin hw0 hw1 hwidth coeff [p,q] hpair c stage depth)
        (Q'.neg_eqv_congr _ _ (family_reference_pin hw0 hw1 hwidth coeff [p] hsinglep c stage depth)))
      (Q'.neg_eqv_congr _ _ (family_reference_pin hw0 hw1 hwidth coeff [q] hsingleq c stage depth)))
    (margin_difference _ _ _ _ _ _ _ _
      (odd_variance_pair hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) depth coeff p q))

#print axioms commutator_pair
#print axioms commutator_source_zero
#print axioms centered_commutator_zero
#print axioms disjoint_gamma_zero
#print axioms originalCenter
#print axioms ownCovariance
#print axioms centeredSource
#print axioms residual
#print axioms residualSquare
#print axioms heatCovarianceDefect
#print axioms jointMargin
#print axioms own_covariance_mass_pin
#print axioms source_covariance_defect_pin
#print axioms joint_margin_pin
#print axioms corrected_joint_margin_square_bound
#print axioms matchingRightScale
#print axioms matchingRightScale_pin
#print axioms familyReferenceMargin
#print axioms reference_margin_difference_pin

end YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceJointMargin
