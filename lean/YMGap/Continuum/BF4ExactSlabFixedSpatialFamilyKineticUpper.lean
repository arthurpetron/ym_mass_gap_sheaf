/-
# Error-free whole signed-family energy upper on the original edge law

Exact SU(2) fusion alignment, the literal four-link word telescope and ONE
finite Cauchy certificate give

    E(sum c_p chi_p) <= 192*(1-w)*|qs|*sum(c_p^2)*oddMass.

The common diagonal bound also gives the coefficient-L1 ceiling

    E(sum c_p chi_p) <= 192*(1-w)*(sum |c_p|)^2*oddMass.

All signed cross terms occur in the original squared jump on the left.
The right pays the stated list-length Cauchy loss, including repetitions.
There is no endpoint source floor/cap, spectator-volume, terminal-depth or
cutoff-error coefficient after the computed onset. This is an ABSOLUTE
mass-normalized bound, NOT a SAME-variance or continuum-survival estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialExactKineticAlignment
import YMGap.Continuum.BF4ExactSlabFixedSpatialLinkQuartic
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
import YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
import YMGap.Continuum.QuaternionHaarFiniteCauchyCertificate
import YMGap.Continuum.QuaternionHaarUniformFamilyCost

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyKineticUpper

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement
  (upperOriented wilson_energy_of_link_budget)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLinkQuartic
  (lower_supported upper_supported lower_unit upper_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialExactKineticAlignment
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (supported_smul)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_add lift_smul lift_coeff)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary liftHead)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarFiniteCauchyCertificate
open YMGap.Continuum.QuaternionHaarWordDifference
open YMGap.Continuum.QuaternionHaarChordalDifference
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_sum_indexed)
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment)
open YMGap.Continuum.QuaternionHaarUniformFamilyCost (normalized_family_l1_cost)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks terminalMessage oddMass plaquette

/-- A literal oriented active link inherits exact SAME-edge displacement. -/
theorem oriented_displacement_bound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width depth : Nat)
    (hK : sufficientCutoff w ≤ K+1) {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) (hi : (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w (K+1) width (terminalMessage w (K+1) width depth))
        (polyQuaternionNorm (difference (orientedLink width e) (upperOriented width e)))) ≤
      (6*(1-w))*oddMass w (K+1) width depth := by
  have h := exact_link_displacement_nome_bound hw0 hw1 K hK width depth _ hi
  unfold orientedLink link upperOriented
  rw [if_pos he]
  split
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
      (haar_of_coeff ((norm_difference_conj _ _).mul_left _))) h
  · exact h

/-- Error-free active Wilson-word energy, with the squared path length
explicit and every original source/action factor retained. -/
theorem wilson_energy_nome_bound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width depth : Nat)
    (hK : sufficientCutoff w ≤ K+1) (hH : headCutoff w ≤ K+1)
    (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    (2 : Q') * energy w (K+1) width (terminalMessage w (K+1) width depth)
      (sourceCharacter width loop.edges 1) ≤
      (24*(1-w)*(Q'.ofNat loop.edges.length*Q'.ofNat loop.edges.length))*
        oddMass w (K+1) width depth := by
  have h := wilson_energy_of_link_budget hw0 hw1 (K+1) width hH depth loop
    ((6*(1-w))*oddMass w (K+1) width depth)
    (fun e he => oriented_displacement_bound hw0 hw1 K width depth hK
      (loop.physical e he) (hactive e he))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.mul (.const 4) (.mul (.var 0) (.mul (.mul (.const 6) (.var 1)) (.var 2))))
      (.mul (.mul (.mul (.const 24) (.var 1)) (.var 0)) (.var 2)) (by decide)
      (fun | 0 => Q'.ofNat loop.edges.length*Q'.ofNat loop.edges.length
           | 1 => (1 : Q')-w | _ => oddMass w (K+1) width depth)))

private theorem jump_congr (width : Nat) {f g : RatPoly} (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (jump width f) (jump width g) :=
  h.add (RatPolyCoeffEqv.neg (lift_coeff (N width) h))

/-- Strict padding proves ALL four literal plaquette edges active. No
gauge-dependent private-link or source-factorization assumption enters. -/
theorem face_jump_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : sufficientCutoff w ≤ K+1) (hH : headCutoff w ≤ K+1)
    {base width : Nat} (hwidth : base < width) (depth : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w (K+1) width (terminalMessage w (K+1) width depth))
        (polyMul (jump width (characterPolynomial (plaquette width face).scalar 1))
          (jump width (characterPolynomial (plaquette width face).scalar 1)))) ≤
      (384*(1-w))*oddMass w (K+1) width depth := by
  let loop : SourceLoop width := plaquetteLoop face (spatialFaces_mono (Nat.le_of_lt hwidth) hf)
  have hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width :=
    fun e he => source_edges_active_after_padding hwidth (plaquetteLoop face hf) e he
  have h := wilson_energy_nome_bound hw0 hw1 K width depth hK hH loop hactive
  have hlen : loop.edges.length = 4 := by rfl
  rw [hlen] at h
  have hj := jump_congr width (sourceCharacter_plaquette width face 1)
  have he := Q'.eqv_trans _ _ _
    (energy_identity w (K+1) width (terminalMessage_supported w (K+1) width depth)
      (sourceCharacter_supported width loop.edges 1))
    (haar_of_coeff ((hj.mul hj).mul_left _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ _
        (poly_identity_of_normal_eq
          (.mul (.mul (.const 24) (.var 0)) (.mul (.const 4) (.const 4)))
          (.mul (.const 384) (.var 0)) (by decide) (fun _ => (1 : Q')-w)))))

private theorem neg_smul (c : Q') (f : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polySmul c f)) (polySmul c (polyNeg f)) :=
  (RatPolyCoeffEqv.neg (cap_mul_left c f)).symm.trans
    ((coeffEvalExpr_eqv_of_normalize_eq
      (.neg (.mul (.var 0) (.var 1))) (.mul (.var 0) (.neg (.var 1)))
      (by decide) (fun | 0 => cap c | _ => f)).trans (cap_mul_left c (polyNeg f)))

private theorem jump_add (width : Nat) (f g : RatPoly) :
    RatPolyCoeffEqv (jump width (polyAdd f g)) (polyAdd (jump width f) (jump width g)) := by
  unfold jump
  rw [lift_add]
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
    (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
    (by decide) (fun
      | 0 => f | 1 => g | 2 => liftBoundary (N width) f
      | _ => liftBoundary (N width) g)

private theorem jump_smul (width : Nat) (c : Q') (f : RatPoly) :
    RatPolyCoeffEqv (jump width (polySmul c f)) (polySmul c (jump width f)) := by
  unfold jump
  rw [lift_smul]
  exact ((RatPolyCoeffEqv.refl _).add (neg_smul c _)).trans
    (RatPolyCoeffEqv.smul_add c _ _).symm

private theorem lift_zero : ∀ n : Nat, liftBoundary n polyZero = polyZero
  | 0 => rfl
  | n+1 => by change liftHead (liftBoundary n polyZero) = polyZero; rw [lift_zero n]; rfl

/-- The WHOLE jump, before squaring, retains the exact signed list. -/
theorem family_jump_sum (width : Nat) (c : Z4Plaq → Q') : ∀ qs : List Z4Plaq,
    RatPolyCoeffEqv (jump width (spatialSpan width c qs))
      (polySum (qs.map fun p => polySmul (c p)
        (jump width (characterPolynomial (plaquette width p).scalar 1))))
  | [] => by
      change RatPolyCoeffEqv (polyAdd polyZero (polyNeg (liftBoundary (N width) polyZero))) polyZero
      rw [lift_zero]
      exact (RatPolyCoeffEqv.zero_add _).trans (RatPolyCoeffEqv.refl _)
  | p :: qs => (jump_add width _ _).trans
      ((jump_smul width (c p) _).add (family_jump_sum width c qs))

/-- Finite Cauchy retains actual diagonal costs, not a source norm cap. -/
theorem weighted_sum_square_le {n : Nat} {W : RatPoly} (R : Certificate n W)
    (ps : List RatPoly) (hs : ∀ p, p ∈ ps → SupportedQuaternionBlocks n p) :
    quaternionHaar n (polyMul W (polyMul (polySum ps) (polySum ps))) ≤
      Q'.ofNat ps.length * qListSum (ps.map fun p => quaternionHaar n (polyMul W (polyMul p p))) :=
  Q'.le_trans' _ _ _ (weighted_order R (sum_square_certificate ps hs))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (weighted_scale n W _ _)
      (Q'.mul_eqv_congr_left _ _ _ (haar_weighted_sum_indexed n W (fun p => polyMul p p) ps))))

private theorem square_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polyMul (polySmul c p) (polySmul c p)) (polySmul (c*c) (polyMul p p)) :=
  (RatPolyCoeffEqv.polyMul_smul_left c p (polySmul c p)).trans
    (((RatPolyCoeffEqv.polyMul_smul_right c p p).smul c).trans (RatPolyCoeffEqv.smul_assoc c c _))

private theorem scaled_sum_bound {A : Type} (a b : A → Q') (C : Q') :
    ∀ ids : List A, (∀ i, i ∈ ids → a i ≤ C*b i) →
      qListSum (ids.map a) ≤ C*listQSum b ids
  | [], _ => Q'.ge_of_eqv (Q'.mul_zero_eqv C)
  | i :: ids, h => Q'.le_trans' _ _ _
      (Q'.add_le_add (h i List.mem_cons_self)
        (scaled_sum_bound a b C ids (fun j hj => h j (List.mem_cons_of_mem i hj))))
      (Q'.ge_of_eqv (Q'.mul_add_eqv C (b i) (listQSum b ids)))

/-- No coefficient sign, distinctness, source floor/cap or positive-depth
premise. The stated linear Cauchy loss is explicit, not a variance estimate. -/
theorem family_energy_nome_cleared {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : sufficientCutoff w ≤ K+1)
    (hH : headCutoff w ≤ K+1) {base width : Nat} (hwidth : base < width)
    (depth : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    (2 : Q')*energy w (K+1) width (terminalMessage w (K+1) width depth) (spatialSpan width c qs) ≤
      (384*(1-w)*(Q'.ofNat qs.length*listQSum (fun p => c p*c p) qs))*oddMass w (K+1) width depth := by
  let W := edgeDensity w (K+1) width (terminalMessage w (K+1) width depth)
  let f (p : Z4Plaq) := jump width (characterPolynomial (plaquette width p).scalar 1)
  let ps := qs.map fun p => polySmul (c p) (f p)
  have R := edgeCertificate hw0 hw1 (K+1) width hH
    (terminalMessage_supported w (K+1) width depth) (terminalMessage_certificate hw0 hw1 (K+1) width hH depth)
  have hs : ∀ p, p ∈ ps → SupportedQuaternionBlocks (N width+N width) p := by
    intro p hp
    obtain ⟨face, _, rfl⟩ := List.mem_map.mp hp
    exact supported_smul (jump_supported width
      (character_supported (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1)) _
  have hc := weighted_sum_square_le R ps hs
  have hsum := scaled_sum_bound
    (fun p => quaternionHaar (N width+N width) (polyMul W (polyMul (polySmul (c p) (f p)) (polySmul (c p) (f p)))))
    (fun p => c p*c p) ((384*(1-w))*oddMass w (K+1) width depth) qs (by
      intro p hp
      have h := Q'.mul_le_mul_of_nonneg_left _ _ (c p*c p)
        (face_jump_bound hw0 hw1 K hK hH hwidth depth p (hqs p hp)) (SumOfSquares.q_mul_self_nonneg _)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (haar_of_coeff ((square_smul (c p) (f p)).mul_left W)) (weighted_scale _ W _ _)))
        (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))))
  simp only [ps, List.length_map, List.map_map, Function.comp_def] at hc
  have hj := family_jump_sum width c qs
  have he := Q'.eqv_trans _ _ _ (energy_identity w (K+1) width
    (terminalMessage_supported w (K+1) width depth) (spatialSpan_supported width c qs))
    (haar_of_coeff ((hj.mul hj).mul_left W))
  have hfinal : Q'.ofNat qs.length *
      (((384*(1-w))*oddMass w (K+1) width depth)*listQSum (fun p => c p*c p) qs) ≈
      (384*(1-w)*(Q'.ofNat qs.length*listQSum (fun p => c p*c p) qs))*oddMass w (K+1) width depth :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.mul (.const 384) (.var 1)) (.var 2)) (.var 3)))
      (.mul (.mul (.mul (.const 384) (.var 1)) (.mul (.var 0) (.var 3))) (.var 2)) (by decide)
      (fun
        | 0 => Q'.ofNat qs.length | 1 => (1 : Q')-w
        | 2 => oddMass w (K+1) width depth | _ => listQSum (fun p => c p*c p) qs)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (Q'.le_trans' _ _ _ hc
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hsum (Q'.ofNat_nonneg _))
      (Q'.le_of_eqv hfinal)))

/-- Divide ONLY by the SAME original positive odd partition. -/
theorem family_energy_nome_normalized {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : sufficientCutoff w ≤ K+1)
    (hH : headCutoff w ≤ K+1) {base width : Nat} (hwidth : base < width)
    (depth : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    (2 : Q')*normalizedEnergy hw0 hw1 (K+1) width hH depth (spatialSpan width c qs) ≤
      384*(1-w)*(Q'.ofNat qs.length*listQSum (fun p => c p*c p) qs) := by
  have hz := oddMass_positive hw0 hw1 (K+1) width hH depth
  have h := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos _ hz)
    (family_energy_nome_cleared hw0 hw1 K hK hH hwidth depth c qs hqs)
    (Q'.le_of_lt (Q'.recipPos_pos _ hz))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv _ hz))
        (Q'.mul_one_eqv _)))))

private theorem finite_sum_map {Index : Type} (f : Index → RatPoly) :
    ∀ xs : List Index, finitePolySum f xs = polySum (xs.map f)
  | [] => rfl
  | _ :: xs => congrArg (polyAdd _) (finite_sum_map f xs)

/-- The SAME edge law controls the entire signed family with coefficient-L1
cost, without a list-length factor. The mixed entries need not vanish.
Absolute-value ceilings do not exploit cancellation on the right. -/
theorem family_energy_l1_normalized {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : sufficientCutoff w ≤ K+1)
    (hH : headCutoff w ≤ K+1) {base width : Nat} (hwidth : base < width)
    (depth : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    (2 : Q')*normalizedEnergy hw0 hw1 (K+1) width hH depth (spatialSpan width c qs) ≤
      384*(1-w)*(listQSum (fun p => Q'.abs (c p)) qs *
        listQSum (fun p => Q'.abs (c p)) qs) := by
  let W := edgeDensity w (K+1) width (terminalMessage w (K+1) width depth)
  let f (p : Z4Plaq) := jump width (characterPolynomial (plaquette width p).scalar 1)
  let F := finitePolySum (fun p => polySmul (c p) (f p)) qs
  have R := edgeCertificate hw0 hw1 (K+1) width hH
    (terminalMessage_supported w (K+1) width depth)
    (terminalMessage_certificate hw0 hw1 (K+1) width hH depth)
  have hz := oddMass_positive hw0 hw1 (K+1) width hH depth
  have hm := edge_total_mass w (K+1) width depth
  have hW : (0 : Q') < quaternionHaar (N width+N width) W :=
    Q'.pos_of_lt_of_le hz (Q'.ge_of_eqv hm)
  have hr : Q'.recipPos (quaternionHaar (N width+N width) W) hW ≈
      Q'.recipPos (oddMass w (K+1) width depth) hz :=
    Q'.recipPos_eqv_congr _ _ hW hz hm
  have hcost : ∀ p, p ∈ qs → normalizedMoment (N width+N width) W
      (polyMul (f p) (f p)) hW ≤ 384*(1-w) := by
    intro p hp
    have h := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos _ hz)
      (face_jump_bound hw0 hw1 K hK hH hwidth depth p (hqs p hp))
      (Q'.le_of_lt (Q'.recipPos_pos _ hz))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hr))
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv _ hz))
            (Q'.mul_one_eqv _)))))
  have hs : ∀ p, p ∈ qs → SupportedQuaternionBlocks (N width+N width) (f p) :=
    fun p _ => jump_supported width
      (character_supported (plaquette_supported width (N width) (Nat.le_refl _) p).scalar 1)
  have h := normalized_family_l1_cost R hW f c qs (384*(1-w)) hs hcost
  have hj : RatPolyCoeffEqv (jump width (spatialSpan width c qs)) F := by
    dsimp only [F]
    rw [finite_sum_map]
    exact family_jump_sum width c qs
  have he := Q'.eqv_trans _ _ _ (energy_identity w (K+1) width
    (terminalMessage_supported w (K+1) width depth) (spatialSpan_supported width c qs))
    (haar_of_coeff ((hj.mul hj).mul_left W))
  have hn : (2 : Q')*normalizedEnergy hw0 hw1 (K+1) width hH depth
      (spatialSpan width c qs) ≈ normalizedMoment (N width+N width) W (polyMul F F) hW :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ he)
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hr)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hn) h

#print axioms oriented_displacement_bound
#print axioms wilson_energy_nome_bound
#print axioms face_jump_bound
#print axioms family_jump_sum
#print axioms weighted_sum_square_le
#print axioms family_energy_nome_cleared
#print axioms family_energy_nome_normalized
#print axioms family_energy_l1_normalized

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyKineticUpper
