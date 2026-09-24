/-
# Width-local relative angular control of the fixed spatial action

At a selected physical link only its incident spatial plaquettes contribute
to an angular derivative.  There are at most six such faces.  Combining the
one-face relative heat certificate with the exact independent complement
therefore gives a relative bound whose constant is independent of width and
cutoff at fixed nome.

The conservative scalar derivative cap below is finite polynomial algebra.
This is source regularity only, not a relative energy/variance estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
import YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
import YMGap.Continuum.QuaternionHaarAngularProductBounds
import YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport
import YMGap.Continuum.SU2QuaternionHaarTailDerivative
import YMGap.Continuum.BF4ExactSlabCollarDegreeBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLocalRelativeBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarCoordinateAngularInterval
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)

/-- Actual spatial faces incident to the selected retained link. -/
def spatialIncidentFaces (width : Nat) (selected : Z4Link) : List Z4Plaq :=
  (spatialFaces width).filter (fun face => decide (selected ∈ edgesOf face))

def spatialComplementFaces (width : Nat) (selected : Z4Link) : List Z4Plaq :=
  (spatialFaces width).filter (fun face => !(decide (selected ∈ edgesOf face)))

theorem spatialFace_partition (width : Nat) (selected : Z4Link) :
    (spatialIncidentFaces width selected ++ spatialComplementFaces width selected).Perm
      (spatialFaces width) :=
  List.filter_append_perm _ _

theorem spatialIncidentFaces_length_le_six (width : Nat) (selected : Z4Link) :
    (spatialIncidentFaces width selected).length ≤ 6 := by
  have hn : (spatialIncidentFaces width selected).Nodup :=
    List.filter_sublist.nodup (spatialFaces_nodup width)
  have hs : ∀ face, face ∈ spatialIncidentFaces width selected →
      face ∈ edgePlaqs selected.1 selected.2 := by
    intro face hf
    have hi : selected ∈ edgesOf face := of_decide_eq_true (List.mem_filter.mp hf).2
    exact edge_complete face selected.1 selected.2 hi
  have h := CayleyPruferInjection.nodup_subset_length_le
    (spatialIncidentFaces width selected) (edgePlaqs selected.1 selected.2) hn hs
  simpa only [edgePlaqs_length] using h

private structure GlobalAngularBound (blocks i j : Nat) (p : RatPoly) (a b : Q') where
  value : Interval blocks p a
  derivative : Interval blocks (angularDerivative i j p) b

private def derivativeCoordinateInterval {blocks coordinate : Nat}
    (i : Nat) (hc : coordinate < 4*blocks) :
    Interval blocks (ratDerivative i (polyVar coordinate)) 2 := by
  refine (polynomialInterval blocks _
    (ratDerivative_supported (coordinateInterval hc).support)).weaken ?_
  change ((Q'.ofNat (exponentAt (varMono coordinate) i) * 1) *
    (Q'.ofNat (exponentAt (varMono coordinate) i) * 1) + 1) + 0 ≤ (2 : Q')
  rw [exponentAt_varMono]
  by_cases h : i = coordinate
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

private def globalCoordinateBound {blocks i j coordinate : Nat}
    (hi : i < 4*blocks) (hj : j < 4*blocks) (hc : coordinate < 4*blocks) :
    GlobalAngularBound blocks i j (polyVar coordinate) 1 4 := by
  let V := coordinateInterval hc
  let D (k c : Nat) (hk : k < 4*blocks) :
      Interval blocks (polyMul (polyVar k) (ratDerivative c (polyVar coordinate))) 2 := by
    exact ((coordinateInterval hk).mul (derivativeCoordinateInterval c hc)).weaken
      (by decide)
  exact ⟨V, ((D i j hi).add
    (Interval.ofCoeff (polySmul_supported (D j i hj).support (-1))
      (QuaternionHaarAngularCarrier.neg_smul _).symm
      (intervalNeg (D j i hj)))).changeCap (by decide)⟩

private def globalAdd {blocks i j : Nat} {p q : RatPoly} {a b c d : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    (P : GlobalAngularBound blocks i j p a b) (Q : GlobalAngularBound blocks i j q c d) :
    GlobalAngularBound blocks i j (polyAdd p q) (a+c) (b+d) :=
  ⟨P.value.add Q.value, Interval.ofCoeff
    (angularDerivative_supported_at hi hj (P.value.add Q.value).support)
    (angularDerivative_add i j p q) (P.derivative.add Q.derivative)⟩

private def globalNeg {blocks i j : Nat} {p : RatPoly} {a b : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    (P : GlobalAngularBound blocks i j p a b) :
    GlobalAngularBound blocks i j (polyNeg p) a b :=
  ⟨intervalNeg P.value, Interval.ofCoeff
    (angularDerivative_supported_at hi hj (intervalNeg P.value).support)
    (angularDerivative_neg i j p) (intervalNeg P.derivative)⟩

private def globalMul {blocks i j : Nat} {p q : RatPoly} {a b c d : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    (P : GlobalAngularBound blocks i j p a b) (Q : GlobalAngularBound blocks i j q c d) :
    GlobalAngularBound blocks i j (polyMul p q) (a*c) (b*c+a*d) :=
  ⟨P.value.mul Q.value, Interval.ofCoeff
    (angularDerivative_supported_at hi hj (P.value.mul Q.value).support)
    (angularDerivative_mul i j p q)
    ((P.derivative.mul Q.value).add (P.value.mul Q.derivative))⟩

private structure GlobalQuaternionBound (blocks i j : Nat)
    (p : PolyQuaternion) (a b : Q') where
  scalar : GlobalAngularBound blocks i j p.scalar a b
  iPart : GlobalAngularBound blocks i j p.iPart a b
  jPart : GlobalAngularBound blocks i j p.jPart a b
  kPart : GlobalAngularBound blocks i j p.kPart a b

private def globalQuaternionOne {blocks i j : Nat}
    (hi : i < 4*blocks) (hj : j < 4*blocks) :
    GlobalQuaternionBound blocks i j PolyQuaternion.one 1 0 := by
  let Z : GlobalAngularBound blocks i j polyZero 1 0 :=
    ⟨(Interval.zero blocks).weaken (by decide), Interval.zero blocks⟩
  exact ⟨⟨Interval.one blocks, Interval.ofCoeff
    (angularDerivative_supported_at hi hj (supported_one blocks))
    (angularDerivative_one i j) (Interval.zero blocks)⟩, Z, Z, Z⟩

private def globalQuaternionCoordinate {blocks i j block : Nat}
    (hi : i < 4*blocks) (hj : j < 4*blocks) (hb : block < blocks) :
    GlobalQuaternionBound blocks i j (PolyQuaternion.coordinateVariable block) 1 4 :=
  ⟨globalCoordinateBound hi hj (by omega), globalCoordinateBound hi hj (by omega),
    globalCoordinateBound hi hj (by omega), globalCoordinateBound hi hj (by omega)⟩

private def globalQuaternionConj {blocks i j : Nat} {p : PolyQuaternion} {a b : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    (P : GlobalQuaternionBound blocks i j p a b) :
    GlobalQuaternionBound blocks i j (PolyQuaternion.conj p) a b :=
  ⟨P.scalar, globalNeg hi hj P.iPart, globalNeg hi hj P.jPart, globalNeg hi hj P.kPart⟩

private def globalQuaternionMul {blocks i j : Nat} {p q : PolyQuaternion} {a b c d : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    (P : GlobalQuaternionBound blocks i j p a b)
    (Q : GlobalQuaternionBound blocks i j q c d) :
    GlobalQuaternionBound blocks i j (PolyQuaternion.mul p q)
      (QuaternionHaarAngularProductBounds.fourCap (a*c))
      (QuaternionHaarAngularProductBounds.fourCap (b*c+a*d)) :=
  ⟨globalAdd hi hj (globalMul hi hj P.scalar Q.scalar)
      (globalNeg hi hj (globalAdd hi hj (globalMul hi hj P.iPart Q.iPart)
        (globalAdd hi hj (globalMul hi hj P.jPart Q.jPart) (globalMul hi hj P.kPart Q.kPart)))),
    globalAdd hi hj (globalMul hi hj P.scalar Q.iPart)
      (globalAdd hi hj (globalMul hi hj P.iPart Q.scalar)
        (globalAdd hi hj (globalMul hi hj P.jPart Q.kPart)
          (globalNeg hi hj (globalMul hi hj P.kPart Q.jPart)))),
    globalAdd hi hj (globalMul hi hj P.scalar Q.jPart)
      (globalAdd hi hj (globalMul hi hj P.jPart Q.scalar)
        (globalAdd hi hj (globalMul hi hj P.kPart Q.iPart)
          (globalNeg hi hj (globalMul hi hj P.iPart Q.kPart)))),
    globalAdd hi hj (globalMul hi hj P.scalar Q.kPart)
      (globalAdd hi hj (globalMul hi hj P.kPart Q.scalar)
        (globalAdd hi hj (globalMul hi hj P.iPart Q.jPart)
          (globalNeg hi hj (globalMul hi hj P.jPart Q.iPart))))⟩

private def globalQuaternionWeaken {blocks i j : Nat} {p : PolyQuaternion} {a b c d : Q'}
    (P : GlobalQuaternionBound blocks i j p a b) (ha : a ≤ c) (hb : b ≤ d) :
    GlobalQuaternionBound blocks i j p c d :=
  ⟨⟨P.scalar.value.weaken ha, P.scalar.derivative.weaken hb⟩,
    ⟨P.iPart.value.weaken ha, P.iPart.derivative.weaken hb⟩,
    ⟨P.jPart.value.weaken ha, P.jPart.derivative.weaken hb⟩,
    ⟨P.kPart.value.weaken ha, P.kPart.derivative.weaken hb⟩⟩

private def linkBound (width : Nat) {i j : Nat} (hi : i < 4*N width) (hj : j < 4*N width)
    (l : Z4Link) : GlobalQuaternionBound (N width) i j (link width l) 1 4 := by
  unfold link
  split
  · exact globalQuaternionCoordinate hi hj (List.idxOf_lt_length_of_mem ‹l ∈ baseLinks width›)
  · exact globalQuaternionWeaken (globalQuaternionOne hi hj) (Q'.le_refl' _) (by decide)

private def orientedBound (width : Nat) {i j : Nat}
    (hi : i < 4*N width) (hj : j < 4*N width) (entry : OrientedBF4Link) :
    GlobalQuaternionBound (N width) i j (orientedLink width entry) 1 4 := by
  unfold orientedLink
  split
  · exact globalQuaternionConj hi hj (linkBound width hi hj entry.link)
  · exact linkBound width hi hj entry.link

/-- Conservative derivative interval for the actual fixed-spatial plaquette
word, valid at arbitrary coordinate-plane indices of the product carrier. -/
def plaquetteScalarAngularInterval (width : Nat) (face : Z4Plaq) {i j : Nat}
    (hi : i < 4*N width) (hj : j < 4*N width) :
    Interval (N width) (angularDerivative i j (plaquette width face).scalar) 4096 := by
  let a := (dirsOf face.2).1
  let b := (dirsOf face.2).2
  let e0 : OrientedBF4Link := ⟨(face.1, a), false⟩
  let e1 : OrientedBF4Link := ⟨(addE face.1 a, b), false⟩
  let e2 : OrientedBF4Link := ⟨(addE face.1 b, a), true⟩
  let e3 : OrientedBF4Link := ⟨(face.1, b), true⟩
  have P := globalQuaternionMul hi hj
    (globalQuaternionMul hi hj
      (globalQuaternionMul hi hj
        (globalQuaternionMul hi hj (globalQuaternionOne hi hj)
          (orientedBound width hi hj e0))
        (orientedBound width hi hj e1))
      (orientedBound width hi hj e2))
    (orientedBound width hi hj e3)
  change Interval (N width) (angularDerivative i j
    (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul
      PolyQuaternion.one (orientedLink width e0)) (orientedLink width e1))
      (orientedLink width e2)) (orientedLink width e3)).scalar) 4096
  exact P.scalar.derivative.changeCap (by decide)

private theorem complement_omits (width : Nat) (selected : Z4Link) :
    ∀ face, face ∈ spatialComplementFaces width selected → selected ∉ edgesOf face := by
  intro face hf
  exact of_decide_eq_false (by
    simpa only [Bool.not_eq_true'] using (List.mem_filter.mp hf).2)

private def faceProductCertificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) : ∀ faces : List Z4Plaq,
    Certificate (N width)
      (polynomialProduct (fun face => heatPrefix w K (plaquette width face).scalar) faces)
  | [] => .one _
  | face::faces => (faceCertificate hw0 hw1 K width (N width) (Nat.le_refl _) face hK).mul
      (faceProductCertificate hw0 hw1 K width hK faces)

private def complementRelativeBound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (selected : Z4Link)
    (hl : selected ∈ baseLinks width) {a b : Nat} (ha : a < 4) (hb : b < 4) :
    RelativeBound (N width) (4*(baseLinks width).idxOf selected+a)
      (4*(baseLinks width).idxOf selected+b)
      (polynomialProduct (fun face => heatPrefix w K (plaquette width face).scalar)
        (spatialComplementFaces width selected)) 0 :=
  RelativeBound.ofZeroDerivative
    (faceProductCertificate hw0 hw1 K width hK _)
    (angularDerivative_blockIndependent_zero ha hb
      (heatProduct_independent w K hl _ (complement_omits width selected)))

private def incidentRelativeBound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : relativeCutoff w 4096 ≤ K)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    {a b : Nat} (ha : a < 4) (hb : b < 4) :
    ∀ faces : List Z4Plaq,
    RelativeBound (N width) (4*(baseLinks width).idxOf selected+a)
      (4*(baseLinks width).idxOf selected+b)
      (polynomialProduct (fun face => heatPrefix w K (plaquette width face).scalar) faces)
      (Q'.ofNat faces.length * relativeCap w 4096)
  | [] => (RelativeBound.ofCoeff (RatPolyCoeffEqv.one_smul polyOne).symm
      (RelativeBound.constant (N width) _ _ 1 Q'.zero_le_one)).changeCap
        (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | face::faces => by
      have hi : 4*(baseLinks width).idxOf selected+a < 4*N width := by
        have := List.idxOf_lt_length_of_mem hl; omega
      have hj : 4*(baseLinks width).idxOf selected+b < 4*N width := by
        have := List.idxOf_lt_length_of_mem hl; omega
      have F := heatPrefixRelativeBoundAt hw0 hw1 hi hj
        (plaquette_supported width (N width) (Nat.le_refl _) face)
        (plaquette_unit width (N width) (Nat.le_refl _) face)
        (plaquetteScalarAngularInterval width face hi hj) K hK
      have T := incidentRelativeBound hw0 hw1 K width hK selected hl ha hb faces
      have hpoly := poly_identity_of_normal_eq
          (.add (.var 0) (.mul (.var 1) (.var 0)))
          (.mul (.add (.var 1) (.const 1)) (.var 0)) (by decide)
          (fun | 0 => relativeCap w 4096 | _ => Q'.ofNat faces.length)
      have hnat : Q'.eqv (Q'.ofNat faces.length + 1)
          (Q'.ofNat (face :: faces).length) := by
        simpa only [List.length_cons, Nat.succ_eq_add_one] using
          Q'.eqv_symm (Q'.ofNat_add_eqv faces.length 1)
      exact (F.mul T).changeCap (Q'.eqv_trans _ _ _ hpoly
        (Q'.mul_eqv_congr_right _ _ _ hnat))

/-- Actual fixed-spatial action, with a constant independent of width and
cutoff at fixed strict nome.  The cutoff guard and selected physical link are
explicit; no terminal-source or variance conclusion is included. -/
def spatialWeightRelativeBound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : relativeCutoff w 4096 ≤ K)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    {a b : Nat} (ha : a < 4) (hb : b < 4) :
    RelativeBound (N width) (4*(baseLinks width).idxOf selected+a)
      (4*(baseLinks width).idxOf selected+b)
      (spatialWeight w K width) (6 * relativeCap w 4096) := by
  let I := spatialIncidentFaces width selected
  let C := spatialComplementFaces width selected
  have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 4096) hK
  have P := incidentRelativeBound hw0 hw1 K width hK selected hl ha hb I
  have Q := complementRelativeBound hw0 hw1 K width hhead selected hl ha hb
  have hprod := P.mul Q
  have hcap : Q'.ofNat I.length * relativeCap w 4096 + 0 ≤
      6 * relativeCap w 4096 := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (QPoly.q_add_zero_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (CReal.ofNat_le_ofNat (spatialIncidentFaces_length_le_six width selected))
        (Q'.le_of_lt (relativeCap_positive hw0 (by decide))))
  exact (RelativeBound.ofCoeff
    ((polynomialProduct_perm _ (spatialFace_partition width selected).symm).trans
      (polynomialProduct_append _ I C)) hprod).weaken hcap

end YMGap.Continuum.BF4ExactSlabFixedSpatialLocalRelativeBound

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalRelativeBound.spatialIncidentFaces_length_le_six
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalRelativeBound.plaquetteScalarAngularInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalRelativeBound.spatialWeightRelativeBound
