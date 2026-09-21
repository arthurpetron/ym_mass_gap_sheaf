/-
# A computed finite Fischer decomposition, with signed reassembly

Decompose Delta p recursively, lift each radial-harmonic term with its
explicit positive integer denominator, then subtract that lift from p.
The remaining term is harmonic. Recursion decreases head degree by two.
All tail coefficients, signs, finite support and raw padding are retained.
This is algebraic decomposition, not an estimate on interacting cross terms.
-/

import YMGap.Continuum.SU2QuaternionFischerRadial

namespace YMGap.Continuum.SU2QuaternionFischerDecomposition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionFischerRadial

local infix:50 " ≈ " => Q'.eqv

/-- A finite polynomial mode, not an unsupplied analytic certificate. -/
structure Mode (blocks : Nat) where
  degree : Nat
  radial : Nat
  coefficient : Q'
  polynomial : RatPoly
  homogeneous : HasQuaternionBlockDegree 0 degree polynomial
  harmonic : RatPolyCoeffEqv (headLaplacian polynomial) polyZero
  support : SupportedQuaternionBlocks blocks polynomial
  padded : HeadPadded polynomial

def Mode.totalDegree {blocks : Nat} (m : Mode blocks) : Nat := m.degree + 2*m.radial

def Mode.value {blocks : Nat} (m : Mode blocks) : RatPoly :=
  polySmul m.coefficient (quaternionRadiusIter 0 m.radial m.polynomial)

theorem Mode.value_degree {blocks : Nat} (m : Mode blocks) :
    HasQuaternionBlockDegree 0 m.totalDegree m.value :=
  (radiusIter_degree m.homogeneous m.radial).smul m.coefficient

theorem Mode.value_supported {blocks : Nat} (hb : 0 < blocks) (m : Mode blocks) :
    SupportedQuaternionBlocks blocks m.value :=
  polySmul_supported (radiusIter_supported hb m.support m.radial) _

theorem Mode.value_padded {blocks : Nat} (m : Mode blocks) : HeadPadded m.value :=
  (radiusIter_padded m.padded m.radial).smul _

/-- The rational reciprocal is returned as data and its denominator is positive. -/
def Mode.raise {blocks : Nat} (m : Mode blocks) : Mode blocks :=
  { m with radial := m.radial+1
           coefficient := Q'.invSucc (radialFactor m.degree m.radial - 1) * m.coefficient }

private theorem inverse_coefficient (d k : Nat) (c : Q') :
    (Q'.invSucc (radialFactor d k - 1) * c) * Q'.ofNat (radialFactor d k) ≈ c := by
  let inv := Q'.invSucc (radialFactor d k - 1)
  let a := Q'.ofNat (radialFactor d k)
  have hi : inv*a ≈ (1 : Q') := by
    apply Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    have hn : radialFactor d k - 1 + 1 = radialFactor d k := by
      have := radialFactor_positive d k
      omega
    exact Q'.eqv_trans _ (Q'.ofNat (radialFactor d k - 1 + 1) * inv) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_of_eq (congrArg Q'.ofNat hn.symm)))
      (Q'.ofNat_succ_mul_invSucc (radialFactor d k - 1))
  exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv inv c a)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv c a))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv inv a c))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hi) (Q'.one_mul_eqv c))))

theorem Mode.raise_laplacian {blocks : Nat} (m : Mode blocks) :
    RatPolyCoeffEqv (headLaplacian m.raise.value) m.value :=
  (headLaplacian_smul _ _).trans
    (((laplacian_radiusIter m.homogeneous m.harmonic m.padded m.radial).smul _).trans
      ((RatPolyCoeffEqv.smul_assoc _ _ _).trans
        (RatPolyCoeffEqv.smul_coefficient (inverse_coefficient _ _ _) _)))

def sumValues {blocks : Nat} : List (Mode blocks) → RatPoly
  | [] => polyZero
  | m::ms => polyAdd m.value (sumValues ms)

theorem sumValues_degree {blocks n : Nat} : ∀ ms : List (Mode blocks),
    (∀ m, m ∈ ms → m.totalDegree = n) → HasQuaternionBlockDegree 0 n (sumValues ms)
  | [], _ => hasQuaternionBlockDegree_zero _ _
  | m::ms, hd =>
      (m.value_degree.relabel (hd m List.mem_cons_self)).add
        (sumValues_degree ms (fun q hq => hd q (List.mem_cons_of_mem m hq)))

theorem sumValues_supported {blocks : Nat} (hb : 0 < blocks) : ∀ ms : List (Mode blocks),
    SupportedQuaternionBlocks blocks (sumValues ms)
  | [] => by intro t ht; contradiction
  | m::ms => polyAdd_supported (m.value_supported hb) (sumValues_supported hb ms)

theorem sumValues_padded {blocks : Nat} : ∀ ms : List (Mode blocks), HeadPadded (sumValues ms)
  | [] => by intro t ht; contradiction
  | m::ms => m.value_padded.add (sumValues_padded ms)

theorem raiseSum_laplacian {blocks : Nat} : ∀ ms : List (Mode blocks),
    RatPolyCoeffEqv (headLaplacian (sumValues (ms.map Mode.raise))) (sumValues ms)
  | [] => RatPolyCoeffEqv.refl _
  | m::ms => (headLaplacian_add _ _).trans (m.raise_laplacian.add (raiseSum_laplacian ms))

/-- Exact finite signed reassembly on the ORIGINAL raw polynomial carrier. -/
structure Expansion (blocks degree : Nat) (p : RatPoly) where
  modes : List (Mode blocks)
  degrees : ∀ m, m ∈ modes → m.totalDegree = degree
  reassembly : RatPolyCoeffEqv (sumValues modes) p

private def pureMode {blocks n : Nat} (p : RatPoly)
    (hd : HasQuaternionBlockDegree 0 n p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero)
    (hs : SupportedQuaternionBlocks blocks p) (hp : HeadPadded p) : Mode blocks :=
  ⟨n, 0, 1, p, hd, hh, hs, hp⟩

private def harmonicExpansion {blocks n : Nat} (p : RatPoly)
    (hd : HasQuaternionBlockDegree 0 n p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero)
    (hs : SupportedQuaternionBlocks blocks p) (hp : HeadPadded p) : Expansion blocks n p where
  modes := [pureMode p hd hh hs hp]
  degrees := by
    intro m hm
    have he := List.mem_singleton.mp hm
    subst m
    rfl
  reassembly := (RatPolyCoeffEqv.add_zero _).trans (RatPolyCoeffEqv.one_smul p)

/-- No existence choice: the list of modes is computed by degree recursion. -/
def decomposeHomogeneous (blocks : Nat) (hb : 0 < blocks) :
    (n : Nat) → (p : RatPoly) → HasQuaternionBlockDegree 0 n p →
    SupportedQuaternionBlocks blocks p → HeadPadded p → Expansion blocks n p
  | 0, p, hd, hs, hp => harmonicExpansion p hd (harmonic_low_degree hd (by decide)) hs hp
  | 1, p, hd, hs, hp => harmonicExpansion p hd (harmonic_low_degree hd (by decide)) hs hp
  | n+2, p, hd, hs, hp => by
      let D := decomposeHomogeneous blocks hb n (activeLaplacian p)
        ((activeLaplacian_degree hd).relabel (by omega))
        (activeLaplacian_supported hs) hp.activeLaplacian
      let ms := D.modes.map Mode.raise
      let q := sumValues ms
      have hdegrees : ∀ m, m ∈ ms → m.totalDegree = n+2 := by
        intro m hm
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        have h := D.degrees a ha
        change a.degree + 2*(a.radial+1) = n+2
        unfold Mode.totalDegree at h
        omega
      have hqd : HasQuaternionBlockDegree 0 (n+2) q := sumValues_degree ms hdegrees
      have hqs : SupportedQuaternionBlocks blocks q := sumValues_supported hb ms
      have hqp : HeadPadded q := sumValues_padded ms
      have hql : RatPolyCoeffEqv (headLaplacian q) (headLaplacian p) :=
        (raiseSum_laplacian D.modes).trans (D.reassembly.trans (activeLaplacian_coeff p))
      let h := polyAdd p (polySmul (-1) q)
      have hhd : HasQuaternionBlockDegree 0 (n+2) h := hd.add (hqd.smul (-1))
      have hhs : SupportedQuaternionBlocks blocks h := polyAdd_supported hs (polySmul_supported hqs (-1))
      have hhp : HeadPadded h := hp.add (hqp.smul (-1))
      have hhl : RatPolyCoeffEqv (headLaplacian h) polyZero :=
        (headLaplacian_add _ _).trans
          (((RatPolyCoeffEqv.refl _).add
            ((headLaplacian_smul (-1) q).trans (hql.smul (-1)))).trans
              (RatPolyCoeffEqv.add_neg_smul _))
      refine ⟨pureMode h hhd hhl hhs hhp :: ms, ?_, ?_⟩
      · intro m hm
        rcases List.mem_cons.mp hm with he | hm
        · subst m; rfl
        · exact hdegrees m hm
      · change RatPolyCoeffEqv (polyAdd (polySmul 1 h) q) p
        exact ((RatPolyCoeffEqv.one_smul h).add (RatPolyCoeffEqv.refl q)).trans
          ((RatPolyCoeffEqv.add_assoc p (polySmul (-1) q) q).trans
            (((RatPolyCoeffEqv.refl p).add
              ((RatPolyCoeffEqv.add_comm _ _).trans (RatPolyCoeffEqv.add_neg_smul q))).trans
                (RatPolyCoeffEqv.add_zero p)))

end YMGap.Continuum.SU2QuaternionFischerDecomposition

#print axioms YMGap.Continuum.SU2QuaternionFischerDecomposition.Mode.value_degree
#print axioms YMGap.Continuum.SU2QuaternionFischerDecomposition.Mode.value_supported
#print axioms YMGap.Continuum.SU2QuaternionFischerDecomposition.Mode.value_padded
#print axioms YMGap.Continuum.SU2QuaternionFischerDecomposition.Mode.raise_laplacian
#print axioms YMGap.Continuum.SU2QuaternionFischerDecomposition.sumValues_degree
#print axioms YMGap.Continuum.SU2QuaternionFischerDecomposition.sumValues_supported
#print axioms YMGap.Continuum.SU2QuaternionFischerDecomposition.sumValues_padded
#print axioms YMGap.Continuum.SU2QuaternionFischerDecomposition.raiseSum_laplacian
#print axioms YMGap.Continuum.SU2QuaternionFischerDecomposition.decomposeHomogeneous
