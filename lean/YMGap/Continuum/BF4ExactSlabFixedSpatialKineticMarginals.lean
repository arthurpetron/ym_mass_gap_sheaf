/-
# Both exact Haar marginals of the original fixed-spatial kinetic layer

The original temporal faces select distinct spatial-link indices. Each
factor is precisely the heat kernel between that index in the lower slice
and the same index in the upper slice. Peeling those factors against an
arbitrary supported endpoint polynomial proves both normalized marginals.

The source slice retains unused fringe links. They remain normalized Haar
variables, not extra heat factors. No bijection between temporal faces and
the complete source-link list is asserted. The immediate consumer is the
ordinary-Haar nonexpansivity of this actual free kinetic map; no spatial
potential or interacting OS gap is part of the statement.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry
import YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum
import YMGap.Continuum.SU2QuaternionHaarKernelBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram (faceLinkA)
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary (SliceLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry (kineticWeight_swap)
open YMGap.Continuum.CayleyPruferInjection (nodup_map_of_injOn)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

private theorem lower_member {width : Nat} {face : Z4Plaq}
    (hf : face ∈ temporalFaces width) : faceLinkA face ∈ baseLinks width := by
  obtain ⟨hx,hy,hz,ht,hd⟩ := (temporalFaces_mem_iff width face).mp hf
  apply (baseLinks_mem_iff width _).mpr
  rcases face with ⟨⟨x,y,z,t⟩,plane⟩
  cases plane <;> simp only [dirsOf] at hd <;> try cases hd
  all_goals dsimp only at hx hy hz ht
  all_goals simp only [SliceLink, faceLinkA, dirsOf]
  all_goals refine ⟨(by intro h; cases h), ?_, ?_, ?_, ?_⟩ <;> omega

private theorem lower_injective {width : Nat} {p q : Z4Plaq}
    (hp : p ∈ temporalFaces width) (hq : q ∈ temporalFaces width)
    (he : faceLinkA p = faceLinkA q) : p = q := by
  have hpd := ((temporalFaces_mem_iff width p).mp hp).2.2.2.2
  have hqd := ((temporalFaces_mem_iff width q).mp hq).2.2.2.2
  have hbase : p.1 = q.1 := congrArg (fun l : Z4Link => l.1) he
  have hdir : (dirsOf p.2).1 = (dirsOf q.2).1 := congrArg (fun l : Z4Link => l.2) he
  have hplane : p.2 = q.2 := by
    calc
      p.2 = planeOf (dirsOf p.2).1 (dirsOf p.2).2 := (planeOf_dirsOf p.2).symm
      _ = planeOf (dirsOf q.2).1 (dirsOf q.2).2 := by rw [hpd, hqd, hdir]
      _ = q.2 := planeOf_dirsOf q.2
  exact Prod.ext hbase hplane

/-- Exactly the link indices selected by the original temporal-face list. -/
def activeBlocks (width : Nat) : List Nat :=
  (temporalFaces width).map (fun face => (baseLinks width).idxOf (faceLinkA face))

theorem activeBlocks_lt (width : Nat) (i : Nat) (hi : i ∈ activeBlocks width) :
    i < N width := by
  obtain ⟨face,hface,rfl⟩ := List.mem_map.mp hi
  exact List.idxOf_lt_length_of_mem (lower_member hface)

/-- Distinct original temporal faces couple distinct lower/upper link pairs. -/
theorem activeBlocks_nodup (width : Nat) : (activeBlocks width).Nodup :=
  nodup_map_of_injOn _ _ (temporalFaces_nodup width)
    (fun _ hp _ hq he => lower_injective hp hq
      (idxOf_injective_on_members (lower_member hp) (lower_member hq) he))

private theorem sum_map {A B : Type} (f : B → RatPoly) (g : A → B) :
    ∀ xs : List A,
      finitePolySum f (xs.map g) = finitePolySum (fun a => f (g a)) xs
  | [] => rfl
  | a::xs => by simp only [List.map_cons, finitePolySum, sum_map f g xs]

private theorem face_heat_eq (w : Q') (K width : Nat) (face : Z4Plaq)
    (hf : face ∈ temporalFaces width) :
    factor (fun f spin => characterPolynomial (relative width f).scalar spin)
      (face,heatWeights w K) =
      heatAt ((baseLinks width).idxOf (faceLinkA face))
        (N width+(baseLinks width).idxOf (faceLinkA face)) w K := by
  have hm := lower_member hf
  simp only [factor, heatWeights, sum_map, relative, lowerLink, upperLink, if_pos hm]
  rfl

private theorem product_map {A B : Type} (f : B → RatPoly) (g : A → B) (xs : List A) :
    polynomialProduct f (xs.map g) = polynomialProduct (fun a => f (g a)) xs := by
  simp only [polynomialProduct, List.foldr_map]

/-- Literal factorization, on the original lower-then-upper carrier and in the original order. -/
theorem kineticWeight_eq_indexedProduct (w : Q') (K width : Nat) :
    kineticWeight w K width =
      polynomialProduct (fun i => heatAt i (N width+i) w K) (activeBlocks width) := by
  unfold kineticWeight activeBlocks
  rw [product_map]
  exact polynomialProduct_congr _ _ _ (fun face hf => face_heat_eq w K width face hf)

private theorem indexed_supported (n : Nat) (w : Q') (K : Nat) :
    ∀ ids : List Nat, (∀ i, i ∈ ids → i < n) →
      SupportedQuaternionBlocks (n+n)
        (polynomialProduct (fun i => heatAt i (n+i) w K) ids)
  | [], _ => supported_one _
  | i::ids, hi => supported_polyMul
      (heat_supported (by have := hi i List.mem_cons_self; omega)
        (by have := hi i List.mem_cons_self; omega) w K)
      (indexed_supported n w K ids (fun j hj => hi j (List.mem_cons_of_mem i hj)))

private theorem indexed_independent (n slot : Nat) (w : Q') (K : Nat) :
    ∀ ids : List Nat, (∀ i, i ∈ ids → slot ≠ i ∧ slot ≠ n+i) →
      HasQuaternionBlockDegree slot 0
        (polynomialProduct (fun i => heatAt i (n+i) w K) ids)
  | [], _ => hasQuaternionBlockDegree_one slot
  | i::ids, hi =>
      (heat_independent slot i (n+i) (hi i List.mem_cons_self).1
        (hi i List.mem_cons_self).2 w K).mul
        (indexed_independent n slot w K ids (fun j hj => hi j (List.mem_cons_of_mem i hj)))

private theorem indexed_marginal (n : Nat) (w : Q') (K : Nat) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (n+n) r) :
    ∀ ids : List Nat, ids.Nodup → (∀ i, i ∈ ids → i < n) →
      (∀ i, i ∈ ids → HasQuaternionBlockDegree i 0 r) →
      quaternionHaar (n+n)
        (polyMul (polynomialProduct (fun i => heatAt i (n+i) w K) ids) r) ≈
        quaternionHaar (n+n) r
  | [], _, _, _ => haar_of_coeff (RatPolyCoeffEqv.one_mul r)
  | i::ids, hn, hi, hd => by
      have hin := hi i List.mem_cons_self
      have hnd := List.nodup_cons.mp hn
      have hit (j : Nat) (hj : j ∈ ids) : j < n := hi j (List.mem_cons_of_mem i hj)
      have hdt (j : Nat) (hj : j ∈ ids) : HasQuaternionBlockDegree j 0 r :=
        hd j (List.mem_cons_of_mem i hj)
      have hrest := supported_polyMul (indexed_supported n w K ids hit) hr
      have hdegree : HasQuaternionBlockDegree i 0
          (polyMul (polynomialProduct (fun j => heatAt j (n+j) w K) ids) r) :=
        (indexed_independent n i w K ids (fun j hj =>
          ⟨(by intro he; subst j; exact hnd.1 hj), (by have := hit j hj; omega)⟩)).mul
          (hd i List.mem_cons_self)
      have he : (n+n-1)+1 = n+n := by omega
      have hp := pair_vacuum (n+n-1) (by omega)
        ⟨i,by omega⟩ ⟨n+i,by omega⟩ (by change i ≠ n+i; omega) w K
        (polyMul (polynomialProduct (fun j => heatAt j (n+j) w K) ids) r)
        (by simpa only [he] using hrest) hdegree
      have hpeel : quaternionHaar (n+n)
          (polyMul (heatAt i (n+i) w K)
            (polyMul (polynomialProduct (fun j => heatAt j (n+j) w K) ids) r)) ≈
          quaternionHaar (n+n)
            (polyMul (polynomialProduct (fun j => heatAt j (n+j) w K) ids) r) := by
        simpa only [he] using hp
      exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
        (Q'.eqv_trans _ _ _ hpeel (indexed_marginal n w K r hr ids hnd.2 hit hdt))

private theorem lift_independent (n : Nat) (f : RatPoly) :
    ∀ i, i < n → HasQuaternionBlockDegree i 0 (liftBoundary n f) := by
  induction n with
  | zero => intro i hi; exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
      intro i hi term hterm
      change term ∈ liftHead (liftBoundary n f) at hterm
      obtain ⟨source,hsource,rfl⟩ := List.mem_map.mp hterm
      cases i with
      | zero => rfl
      | succ i =>
          have h := ih i (by omega) source hsource
          change quaternionBlockDegree (0::0::0::0::source.1) (i+1) = 0
          unfold quaternionBlockDegree exponentAt
          rw [Nat.mul_succ]
          change quaternionBlockDegree source.1 i = 0
          exact h

/-- Every supported upper insertion has its original product-Haar marginal. -/
theorem kineticWeight_upper_marginal (w : Q') (K width : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) :
    quaternionHaar (N width+N width)
      (polyMul (kineticWeight w K width) (liftBoundary (N width) f)) ≈
      quaternionHaar (N width) f := by
  rw [kineticWeight_eq_indexedProduct]
  exact Q'.eqv_trans _ _ _
    (indexed_marginal (N width) w K _ (lift_supported hf (N width))
      (activeBlocks width) (activeBlocks_nodup width) (activeBlocks_lt width)
      (fun i hi => lift_independent (N width) f i (activeBlocks_lt width i hi)))
    (haar_liftBoundary (N width) (N width) f)

/-- Whole-slice swap gives the other marginal without altering any face factor. -/
theorem kineticWeight_lower_marginal (w : Q') (K width : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) :
    quaternionHaar (N width+N width) (polyMul (kineticWeight w K width) f) ≈
      quaternionHaar (N width) f := by
  have hf2 : SupportedQuaternionBlocks (N width+N width) f :=
    fun term hterm => Nat.le_trans (hf term hterm) (by omega)
  have hs := supported_polyMul (kineticWeight_supported w K width) hf2
  have ht := supported_polyMul (kineticWeight_supported w K width) (lift_supported hf (N width))
  have hpin : PaddedPolynomialCoeffEqv (N width+N width)
      (reindexQuaternionPolynomial (SU2QuaternionTwoSliceSwap.swap (N width))
        (polyMul (kineticWeight w K width) f))
      (polyMul (kineticWeight w K width) (liftBoundary (N width) f)) := by
    rw [reindexQuaternionPolynomial_mul]
    exact (kineticWeight_swap w K width).mul
      (PaddedPolynomialCoeffEqv.of_prefix (SU2QuaternionTwoSliceSwap.lower_prefix (N width) f hf))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (SU2QuaternionTwoSliceSwap.haar (N width) _ hs))
    (Q'.eqv_trans _ _ _
      (hpin.haar (SU2QuaternionTwoSliceSwap.polynomial_supported (N width) _) ht)
      (kineticWeight_upper_marginal w K width f hf))

-- Guard the elementary lifted-coordinate proof as well as its public consumers.
#print axioms lift_independent

end YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals.activeBlocks
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals.activeBlocks_lt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals.activeBlocks_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals.kineticWeight_eq_indexedProduct
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals.kineticWeight_upper_marginal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals.kineticWeight_lower_marginal
