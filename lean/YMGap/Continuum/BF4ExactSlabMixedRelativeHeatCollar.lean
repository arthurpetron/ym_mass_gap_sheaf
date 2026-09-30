/-
# Mixed relative bounds for the ORIGINAL two-link heat collar

The literal physical four-link plaquette supplies both scalar derivatives
and their ordered mixed derivative. Original-prefix weight removal then
controls each face heat, and the exact finite product controls the actual
collar. At most twelve face factors meet two links in this slab geometry.

Constants depend explicitly on nome, not extent or sufficiently late cutoff.
No reciprocal heat minimum enters them. This bounds derivatives of the
collar A itself, not yet Y X(A*g), its reciprocal-dual Gram matrix, or a
normalized family temporal energy. No scaling or physical mass is inferred.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteMixedAngularInterval
import YMGap.Continuum.QuaternionHaarHeatMixedRelativeAngularBound
import YMGap.Continuum.QuaternionHaarMixedRelativeProduct
import YMGap.Continuum.BF4ExactSlabBlockNormalizer

namespace YMGap.Continuum.BF4ExactSlabMixedRelativeHeatCollar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Link)
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (haarNorm_slabPlaquette)
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabBlockNormalizer (collarHeat)
open YMGap.Continuum.BF4ExactSlabPlaquetteMixedAngularInterval
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarMixedRelativeAngularBound
open YMGap.Continuum.QuaternionHaarMixedRelativeProduct
open YMGap.Continuum.QuaternionHaarHeatMixedRelativeAngularBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

def faceFirstCap (w : Q') : Q' :=
  QuaternionHaarHeatRelativeAngularBound.relativeCap w 2048

def faceMixedCap (w : Q') : Q' := mixedRelativeCap w 2048 2048 16384

def cutoff (w : Q') : Nat := mixedRelativeCutoff w 2048 2048 16384

/-- Literal original face heat, not the weighted Jacobi approximant. -/
def faceMixedRelativeBound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : cutoff w ≤ K)
    {ob ib oi oj ii ij : Nat} (hob : ob < blocks extent) (hib : ib < blocks extent)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent) :
    MixedBound (blocks extent) (4*ob+oi) (4*ob+oj) (4*ib+ii) (4*ib+ij)
      (faceHeatPolynomial w K extent id) (faceFirstCap w) (faceFirstCap w) (faceMixedCap w) := by
  dsimp [blocks] at hob hib
  let J := plaquetteMixedAngularJet extent hob hib hoi hoj hii hij (slabPlaquetteAt extent id)
  rw [faceHeatPolynomial_eq_sum]
  exact heatPrefixMixedRelativeBoundAt hw0 hw1 (by omega) (by omega) (by omega) (by omega)
    (supported_slabPlaquette extent (slabPlaquetteAt extent id))
    (haarNorm_slabPlaquette (slabPlaquetteAt_mem hid)) J.outer J.inner J.mixed K hK

def collarFirstCap (w : Q') : Q' := Q'.ofNat 12 * faceFirstCap w

def collarMixedCap (w : Q') : Q' := productMixedCost (faceFirstCap w) (faceMixedCap w) 12

/-- All factors in the literal original collar are retained. The list may
contain zero, one or two links; supported angular planes may overlap. The
constant does not contain the ambient extent or cutoff. -/
def twoLinkCollarMixedRelativeBound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : cutoff w ≤ K)
    {ob ib oi oj ii ij : Nat} (hob : ob < blocks extent) (hib : ib < blocks extent)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4)
    (links : List Z4Link) (hlinks : links.length ≤ 2) :
    MixedBound (blocks extent) (4*ob+oi) (4*ob+oj) (4*ib+ii) (4*ib+ij)
      (collarHeat w K extent links) (collarFirstCap w) (collarFirstCap w) (collarMixedCap w) := by
  have hc : (0 : Q') ≤ faceFirstCap w :=
    Q'.le_of_lt (QuaternionHaarHeatRelativeAngularBound.relativeCap_positive hw0 (by decide))
  have hm : (0 : Q') ≤ faceMixedCap w :=
    Q'.le_of_lt (mixedRelativeCap_positive hw0 (by decide) (by decide) (by decide))
  have hsize : (collar extent links).length ≤ 12 := by
    have h := collarCount_le extent links
    change (collar extent links).length ≤ 6*links.length at h
    omega
  exact productBoundAtLength (faceHeatPolynomial w K extent) (collar extent links)
    (fun id hid => faceMixedRelativeBound hw0 hw1 K extent hK hob hib hoi hoj hii hij
      id (collar_physical hid)) hc hm 12 hsize

#print axioms faceFirstCap
#print axioms faceMixedCap
#print axioms cutoff
#print axioms faceMixedRelativeBound
#print axioms collarFirstCap
#print axioms collarMixedCap
#print axioms twoLinkCollarMixedRelativeBound

end YMGap.Continuum.BF4ExactSlabMixedRelativeHeatCollar
