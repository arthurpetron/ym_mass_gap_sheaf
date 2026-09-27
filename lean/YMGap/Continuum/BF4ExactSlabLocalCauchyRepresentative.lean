/-
# Explicit link-local Cauchy representatives on the original full action

Locality is carried by an actual Type-level Cauchy representative, not
selected from a quotient. The conditional constructor uses the existing
cofinal diagonal of the same full-action DenseMap, so its modulus and
completed operator pin are unchanged. This module makes no quantitative
mixing or cutoff-uniform cone claim.
-/

import YMGap.Continuum.BF4ExactSlabStarConditionalLocality
import YMGap.Continuum.BF4ExactSlabChebyshevRepresentative

namespace YMGap.Continuum.BF4ExactSlabLocalCauchyRepresentative

set_option autoImplicit false
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionExtension
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabStarConditionalLocality
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- A supplied completed original-action vector together with an explicit
fixed-support representative and its genuine Cauchy modulus. -/
structure LocalRep {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K)
    (support : List Z4Link)
    (x : GNSCompletionSpace (fullData hw0 hw1 K extent hK)) where
  rep : CauchyGNS (fullData hw0 hw1 K extent hK)
  isLocal : ∀ n, LinkLocal extent support (rep.seq n).val
  pin : Quotient.mk (cauchySetoid (fullData hw0 hw1 K extent hK)) rep = x

namespace LocalRep

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "S" => fullScalarData hw0 hw1 K extent hK

def embed (support : List Z4Link) (p : (F).V)
    (hp : LinkLocal extent support p.val) :
    LocalRep hw0 hw1 K extent hK support (embedV F p) where
  rep := constCauchy F p
  isLocal := fun _ => hp
  pin := rfl

def zero (support : List Z4Link) :
    LocalRep hw0 hw1 K extent hK support (embedV F (F).zero) :=
  embed hw0 hw1 K extent hK support (F).zero ((BlockLocal.one _ _).smul 0)

def mono {support target : List Z4Link} {x : GNSCompletionSpace F}
    (a : LocalRep hw0 hw1 K extent hK support x)
    (h : ∀ link, link ∈ support → link ∈ target) :
    LocalRep hw0 hw1 K extent hK target x where
  rep := a.rep
  isLocal := fun n => (a.isLocal n).mono h
  pin := a.pin

def add (support : List Z4Link) {x y : GNSCompletionSpace F}
    (a : LocalRep hw0 hw1 K extent hK support x)
    (b : LocalRep hw0 hw1 K extent hK support y) :
    LocalRep hw0 hw1 K extent hK support ((F).cAdd x y) where
  rep := (F).cAddCauchy a.rep b.rep
  isLocal := fun n => (a.isLocal n).add (b.isLocal n)
  pin := by
    change (F).cAdd (Quotient.mk (cauchySetoid F) a.rep)
      (Quotient.mk (cauchySetoid F) b.rep) = (F).cAdd x y
    rw [a.pin, b.pin]

def sub (support : List Z4Link) {x y : GNSCompletionSpace F}
    (a : LocalRep hw0 hw1 K extent hK support x)
    (b : LocalRep hw0 hw1 K extent hK support y) :
    LocalRep hw0 hw1 K extent hK support ((F).cSub x y) where
  rep := (F).subCauchy a.rep b.rep
  isLocal := fun n => (a.isLocal n).add ((b.isLocal n).smul (-1))
  pin := by
    change (F).cSub (Quotient.mk (cauchySetoid F) a.rep)
      (Quotient.mk (cauchySetoid F) b.rep) = (F).cSub x y
    rw [a.pin, b.pin]

def smul (support : List Z4Link) (c : Q') {x : GNSCompletionSpace F}
    (a : LocalRep hw0 hw1 K extent hK support x) :
    LocalRep hw0 hw1 K extent hK support ((S).cSmul c x) where
  rep := (S).cSmulCauchy c a.rep
  isLocal := fun n => (a.isLocal n).smul c
  pin := by
    change (S).cSmul c (Quotient.mk (cauchySetoid F) a.rep) = (S).cSmul c x
    rw [a.pin]

/-- The output is the exact original completed conditional projection. Each
diagonal polynomial is a finite approximant with the computed star support. -/
def conditional {support : List Z4Link} {x : GNSCompletionSpace F}
    (a : LocalRep hw0 hw1 K extent hK support x)
    (i : PhysicalLink extent) :
    LocalRep hw0 hw1 K extent hK (updateLinks extent i.val support)
      (conditionalProjection hw0 hw1 K extent hK i.val i.property x) := by
  let T := conditionalDenseMap hw0 hw1 K extent hK i.val i.property
  refine ⟨T.mapRep a.rep, ?_, ?_⟩
  · intro n
    let m := (T.mapOuter a.rep).phi n
    let j := (T.mapOuter a.rep).reindex.Jidx n
    change LinkLocal extent (updateLinks extent i.val support)
      ((T.toRep (a.rep.seq m)).seq j).val
    exact (conditionalProjection_localRepresentative hw0 hw1 K extent hK
      i.val i.property support (a.rep.seq m) (a.isLocal m)).property.1 j
  · calc
      Quotient.mk (cauchySetoid F) (T.mapRep a.rep) =
          T.completionMap (Quotient.mk (cauchySetoid F) a.rep) :=
        (T.completionMap_mk a.rep).symm
      _ = conditionalProjection hw0 hw1 K extent hK i.val i.property x := by
        rw [a.pin]
        rfl

end LocalRep
end YMGap.Continuum.BF4ExactSlabLocalCauchyRepresentative

#print axioms YMGap.Continuum.BF4ExactSlabLocalCauchyRepresentative.LocalRep
#print axioms YMGap.Continuum.BF4ExactSlabLocalCauchyRepresentative.LocalRep.embed
#print axioms YMGap.Continuum.BF4ExactSlabLocalCauchyRepresentative.LocalRep.zero
#print axioms YMGap.Continuum.BF4ExactSlabLocalCauchyRepresentative.LocalRep.mono
#print axioms YMGap.Continuum.BF4ExactSlabLocalCauchyRepresentative.LocalRep.add
#print axioms YMGap.Continuum.BF4ExactSlabLocalCauchyRepresentative.LocalRep.sub
#print axioms YMGap.Continuum.BF4ExactSlabLocalCauchyRepresentative.LocalRep.smul
#print axioms YMGap.Continuum.BF4ExactSlabLocalCauchyRepresentative.LocalRep.conditional
