/-
# Explicit valence-zero-through-six SU(2) link multiplicities

After canonical identifier transport, a local link factor contains at most
three internal channels.  This file states those factors as literal finite
counts of SU(2) fusion paths.  The formulas expose the exact objects that
subsequent estimates may bound; no graph identifiers or packet amplitudes
remain in them.
-/

import YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity

namespace YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Literal path sets -/

def boolMultiplicity (allowed : Bool) : Nat :=
  if allowed then 1 else 0

def oneValentMultiplicity (cutoff a : Nat) : Nat :=
  ((List.range (cutoff + 1)).filter fun vacuum =>
    fusionOK a vacuum vacuum && decide (vacuum = 0)).length

def twoValentMultiplicity (cutoff a b : Nat) : Nat :=
  ((List.range (cutoff + 1)).filter fun vacuum =>
    fusionOK a b vacuum && decide (vacuum = 0)).length

def oneChannelMultiplicity (cutoff a b c d : Nat) : Nat :=
  ((List.range (cutoff + 1)).filter fun x =>
    fusionOK a b x && fusionOK x c d).length

def twoChannelMultiplicity (cutoff a b c d e : Nat) : Nat :=
  (((List.range (cutoff + 1)).flatMap fun x =>
      (List.range (cutoff + 1)).map fun y => (x, y)).filter fun xy =>
    fusionOK a b xy.1 &&
      (fusionOK xy.1 c xy.2 &&
        fusionOK xy.2 d e)).length

def threeChannelMultiplicity (cutoff a b c d e f : Nat) : Nat :=
  (((List.range (cutoff + 1)).flatMap fun x =>
      (List.range (cutoff + 1)).flatMap fun y =>
        (List.range (cutoff + 1)).map fun z => (x, y, z)).filter fun xyz =>
    fusionOK a b xyz.1 &&
      (fusionOK xyz.1 c xyz.2.1 &&
        (fusionOK xyz.2.1 d xyz.2.2 &&
          fusionOK xyz.2.2 e f))).length

/-! ## 2. Canonical counts, first cases -/

private theorem range_one : List.range 1 = [0] := rfl
private theorem range_two : List.range 2 = [0, 1] := rfl
private theorem range_three : List.range 3 = [0, 1, 2] := rfl
private theorem range_four : List.range 4 = [0, 1, 2, 3] := rfl
private theorem range_five : List.range 5 = [0, 1, 2, 3, 4] := rfl
private theorem range_six : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl

private theorem canonicalAllowed_one (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 1 external auxiliary =
      (fusionOK (external 0) (auxiliary 1) (auxiliary 1) &&
        decide (auxiliary 1 = 0)) := by
  unfold canonicalLinkConditionalAllowedB
  rw [range_one]
  simp [fuseLabels, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    canonicalAuxiliaryEdgeAllowedB, overlayOn]

private theorem canonicalAllowed_two (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 2 external auxiliary =
      (fusionOK (external 0) (external 1) (auxiliary 2) &&
        decide (auxiliary 2 = 0)) := by
  unfold canonicalLinkConditionalAllowedB
  rw [range_two]
  simp [fuseLabels, fuseChain, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    canonicalAuxiliaryEdgeAllowedB, overlayOn]

private theorem canonicalAllowed_three (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 3 external auxiliary =
      fusionOK (external 0) (external 1) (external 2) := by
  unfold canonicalLinkConditionalAllowedB
  rw [range_three]
  simp [fuseLabels, fuseChain, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    overlayOn]

private theorem canonicalAllowed_four (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 4 external auxiliary =
      (fusionOK (external 0) (external 1) (auxiliary 5) &&
        fusionOK (auxiliary 5) (external 2) (external 3)) := by
  unfold canonicalLinkConditionalAllowedB
  rw [range_four]
  simp [fuseLabels, fuseChain, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    canonicalAuxiliaryEdgeAllowedB, overlayOn]

private theorem canonicalAllowed_five (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 5 external auxiliary =
      (fusionOK (external 0) (external 1) (auxiliary 6) &&
        (fusionOK (auxiliary 6) (external 2) (auxiliary 7) &&
          fusionOK (auxiliary 7) (external 3) (external 4))) := by
  unfold canonicalLinkConditionalAllowedB
  rw [range_five]
  simp [fuseLabels, fuseChain, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    canonicalAuxiliaryEdgeAllowedB, overlayOn]

private theorem canonicalAllowed_six (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 6 external auxiliary =
      (fusionOK (external 0) (external 1) (auxiliary 7) &&
        (fusionOK (auxiliary 7) (external 2) (auxiliary 8) &&
          (fusionOK (auxiliary 8) (external 3) (auxiliary 9) &&
            fusionOK (auxiliary 9) (external 4) (external 5)))) := by
  unfold canonicalLinkConditionalAllowedB
  rw [range_six]
  simp [fuseLabels, fuseChain, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    canonicalAuxiliaryEdgeAllowedB, overlayOn]

private theorem flatMap_singleton_eq_map {A B : Type} (f : A → B) :
    ∀ xs : List A, xs.flatMap (fun x => [f x]) = xs.map f
  | [] => rfl
  | x :: xs => by
      simp only [List.flatMap_cons, List.map_cons, List.singleton_append]
      rw [flatMap_singleton_eq_map f xs]

private theorem boundedEdgeLabellings_single (cutoff edge : Nat) :
    boundedEdgeLabellings cutoff [edge] =
      (List.range (cutoff + 1)).map
        (fun spin => setEdgeLabel zeroEdgeLabelling edge spin) := by
  unfold boundedEdgeLabellings
  simpa only [List.map_singleton] using
    flatMap_singleton_eq_map
      (fun spin => setEdgeLabel zeroEdgeLabelling edge spin)
      (List.range (cutoff + 1))

private theorem boundedEdgeLabellings_two
    (cutoff first second : Nat) :
    boundedEdgeLabellings cutoff [first, second] =
      ((List.range (cutoff + 1)).flatMap fun x =>
        (List.range (cutoff + 1)).map fun y => (x, y)).map
          (fun xy => setEdgeLabel
            (setEdgeLabel zeroEdgeLabelling second xy.2) first xy.1) := by
  simp [boundedEdgeLabellings,
    flatMap_singleton_eq_map, List.map_flatMap, List.map_map,
    Function.comp_def]

private theorem boundedEdgeLabellings_three
    (cutoff first second third : Nat) :
    boundedEdgeLabellings cutoff [first, second, third] =
      ((List.range (cutoff + 1)).flatMap fun x =>
        (List.range (cutoff + 1)).flatMap fun y =>
          (List.range (cutoff + 1)).map fun z => (x, y, z)).map
            (fun xyz => setEdgeLabel
              (setEdgeLabel
                (setEdgeLabel zeroEdgeLabelling third xyz.2.2)
                second xyz.2.1)
              first xyz.1) := by
  simp [boundedEdgeLabellings,
    flatMap_singleton_eq_map, List.map_flatMap, List.map_map,
    Function.comp_def]

private theorem filter_map_length_congr {A B : Type}
    (f : A → B) (left : B → Bool) (right : A → Bool) :
    ∀ xs : List A, (∀ x, x ∈ xs → left (f x) = right x) →
      ((xs.map f).filter left).length = (xs.filter right).length
  | [], _ => rfl
  | x :: xs, hagree => by
      simp only [List.map_cons, List.filter_cons]
      rw [hagree x List.mem_cons_self]
      have ih := filter_map_length_congr f left right xs
        (fun y hy => hagree y (List.mem_cons_of_mem x hy))
      cases right x <;> simp [ih]

theorem canonicalMultiplicity_zero (cutoff : Nat)
    (external : EdgeLabelling) :
    canonicalLinkInvariantMultiplicityCount cutoff 0 external = 1 := by
  rfl

theorem canonicalMultiplicity_one (cutoff : Nat)
    (external : EdgeLabelling) :
    canonicalLinkInvariantMultiplicityCount cutoff 1 external =
      oneValentMultiplicity cutoff (external 0) := by
  unfold canonicalLinkInvariantMultiplicityCount oneValentMultiplicity
  rw [show canonicalUsedAuxiliaryCoordinates 1 = [1] by rfl,
    boundedEdgeLabellings_single]
  apply filter_map_length_congr
  intro spin _
  rw [canonicalAllowed_one]
  simp [setEdgeLabel]

theorem canonicalMultiplicity_two (cutoff : Nat)
    (external : EdgeLabelling) :
    canonicalLinkInvariantMultiplicityCount cutoff 2 external =
      twoValentMultiplicity cutoff (external 0) (external 1) := by
  unfold canonicalLinkInvariantMultiplicityCount twoValentMultiplicity
  rw [show canonicalUsedAuxiliaryCoordinates 2 = [2] by rfl,
    boundedEdgeLabellings_single]
  apply filter_map_length_congr
  intro spin _
  rw [canonicalAllowed_two]
  simp [setEdgeLabel]

theorem canonicalMultiplicity_three (cutoff : Nat)
    (external : EdgeLabelling) :
    canonicalLinkInvariantMultiplicityCount cutoff 3 external =
      boolMultiplicity
        (fusionOK (external 0) (external 1) (external 2)) := by
  unfold canonicalLinkInvariantMultiplicityCount boolMultiplicity
  rw [show canonicalUsedAuxiliaryCoordinates 3 = [] by rfl]
  rw [show boundedEdgeLabellings cutoff [] = [zeroEdgeLabelling] by rfl]
  simp only [List.filter_cons, List.filter_nil]
  rw [canonicalAllowed_three]
  cases fusionOK (external 0) (external 1) (external 2) <;> rfl

theorem canonicalMultiplicity_four (cutoff : Nat)
    (external : EdgeLabelling) :
    canonicalLinkInvariantMultiplicityCount cutoff 4 external =
      oneChannelMultiplicity cutoff
        (external 0) (external 1) (external 2) (external 3) := by
  unfold canonicalLinkInvariantMultiplicityCount oneChannelMultiplicity
  rw [show canonicalUsedAuxiliaryCoordinates 4 = [5] by rfl,
    boundedEdgeLabellings_single]
  apply filter_map_length_congr
  intro spin _
  rw [canonicalAllowed_four]
  simp [setEdgeLabel]

theorem canonicalMultiplicity_five (cutoff : Nat)
    (external : EdgeLabelling) :
    canonicalLinkInvariantMultiplicityCount cutoff 5 external =
      twoChannelMultiplicity cutoff (external 0) (external 1)
        (external 2) (external 3) (external 4) := by
  unfold canonicalLinkInvariantMultiplicityCount twoChannelMultiplicity
  rw [show canonicalUsedAuxiliaryCoordinates 5 = [6, 7] by rfl,
    boundedEdgeLabellings_two]
  apply filter_map_length_congr
  intro channels _
  rw [canonicalAllowed_five]
  simp [setEdgeLabel]

theorem canonicalMultiplicity_six (cutoff : Nat)
    (external : EdgeLabelling) :
    canonicalLinkInvariantMultiplicityCount cutoff 6 external =
      threeChannelMultiplicity cutoff (external 0) (external 1)
        (external 2) (external 3) (external 4) (external 5) := by
  unfold canonicalLinkInvariantMultiplicityCount threeChannelMultiplicity
  rw [show canonicalUsedAuxiliaryCoordinates 6 = [7, 8, 9] by rfl,
    boundedEdgeLabellings_three]
  apply filter_map_length_congr
  intro channels _
  rw [canonicalAllowed_six]
  simp [setEdgeLabel]

/-! ## 3. Uniform actual-link formula -/

/-- The seven explicit local formulas in one total function.  The fallback
branch is unreachable for a four-dimensional box link. -/
def explicitValenceMultiplicity (cutoff degree : Nat)
    (external : EdgeLabelling) : Nat :=
  match degree with
  | 0 => 1
  | 1 => oneValentMultiplicity cutoff (external 0)
  | 2 => twoValentMultiplicity cutoff (external 0) (external 1)
  | 3 => boolMultiplicity
      (fusionOK (external 0) (external 1) (external 2))
  | 4 => oneChannelMultiplicity cutoff
      (external 0) (external 1) (external 2) (external 3)
  | 5 => twoChannelMultiplicity cutoff
      (external 0) (external 1) (external 2) (external 3) (external 4)
  | 6 => threeChannelMultiplicity cutoff
      (external 0) (external 1) (external 2) (external 3) (external 4)
        (external 5)
  | _ => 0

theorem canonicalMultiplicity_eq_explicit
    {cutoff degree : Nat} (external : EdgeLabelling)
    (hdegree : degree ≤ linkIncidenceBound) :
    canonicalLinkInvariantMultiplicityCount cutoff degree external =
      explicitValenceMultiplicity cutoff degree external := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact canonicalMultiplicity_zero cutoff external
  · exact canonicalMultiplicity_one cutoff external
  · exact canonicalMultiplicity_two cutoff external
  · exact canonicalMultiplicity_three cutoff external
  · exact canonicalMultiplicity_four cutoff external
  · exact canonicalMultiplicity_five cutoff external
  · exact canonicalMultiplicity_six cutoff external

/-- **Explicit actual-link factor.**  Every factor in the global finite-box
spin-foam product is one of the seven displayed fusion-path counts. -/
theorem linkInvariantMultiplicityCount_eq_explicit
    {K n i : Nat} {ell :
      YMGap.Continuum.ClusterCount4DProgress.Z4Link}
    (hindexed : (i, ell) ∈ enumerate (distinctBoxLinks n))
    (physical : EdgeLabelling) :
    linkInvariantMultiplicityCount K n physical (i, ell) =
      explicitValenceMultiplicity (linkAuxiliaryCutoff K)
        (incidentPlaqIds n ell).length
        (fun edge => physical
          (localIdentifierRename (incidentPlaqIds n ell)
            (linkBlockBase n i) edge)) := by
  rw [linkInvariantMultiplicityCount_eq_canonical hindexed physical]
  exact canonicalMultiplicity_eq_explicit _
    (incidentPlaqIds_length_le_six n ell)

/-! ## 4. Geometry-driven support of every internal channel -/

theorem oneChannel_support
    {K a b c d x : Nat} (ha : a ≤ K) (hb : b ≤ K)
    (hallowed :
      (fusionOK a b x && fusionOK x c d) = true) :
    x ≤ 2 * K := by
  have hfirst := ((Bool.and_eq_true _ _).mp hallowed).1
  have hx := fusionOK_output_le_add hfirst
  omega

theorem twoChannel_support
    {K a b c d e x y : Nat}
    (ha : a ≤ K) (hb : b ≤ K) (hc : c ≤ K)
    (hallowed :
      (fusionOK a b x &&
        (fusionOK x c y && fusionOK y d e)) = true) :
    x ≤ 2 * K ∧ y ≤ 3 * K := by
  have hparts := (Bool.and_eq_true _ _).mp hallowed
  have htail := (Bool.and_eq_true _ _).mp hparts.2
  have hx := fusionOK_output_le_add hparts.1
  have hy := fusionOK_output_le_add htail.1
  constructor <;> omega

theorem threeChannel_support
    {K a b c d e f x y z : Nat}
    (ha : a ≤ K) (hb : b ≤ K) (hc : c ≤ K) (hd : d ≤ K)
    (hallowed :
      (fusionOK a b x &&
        (fusionOK x c y &&
          (fusionOK y d z && fusionOK z e f))) = true) :
    x ≤ 2 * K ∧ y ≤ 3 * K ∧ z ≤ 4 * K := by
  have hparts := (Bool.and_eq_true _ _).mp hallowed
  have htail := (Bool.and_eq_true _ _).mp hparts.2
  have hlast := (Bool.and_eq_true _ _).mp htail.2
  have hx := fusionOK_output_le_add hparts.1
  have hy := fusionOK_output_le_add htail.1
  have hz := fusionOK_output_le_add hlast.1
  constructor
  · omega
  · constructor <;> omega

theorem oneChannel_support_within_linkCutoff
    {K a b c d x : Nat} (ha : a ≤ K) (hb : b ≤ K)
    (hallowed : (fusionOK a b x && fusionOK x c d) = true) :
    x ≤ linkAuxiliaryCutoff K := by
  have hx := oneChannel_support ha hb hallowed
  unfold linkAuxiliaryCutoff linkIncidenceBound
  omega

theorem twoChannel_support_within_linkCutoff
    {K a b c d e x y : Nat}
    (ha : a ≤ K) (hb : b ≤ K) (hc : c ≤ K)
    (hallowed : (fusionOK a b x &&
      (fusionOK x c y && fusionOK y d e)) = true) :
    x ≤ linkAuxiliaryCutoff K ∧ y ≤ linkAuxiliaryCutoff K := by
  have hxy := twoChannel_support ha hb hc hallowed
  unfold linkAuxiliaryCutoff linkIncidenceBound
  constructor <;> omega

theorem threeChannel_support_within_linkCutoff
    {K a b c d e f x y z : Nat}
    (ha : a ≤ K) (hb : b ≤ K) (hc : c ≤ K) (hd : d ≤ K)
    (hallowed : (fusionOK a b x &&
      (fusionOK x c y &&
        (fusionOK y d z && fusionOK z e f))) = true) :
    x ≤ linkAuxiliaryCutoff K ∧ y ≤ linkAuxiliaryCutoff K ∧
      z ≤ linkAuxiliaryCutoff K := by
  have hxyz := threeChannel_support ha hb hc hd hallowed
  unfold linkAuxiliaryCutoff linkIncidenceBound
  constructor
  · omega
  · constructor <;> omega

end YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity.canonicalMultiplicity_zero
#print axioms YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity.canonicalMultiplicity_one
#print axioms YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity.canonicalMultiplicity_two
#print axioms YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity.canonicalMultiplicity_three
#print axioms YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity.canonicalMultiplicity_four
#print axioms YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity.canonicalMultiplicity_five
#print axioms YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity.canonicalMultiplicity_six
#print axioms YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity.canonicalMultiplicity_eq_explicit
#print axioms YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity.linkInvariantMultiplicityCount_eq_explicit
#print axioms YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity.oneChannel_support_within_linkCutoff
#print axioms YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity.twoChannel_support_within_linkCutoff
#print axioms YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity.threeChannel_support_within_linkCutoff
