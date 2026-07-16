/-
# Exact Haar/packet identification for the elementary cube sector

This module proves one concrete rung of the packet-to-Haar bridge on every
finite Z4 box containing the elementary cube.

The construction is not a free equality field and not a small spectral
carrier.  It uses the complete finite box geometry:

* every box plaquette is assigned its exact heat-kernel coefficient, with
  representation two on the six cube faces and representation zero outside;
* for every distinct physical box link, the actual list of incident box faces
  is converted into a product of Chebyshev character polynomials;
* the constructive bare Haar functional is applied to that polynomial;
* all link values and all plaquette coefficients are multiplied over the
  complete finite box.

The geometric core proves that a link meets either zero or exactly two cube
faces.  Hence its incident polynomial is Haar-equivalent either to `chi_0` or
to `chi_2 * chi_2`; character orthogonality evaluates both to one.  All
vacuum exterior factors therefore cancel exactly.  The resulting cube-sector
Haar weight is `(coeffW coupling 2)^6`, exactly the projected packet-graph
cube amplitude at every volume.  The all-vacuum sector is constructed on the
same box and evaluates to one.

Honest residual: this closes one character sector only.  It does not sum all
spin assignments, prove the full oriented matrix-coefficient lattice integral
equals the packet partition, control the resulting partition ratios, or take
a thermodynamic limit.  Those are now isolated beyond a genuine nontrivial
sector rather than hidden behind an assumed packet-to-Haar equality.

Constructive contract: Mathlib-free exact rational and finite-list substrate;
no nonconstructive imports, trusted compiled decisions, proof holes, or new
postulates.  Closed finite rational identities use kernel reduction only.
-/

import YMGap.Continuum.Z4UnitCubeAllVolumeAmplitude
import YMGap.Continuum.Z4UnitCubeEnumerationParity
import YMGap.Continuum.SU2ClassPolynomialChebUniqueness
import YMGap.Continuum.SU2ClassPolynomialHaarDescent
import YMGap.Continuum.SU2CharacterFusionSynthesis

namespace YMGap.Continuum.Z4UnitCubeHaarSectorBridge

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2ClassPolynomialHaarDescent
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4UnitCubeAllVolumeAmplitude
open YMGap.Continuum.Z4UnitCubeEnumerationParity
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≈ₚ " => PolyEqv

/-! ## 1. Exact twelve-link support and incidence dichotomy -/

/-- The twelve distinct positive-direction links of the elementary cube. -/
def unitCubeDistinctLinks : List Z4Link :=
  [((0, 0, 0, 0), .x0), ((0, 0, 0, 0), .x1),
   ((0, 1, 0, 0), .x0), ((1, 0, 0, 0), .x1),
   ((0, 0, 1, 0), .x0), ((0, 0, 1, 0), .x1),
   ((0, 1, 1, 0), .x0), ((1, 0, 1, 0), .x1),
   ((0, 0, 0, 0), .x2), ((1, 0, 0, 0), .x2),
   ((0, 1, 0, 0), .x2), ((1, 1, 0, 0), .x2)]

/-- The explicit twelve-link list is exactly the duplicate-free flattened
boundary of the six cube faces. -/
theorem unitCubeDistinctLinks_eq_boundary :
    unitCubeDistinctLinks =
      (unitCubeSurface.flatMap edgesOf).eraseDups := by
  decide

/-- Every listed cube link is incident on exactly two cube faces. -/
theorem unitCubeFaceIncidenceCount_two_of_mem {ell : Z4Link}
    (hell : ell ∈ unitCubeDistinctLinks) :
    faceIncidenceCount ell unitCubeSurface = 2 := by
  simp only [unitCubeDistinctLinks, List.mem_cons, List.not_mem_nil,
    or_false] at hell
  rcases hell with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- Every link outside the explicit cube boundary has zero cube-face
incidence. -/
theorem unitCubeFaceIncidenceCount_zero_of_not_mem {ell : Z4Link}
    (hell : ell ∉ unitCubeDistinctLinks) :
    faceIncidenceCount ell unitCubeSurface = 0 := by
  rw [← occurrenceCount_flatMap_edgesOf]
  apply occurrenceCount_eq_zero_of_not_mem
  have hboundary :
      ell ∉ (unitCubeSurface.flatMap edgesOf).eraseDups := by
    rw [← unitCubeDistinctLinks_eq_boundary]
    exact hell
  simpa only [List.mem_eraseDups] using hboundary

/-- Every lattice link meets zero or exactly two cube faces. -/
theorem unitCubeFaceIncidenceCount_zero_or_two (ell : Z4Link) :
    faceIncidenceCount ell unitCubeSurface = 0 ∨
      faceIncidenceCount ell unitCubeSurface = 2 := by
  by_cases hell : ell ∈ unitCubeDistinctLinks
  · exact Or.inr (unitCubeFaceIncidenceCount_two_of_mem hell)
  · exact Or.inl (unitCubeFaceIncidenceCount_zero_of_not_mem hell)

/-- Every one of the twelve cube links really occurs in the distinct physical
link list of every box containing the cube. -/
theorem unitCubeDistinctLinks_mem_box {n : Nat} (hn : 2 ≤ n)
    {ell : Z4Link} (hell : ell ∈ unitCubeDistinctLinks) :
    ell ∈ distinctBoxLinks n := by
  have herased :
      ell ∈ (unitCubeSurface.flatMap edgesOf).eraseDups := by
    rw [← unitCubeDistinctLinks_eq_boundary]
    exact hell
  have hflat : ell ∈ unitCubeSurface.flatMap edgesOf := by
    simpa only [List.mem_eraseDups] using herased
  obtain ⟨p, hpSurface, hpEdge⟩ := List.mem_flatMap.mp hflat
  have hpBox : p ∈ boxPlaquettes n := unitCubeSurface_mem_box hn hpSurface
  have hboxLink : ell ∈ boxLinks n := boundary_mem_boxLinks hpBox hpEdge
  simpa only [distinctBoxLinks, List.mem_eraseDups] using hboxLink

/-! ## 2. Incident character products and their selected-power collapse -/

/-- Right-associated polynomial power with the character identity as the
zero-th power. -/
def characterPow (p : Poly) : Nat → Poly
  | 0 => pone
  | k + 1 => pmul p (characterPow p k)

/-- Product of representation-two characters on selected entries and vacuum
characters on every unselected entry. -/
def selectedCharacterProduct {a : Type} (selected : a → Bool) :
    List a → Poly
  | [] => pone
  | x :: xs =>
      pmul (if selected x then chebPoly 2 else pone)
        (selectedCharacterProduct selected xs)

/-- Vacuum factors disappear from the actual polynomial product: it depends
only on the number of selected representation-two entries. -/
theorem selectedCharacterProduct_eq_power {a : Type}
    (selected : a → Bool) : ∀ xs : List a,
    selectedCharacterProduct selected xs ≈ₚ
      characterPow (chebPoly 2) ((xs.filter selected).length)
  | [] => peqv_refl _
  | x :: xs => by
      cases hx : selected x with
      | false =>
          simp only [selectedCharacterProduct, List.filter_cons, hx]
          exact peqv_trans (pone_pmul _)
            (selectedCharacterProduct_eq_power selected xs)
      | true =>
          simp only [selectedCharacterProduct, List.filter_cons, hx]
          exact pmul_congr (peqv_refl _)
            (selectedCharacterProduct_eq_power selected xs)

/-- The actual box plaquettes incident on a physical link. -/
def incidentBoxFaces (n : Nat) (ell : Z4Link) : List Z4Plaq :=
  (boxPlaquettes n).filter fun p => decide (ell ∈ edgesOf p)

/-- In a box containing the cube, the number of selected incident box faces
is the intrinsic cube-face incidence count. -/
theorem incidentBoxFaces_selected_length {n : Nat} (hn : 2 ≤ n)
    (ell : Z4Link) :
    (((incidentBoxFaces n ell).filter fun p =>
      decide (p ∈ unitCubeSurface)).length) =
      faceIncidenceCount ell unitCubeSurface := by
  rw [← selectedBoxFaces_length_eq_faceIncidenceCount hn ell]
  unfold incidentBoxFaces
  rw [List.filter_filter]

/-! ## 3. Genuine Haar evaluation of every link integrand -/

/-- The representation-two basis packet at cutoff two. -/
def spinTwoIndex : Fin 3 := ⟨2, by decide⟩

def spinTwoPacket : CharacterPacket 2 := basisPacket spinTwoIndex

/-- Exact character orthogonality on the ordinary bare Haar polynomial:
`Haar(chi_2 * chi_2) = 1`.  The proof passes through packet synthesis,
Clebsch--Gordan multiplication, and the all-mode Haar delta theorem. -/
theorem bareHaar_spinTwo_square :
    bareVacuumHaar (pmul (chebPoly 2) (chebPoly 2)) ≈ 1 := by
  let P : CharacterPacket 2 := spinTwoPacket
  have hs : synthesis P ≈ₚ chebPoly 2 := synthesis_basis spinTwoIndex
  have hproduct : synthesis (fusionPacket P P) ≈ₚ
      pmul (synthesis P) (synthesis P) :=
    synthesis_fusionPacket_product P P
  refine Q'.eqv_trans _
    (bareVacuumHaar (pmul (synthesis P) (synthesis P))) _ ?_ ?_
  · exact bareVacuumHaar_congr (peqv_symm (pmul_congr hs hs))
  refine Q'.eqv_trans _
    (bareVacuumHaar (synthesis (fusionPacket P P))) _ ?_ ?_
  · exact bareVacuumHaar_congr (peqv_symm hproduct)
  refine Q'.eqv_trans _ (vacuumHaar (fusionPacket P P)) _
    (bareVacuumHaar_synthesis_packet (fusionPacket P P)) ?_
  refine Q'.eqv_trans _ (fusionHaar P P) _
    (vacuumHaar_fusionPacket P P) ?_
  simpa [P, spinTwoPacket, spinTwoIndex] using
    (fusionHaar_basis_delta spinTwoIndex spinTwoIndex)

theorem bareHaar_characterPow_zero :
    bareVacuumHaar (characterPow (chebPoly 2) 0) ≈ 1 := by
  decide

theorem bareHaar_characterPow_two :
    bareVacuumHaar (characterPow (chebPoly 2) 2) ≈ 1 := by
  refine Q'.eqv_trans _
    (bareVacuumHaar (pmul (chebPoly 2) (chebPoly 2))) _ ?_
    bareHaar_spinTwo_square
  exact bareVacuumHaar_congr
    (pmul_congr (peqv_refl _) (pmul_pone _))

/-- The literal product of incident box-face characters at a link, with the
cube sector selected and every exterior face in the vacuum character. -/
def cubeLinkCharacterProduct (n : Nat) (ell : Z4Link) : Poly :=
  selectedCharacterProduct (fun p => decide (p ∈ unitCubeSurface))
    (incidentBoxFaces n ell)

/-- The constructive Haar integral of the literal link character product. -/
def cubeLinkHaarValue (n : Nat) (ell : Z4Link) : Q' :=
  bareVacuumHaar (cubeLinkCharacterProduct n ell)

/-- **Support-local Haar cancellation.**  Every link integral in the cube
sector is exactly one: outside links integrate the vacuum character, while
cube links integrate `chi_2 * chi_2`; every additional incident box face is
an exact polynomial identity factor. -/
theorem cubeLinkHaarValue_eq_one {n : Nat} (hn : 2 ≤ n)
    (ell : Z4Link) : cubeLinkHaarValue n ell ≈ 1 := by
  have hproduct := selectedCharacterProduct_eq_power
    (fun p : Z4Plaq => decide (p ∈ unitCubeSurface))
    (incidentBoxFaces n ell)
  rw [incidentBoxFaces_selected_length hn ell] at hproduct
  rcases unitCubeFaceIncidenceCount_zero_or_two ell with hzero | htwo
  · rw [hzero] at hproduct
    exact Q'.eqv_trans _ _ _ (bareVacuumHaar_congr hproduct)
      bareHaar_characterPow_zero
  · rw [htwo] at hproduct
    exact Q'.eqv_trans _ _ _ (bareVacuumHaar_congr hproduct)
      bareHaar_characterPow_two

/-! ## 4. Complete finite-box products -/

/-- Exact finite product over a list. -/
def rationalListProduct {a : Type} (f : a → Q') : List a → Q'
  | [] => 1
  | x :: xs => f x * rationalListProduct f xs

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem rationalListProduct_one_of_eqv {a : Type} (f : a → Q')
    (hf : ∀ x, f x ≈ 1) : ∀ xs,
    rationalListProduct f xs ≈ 1
  | [] => Q'.eqv_refl _
  | x :: xs =>
      Q'.eqv_trans _ _ _
        (qmul_congr (hf x) (rationalListProduct_one_of_eqv f hf xs))
        (Q'.one_mul_eqv 1)

/-- Product of the genuine local Haar values over every distinct physical
link of the box. -/
def cubeBoxHaarLinkFactor (n : Nat) : Q' :=
  rationalListProduct (cubeLinkHaarValue n) (distinctBoxLinks n)

theorem cubeBoxHaarLinkFactor_eq_one {n : Nat} (hn : 2 ≤ n) :
    cubeBoxHaarLinkFactor n ≈ 1 :=
  rationalListProduct_one_of_eqv _ (cubeLinkHaarValue_eq_one hn) _

/-- Heat-kernel coefficient of a box face in the cube sector.  Exterior faces
carry the real vacuum coefficient `coeffW coupling 0`, not a stipulated unit. -/
def cubeFaceCoefficient (p : Z4Plaq) : Q' :=
  if p ∈ unitCubeSurface then coeffW coupling 2 else coeffW coupling 0

/-- The product of cube-sector face coefficients depends only on the selected
face count; every exterior vacuum coefficient is derived to be one. -/
theorem cubeFaceCoefficientProduct_eq_power : ∀ xs : List Z4Plaq,
    rationalListProduct cubeFaceCoefficient xs ≈
      (coeffW coupling 2) ^
        ((xs.filter fun p => decide (p ∈ unitCubeSurface)).length)
  | [] => Q'.eqv_refl _
  | p :: ps => by
      by_cases hp : p ∈ unitCubeSurface
      · simp only [rationalListProduct, cubeFaceCoefficient, hp, if_pos,
          List.filter_cons, decide_true, List.length_cons, Q'.pow_succ]
        exact qmul_congr (Q'.eqv_refl _)
          (cubeFaceCoefficientProduct_eq_power ps)
      · simp only [rationalListProduct, cubeFaceCoefficient, hp,
          List.filter_cons, decide_false]
        exact Q'.eqv_trans _ _ _
          (qmul_congr (Q'.eqv_of_eq (coeffW_zero coupling))
            (cubeFaceCoefficientProduct_eq_power ps))
          (Q'.one_mul_eqv _)

/-- Exactly six selected cube faces occur in every box of side at least two. -/
theorem selectedCubeFaces_length {n : Nat} (hn : 2 ≤ n) :
    ((boxPlaquettes n).filter fun p =>
      decide (p ∈ unitCubeSurface)).length = 6 := by
  let selected := (boxPlaquettes n).filter fun p =>
    decide (p ∈ unitCubeSurface)
  have hselectedNodup : selected.Nodup :=
    List.filter_sublist.nodup (boxPlaquettes_nodup n)
  have hsurfaceLe : unitCubeSurface.length ≤ selected.length := by
    apply nodup_subset_length_le unitCubeSurface selected
      unitCubeSurface_nodup
    intro p hp
    exact List.mem_filter.mpr
      ⟨unitCubeSurface_mem_box hn hp, by simpa⟩
  have hselectedLe : selected.length ≤ unitCubeSurface.length := by
    apply nodup_subset_length_le selected unitCubeSurface hselectedNodup
    intro p hp
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hp).2
  rw [← unitCubeSurface_length]
  exact Nat.le_antisymm hselectedLe hsurfaceLe

/-- Product of heat-kernel coefficients over every plaquette of the box. -/
def cubeBoxFaceCoefficientFactor (n : Nat) : Q' :=
  rationalListProduct cubeFaceCoefficient (boxPlaquettes n)

theorem cubeBoxFaceCoefficientFactor_exact {n : Nat} (hn : 2 ≤ n) :
    cubeBoxFaceCoefficientFactor n ≈ (coeffW coupling 2) ^ 6 := by
  unfold cubeBoxFaceCoefficientFactor
  have h := cubeFaceCoefficientProduct_eq_power (boxPlaquettes n)
  rw [selectedCubeFaces_length hn] at h
  exact h

/-- The full finite-box Haar/character weight of the cube sector: every box
plaquette coefficient times every distinct box-link Haar integral. -/
def cubeBoxHaarCharacterSector (n : Nat) : Q' :=
  cubeBoxFaceCoefficientFactor n * cubeBoxHaarLinkFactor n

theorem cubeBoxHaarCharacterSector_exact {n : Nat} (hn : 2 ≤ n) :
    cubeBoxHaarCharacterSector n ≈ (coeffW coupling 2) ^ 6 := by
  unfold cubeBoxHaarCharacterSector
  exact Q'.eqv_trans _ _ _
    (qmul_congr (cubeBoxFaceCoefficientFactor_exact hn)
      (cubeBoxHaarLinkFactor_eq_one hn))
    (Q'.mul_one_eqv _)

/-! ## 5. The all-vacuum sector on the same box -/

def vacuumLinkCharacterProduct (n : Nat) (ell : Z4Link) : Poly :=
  selectedCharacterProduct (fun _ : Z4Plaq => false)
    (incidentBoxFaces n ell)

def vacuumLinkHaarValue (n : Nat) (ell : Z4Link) : Q' :=
  bareVacuumHaar (vacuumLinkCharacterProduct n ell)

theorem vacuumLinkHaarValue_eq_one (n : Nat) (ell : Z4Link) :
    vacuumLinkHaarValue n ell ≈ 1 := by
  have h := selectedCharacterProduct_eq_power
    (fun _ : Z4Plaq => false) (incidentBoxFaces n ell)
  have hlength :
      ((incidentBoxFaces n ell).filter fun _ : Z4Plaq => false).length = 0 := by
    generalize incidentBoxFaces n ell = faces
    induction faces with
    | nil => rfl
    | cons _ rest ih => exact ih
  rw [hlength] at h
  exact Q'.eqv_trans _ _ _ (bareVacuumHaar_congr h)
    bareHaar_characterPow_zero

def vacuumBoxHaarLinkFactor (n : Nat) : Q' :=
  rationalListProduct (vacuumLinkHaarValue n) (distinctBoxLinks n)

theorem vacuumBoxHaarLinkFactor_eq_one (n : Nat) :
    vacuumBoxHaarLinkFactor n ≈ 1 :=
  rationalListProduct_one_of_eqv _ (vacuumLinkHaarValue_eq_one n) _

def vacuumBoxFaceCoefficientFactor (n : Nat) : Q' :=
  rationalListProduct (fun _ : Z4Plaq => coeffW coupling 0)
    (boxPlaquettes n)

theorem vacuumBoxFaceCoefficientFactor_eq_one (n : Nat) :
    vacuumBoxFaceCoefficientFactor n ≈ 1 := by
  apply rationalListProduct_one_of_eqv
  intro _
  exact Q'.eqv_of_eq (coeffW_zero coupling)

/-- The explicitly constructed all-vacuum character sector on the same box. -/
def vacuumBoxHaarCharacterSector (n : Nat) : Q' :=
  vacuumBoxFaceCoefficientFactor n * vacuumBoxHaarLinkFactor n

theorem vacuumBoxHaarCharacterSector_eq_one (n : Nat) :
    vacuumBoxHaarCharacterSector n ≈ 1 := by
  unfold vacuumBoxHaarCharacterSector
  exact Q'.eqv_trans _ _ _
    (qmul_congr (vacuumBoxFaceCoefficientFactor_eq_one n)
      (vacuumBoxHaarLinkFactor_eq_one n))
    (Q'.one_mul_eqv 1)

/-! ## 6. Exact identification with the packet cube mode -/

private theorem cubeCoefficientPower_exact :
    (coeffW coupling 2) ^ 6 ≈ unitCubeHeatKernelAmplitude := by
  decide

/-- **Concrete packet-to-Haar sector bridge.**  The complete finite-box
Haar/character cube sector equals the actual projected packet-graph amplitude
of the all-volume cube label. -/
theorem cubeBoxHaarCharacterSector_eq_packetAmplitude
    {n : Nat} (hn : 2 ≤ n) :
    cubeBoxHaarCharacterSector n ≈
      packetGraphProjectedAmplitude (usedResolutionEdges n)
        (resolutionVertices n) (gaugeHeatKernelBoxPackets n)
        (unitCubeSurfaceLabel n) :=
  Q'.eqv_trans _ (coeffW coupling 2 ^ 6) _
    (cubeBoxHaarCharacterSector_exact hn)
    (Q'.eqv_trans _ unitCubeHeatKernelAmplitude _
      cubeCoefficientPower_exact
      (Q'.eqv_symm (unitCube_heatKernel_amplitude_exact_all_volumes hn)))

/-- The cube sector is its derived local amplitude times the all-vacuum sector
on the same finite box. -/
theorem cubeBoxHaarCharacterSector_eq_amplitude_mul_vacuum
    {n : Nat} (hn : 2 ≤ n) :
    cubeBoxHaarCharacterSector n ≈
      unitCubeHeatKernelAmplitude * vacuumBoxHaarCharacterSector n := by
  refine Q'.eqv_trans _ unitCubeHeatKernelAmplitude _ ?_ ?_
  · exact Q'.eqv_trans _ _ _ (cubeBoxHaarCharacterSector_exact hn)
      cubeCoefficientPower_exact
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left unitCubeHeatKernelAmplitude _ _
      (vacuumBoxHaarCharacterSector_eq_one n))
    (Q'.mul_one_eqv unitCubeHeatKernelAmplitude))

end YMGap.Continuum.Z4UnitCubeHaarSectorBridge

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.unitCubeDistinctLinks_eq_boundary
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.unitCubeFaceIncidenceCount_two_of_mem
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.unitCubeFaceIncidenceCount_zero_of_not_mem
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.unitCubeFaceIncidenceCount_zero_or_two
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.unitCubeDistinctLinks_mem_box
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.selectedCharacterProduct_eq_power
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.incidentBoxFaces_selected_length
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.bareHaar_spinTwo_square
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.cubeLinkHaarValue_eq_one
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.cubeBoxHaarLinkFactor_eq_one
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.cubeFaceCoefficientProduct_eq_power
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.selectedCubeFaces_length
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.cubeBoxFaceCoefficientFactor_exact
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.cubeBoxHaarCharacterSector_exact
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.vacuumLinkHaarValue_eq_one
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.vacuumBoxHaarCharacterSector_eq_one
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.cubeBoxHaarCharacterSector_eq_packetAmplitude
#print axioms YMGap.Continuum.Z4UnitCubeHaarSectorBridge.cubeBoxHaarCharacterSector_eq_amplitude_mul_vacuum
