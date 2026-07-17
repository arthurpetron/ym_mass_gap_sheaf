import YMGap.Continuum.Z4UnitCubeEnumerationParity
import YMGap.Continuum.SU2ClassPolynomialChebUniqueness
import YMGap.Continuum.SU2ClassPolynomialHaarDescent
import YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
def encDir : Dir4 → Nat | .x0 => 0 | .x1 => 1 | .x2 => 2 | .x3 => 3
def encLink (l : Z4Link) : Nat × Nat × Nat × Nat × Nat :=
  (l.1.1, l.1.2.1, l.1.2.2.1, l.1.2.2.2, encDir l.2)
#eval repr (((unitCubeSurface.flatMap edgesOf).eraseDups).map encLink)

open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

def cubeLinks : List Z4Link :=
  [((0,0,0,0), .x0), ((0,0,0,0), .x1),
   ((0,1,0,0), .x0), ((1,0,0,0), .x1),
   ((0,0,1,0), .x0), ((0,0,1,0), .x1),
   ((0,1,1,0), .x0), ((1,0,1,0), .x1),
   ((0,0,0,0), .x2), ((1,0,0,0), .x2),
   ((0,1,0,0), .x2), ((1,1,0,0), .x2)]

theorem cubeLinks_eq : cubeLinks =
    (unitCubeSurface.flatMap edgesOf).eraseDups := by decide

theorem mem_count_two {ell : Z4Link} (h : ell ∈ cubeLinks) :
    faceIncidenceCount ell unitCubeSurface = 2 := by
  simp only [cubeLinks, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem not_mem_count_zero {ell : Z4Link} (h : ell ∉ cubeLinks) :
    faceIncidenceCount ell unitCubeSurface = 0 := by
  rw [← occurrenceCount_flatMap_edgesOf]
  apply occurrenceCount_eq_zero_of_not_mem
  have h' : ell ∉ (unitCubeSurface.flatMap edgesOf).eraseDups := by
    rw [← cubeLinks_eq]
    exact h
  simpa only [List.mem_eraseDups] using h'

theorem count_zero_or_two (ell : Z4Link) :
    faceIncidenceCount ell unitCubeSurface = 0 ∨
      faceIncidenceCount ell unitCubeSurface = 2 := by
  by_cases h : ell ∈ cubeLinks
  · exact Or.inr (mem_count_two h)
  · exact Or.inl (not_mem_count_zero h)

open YMGap.Constructive.QPoly
open YMGap.Constructive
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2ClassPolynomialHaarDescent
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ₚ " => PolyEqv
local infix:50 " ≈ " => Q'.eqv

def charPow (p : Poly) : Nat → Poly
  | 0 => pone
  | k + 1 => pmul p (charPow p k)

def selectedCharProduct {a : Type} (sel : a → Bool) : List a → Poly
  | [] => pone
  | x :: xs => pmul (if sel x then chebPoly 2 else pone)
      (selectedCharProduct sel xs)

theorem selectedCharProduct_eq_pow {a : Type} (sel : a → Bool) :
    ∀ xs : List a, selectedCharProduct sel xs ≈ₚ
      charPow (chebPoly 2) ((xs.filter sel).length)
  | [] => peqv_refl _
  | x :: xs => by
      cases hx : sel x with
      | false =>
        simp only [selectedCharProduct, List.filter_cons, hx]
        exact peqv_trans (pone_pmul _) (selectedCharProduct_eq_pow sel xs)
      | true =>
        simp only [selectedCharProduct, List.filter_cons, hx,
          List.length_cons, charPow]
        exact pmul_congr (peqv_refl _) (selectedCharProduct_eq_pow sel xs)

def incidentBoxFaces (n : Nat) (ell : Z4Link) : List Z4Plaq :=
  (boxPlaquettes n).filter fun p => decide (ell ∈ edgesOf p)

theorem incident_selected_length {n : Nat} (hn : 2 ≤ n) (ell : Z4Link) :
    (((incidentBoxFaces n ell).filter fun p =>
      decide (p ∈ unitCubeSurface)).length) =
      faceIncidenceCount ell unitCubeSurface := by
  rw [← selectedBoxFaces_length_eq_faceIncidenceCount hn ell]
  unfold incidentBoxFaces
  rw [List.filter_filter]

def spinTwoIndex : Fin 3 := ⟨2, by decide⟩
def spinTwoPacket : CharacterPacket 2 := basisPacket spinTwoIndex

theorem bareHaar_spinTwo_square :
    bareVacuumHaar (pmul (chebPoly 2) (chebPoly 2)) ≈ 1 := by
  let P : CharacterPacket 2 := spinTwoPacket
  have hs : synthesis P ≈ₚ chebPoly 2 := synthesis_basis spinTwoIndex
  have hprod : synthesis (fusionPacket P P) ≈ₚ
      pmul (synthesis P) (synthesis P) :=
    synthesis_fusionPacket_product P P
  refine Q'.eqv_trans _
    (bareVacuumHaar (pmul (synthesis P) (synthesis P))) _ ?_ ?_
  · exact bareVacuumHaar_congr (peqv_symm (pmul_congr hs hs))
  refine Q'.eqv_trans _ (bareVacuumHaar (synthesis (fusionPacket P P))) _ ?_ ?_
  · exact bareVacuumHaar_congr (peqv_symm hprod)
  refine Q'.eqv_trans _ (vacuumHaar (fusionPacket P P)) _
    (bareVacuumHaar_synthesis_packet (fusionPacket P P)) ?_
  refine Q'.eqv_trans _ (fusionHaar P P) _
    (vacuumHaar_fusionPacket P P) ?_
  simpa [P, spinTwoPacket, spinTwoIndex] using
    (fusionHaar_basis_delta spinTwoIndex spinTwoIndex)

theorem bareHaar_charPow_zero :
    bareVacuumHaar (charPow (chebPoly 2) 0) ≈ 1 := by decide

theorem bareHaar_charPow_two :
    bareVacuumHaar (charPow (chebPoly 2) 2) ≈ 1 := by
  refine Q'.eqv_trans _
    (bareVacuumHaar (pmul (chebPoly 2) (chebPoly 2))) _ ?_
    bareHaar_spinTwo_square
  apply bareVacuumHaar_congr
  exact pmul_congr (peqv_refl _) (pmul_pone _)

def cubeLinkCharacterProduct (n : Nat) (ell : Z4Link) : Poly :=
  selectedCharProduct (fun p => decide (p ∈ unitCubeSurface))
    (incidentBoxFaces n ell)

def cubeLinkHaarValue (n : Nat) (ell : Z4Link) : Q' :=
  bareVacuumHaar (cubeLinkCharacterProduct n ell)

theorem cubeLinkHaarValue_one {n : Nat} (hn : 2 ≤ n) (ell : Z4Link) :
    cubeLinkHaarValue n ell ≈ 1 := by
  have hp := selectedCharProduct_eq_pow
    (fun p : Z4Plaq => decide (p ∈ unitCubeSurface))
    (incidentBoxFaces n ell)
  rw [incident_selected_length hn ell] at hp
  rcases count_zero_or_two ell with h0 | h2
  · rw [h0] at hp
    exact Q'.eqv_trans _ _ _ (bareVacuumHaar_congr hp)
      bareHaar_charPow_zero
  · rw [h2] at hp
    exact Q'.eqv_trans _ _ _ (bareVacuumHaar_congr hp)
      bareHaar_charPow_two

def qListProduct {a : Type} (f : a → Q') : List a → Q'
  | [] => 1
  | x :: xs => f x * qListProduct f xs

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem qListProduct_one_of_eqv {a : Type} (f : a → Q')
    (hf : ∀ x, f x ≈ 1) : ∀ xs, qListProduct f xs ≈ 1
  | [] => Q'.eqv_refl _
  | x :: xs =>
      Q'.eqv_trans _ _ _
        (qmul_congr (hf x) (qListProduct_one_of_eqv f hf xs))
        (Q'.one_mul_eqv 1)

def cubeBoxHaarLinkFactor (n : Nat) : Q' :=
  qListProduct (cubeLinkHaarValue n)
    (YMGap.Continuum.Z4FiniteBoxTrivalentResolution.distinctBoxLinks n)

theorem cubeBoxHaarLinkFactor_one {n : Nat} (hn : 2 ≤ n) :
    cubeBoxHaarLinkFactor n ≈ 1 :=
  qListProduct_one_of_eqv _ (cubeLinkHaarValue_one hn) _

def cubeFaceCoefficient (p : Z4Plaq) : Q' :=
  if p ∈ unitCubeSurface then
    YMGap.Continuum.BondMovingStep.coeffW
      YMGap.Continuum.SU2PeterWeylWilsonBlock.coupling 2
  else
    YMGap.Continuum.BondMovingStep.coeffW
      YMGap.Continuum.SU2PeterWeylWilsonBlock.coupling 0

theorem cubeFaceProduct_eq_pow : ∀ xs : List Z4Plaq,
    qListProduct cubeFaceCoefficient xs ≈
      (YMGap.Continuum.BondMovingStep.coeffW
        YMGap.Continuum.SU2PeterWeylWilsonBlock.coupling 2) ^
          ((xs.filter fun p => decide (p ∈ unitCubeSurface)).length)
  | [] => Q'.eqv_refl _
  | p :: ps => by
      by_cases hp : p ∈ unitCubeSurface
      · simp only [qListProduct, cubeFaceCoefficient, hp, if_pos,
          List.filter_cons, decide_true, List.length_cons, Q'.pow_succ]
        exact qmul_congr (Q'.eqv_refl _) (cubeFaceProduct_eq_pow ps)
      · simp only [qListProduct, cubeFaceCoefficient, hp, if_neg,
          List.filter_cons, decide_false]
        exact Q'.eqv_trans _ _ _
          (qmul_congr
            (Q'.eqv_of_eq
              (YMGap.Continuum.BondMovingStep.coeffW_zero
                YMGap.Continuum.SU2PeterWeylWilsonBlock.coupling))
            (cubeFaceProduct_eq_pow ps))
          (Q'.one_mul_eqv _)

theorem selectedCubeFaces_length {n : Nat} (hn : 2 ≤ n) :
    ((boxPlaquettes n).filter fun p =>
      decide (p ∈ unitCubeSurface)).length = 6 := by
  let selected := (boxPlaquettes n).filter fun p =>
    decide (p ∈ unitCubeSurface)
  have hselectedNodup : selected.Nodup :=
    List.filter_sublist.nodup
      (YMGap.Continuum.Z4UnitCubeEnumerationParity.boxPlaquettes_nodup n)
  have hle1 : unitCubeSurface.length ≤ selected.length := by
    apply nodup_subset_length_le unitCubeSurface selected
      YMGap.Continuum.Z4UnitCubeSurfaceGeometry.unitCubeSurface_nodup
    intro p hp
    exact List.mem_filter.mpr
      ⟨YMGap.Continuum.Z4UnitCubeSurfaceGeometry.unitCubeSurface_mem_box hn hp,
       by simpa⟩
  have hle2 : selected.length ≤ unitCubeSurface.length := by
    apply nodup_subset_length_le selected unitCubeSurface hselectedNodup
    intro p hp
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hp).2
  rw [← YMGap.Continuum.Z4UnitCubeSurfaceGeometry.unitCubeSurface_length]
  exact Nat.le_antisymm hle2 hle1

def cubeBoxFaceCoefficientFactor (n : Nat) : Q' :=
  qListProduct cubeFaceCoefficient (boxPlaquettes n)

theorem cubeBoxFaceCoefficientFactor_exact {n : Nat} (hn : 2 ≤ n) :
    cubeBoxFaceCoefficientFactor n ≈
      (YMGap.Continuum.BondMovingStep.coeffW
        YMGap.Continuum.SU2PeterWeylWilsonBlock.coupling 2) ^ 6 := by
  unfold cubeBoxFaceCoefficientFactor
  have h := cubeFaceProduct_eq_pow (boxPlaquettes n)
  rw [selectedCubeFaces_length hn] at h
  exact h

def cubeBoxHaarCharacterSector (n : Nat) : Q' :=
  cubeBoxFaceCoefficientFactor n * cubeBoxHaarLinkFactor n

theorem cubeBoxHaarCharacterSector_exact {n : Nat} (hn : 2 ≤ n) :
    cubeBoxHaarCharacterSector n ≈
      (YMGap.Continuum.BondMovingStep.coeffW
        YMGap.Continuum.SU2PeterWeylWilsonBlock.coupling 2) ^ 6 := by
  unfold cubeBoxHaarCharacterSector
  exact Q'.eqv_trans _ _ _
    (qmul_congr (cubeBoxFaceCoefficientFactor_exact hn)
      (cubeBoxHaarLinkFactor_one hn))
    (Q'.mul_one_eqv _)
