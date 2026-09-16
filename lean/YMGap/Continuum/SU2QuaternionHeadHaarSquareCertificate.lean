/-
# Polynomial-valued head Haar square certificates

Split a finite polynomial into its even/odd TOTAL head-degree sectors. Each
sector is homogenized only in quaternion block zero by inserting powers of
the original sphere radius. These insertions preserve every tail coefficient.
The homogeneous square has one explicit positive radial denominator, so the
checked polynomial-valued Gaussian SOS compiler supplies its tail certificate.

No tail coordinate is evaluated or discretized. No analytic positivity,
finite-state replacement, stationarity or contraction premise is introduced.
-/

import YMGap.Constructive.Sqrt
import YMGap.Continuum.SU2QuaternionHeadGaussianSquareCertificate
import YMGap.Continuum.SU2QuaternionPartialSphereGaussian

namespace YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHeadGaussianIBP
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHeadGaussianSquareCertificate
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem zero_num : (0 : Q').num = 0 := rfl
private theorem zero_den : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num : (1 : Q').num = 1 := rfl
private theorem one_den : ((1 : Q').den : Int) = 1 := rfl

local macro "q_ring" : tactic =>
  `(tactic| (
      show _ * (_ : Int) = _ * (_ : Int)
      simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
        Q'.mul_den_cast, zero_num, zero_den, one_num, one_den,
        Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one,
        Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]
      all_goals ac_rfl))

private theorem partial_add (p q : RatPoly) :
    partialHaarHead (polyAdd p q) = polyAdd (partialHaarHead p) (partialHaarHead q) :=
  List.map_append

private theorem partial_mul_add_right (p q r : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (polyMul p (polyAdd q r)))
      (polyAdd (partialHaarHead (polyMul p q)) (partialHaarHead (polyMul p r))) := by
  refine (partialHaarHead_congr (RatPolyCoeffEqv.mul_add_right p q r)).trans ?_
  rw [partial_add]
  exact RatPolyCoeffEqv.refl _

private theorem monoMul_right_nil : ∀ m : List Nat, monoMul m [] = m
  | [] => rfl
  | _ :: _ => rfl

private theorem drop_monoMul : ∀ (n : Nat) (m l : List Nat),
    (monoMul m l).drop n = monoMul (m.drop n) (l.drop n)
  | 0, _, _ => by simp
  | n + 1, [], l => by simp [monoMul]
  | n + 1, m, [] => by rw [monoMul_right_nil, List.drop_nil, monoMul_right_nil]
  | n + 1, _ :: m, _ :: l => by
      simp only [monoMul, List.drop_succ_cons]
      exact drop_monoMul n m l

private theorem head_radius_moment (m : List Nat) :
    headQuaternionMoment (monoMul m (coordinateSquareMono 0)) +
      (headQuaternionMoment (monoMul m (coordinateSquareMono 1)) +
        (headQuaternionMoment (monoMul m (coordinateSquareMono 2)) +
          headQuaternionMoment (monoMul m (coordinateSquareMono 3)))) ≈
      headQuaternionMoment m := by
  simpa [headQuaternionMoment, exponentAt_monoMul, exponentAt_coordinateSquareMono]
    using sphereMoment4_radius (exponentAt m 0) (exponentAt m 1)
      (exponentAt m 2) (exponentAt m 3)

private theorem partial_single_mul_radius (t : RatTerm) :
    RatPolyCoeffEqv (partialHaarHead (polyMul [t] (quaternionRadiusPolynomial 0)))
      (partialHaarHead [t]) := by
  intro weight
  have hdrop (i : Nat) (hi : i < 4) : (coordinateSquareMono i).drop 4 = [] :=
    List.drop_eq_nil_of_le (by rw [coordinateSquareMono_length]; omega)
  simp only [quaternionRadiusPolynomial, Nat.mul_zero, Nat.zero_add,
    polyMul, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.append_nil, partialHaarHead, partialHaarHeadTerm, ratWeightedSum,
    drop_monoMul, hdrop 0 (by decide), hdrop 1 (by decide),
    hdrop 2 (by decide), hdrop 3 (by decide), monoMul_right_nil]
  refine Q'.eqv_trans _
    ((t.2 * (headQuaternionMoment (monoMul t.1 (coordinateSquareMono 0)) +
      (headQuaternionMoment (monoMul t.1 (coordinateSquareMono 1)) +
        (headQuaternionMoment (monoMul t.1 (coordinateSquareMono 2)) +
          headQuaternionMoment (monoMul t.1 (coordinateSquareMono 3)))))) *
      weight (t.1.drop 4)) _ (by q_ring) ?_
  refine Q'.eqv_trans _ ((t.2 * headQuaternionMoment t.1) * weight (t.1.drop 4)) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left _ _ _ (head_radius_moment t.1))) ?_
  q_ring

/-- Radius insertion in the head preserves EVERY tail coefficient. -/
theorem partialHaarHead_mul_radius : ∀ p : RatPoly,
    RatPolyCoeffEqv (partialHaarHead (polyMul p (quaternionRadiusPolynomial 0)))
      (partialHaarHead p)
  | [] => RatPolyCoeffEqv.refl _
  | t :: rest => by
      rw [polyMul_cons_left_exact, partial_add]
      exact (partial_single_mul_radius t).add (partialHaarHead_mul_radius rest)

private theorem partial_radiusIter_right (p q : RatPoly) : ∀ n,
    RatPolyCoeffEqv (partialHaarHead (polyMul p (quaternionRadiusIter 0 n q)))
      (partialHaarHead (polyMul p q))
  | 0 => RatPolyCoeffEqv.refl _
  | n + 1 =>
      (partialHaarHead_congr (RatPolyCoeffEqv.mul_assoc p
        (quaternionRadiusIter 0 n q) (quaternionRadiusPolynomial 0)).symm).trans
        ((partialHaarHead_mul_radius _).trans (partial_radiusIter_right p q n))

private theorem partial_radiusIter_left (p q : RatPoly) (n : Nat) :
    RatPolyCoeffEqv (partialHaarHead (polyMul (quaternionRadiusIter 0 n p) q))
      (partialHaarHead (polyMul p q)) :=
  (partialHaarHead_congr (RatPolyCoeffEqv.mul_comm _ _)).trans
    ((partial_radiusIter_right q p n).trans
      (partialHaarHead_congr (RatPolyCoeffEqv.mul_comm _ _)))

/-- Only block zero is homogenized; all tail exponents are untouched. -/
def homogenizeHead (degree : Nat) (p : RatPoly) : RatPoly :=
  homogenizeQuaternionPolynomial (fun _ => degree) 1 p

private theorem homogenize_pair_single (degree : Nat) (s t : RatTerm) :
    RatPolyCoeffEqv (partialHaarHead (polyMul
      (homogenizeQuaternionTerm (fun _ => degree) 1 s)
      (homogenizeQuaternionTerm (fun _ => degree) 1 t)))
      (partialHaarHead (polyMul [s] [t])) :=
  (partial_radiusIter_left [s]
    (quaternionRadiusIter 0 (quaternionRaiseCount (fun _ => degree) 0 t) [t])
    (quaternionRaiseCount (fun _ => degree) 0 s)).trans
      (partial_radiusIter_right [s] [t] (quaternionRaiseCount (fun _ => degree) 0 t))

private theorem homogenize_pair_row (degree : Nat) (s : RatTerm) : ∀ q : RatPoly,
    RatPolyCoeffEqv (partialHaarHead (polyMul
      (homogenizeQuaternionTerm (fun _ => degree) 1 s) (homogenizeHead degree q)))
      (partialHaarHead (polyMul [s] q))
  | [] => by
      exact (partialHaarHead_congr (RatPolyCoeffEqv.mul_zero_right _)).trans
        (partialHaarHead_congr (RatPolyCoeffEqv.mul_zero_right _)).symm
  | t :: rest => by
      change RatPolyCoeffEqv (partialHaarHead (polyMul _
        (polyAdd (homogenizeQuaternionTerm (fun _ => degree) 1 t) (homogenizeHead degree rest)))) _
      refine (partial_mul_add_right _ _ _).trans ?_
      refine ((homogenize_pair_single degree s t).add (homogenize_pair_row degree s rest)).trans ?_
      exact (partial_mul_add_right [s] [t] rest).symm

/-- Head-only homogenization preserves the whole partial pairing, not just
its value after tail integration. -/
theorem homogenizeHead_pair (degree : Nat) : ∀ p q : RatPoly,
    RatPolyCoeffEqv
      (partialHaarHead (polyMul (homogenizeHead degree p) (homogenizeHead degree q)))
      (partialHaarHead (polyMul p q))
  | [], _ => RatPolyCoeffEqv.refl _
  | t :: rest, q => by
      change RatPolyCoeffEqv (partialHaarHead (polyMul
        (polyAdd (homogenizeQuaternionTerm (fun _ => degree) 1 t) (homogenizeHead degree rest))
        (homogenizeHead degree q))) _
      rw [polyMul_add_left_exact, partial_add, polyMul_cons_left_exact, partial_add]
      exact (homogenize_pair_row degree t q).add (homogenizeHead_pair degree rest q)

theorem homogenizeHead_supported (tailBlocks degree : Nat) : ∀ p : RatPoly,
    SupportedQuaternionBlocks (tailBlocks + 1) p →
      SupportedQuaternionBlocks (tailBlocks + 1) (homogenizeHead degree p)
  | [], _ => by intro t ht; cases ht
  | t :: rest, hp => supported_add
      (homogenizeQuaternionTerm_supported (fun _ => degree) (tailBlocks + 1) t
        (hp t List.mem_cons_self) 1 (by omega))
      (homogenizeHead_supported tailBlocks degree rest
        (fun s hs => hp s (List.mem_cons_of_mem t hs)))

theorem homogenizeHead_degree (degree : Nat) (p : RatPoly)
    (hle : ∀ t, t ∈ p → quaternionBlockDegree t.1 0 ≤ degree)
    (heven : ∀ t, t ∈ p → (degree - quaternionBlockDegree t.1 0) % 2 = 0) :
    HasQuaternionBlockDegree 0 degree (homogenizeHead degree p) := by
  intro t ht
  exact homogenizeQuaternionPolynomial_degrees (fun _ => degree) 1 p
    (fun s hs block hb => by
      have hblock : block = 0 := by omega
      subst block
      exact hle s hs)
    (fun s hs block hb => by
      have hblock : block = 0 := by omega
      subst block
      exact heven s hs)
    t ht 0 (by decide)

private theorem smul_one_coeff (p : RatPoly) : RatPolyCoeffEqv (polySmul 1 p) p :=
  fun weight => Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight 1 p) (Q'.one_mul_eqv _)

private def certificate_cancel_positive (blocks : Nat) (c : Q') (hc : (0 : Q') < c)
    (p : RatPoly) (C : Certificate blocks (polySmul c p)) : Certificate blocks p := by
  let r := Q'.recipPos c hc
  have hrc : r * c ≈ 1 := Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv c hc)
  have hcancel : RatPolyCoeffEqv (polySmul r (polySmul c p)) p :=
    (RatPolyCoeffEqv.smul_assoc r c p).trans
      ((RatPolyCoeffEqv.smul_coefficient hrc p).trans (smul_one_coeff p))
  exact Certificate.ofCoeff hcancel.symm
    (.smul r (Q'.le_of_lt (Q'.recipPos_pos c hc)) C)

/-- The Gaussian certificate and the actual positive sphere radial factor
produce a Haar certificate for every head-homogeneous supported square. -/
def homogeneous_square_certificate (tailBlocks degree : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks + 1) p)
    (hd : HasQuaternionBlockDegree 0 degree p) :
    Certificate tailBlocks (partialHaarHead (polyMul p p)) := by
  have hs : HasQuaternionBlockDegree 0 (2 * degree) (polyMul p p) :=
    HasQuaternionBlockDegree.relabel (by omega) (hd.mul hd)
  exact certificate_cancel_positive tailBlocks _ (radialDenominator_positive degree) _
    (Certificate.ofCoeff (partialHaarHead_mul_radial degree (polyMul p p) hs)
      (partialGaussianHead_square_certificate tailBlocks p hp))

/-- The two total-degree parity sectors in the head block. -/
def headSector (parity : Nat) (p : RatPoly) : RatPoly :=
  p.filter (fun t => decide (quaternionBlockDegree t.1 0 % 2 = parity))

private theorem sector_mem {parity : Nat} {p : RatPoly} {t : RatTerm}
    (ht : t ∈ headSector parity p) : t ∈ p ∧ quaternionBlockDegree t.1 0 % 2 = parity := by
  obtain ⟨hmem, hparity⟩ := List.mem_filter.mp ht
  exact ⟨hmem, of_decide_eq_true hparity⟩

private theorem sector_supported (blocks parity : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (headSector parity p) :=
  fun t ht => hp t (sector_mem ht).1

private theorem sector_split : ∀ p : RatPoly,
    RatPolyCoeffEqv p (polyAdd (headSector 0 p) (headSector 1 p))
  | [] => RatPolyCoeffEqv.refl _
  | t :: rest => by
      have h := (RatPolyCoeffEqv.refl [t]).add (sector_split rest)
      by_cases h0 : quaternionBlockDegree t.1 0 % 2 = 0
      · have h1 : ¬ quaternionBlockDegree t.1 0 % 2 = 1 := by omega
        simpa [headSector, h0, h1, polyAdd] using h
      · have h1 : quaternionBlockDegree t.1 0 % 2 = 1 := by omega
        have hswap := (RatPolyCoeffEqv.add_assoc [t] (headSector 0 rest) (headSector 1 rest)).symm.trans
          (((RatPolyCoeffEqv.add_comm [t] (headSector 0 rest)).add
            (RatPolyCoeffEqv.refl (headSector 1 rest))).trans
            (RatPolyCoeffEqv.add_assoc (headSector 0 rest) [t] (headSector 1 rest)))
        simpa [headSector, h0, h1, polyAdd] using h.trans hswap

private theorem degree_mul (m l : List Nat) :
    quaternionBlockDegree (monoMul m l) 0 = quaternionBlockDegree m 0 + quaternionBlockDegree l 0 := by
  unfold quaternionBlockDegree
  simp only [exponentAt_monoMul]
  omega

private theorem sector_cross_odd (p : RatPoly) :
    HeadQuaternionOdd (polyMul (headSector 0 p) (headSector 1 p)) := by
  intro t ht
  obtain ⟨s, hs, ht'⟩ := List.mem_flatMap.mp ht
  obtain ⟨r, hr, heq⟩ := List.mem_map.mp ht'
  rw [← heq]
  change quaternionBlockDegree (monoMul s.1 r.1) 0 % 2 = 1
  rw [degree_mul]
  have hs' := (sector_mem hs).2
  have hr' := (sector_mem hr).2
  omega

/-- The two cross terms vanish coefficientwise, with the entire tail intact. -/
theorem partialHaarHead_sector_square_split (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (polyMul p p))
      (polyAdd (partialHaarHead (polyMul (headSector 0 p) (headSector 0 p)))
        (partialHaarHead (polyMul (headSector 1 p) (headSector 1 p)))) := by
  let e := headSector 0 p
  let o := headSector 1 p
  have hcross : RatPolyCoeffEqv (partialHaarHead (polyMul e o)) polyZero :=
    partialHaarHead_eq_zero_of_odd _ (sector_cross_odd p)
  have hreverse : RatPolyCoeffEqv (partialHaarHead (polyMul o e)) polyZero :=
    (partialHaarHead_congr (RatPolyCoeffEqv.mul_comm o e)).trans hcross
  refine (partialHaarHead_congr ((sector_split p).mul (sector_split p))).trans ?_
  change RatPolyCoeffEqv (partialHaarHead (polyMul (polyAdd e o) (polyAdd e o))) _
  rw [polyMul_add_left_exact, partial_add]
  refine ((partial_mul_add_right e e o).add (partial_mul_add_right o e o)).trans ?_
  exact (((RatPolyCoeffEqv.refl _).add hcross).trans (RatPolyCoeffEqv.add_zero _)).add
    ((hreverse.add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _))

private theorem degree_le_sum {t : RatTerm} : ∀ p : RatPoly,
    t ∈ p → quaternionBlockDegree t.1 0 ≤ quaternionBlockDegreeSum 0 p
  | [], ht => by cases ht
  | s :: rest, ht => by
      rcases List.mem_cons.mp ht with heq | ht
      · subst t
        simp [quaternionBlockDegreeSum]
      · have h := degree_le_sum rest ht
        change _ ≤ quaternionBlockDegree s.1 0 + quaternionBlockDegreeSum 0 rest
        omega

/-- Computed common degree for one of the two head parity sectors. -/
def sectorDegree (parity : Nat) (p : RatPoly) : Nat :=
  2 * quaternionBlockDegreeSum 0 p + parity

private theorem sector_degree_le (parity : Nat) (p : RatPoly) (t : RatTerm)
    (ht : t ∈ headSector parity p) : quaternionBlockDegree t.1 0 ≤ sectorDegree parity p := by
  have h := degree_le_sum p (sector_mem ht).1
  unfold sectorDegree
  omega

private theorem sector_degree_even_gap (parity : Nat) (_hp : parity < 2) (p : RatPoly) (t : RatTerm)
    (ht : t ∈ headSector parity p) :
    (sectorDegree parity p - quaternionBlockDegree t.1 0) % 2 = 0 := by
  have hle := sector_degree_le parity p t ht
  have hmod := (sector_mem ht).2
  unfold sectorDegree at *
  omega

/-- An explicit certificate for either retained head parity sector. -/
def sector_square_certificate (tailBlocks parity : Nat) (hparity : parity < 2) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks + 1) p) :
    Certificate tailBlocks (partialHaarHead (polyMul (headSector parity p) (headSector parity p))) := by
  let degree := sectorDegree parity p
  let q := headSector parity p
  have hq := sector_supported (tailBlocks + 1) parity p hp
  have hd : HasQuaternionBlockDegree 0 degree (homogenizeHead degree q) :=
    homogenizeHead_degree degree q (sector_degree_le parity p)
      (sector_degree_even_gap parity hparity p)
  exact Certificate.ofCoeff (homogenizeHead_pair degree q q).symm
    (homogeneous_square_certificate tailBlocks degree (homogenizeHead degree q)
      (homogenizeHead_supported tailBlocks degree q hq) hd)

/-- Integrate the ORIGINAL compact-Haar head of any supported square,
constructing the existing certificate on ALL retained tail coordinates. -/
def partialHaarHead_square_certificate (tailBlocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks + 1) p) :
    Certificate tailBlocks (partialHaarHead (polyMul p p)) :=
  Certificate.ofCoeff (partialHaarHead_sector_square_split p)
    (.add (sector_square_certificate tailBlocks 0 (by decide) p hp)
      (sector_square_certificate tailBlocks 1 (by decide) p hp))

end YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate

#print axioms YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate.partialHaarHead_mul_radius
#print axioms YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate.homogenizeHead
#print axioms YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate.homogenizeHead_pair
#print axioms YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate.homogenizeHead_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate.homogenizeHead_degree
#print axioms YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate.homogeneous_square_certificate
#print axioms YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate.headSector
#print axioms YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate.partialHaarHead_sector_square_split
#print axioms YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate.sectorDegree
#print axioms YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate.sector_square_certificate
#print axioms YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate.partialHaarHead_square_certificate
