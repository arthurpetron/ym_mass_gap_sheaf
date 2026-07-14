/-
# Product-Haar positivity on bihomogeneous parity blocks

Within a fixed eight-coordinate parity sector and fixed degree on each
quaternion boundary, every monomial pair has the same positive radial
denominator.  The exact sphere-to-Gaussian identity therefore transfers the
arbitrary eight-variable product-Gaussian square theorem to product Haar.
-/

import YMGap.Continuum.SU2QuaternionProductGaussianPositivity
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.SU2QuaternionHaarBihomogeneousPositivity

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarParitySectors
open YMGap.Continuum.SU2QuaternionHaarParityPolynomial
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionProductGaussianTensor
open YMGap.Continuum.SU2QuaternionProductGaussianPositivity

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

def gDegree (m : List Nat) : Nat :=
  exponentAt m 0 + exponentAt m 1 + exponentAt m 2 + exponentAt m 3

def hDegree (m : List Nat) : Nat :=
  exponentAt m 4 + exponentAt m 5 + exponentAt m 6 + exponentAt m 7

def Supported8 (p : RatPoly) : Prop :=
  ∀ t, t ∈ p → t.1.length ≤ 8

def AllGDegree (d : Nat) (p : RatPoly) : Prop :=
  ∀ t, t ∈ p → gDegree t.1 = d

def AllHDegree (d : Nat) (p : RatPoly) : Prop :=
  ∀ t, t ∈ p → hDegree t.1 = d

private theorem exponentAt_monoMul (a b : List Nat) (i : Nat) :
    exponentAt (monoMul a b) i = exponentAt a i + exponentAt b i := by
  induction a generalizing b i with
  | nil => simp [monoMul, exponentAt]
  | cons x xs ih =>
      cases b with
      | nil => simp [monoMul, exponentAt]
      | cons y ys =>
          cases i with
          | zero => simp [monoMul, exponentAt]
          | succ i =>
              change exponentAt (monoMul xs ys) i =
                exponentAt xs i + exponentAt ys i
              exact ih ys i

private theorem monoMul_drop_of_length_le (a b : List Nat) (n : Nat)
    (h : b.length ≤ n) :
    (monoMul a b).drop n = a.drop n := by
  induction n generalizing a b with
  | zero =>
      cases b with
      | nil => cases a <;> rfl
      | cons y ys => simp at h
  | succ n ih =>
      cases a with
      | nil =>
          simp only [monoMul]
          exact List.drop_eq_nil_of_le h
      | cons x xs =>
          cases b with
          | nil => simp [monoMul]
          | cons y ys =>
              simp only [List.length_cons] at h
              simp [monoMul, ih xs ys (by omega)]

private theorem monoMul_tail8_zero {a b : List Nat}
    (ha : a.length ≤ 8) (hb : b.length ≤ 8) :
    allZero ((monoMul a b).drop 8) = true := by
  rw [monoMul_drop_of_length_le a b 8 hb, List.drop_eq_nil_of_le ha]
  rfl

private theorem gHalfDegree_monoMul_eq {a b : List Nat} {d : Nat}
    (hpar : exponentParity8 a = exponentParity8 b)
    (ha : gDegree a = d) (hb : gDegree b = d) :
    gHalfDegree (monoMul a b) = d := by
  have h0 := congrArg Parity8.p0 hpar
  have h1 := congrArg Parity8.p1 hpar
  have h2 := congrArg Parity8.p2 hpar
  have h3 := congrArg Parity8.p3 hpar
  change exponentAt a 0 % 2 = exponentAt b 0 % 2 at h0
  change exponentAt a 1 % 2 = exponentAt b 1 % 2 at h1
  change exponentAt a 2 % 2 = exponentAt b 2 % 2 at h2
  change exponentAt a 3 % 2 = exponentAt b 3 % 2 at h3
  unfold gHalfDegree halfDegree4
  simp only [exponentAt_monoMul]
  unfold gDegree at ha hb
  omega

private theorem hHalfDegree_monoMul_eq {a b : List Nat} {d : Nat}
    (hpar : exponentParity8 a = exponentParity8 b)
    (ha : hDegree a = d) (hb : hDegree b = d) :
    hHalfDegree (monoMul a b) = d := by
  have h4 := congrArg Parity8.p4 hpar
  have h5 := congrArg Parity8.p5 hpar
  have h6 := congrArg Parity8.p6 hpar
  have h7 := congrArg Parity8.p7 hpar
  change exponentAt a 4 % 2 = exponentAt b 4 % 2 at h4
  change exponentAt a 5 % 2 = exponentAt b 5 % 2 at h5
  change exponentAt a 6 % 2 = exponentAt b 6 % 2 at h6
  change exponentAt a 7 % 2 = exponentAt b 7 % 2 at h7
  unfold hHalfDegree halfDegree4
  simp only [exponentAt_monoMul]
  unfold hDegree at ha hb
  omega

/-- The common positive radial factor of a bidegree block. -/
def radialFactor (dg dh : Nat) : Q' :=
  Q'.ofNat (sphereFourDenominator dg) *
    Q'.ofNat (sphereFourDenominator dh)

private theorem ofNat_pos_of_pos {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

theorem radialFactor_pos (dg dh : Nat) :
    (0 : Q') < radialFactor dg dh :=
  Q'.mul_pos
    (ofNat_pos_of_pos (sphereFourDenominator_pos dg))
    (ofNat_pos_of_pos (sphereFourDenominator_pos dh))

private theorem monomialPair_mul_radial {a b : RatTerm} {s : Parity8}
    {dg dh : Nat}
    (ha8 : a.1.length ≤ 8) (hb8 : b.1.length ≤ 8)
    (hpa : exponentParity8 a.1 = s) (hpb : exponentParity8 b.1 = s)
    (hga : gDegree a.1 = dg) (hgb : gDegree b.1 = dg)
    (hha : hDegree a.1 = dh) (hhb : hDegree b.1 = dh) :
    ((a.2 * b.2) * productHaarMono (monoMul a.1 b.1)) *
        radialFactor dg dh ≈
      (a.2 * b.2) * productGaussianMono (monoMul a.1 b.1) := by
  have hpar : exponentParity8 a.1 = exponentParity8 b.1 := hpa.trans hpb.symm
  have hg := gHalfDegree_monoMul_eq hpar hga hgb
  have hh := hHalfDegree_monoMul_eq hpar hha hhb
  have htail := monoMul_tail8_zero ha8 hb8
  have hrad := productHaarMono_mul_radialDenominators
    (monoMul a.1 b.1) htail
  rw [hg, hh] at hrad
  unfold radialFactor
  refine Q'.eqv_trans _
    ((a.2 * b.2) *
      (productHaarMono (monoMul a.1 b.1) *
        (Q'.ofNat (sphereFourDenominator dg) *
          Q'.ofNat (sphereFourDenominator dh)))) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  exact Q'.mul_eqv_congr_left _ _ _ hrad

/-- Raw product-Haar row and bilinear folds, parallel to the product-Gaussian
folds used by the eight-variable theorem. -/
def haarRow (a : RatTerm) : RatPoly → Q'
  | [] => 0
  | b :: q =>
      (a.2 * b.2) * productHaarMono (monoMul a.1 b.1) + haarRow a q

def haarBilinear : RatPoly → RatPoly → Q'
  | [], _ => 0
  | a :: p, q => haarRow a q + haarBilinear p q

private theorem productHaarLinearSum_append : ∀ p q : RatPoly,
    productHaarLinearSum (p ++ q) ≈
      productHaarLinearSum p + productHaarLinearSum q
  | [], q => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | t :: p, q => by
      change t.2 * productHaarMono t.1 + productHaarLinearSum (p ++ q) ≈
        (t.2 * productHaarMono t.1 + productHaarLinearSum p) +
          productHaarLinearSum q
      refine Q'.eqv_trans _
        (t.2 * productHaarMono t.1 +
          (productHaarLinearSum p + productHaarLinearSum q)) _
        (Q'.add_eqv_congr_left _ _ _ (productHaarLinearSum_append p q)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem productHaarLinearSum_map_row (a : RatTerm) : ∀ q : RatPoly,
    productHaarLinearSum
      (q.map fun b => (monoMul a.1 b.1, a.2 * b.2)) ≈ haarRow a q
  | [] => Q'.eqv_refl 0
  | b :: q => by
      change (a.2 * b.2) * productHaarMono (monoMul a.1 b.1) +
          productHaarLinearSum
            (q.map fun c => (monoMul a.1 c.1, a.2 * c.2)) ≈
        (a.2 * b.2) * productHaarMono (monoMul a.1 b.1) + haarRow a q
      exact Q'.add_eqv_congr_left _ _ _ (productHaarLinearSum_map_row a q)

private theorem productHaarLinearSum_polyMul : ∀ p q : RatPoly,
    productHaarLinearSum (polyMul p q) ≈ haarBilinear p q
  | [], _ => Q'.eqv_refl 0
  | a :: p, q => by
      unfold polyMul List.flatMap
      refine Q'.eqv_trans _
        (productHaarLinearSum
            (q.map fun b => (monoMul a.1 b.1, a.2 * b.2)) +
          productHaarLinearSum (polyMul p q)) _
        (productHaarLinearSum_append _ _) ?_
      exact QPoly.q_add_congr
        (productHaarLinearSum_map_row a q)
        (productHaarLinearSum_polyMul p q)

theorem productHaar_polyMul_eq_bilinear (p q : RatPoly) :
    productHaar (polyMul p q) ≈ haarBilinear p q :=
  Q'.eqv_trans _ _ _ (productHaar_eqv_linearSum _)
    (productHaarLinearSum_polyMul p q)

private theorem haarRow_mul_radial
    (s : Parity8) (dg dh : Nat) (a : RatTerm)
    (ha8 : a.1.length ≤ 8) (hpa : exponentParity8 a.1 = s)
    (hga : gDegree a.1 = dg) (hha : hDegree a.1 = dh) :
    ∀ (q : RatPoly), Supported8 q → AllParity8 s q →
      AllGDegree dg q → AllHDegree dh q →
      haarRow a q * radialFactor dg dh ≈ gaussianRow a q
  | [], _, _, _, _ => QPoly.q_zero_mul _
  | b :: q, hq8, hpq, hgq, hhq => by
      have hb8 := hq8 b (by simp)
      have hpb := hpq b (by simp)
      have hgb := hgq b (by simp)
      have hhb := hhq b (by simp)
      refine Q'.eqv_trans _
        (((a.2 * b.2) * productHaarMono (monoMul a.1 b.1)) *
            radialFactor dg dh +
          haarRow a q * radialFactor dg dh) _
        (Q'.add_mul_eqv _ _ _) ?_
      exact QPoly.q_add_congr
        (monomialPair_mul_radial ha8 hb8 hpa hpb hga hgb hha hhb)
        (haarRow_mul_radial s dg dh a ha8 hpa hga hha q
          (fun t ht => hq8 t (by simp [ht]))
          (fun t ht => hpq t (by simp [ht]))
          (fun t ht => hgq t (by simp [ht]))
          (fun t ht => hhq t (by simp [ht])))

private theorem haarBilinear_mul_radial
    (s : Parity8) (dg dh : Nat) : ∀ p : RatPoly,
    Supported8 p → AllParity8 s p → AllGDegree dg p → AllHDegree dh p →
    haarBilinear p p * radialFactor dg dh ≈ gaussianBilinear p p
  | [], _, _, _, _ => QPoly.q_zero_mul _
  | a :: p, hp8, hpp, hpg, hph => by
      have ha8 := hp8 a (by simp)
      have hpa := hpp a (by simp)
      have hga := hpg a (by simp)
      have hha := hph a (by simp)
      refine Q'.eqv_trans _
        (haarRow a (a :: p) * radialFactor dg dh +
          haarBilinear p (a :: p) * radialFactor dg dh) _
        (Q'.add_mul_eqv _ _ _) ?_
      refine QPoly.q_add_congr
        (haarRow_mul_radial s dg dh a ha8 hpa hga hha (a :: p)
          hp8 hpp hpg hph) ?_
      -- The remaining left terms still pair with the full right block.
      -- Prove this rectangular tail directly by induction on the left list.
      let rec rectangular : ∀ r : RatPoly,
          Supported8 r → AllParity8 s r → AllGDegree dg r → AllHDegree dh r →
          haarBilinear r (a :: p) * radialFactor dg dh ≈
            gaussianBilinear r (a :: p) := by
        intro r hr8 hrp hrg hrh
        induction r with
        | nil => exact QPoly.q_zero_mul _
        | cons c r ih =>
            have hc8 := hr8 c (by simp)
            have hcp := hrp c (by simp)
            have hcg := hrg c (by simp)
            have hch := hrh c (by simp)
            refine Q'.eqv_trans _
              (haarRow c (a :: p) * radialFactor dg dh +
                haarBilinear r (a :: p) * radialFactor dg dh) _
              (Q'.add_mul_eqv _ _ _) ?_
            exact QPoly.q_add_congr
              (haarRow_mul_radial s dg dh c hc8 hcp hcg hch (a :: p)
                hp8 hpp hpg hph)
              (ih
                (fun t ht => hr8 t (by simp [ht]))
                (fun t ht => hrp t (by simp [ht]))
                (fun t ht => hrg t (by simp [ht]))
                (fun t ht => hrh t (by simp [ht])))
      exact rectangular p
        (fun t ht => hp8 t (by simp [ht]))
        (fun t ht => hpp t (by simp [ht]))
        (fun t ht => hpg t (by simp [ht]))
        (fun t ht => hph t (by simp [ht]))

/-- Exact constant-radial-factor transfer on a bihomogeneous parity block. -/
theorem productHaar_square_mul_radial_eq_productGaussian
    (s : Parity8) (dg dh : Nat) (p : RatPoly)
    (hp8 : Supported8 p) (hpp : AllParity8 s p)
    (hpg : AllGDegree dg p) (hph : AllHDegree dh p) :
    productHaar (polyMul p p) * radialFactor dg dh ≈
      productGaussian (polyMul p p) := by
  refine Q'.eqv_trans _ (haarBilinear p p * radialFactor dg dh) _
    (Q'.mul_eqv_congr_right _ _ _ (productHaar_polyMul_eq_bilinear p p)) ?_
  refine Q'.eqv_trans _ (gaussianBilinear p p) _
    (haarBilinear_mul_radial s dg dh p hp8 hpp hpg hph) ?_
  exact Q'.eqv_symm (productGaussian_polyMul p p)

/-- **Product-Haar positivity for every fixed bidegree/parity block.** -/
theorem productHaar_square_nonneg_of_bihomogeneous_parity
    (s : Parity8) (dg dh : Nat) (p : RatPoly)
    (hp8 : Supported8 p) (hpp : AllParity8 s p)
    (hpg : AllGDegree dg p) (hph : AllHDegree dh p) :
    (0 : Q') ≤ productHaar (polyMul p p) := by
  have hG := productGaussian_square_nonneg p
  have heq := productHaar_square_mul_radial_eq_productGaussian
    s dg dh p hp8 hpp hpg hph
  have hscaled : (0 : Q') ≤ productHaar (polyMul p p) * radialFactor dg dh :=
    Q'.le_trans' _ _ _ hG (Q'.le_of_eqv (Q'.eqv_symm heq))
  have hleft : (0 : Q') ≤ radialFactor dg dh * productHaar (polyMul p p) :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.eqv_symm
        (Q'.mul_comm_eqv (radialFactor dg dh) (productHaar (polyMul p p)))))
  exact Q'.nonneg_of_mul_pos (radialFactor_pos dg dh) hleft

end YMGap.Continuum.SU2QuaternionHaarBihomogeneousPositivity

#print axioms YMGap.Continuum.SU2QuaternionHaarBihomogeneousPositivity.productHaar_square_mul_radial_eq_productGaussian
#print axioms YMGap.Continuum.SU2QuaternionHaarBihomogeneousPositivity.productHaar_square_nonneg_of_bihomogeneous_parity
