/-
# Constructive mixed-degree homogenization inside a parity sector

Each monomial is multiplied by a computable number of boundary radius-square
polynomials until prescribed first- and second-boundary target degrees are
reached.  Radius insertion leaves every product-Haar pairing unchanged, while
the resulting finite polynomial is bihomogeneous and stays in the same parity
sector.
-/

import YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization

namespace YMGap.Continuum.SU2QuaternionHaarParityHomogenization

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarParitySectors
open YMGap.Continuum.SU2QuaternionHaarParityPolynomial
open YMGap.Continuum.SU2QuaternionHaarBihomogeneousPositivity
open YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def zeroParity8 : Parity8 := exponentParity8 []

private theorem parity8_eq (a b : Parity8)
    (h0 : a.p0 = b.p0) (h1 : a.p1 = b.p1)
    (h2 : a.p2 = b.p2) (h3 : a.p3 = b.p3)
    (h4 : a.p4 = b.p4) (h5 : a.p5 = b.p5)
    (h6 : a.p6 = b.p6) (h7 : a.p7 = b.p7) : a = b := by
  cases a
  cases b
  simp_all

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

private theorem monoMul_length_le_eight {a b : List Nat}
    (ha : a.length ≤ 8) (hb : b.length ≤ 8) :
    (monoMul a b).length ≤ 8 := by
  apply List.drop_eq_nil_iff.mp
  rw [monoMul_drop_of_length_le a b 8 hb]
  exact List.drop_eq_nil_of_le ha

private theorem mem_polyMul {p q : RatPoly} {u : RatTerm}
    (hu : u ∈ polyMul p q) :
    ∃ a, a ∈ p ∧ ∃ b, b ∈ q ∧
      u = (monoMul a.1 b.1, a.2 * b.2) := by
  unfold polyMul at hu
  rw [List.mem_flatMap] at hu
  obtain ⟨a, ha, hu⟩ := hu
  rw [List.mem_map] at hu
  obtain ⟨b, hb, rfl⟩ := hu
  exact ⟨a, ha, b, hb, rfl⟩

private theorem gDegree_monoMul (a b : List Nat) :
    gDegree (monoMul a b) = gDegree a + gDegree b := by
  unfold gDegree
  simp only [exponentAt_monoMul]
  omega

private theorem hDegree_monoMul (a b : List Nat) :
    hDegree (monoMul a b) = hDegree a + hDegree b := by
  unfold hDegree
  simp only [exponentAt_monoMul]
  omega

private theorem parity_monoMul_zero {a b : List Nat} {s : Parity8}
    (ha : exponentParity8 a = s) (hb : exponentParity8 b = zeroParity8) :
    exponentParity8 (monoMul a b) = s := by
  rw [← ha]
  have h0 := congrArg Parity8.p0 hb
  have h1 := congrArg Parity8.p1 hb
  have h2 := congrArg Parity8.p2 hb
  have h3 := congrArg Parity8.p3 hb
  have h4 := congrArg Parity8.p4 hb
  have h5 := congrArg Parity8.p5 hb
  have h6 := congrArg Parity8.p6 hb
  have h7 := congrArg Parity8.p7 hb
  change exponentAt b 0 % 2 = 0 at h0
  change exponentAt b 1 % 2 = 0 at h1
  change exponentAt b 2 % 2 = 0 at h2
  change exponentAt b 3 % 2 = 0 at h3
  change exponentAt b 4 % 2 = 0 at h4
  change exponentAt b 5 % 2 = 0 at h5
  change exponentAt b 6 % 2 = 0 at h6
  change exponentAt b 7 % 2 = 0 at h7
  have hp0 : (exponentAt a 0 + exponentAt b 0) % 2 = exponentAt a 0 % 2 := by omega
  have hp1 : (exponentAt a 1 + exponentAt b 1) % 2 = exponentAt a 1 % 2 := by omega
  have hp2 : (exponentAt a 2 + exponentAt b 2) % 2 = exponentAt a 2 % 2 := by omega
  have hp3 : (exponentAt a 3 + exponentAt b 3) % 2 = exponentAt a 3 % 2 := by omega
  have hp4 : (exponentAt a 4 + exponentAt b 4) % 2 = exponentAt a 4 % 2 := by omega
  have hp5 : (exponentAt a 5 + exponentAt b 5) % 2 = exponentAt a 5 % 2 := by omega
  have hp6 : (exponentAt a 6 + exponentAt b 6) % 2 = exponentAt a 6 % 2 := by omega
  have hp7 : (exponentAt a 7 + exponentAt b 7) % 2 = exponentAt a 7 % 2 := by omega
  apply parity8_eq
  · simpa only [exponentParity8, exponentAt_monoMul] using hp0
  · simpa only [exponentParity8, exponentAt_monoMul] using hp1
  · simpa only [exponentParity8, exponentAt_monoMul] using hp2
  · simpa only [exponentParity8, exponentAt_monoMul] using hp3
  · simpa only [exponentParity8, exponentAt_monoMul] using hp4
  · simpa only [exponentParity8, exponentAt_monoMul] using hp5
  · simpa only [exponentParity8, exponentAt_monoMul] using hp6
  · simpa only [exponentParity8, exponentAt_monoMul] using hp7

theorem gRadius_supported : Supported8 gRadiusPolynomial := by
  intro t ht
  simp [gRadiusPolynomial] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> decide

theorem hRadius_supported : Supported8 hRadiusPolynomial := by
  intro t ht
  simp [hRadiusPolynomial] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> decide

theorem gRadius_parity : AllParity8 zeroParity8 gRadiusPolynomial := by
  intro t ht
  simp [gRadiusPolynomial] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> decide

theorem hRadius_parity : AllParity8 zeroParity8 hRadiusPolynomial := by
  intro t ht
  simp [hRadiusPolynomial] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> decide

theorem gRadius_gDegree : AllGDegree 2 gRadiusPolynomial := by
  intro t ht
  simp [gRadiusPolynomial] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> decide

theorem gRadius_hDegree : AllHDegree 0 gRadiusPolynomial := by
  intro t ht
  simp [gRadiusPolynomial] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> decide

theorem hRadius_gDegree : AllGDegree 0 hRadiusPolynomial := by
  intro t ht
  simp [hRadiusPolynomial] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> decide

theorem hRadius_hDegree : AllHDegree 2 hRadiusPolynomial := by
  intro t ht
  simp [hRadiusPolynomial] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> decide

private theorem Supported8_mul {p q : RatPoly}
    (hp : Supported8 p) (hq : Supported8 q) : Supported8 (polyMul p q) := by
  intro u hu
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_polyMul hu
  exact monoMul_length_le_eight (hp a ha) (hq b hb)

private theorem AllParity8_mul_zero {p q : RatPoly} {s : Parity8}
    (hp : AllParity8 s p) (hq : AllParity8 zeroParity8 q) :
    AllParity8 s (polyMul p q) := by
  intro u hu
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_polyMul hu
  exact parity_monoMul_zero (hp a ha) (hq b hb)

private theorem AllGDegree_mul {p q : RatPoly} {a b : Nat}
    (hp : AllGDegree a p) (hq : AllGDegree b q) :
    AllGDegree (a + b) (polyMul p q) := by
  intro u hu
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_polyMul hu
  rw [gDegree_monoMul, hp x hx, hq y hy]

private theorem AllHDegree_mul {p q : RatPoly} {a b : Nat}
    (hp : AllHDegree a p) (hq : AllHDegree b q) :
    AllHDegree (a + b) (polyMul p q) := by
  intro u hu
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_polyMul hu
  rw [hDegree_monoMul, hp x hx, hq y hy]

private theorem radiusIter_supported (R p : RatPoly)
    (hR : Supported8 R) (hp : Supported8 p) : ∀ n,
    Supported8 (radiusIter R n p)
  | 0 => hp
  | n + 1 => Supported8_mul (radiusIter_supported R p hR hp n) hR

private theorem radiusIter_parity (R p : RatPoly) (s : Parity8)
    (hR : AllParity8 zeroParity8 R) (hp : AllParity8 s p) : ∀ n,
    AllParity8 s (radiusIter R n p)
  | 0 => hp
  | n + 1 => AllParity8_mul_zero (radiusIter_parity R p s hR hp n) hR

private theorem radiusIter_gDegree (R p : RatPoly) (a b : Nat)
    (hR : AllGDegree b R) (hp : AllGDegree a p) : ∀ n,
    AllGDegree (a + n * b) (radiusIter R n p)
  | 0 => by simpa using hp
  | n + 1 => by
      have h := AllGDegree_mul (radiusIter_gDegree R p a b hR hp n) hR
      simpa [Nat.succ_mul, Nat.add_assoc] using h

private theorem radiusIter_hDegree (R p : RatPoly) (a b : Nat)
    (hR : AllHDegree b R) (hp : AllHDegree a p) : ∀ n,
    AllHDegree (a + n * b) (radiusIter R n p)
  | 0 => by simpa using hp
  | n + 1 => by
      have h := AllHDegree_mul (radiusIter_hDegree R p a b hR hp n) hR
      simpa [Nat.succ_mul, Nat.add_assoc] using h

def gRaiseCount (D : Nat) (t : RatTerm) : Nat := (D - gDegree t.1) / 2
def hRaiseCount (D : Nat) (t : RatTerm) : Nat := (D - hDegree t.1) / 2

/-- Homogenize one monomial by explicit powers of both radius polynomials. -/
def homogenizeTerm (Dg Dh : Nat) (t : RatTerm) : RatPoly :=
  radiusIter hRadiusPolynomial (hRaiseCount Dh t)
    (radiusIter gRadiusPolynomial (gRaiseCount Dg t) [t])

/-- Homogenize each term separately and concatenate the finite expansions. -/
def homogenizeParity (Dg Dh : Nat) : RatPoly → RatPoly
  | [] => []
  | t :: p => homogenizeTerm Dg Dh t ++ homogenizeParity Dg Dh p

/-- Sum of the first-boundary degrees of all listed monomials. -/
def gDegreeSum : RatPoly → Nat
  | [] => 0
  | t :: p => gDegree t.1 + gDegreeSum p

/-- Sum of the second-boundary degrees of all listed monomials. -/
def hDegreeSum : RatPoly → Nat
  | [] => 0
  | t :: p => hDegree t.1 + hDegreeSum p

/-- A common first-boundary target degree with the parity of the head term.
The doubled tail sum makes it at least every degree in the finite list. -/
def targetGDegree : RatPoly → Nat
  | [] => 0
  | t :: p => gDegree t.1 + 2 * gDegreeSum p

/-- A common second-boundary target degree with the parity of the head term. -/
def targetHDegree : RatPoly → Nat
  | [] => 0
  | t :: p => hDegree t.1 + 2 * hDegreeSum p

private theorem singleton_supported {t : RatTerm} (ht : t.1.length ≤ 8) :
    Supported8 [t] := by
  intro u hu
  have hut : u = t := by simpa using hu
  subst u
  exact ht

private theorem singleton_parity {t : RatTerm} {s : Parity8}
    (ht : exponentParity8 t.1 = s) : AllParity8 s [t] := by
  intro u hu
  have hut : u = t := by simpa using hu
  subst u
  exact ht

private theorem singleton_gDegree (t : RatTerm) :
    AllGDegree (gDegree t.1) [t] := by
  intro u hu
  have hut : u = t := by simpa using hu
  subst u
  rfl

private theorem singleton_hDegree (t : RatTerm) :
    AllHDegree (hDegree t.1) [t] := by
  intro u hu
  have hut : u = t := by simpa using hu
  subst u
  rfl

theorem homogenizeTerm_supported {Dg Dh : Nat} {t : RatTerm}
    (ht : t.1.length ≤ 8) : Supported8 (homogenizeTerm Dg Dh t) := by
  unfold homogenizeTerm
  exact radiusIter_supported hRadiusPolynomial _ hRadius_supported
    (radiusIter_supported gRadiusPolynomial [t] gRadius_supported
      (singleton_supported ht) _ ) _

theorem homogenizeTerm_parity {Dg Dh : Nat} {t : RatTerm} {s : Parity8}
    (ht : exponentParity8 t.1 = s) : AllParity8 s (homogenizeTerm Dg Dh t) := by
  unfold homogenizeTerm
  exact radiusIter_parity hRadiusPolynomial _ s hRadius_parity
    (radiusIter_parity gRadiusPolynomial [t] s gRadius_parity
      (singleton_parity ht) _) _

theorem homogenizeTerm_gDegree {Dg Dh : Nat} {t : RatTerm}
    (hle : gDegree t.1 ≤ Dg) (heven : (Dg - gDegree t.1) % 2 = 0) :
    AllGDegree Dg (homogenizeTerm Dg Dh t) := by
  unfold homogenizeTerm
  have hg := radiusIter_gDegree gRadiusPolynomial [t]
    (gDegree t.1) 2 gRadius_gDegree (singleton_gDegree t)
    (gRaiseCount Dg t)
  have hgh := radiusIter_gDegree hRadiusPolynomial _
    (gDegree t.1 + gRaiseCount Dg t * 2) 0 hRadius_gDegree hg
    (hRaiseCount Dh t)
  have heq : gDegree t.1 + gRaiseCount Dg t * 2 = Dg := by
    unfold gRaiseCount
    omega
  simpa [heq] using hgh

theorem homogenizeTerm_hDegree {Dg Dh : Nat} {t : RatTerm}
    (hle : hDegree t.1 ≤ Dh) (heven : (Dh - hDegree t.1) % 2 = 0) :
    AllHDegree Dh (homogenizeTerm Dg Dh t) := by
  unfold homogenizeTerm
  have hg := radiusIter_hDegree gRadiusPolynomial [t]
    (hDegree t.1) 0 gRadius_hDegree (singleton_hDegree t)
    (gRaiseCount Dg t)
  have hgh := radiusIter_hDegree hRadiusPolynomial _
    (hDegree t.1 + gRaiseCount Dg t * 0) 2 hRadius_hDegree hg
    (hRaiseCount Dh t)
  have heq : hDegree t.1 + hRaiseCount Dh t * 2 = Dh := by
    unfold hRaiseCount
    omega
  simpa [heq] using hgh

private theorem Supported8_append {p q : RatPoly}
    (hp : Supported8 p) (hq : Supported8 q) : Supported8 (p ++ q) := by
  intro t ht
  simp only [List.mem_append] at ht
  rcases ht with ht | ht
  · exact hp t ht
  · exact hq t ht

private theorem AllParity8_append {s : Parity8} {p q : RatPoly}
    (hp : AllParity8 s p) (hq : AllParity8 s q) : AllParity8 s (p ++ q) := by
  intro t ht
  simp only [List.mem_append] at ht
  rcases ht with ht | ht
  · exact hp t ht
  · exact hq t ht

private theorem AllGDegree_append {d : Nat} {p q : RatPoly}
    (hp : AllGDegree d p) (hq : AllGDegree d q) : AllGDegree d (p ++ q) := by
  intro t ht
  simp only [List.mem_append] at ht
  rcases ht with ht | ht
  · exact hp t ht
  · exact hq t ht

private theorem AllHDegree_append {d : Nat} {p q : RatPoly}
    (hp : AllHDegree d p) (hq : AllHDegree d q) : AllHDegree d (p ++ q) := by
  intro t ht
  simp only [List.mem_append] at ht
  rcases ht with ht | ht
  · exact hp t ht
  · exact hq t ht

theorem homogenizeParity_supported (Dg Dh : Nat) : ∀ p : RatPoly,
    Supported8 p → Supported8 (homogenizeParity Dg Dh p)
  | [], _ => by
      intro t ht
      simp [homogenizeParity] at ht
  | a :: p, hp => by
      rw [homogenizeParity]
      apply Supported8_append
      · exact homogenizeTerm_supported (hp a (by simp))
      · exact homogenizeParity_supported Dg Dh p (by
          intro t ht
          exact hp t (by simp [ht]))

theorem homogenizeParity_parity (Dg Dh : Nat) (s : Parity8) : ∀ p : RatPoly,
    AllParity8 s p → AllParity8 s (homogenizeParity Dg Dh p)
  | [], _ => by
      intro t ht
      simp [homogenizeParity] at ht
  | a :: p, hp => by
      rw [homogenizeParity]
      apply AllParity8_append
      · exact homogenizeTerm_parity (hp a (by simp))
      · exact homogenizeParity_parity Dg Dh s p (by
          intro t ht
          exact hp t (by simp [ht]))

theorem homogenizeParity_gDegree (Dg Dh : Nat) : ∀ p : RatPoly,
    (∀ t, t ∈ p → gDegree t.1 ≤ Dg) →
    (∀ t, t ∈ p → (Dg - gDegree t.1) % 2 = 0) →
    AllGDegree Dg (homogenizeParity Dg Dh p)
  | [], _, _ => by
      intro t ht
      simp [homogenizeParity] at ht
  | a :: p, hle, heven => by
      rw [homogenizeParity]
      apply AllGDegree_append
      · exact homogenizeTerm_gDegree (hle a (by simp)) (heven a (by simp))
      · exact homogenizeParity_gDegree Dg Dh p
          (fun t ht => hle t (by simp [ht]))
          (fun t ht => heven t (by simp [ht]))

theorem homogenizeParity_hDegree (Dg Dh : Nat) : ∀ p : RatPoly,
    (∀ t, t ∈ p → hDegree t.1 ≤ Dh) →
    (∀ t, t ∈ p → (Dh - hDegree t.1) % 2 = 0) →
    AllHDegree Dh (homogenizeParity Dg Dh p)
  | [], _, _ => by
      intro t ht
      simp [homogenizeParity] at ht
  | a :: p, hle, heven => by
      rw [homogenizeParity]
      apply AllHDegree_append
      · exact homogenizeTerm_hDegree (hle a (by simp)) (heven a (by simp))
      · exact homogenizeParity_hDegree Dg Dh p
          (fun t ht => hle t (by simp [ht]))
          (fun t ht => heven t (by simp [ht]))

private theorem gDegree_le_sum {t : RatTerm} : ∀ {p : RatPoly},
    t ∈ p → gDegree t.1 ≤ gDegreeSum p
  | [], ht => by simp at ht
  | a :: p, ht => by
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · simp [gDegreeSum]
      · have h := gDegree_le_sum ht
        simp only [gDegreeSum]
        omega

private theorem hDegree_le_sum {t : RatTerm} : ∀ {p : RatPoly},
    t ∈ p → hDegree t.1 ≤ hDegreeSum p
  | [], ht => by simp at ht
  | a :: p, ht => by
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · simp [hDegreeSum]
      · have h := hDegree_le_sum ht
        simp only [hDegreeSum]
        omega

theorem gDegree_le_target {t : RatTerm} : ∀ {p : RatPoly},
    t ∈ p → gDegree t.1 ≤ targetGDegree p
  | [], ht => by simp at ht
  | a :: p, ht => by
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · simp [targetGDegree]
      · have h := gDegree_le_sum ht
        simp only [targetGDegree]
        omega

theorem hDegree_le_target {t : RatTerm} : ∀ {p : RatPoly},
    t ∈ p → hDegree t.1 ≤ targetHDegree p
  | [], ht => by simp at ht
  | a :: p, ht => by
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · simp [targetHDegree]
      · have h := hDegree_le_sum ht
        simp only [targetHDegree]
        omega

private theorem gDegree_mod_two_eq_of_parity {a b : List Nat}
    (hpar : exponentParity8 a = exponentParity8 b) :
    gDegree a % 2 = gDegree b % 2 := by
  have h0 := congrArg Parity8.p0 hpar
  have h1 := congrArg Parity8.p1 hpar
  have h2 := congrArg Parity8.p2 hpar
  have h3 := congrArg Parity8.p3 hpar
  change exponentAt a 0 % 2 = exponentAt b 0 % 2 at h0
  change exponentAt a 1 % 2 = exponentAt b 1 % 2 at h1
  change exponentAt a 2 % 2 = exponentAt b 2 % 2 at h2
  change exponentAt a 3 % 2 = exponentAt b 3 % 2 at h3
  unfold gDegree
  omega

private theorem hDegree_mod_two_eq_of_parity {a b : List Nat}
    (hpar : exponentParity8 a = exponentParity8 b) :
    hDegree a % 2 = hDegree b % 2 := by
  have h4 := congrArg Parity8.p4 hpar
  have h5 := congrArg Parity8.p5 hpar
  have h6 := congrArg Parity8.p6 hpar
  have h7 := congrArg Parity8.p7 hpar
  change exponentAt a 4 % 2 = exponentAt b 4 % 2 at h4
  change exponentAt a 5 % 2 = exponentAt b 5 % 2 at h5
  change exponentAt a 6 % 2 = exponentAt b 6 % 2 at h6
  change exponentAt a 7 % 2 = exponentAt b 7 % 2 at h7
  unfold hDegree
  omega

theorem targetGDegree_even_gap {s : Parity8} {t : RatTerm} {p : RatPoly}
    (hp : AllParity8 s p) (ht : t ∈ p) :
    (targetGDegree p - gDegree t.1) % 2 = 0 := by
  cases p with
  | nil => simp at ht
  | cons a p =>
      have ha : exponentParity8 a.1 = s := hp a (by simp)
      have htpar : exponentParity8 t.1 = s := hp t ht
      have hmod := gDegree_mod_two_eq_of_parity (ha.trans htpar.symm)
      have hle := gDegree_le_target ht
      simp only [targetGDegree]
      omega

theorem targetHDegree_even_gap {s : Parity8} {t : RatTerm} {p : RatPoly}
    (hp : AllParity8 s p) (ht : t ∈ p) :
    (targetHDegree p - hDegree t.1) % 2 = 0 := by
  cases p with
  | nil => simp at ht
  | cons a p =>
      have ha : exponentParity8 a.1 = s := hp a (by simp)
      have htpar : exponentParity8 t.1 = s := hp t ht
      have hmod := hDegree_mod_two_eq_of_parity (ha.trans htpar.symm)
      have hle := hDegree_le_target ht
      simp only [targetHDegree]
      omega

private theorem productHaar_homogenizeTerm_pair (Dg Dh : Nat)
    (a b : RatTerm) :
    productHaar (polyMul (homogenizeTerm Dg Dh a) (homogenizeTerm Dg Dh b)) ≈
      productHaar (polyMul [a] [b]) := by
  unfold homogenizeTerm
  refine Q'.eqv_trans _
    (productHaar (polyMul
      (radiusIter gRadiusPolynomial (gRaiseCount Dg a) [a])
      (radiusIter hRadiusPolynomial (hRaiseCount Dh b)
        (radiusIter gRadiusPolynomial (gRaiseCount Dg b) [b])))) _
    (productHaar_radiusIter_h_pair _ _ _) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul [a]
      (radiusIter hRadiusPolynomial (hRaiseCount Dh b)
        (radiusIter gRadiusPolynomial (gRaiseCount Dg b) [b])))) _
    (productHaar_radiusIter_g_pair _ _ _) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul
      (radiusIter hRadiusPolynomial (hRaiseCount Dh b)
        (radiusIter gRadiusPolynomial (gRaiseCount Dg b) [b])) [a])) _
    (productHaar_polyMul_comm _ _) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul
      (radiusIter gRadiusPolynomial (gRaiseCount Dg b) [b]) [a])) _
    (productHaar_radiusIter_h_pair _ _ _) ?_
  refine Q'.eqv_trans _ (productHaar (polyMul [b] [a])) _
    (productHaar_radiusIter_g_pair _ _ _) ?_
  exact productHaar_polyMul_comm [b] [a]

private theorem productHaar_polyMul_append_left (p q r : RatPoly) :
    productHaar (polyMul (p ++ q) r) ≈
      productHaar (polyMul p r) + productHaar (polyMul q r) := by
  simp only [polyMul, List.flatMap_append]
  exact productHaar_append_eqv _ _

private theorem productHaar_polyMul_append_right (p q r : RatPoly) :
    productHaar (polyMul p (q ++ r)) ≈
      productHaar (polyMul p q) + productHaar (polyMul p r) := by
  refine Q'.eqv_trans _ (productHaar (polyMul (q ++ r) p)) _
    (productHaar_polyMul_comm p (q ++ r)) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul q p) + productHaar (polyMul r p)) _
    (productHaar_polyMul_append_left q r p) ?_
  exact QPoly.q_add_congr
    (productHaar_polyMul_comm q p) (productHaar_polyMul_comm r p)

private theorem polyMul_nil_right : ∀ p : RatPoly, polyMul p [] = []
  | [] => rfl
  | _ :: p => by simp [polyMul]

private theorem productHaar_homogenizeTerm_right (Dg Dh : Nat)
    (a : RatTerm) : ∀ q : RatPoly,
    productHaar (polyMul (homogenizeTerm Dg Dh a)
      (homogenizeParity Dg Dh q)) ≈ productHaar (polyMul [a] q)
  | [] => by
      change productHaar (polyMul (homogenizeTerm Dg Dh a) []) ≈
        productHaar (polyMul [a] [])
      rw [polyMul_nil_right, polyMul_nil_right]
      exact Q'.eqv_refl 0
  | b :: q => by
      refine Q'.eqv_trans _
        (productHaar (polyMul (homogenizeTerm Dg Dh a)
            (homogenizeTerm Dg Dh b)) +
          productHaar (polyMul (homogenizeTerm Dg Dh a)
            (homogenizeParity Dg Dh q))) _
        (productHaar_polyMul_append_right _ _ _) ?_
      refine Q'.eqv_trans _
        (productHaar (polyMul [a] [b]) + productHaar (polyMul [a] q)) _
        (QPoly.q_add_congr
          (productHaar_homogenizeTerm_pair Dg Dh a b)
          (productHaar_homogenizeTerm_right Dg Dh a q)) ?_
      exact Q'.eqv_symm (productHaar_polyMul_append_right [a] [b] q)

private theorem productHaar_homogenizeParity_pair (Dg Dh : Nat) :
    ∀ p q : RatPoly,
    productHaar (polyMul (homogenizeParity Dg Dh p)
      (homogenizeParity Dg Dh q)) ≈ productHaar (polyMul p q)
  | [], q => by
      simp [homogenizeParity, polyMul]
      exact Q'.eqv_refl 0
  | a :: p, q => by
      refine Q'.eqv_trans _
        (productHaar (polyMul (homogenizeTerm Dg Dh a)
            (homogenizeParity Dg Dh q)) +
          productHaar (polyMul (homogenizeParity Dg Dh p)
            (homogenizeParity Dg Dh q))) _
        (productHaar_polyMul_append_left _ _ _) ?_
      refine Q'.eqv_trans _
        (productHaar (polyMul [a] q) + productHaar (polyMul p q)) _
        (QPoly.q_add_congr
          (productHaar_homogenizeTerm_right Dg Dh a q)
          (productHaar_homogenizeParity_pair Dg Dh p q)) ?_
      exact Q'.eqv_symm (productHaar_polyMul_append_left [a] p q)

/-- The mixed-degree homogenization preserves the full product-Haar square. -/
theorem productHaar_homogenizeParity_square (Dg Dh : Nat) (p : RatPoly) :
    productHaar (polyMul (homogenizeParity Dg Dh p)
      (homogenizeParity Dg Dh p)) ≈ productHaar (polyMul p p) :=
  productHaar_homogenizeParity_pair Dg Dh p p

/-- Exact positivity for an arbitrary finite polynomial contained in one of
the 256 coordinate-parity sectors.  No common-degree assumption remains: the
target degrees and all radius insertions are computed from the input list. -/
theorem productHaar_square_nonneg_of_parity
    (s : Parity8) (p : RatPoly)
    (hp8 : Supported8 p) (hpp : AllParity8 s p) :
    (0 : Q') ≤ productHaar (polyMul p p) := by
  let Dg := targetGDegree p
  let Dh := targetHDegree p
  let q := homogenizeParity Dg Dh p
  have hq8 : Supported8 q := homogenizeParity_supported Dg Dh p hp8
  have hqp : AllParity8 s q := homogenizeParity_parity Dg Dh s p hpp
  have hqg : AllGDegree Dg q := homogenizeParity_gDegree Dg Dh p
    (fun t ht => gDegree_le_target ht)
    (fun t ht => targetGDegree_even_gap hpp ht)
  have hqh : AllHDegree Dh q := homogenizeParity_hDegree Dg Dh p
    (fun t ht => hDegree_le_target ht)
    (fun t ht => targetHDegree_even_gap hpp ht)
  have hq_nonneg := productHaar_square_nonneg_of_bihomogeneous_parity
    s Dg Dh q hq8 hqp hqg hqh
  exact Q'.le_trans' _ _ _ hq_nonneg
    (Q'.le_of_eqv (productHaar_homogenizeParity_square Dg Dh p))

end YMGap.Continuum.SU2QuaternionHaarParityHomogenization

#print axioms YMGap.Continuum.SU2QuaternionHaarParityHomogenization.homogenizeTerm_gDegree
#print axioms YMGap.Continuum.SU2QuaternionHaarParityHomogenization.homogenizeTerm_hDegree
#print axioms YMGap.Continuum.SU2QuaternionHaarParityHomogenization.productHaar_homogenizeParity_square
#print axioms YMGap.Continuum.SU2QuaternionHaarParityHomogenization.productHaar_square_nonneg_of_parity
