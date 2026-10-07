/-
# Positive-link support of the actual OWN-centered torus character

The actual `tau` from `SU2TorusCenteredCovarianceRP` has syntactic `PtSup`
when its spatial plaquette lies at time 1+n ≤ M. Every variable in its
quaternion word belongs to a positive torus link block; adding the actual
OWN mean changes only its constant term. This supplies the `hsup` argument
of `SU2ClusterBridge.torus_gap_bridge`, without replacing the polynomial by
a Haar-equivalent surrogate. The companion pair-shift leaf supplies additivity.
-/

import YMGap.Continuum.SU2TorusCenteredCovarianceRP
import YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport

namespace YMGap.Continuum.SU2TorusCenteredPositiveSupport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (PolyQuaternion)
open YMGap.Continuum.RingNormaliser (varMono monoMul)
open YMGap.Continuum.SU2TorusRPCSShape (PtSup)
open YMGap.Continuum.SU2TorusRPChoosePC (Pt mem_Pt)
open YMGap.Continuum.SU2TorusRPThetaPoly (d0 getD_idxOf)
open YMGap.Continuum.SU2TorusRPCore (length_monoMul)
open YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal (exponentAt_monoMul)
open YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport (exponentAt_varMono)
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (plaqWord linkVar)
open YMGap.Continuum.SU2TorusRPGeom (plaqSide sSide plaq_pos)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2TorusRPPlaqSplit (mem_tp)
open YMGap.Continuum.SU2PlaqSupport (plaqLinks)
open YMGap.Continuum.SU2TorusRPTorusZ (plaqL_mem)
open YMGap.Continuum.SU2WilsonObsActivity (chi)
open YMGap.Continuum.SU2WilsonCenteredCovariance (centeredCharacter)
open YMGap.Continuum.SU2TorusCenteredCovarianceRP (root tau)
open YMGap.Continuum.SU2TimeShift (shv vs)

variable {M : Nat}

private theorem pt_add {p q : RatPoly} (hp : PtSup (M := M) p) (hq : PtSup (M := M) q) :
    PtSup (M := M) (polyAdd p q) := fun t ht =>
  (List.mem_append.mp ht).elim (hp t) (hq t)

private theorem pt_smul (c : Q') {p : RatPoly} (hp : PtSup (M := M) p) :
    PtSup (M := M) (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem pt_neg {p : RatPoly} (hp : PtSup (M := M) p) :
    PtSup (M := M) (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem pt_one : PtSup (M := M) polyOne := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  refine ⟨Nat.zero_le _, ?_⟩
  intro i hi
  exact False.elim (hi rfl)

private theorem pt_mul {p q : RatPoly} (hp : PtSup (M := M) p) (hq : PtSup (M := M) q) :
    PtSup (M := M) (polyMul p q) := by
  intro t ht
  simp only [polyMul, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨x, hx, y, hy, rfl⟩ := ht
  refine ⟨?_, ?_⟩
  · change (monoMul x.1 y.1).length ≤ _
    rw [length_monoMul]
    exact Nat.max_le.mpr ⟨(hp x hx).1, (hq y hy).1⟩
  · intro i hi
    change exponentAt (monoMul x.1 y.1) i ≠ 0 at hi
    rw [exponentAt_monoMul] at hi
    by_cases hxi : exponentAt x.1 i = 0
    · have hyi : exponentAt y.1 i ≠ 0 := by
        intro he
        exact hi (by rw [hxi, he])
      exact (hq y hy).2 i hyi
    · exact (hp x hx).2 i hxi

private theorem pt_var (ell : Z4Link) (hell : ell ∈ Pt M) (component : Nat) (hc : component < 4) :
    PtSup (M := M) (polyVar (4 * (torusLinks (2 * M)).idxOf ell + component)) := by
  have hmem : ell ∈ torusLinks (2 * M) := (List.mem_filter.mp hell).1
  have hidx := List.idxOf_lt_length_of_mem hmem
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  refine ⟨?_, ?_⟩
  · change (varMono (4 * (torusLinks (2 * M)).idxOf ell + component)).length ≤ _
    simp only [varMono, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  · intro i hi
    change exponentAt (varMono (4 * (torusLinks (2 * M)).idxOf ell + component)) i ≠ 0 at hi
    rw [exponentAt_varMono] at hi
    have hei : i = 4 * (torusLinks (2 * M)).idxOf ell + component := by
      by_cases he : i = 4 * (torusLinks (2 * M)).idxOf ell + component
      · exact he
      · exact False.elim (hi (if_neg he))
    rw [hei, show (4 * (torusLinks (2 * M)).idxOf ell + component) / 4 =
      (torusLinks (2 * M)).idxOf ell by omega, getD_idxOf hmem]
    exact hell

private abbrev PtQ (q : PolyQuaternion) : Prop :=
  PtSup (M := M) q.scalar ∧ PtSup (M := M) q.iPart ∧
    PtSup (M := M) q.jPart ∧ PtSup (M := M) q.kPart

private theorem pt_link (ell : Z4Link) (hell : ell ∈ Pt M) :
    PtQ (M := M) (linkVar (torusLinks (2 * M)) ell) :=
  ⟨pt_var ell hell 0 (by decide), pt_var ell hell 1 (by decide),
    pt_var ell hell 2 (by decide), pt_var ell hell 3 (by decide)⟩

private theorem pt_qmul {q r : PolyQuaternion} (hq : PtQ (M := M) q) (hr : PtQ (M := M) r) :
    PtQ (M := M) (PolyQuaternion.mul q r) := by
  obtain ⟨q0, q1, q2, q3⟩ := hq
  obtain ⟨r0, r1, r2, r3⟩ := hr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [PolyQuaternion.mul] <;>
    repeat (first | apply pt_add | apply pt_neg | apply pt_mul | assumption)

private theorem pt_qconj {q : PolyQuaternion} (hq : PtQ (M := M) q) :
    PtQ (M := M) (PolyQuaternion.conj q) :=
  ⟨hq.1, pt_neg hq.2.1, pt_neg hq.2.2.1, pt_neg hq.2.2.2⟩

/-- Syntactic positive-link support of the actual character, before centering. -/
theorem character_ptSup (hM : 1 ≤ M) (p : Z4Plaq)
    (hp : p ∈ torusPlaquettes (2 * M)) (hpos : plaqSide M p = .pos) :
    PtSup (M := M) (chi (torusLinks (2 * M)) (2 * M) p) := by
  have hbox := (mem_tp p).mp hp
  have hlinks : ∀ ell ∈ plaqLinks (2 * M) p, ell ∈ Pt M := by
    intro ell hell
    have hmem := plaqL_mem hM p hp ell hell
    exact (mem_Pt ell).mpr ⟨(mem_torusLinks _ ell.1 ell.2).mp hmem,
      plaq_pos hM p hbox hpos ell hell⟩
  have hword : PtQ (M := M) (plaqWord (torusLinks (2 * M)) (2 * M) p) :=
    pt_qmul
      (pt_qmul (pt_link _ (hlinks _ (List.mem_cons_self ..)))
        (pt_link _ (hlinks _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
      (pt_qmul
        (pt_qconj (pt_link _ (hlinks _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
        (pt_qconj (pt_link _ (hlinks _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))
  exact pt_smul 2 hword.1

/-- The actual translated, OWN-centered source has positive-link support.
The endpoint time M is allowed for spatial links. -/
theorem tau_ptSup (hM : 1 ≤ M) (K b c d : Nat) (plane : Z4Plane)
    (hb : b < 2 * M) (hc : c < 2 * M) (hd : d < 2 * M)
    (hsp : isT (dirsOf plane).1 = false) (n : Nat) (hn : n + 1 ≤ M) :
    PtSup (M := M) (tau M K b c d plane n) := by
  let p := shv (2 * M) n (root b c d plane)
  have he : p = ((1 + n, b, c, d), plane) := by
    change (((1 + n) % (2 * M), b, c, d), plane) = ((1 + n, b, c, d), plane)
    rw [Nat.mod_eq_of_lt (show 1 + n < 2 * M by omega)]
  have hp : p ∈ torusPlaquettes (2 * M) := by
    apply (mem_tp p).mpr
    rw [he]
    change 1 + n < 2 * M ∧ b < 2 * M ∧ c < 2 * M ∧ d < 2 * M
    exact ⟨by omega, hb, hc, hd⟩
  have hpos : plaqSide M p = .pos := by
    rw [he]
    cases plane <;> simp [dirsOf, isT] at hsp
    all_goals change sSide M (1 + n) = .pos
    all_goals unfold sSide
    all_goals rw [if_pos (show 1 ≤ 1 + n by omega), if_pos (show 1 + n ≤ M by omega)]
  change PtSup (M := M) (centeredCharacter (torusLinks (2 * M)) (2 * M) K
    (torusPlaquettes (2 * M)) p)
  exact pt_add (character_ptSup hM p hp hpos) (pt_smul _ pt_one)

/-- The full `hsup` input of the existing finite cluster bridge. -/
theorem hsup (hM : 1 ≤ M) (K b c d : Nat) (plane : Z4Plane)
    (hb : b < 2 * M) (hc : c < 2 * M) (hd : d < 2 * M)
    (hsp : isT (dirsOf plane).1 = false) (X : Nat) (hX : 2 * X + 1 ≤ M) :
    ∀ n, n ≤ X → PtSup (M := M) (tau M K b c d plane n) :=
  fun n hn => tau_ptSup hM K b c d plane hb hc hd hsp n (by omega)

end YMGap.Continuum.SU2TorusCenteredPositiveSupport

#print axioms YMGap.Continuum.SU2TorusCenteredPositiveSupport.character_ptSup
#print axioms YMGap.Continuum.SU2TorusCenteredPositiveSupport.tau_ptSup
#print axioms YMGap.Continuum.SU2TorusCenteredPositiveSupport.hsup
