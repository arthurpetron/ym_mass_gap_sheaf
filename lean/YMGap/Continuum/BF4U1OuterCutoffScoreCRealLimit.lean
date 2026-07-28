/-
# Constructive-real limit of the BF4 U(1) exponent-Gram score

At fixed BF4 geometry, fixed fine nome and candidate nome in `(0,1)`, and a
fixed finite exponent-coordinate list, the literal blocked-versus-coarse U(1)
score has an executable outer-cutoff modulus.  The modulus pays both tensor
thresholds at the retained fine cutoff; this deliberately overpays the
coarse requirement because `K ≤ 4K`.

The resulting exact rational score sequence defines a Bishop `CReal`.
Convergence and uniqueness are constructive and quantitative.  No nome,
spacing, volume, or nonabelian limit is taken.
-/

import YMGap.Continuum.BF4U1OuterCutoffAtlasUniformScoreTube
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.BF4U1OuterCutoffScoreCRealLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 200000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator
open YMGap.Continuum.BF4U1ActualExponentGramScoreTube
open YMGap.Continuum.BF4U1OuterCutoffBlockGramTransport
open YMGap.Continuum.BF4U1OuterCutoffAtlasUniformScoreTube
open YMGap.Continuum.BF4U1OuterCutoffTensorTailModulus
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Executable modulus -/

/-- The exact finite-cutoff score, embedded as a constant constructive real. -/
def u1ExponentGramDistanceSeq
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g)
    (candidate : Q') (hcandidate0 : (0 : Q') < candidate)
    (coordinates : List ExponentGramCoordinate) :
    Nat → CReal :=
  fun K =>
    CReal.ofQ'
      (u1ExponentGramDistance
        G g (Q'.le_of_lt hg0)
        candidate hcandidate0 K coordinates)

/-- Type-level score modulus.  The maximum pays the fine and coarse tensor
thresholds at the same fine cutoff `K`; hence the induced coarse carrier
automatically pays the second threshold at `4K`. -/
def u1ExponentGramDistanceModulus
    (G : CutoffOneGeometry)
    (g candidate : Q') (hcandidate0 : (0 : Q') < candidate)
    (ε : Q')
    (coordinates : List ExponentGramCoordinate) : Nat :=
  atlasU1ExponentGramOuterCutoff G g
    { head := candidate
      tail := []
      head_pos := hcandidate0
      tail_pos := by
        intro item hitem
        exact absurd hitem List.not_mem_nil }
    coordinates ε

private theorem twoSided_of_abs_sub_le
    {a b ε : Q'} (h : Q'.abs (a + (-b)) ≤ ε) :
    a ≤ b + ε ∧ b ≤ a + ε := by
  constructor
  · exact YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le h
  · apply YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a))
      h

/-- Any two score stages past the executable modulus are two-sided
`ε`-close. -/
theorem u1ExponentGramDistance_twoSided_of_modulus
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'} (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    (coordinates : List ExponentGramCoordinate)
    {ε : Q'} (hε : (0 : Q') < ε)
    {K L : Nat}
    (hK :
      u1ExponentGramDistanceModulus
        G g candidate hcandidate0 ε coordinates ≤ K)
    (hL :
      u1ExponentGramDistanceModulus
        G g candidate hcandidate0 ε coordinates ≤ L) :
    u1ExponentGramDistance
          G g (Q'.le_of_lt hg0)
          candidate hcandidate0 K coordinates ≤
        u1ExponentGramDistance
            G g (Q'.le_of_lt hg0)
            candidate hcandidate0 L coordinates + ε ∧
      u1ExponentGramDistance
          G g (Q'.le_of_lt hg0)
          candidate hcandidate0 L coordinates ≤
        u1ExponentGramDistance
            G g (Q'.le_of_lt hg0)
            candidate hcandidate0 K coordinates + ε := by
  let atlas : PositiveCouplingAtlas :=
    { head := candidate
      tail := []
      head_pos := hcandidate0
      tail_pos := by
        intro item hitem
        exact absurd hitem List.not_mem_nil }
  have hmember : candidate ∈ atlas.candidates := by
    exact List.mem_cons_self
  have hatlas1 :
      ∀ item, item ∈ atlas.candidates →
        item < (1 : Q') := by
    intro item hitem
    unfold PositiveCouplingAtlas.candidates atlas at hitem
    rcases List.mem_cons.mp hitem with heq | hnil
    · subst item
      exact hcandidate1
    · exact absurd hnil List.not_mem_nil
  have habs :=
    atlasU1ExponentGramScore_uniform_cauchy_abs_le
      G hg0 hg1 atlas hatlas1 hε coordinates
      hK hL candidate hmember
  rw [
    atlasU1ExponentGramScore_of_mem
      G g (Q'.le_of_lt hg0) atlas L
      coordinates candidate hmember,
    atlasU1ExponentGramScore_of_mem
      G g (Q'.le_of_lt hg0) atlas K
      coordinates candidate hmember] at habs
  have htwo := twoSided_of_abs_sub_le habs
  exact ⟨htwo.2, htwo.1⟩

/-! ## 2. Bishop real, convergence, and uniqueness -/

/-- The fixed-geometry, fixed-nome outer-cutoff limit of the literal finite
exponent-Gram distance. -/
def u1ExponentGramDistanceLimit
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g) (hg1 : g < (1 : Q'))
    (candidate : Q') (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    (coordinates : List ExponentGramCoordinate) : CReal where
  approx K :=
    u1ExponentGramDistance
      G g (Q'.le_of_lt hg0)
      candidate hcandidate0 K coordinates
  cauchy := by
    intro ε hε
    refine
      ⟨u1ExponentGramDistanceModulus
          G g candidate hcandidate0 ε coordinates,
        fun K L hK hL => ?_⟩
    exact u1ExponentGramDistance_twoSided_of_modulus
      G hg0 hg1 hcandidate0 hcandidate1 coordinates hε hK hL

@[simp] theorem u1ExponentGramDistanceLimit_approx
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g) (hg1 : g < (1 : Q'))
    (candidate : Q') (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    (coordinates : List ExponentGramCoordinate)
    (K : Nat) :
    (u1ExponentGramDistanceLimit
      G g hg0 hg1 candidate hcandidate0 hcandidate1
      coordinates).approx K =
        u1ExponentGramDistance
          G g (Q'.le_of_lt hg0)
          candidate hcandidate0 K coordinates := rfl

theorem u1ExponentGramDistanceSeq_converges
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g) (hg1 : g < (1 : Q'))
    (candidate : Q') (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    (coordinates : List ExponentGramCoordinate) :
    CReal.ConvergesTo
      (u1ExponentGramDistanceSeq
        G g hg0 candidate hcandidate0 coordinates)
      (u1ExponentGramDistanceLimit
        G g hg0 hg1 candidate hcandidate0 hcandidate1
        coordinates) := by
  intro ε hε
  let M :=
    u1ExponentGramDistanceModulus
      G g candidate hcandidate0 ε coordinates
  refine ⟨M, fun K hK => ⟨M, fun n hn => ?_⟩⟩
  change
    u1ExponentGramDistance
          G g (Q'.le_of_lt hg0)
          candidate hcandidate0 K coordinates ≤
        u1ExponentGramDistance
            G g (Q'.le_of_lt hg0)
            candidate hcandidate0 n coordinates + ε ∧
      u1ExponentGramDistance
          G g (Q'.le_of_lt hg0)
          candidate hcandidate0 n coordinates ≤
        u1ExponentGramDistance
            G g (Q'.le_of_lt hg0)
            candidate hcandidate0 K coordinates + ε
  exact u1ExponentGramDistance_twoSided_of_modulus
    G hg0 hg1 hcandidate0 hcandidate1 coordinates hε hK hn

private theorem crealEquiv_refl (x : CReal) :
    CReal.Equiv x x :=
  fun ε hε =>
    ⟨0, fun n _ =>
      ⟨Q'.add_le_self_of_nonneg
          (x.approx n) ε (Q'.le_of_lt hε),
        Q'.add_le_self_of_nonneg
          (x.approx n) ε (Q'.le_of_lt hε)⟩⟩

theorem u1ExponentGramDistanceLimit_equiv_of_converges
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g) (hg1 : g < (1 : Q'))
    (candidate : Q') (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    (coordinates : List ExponentGramCoordinate)
    (L : CReal)
    (hL :
      CReal.ConvergesTo
        (u1ExponentGramDistanceSeq
          G g hg0 candidate hcandidate0 coordinates) L) :
    CReal.Equiv
      (u1ExponentGramDistanceLimit
        G g hg0 hg1 candidate hcandidate0 hcandidate1
        coordinates) L := by
  exact CReal.Equiv_of_limit_of_equal
    (fun K =>
      crealEquiv_refl
        (u1ExponentGramDistanceSeq
          G g hg0 candidate hcandidate0 coordinates K))
    (u1ExponentGramDistanceSeq_converges
      G g hg0 hg1 candidate hcandidate0 hcandidate1
      coordinates)
    hL

/-! ## 3. Named atlas candidate -/

/-- The atlas-labelled limit is the same physical fixed-candidate score
limit, with positivity supplied by atlas membership. -/
def atlasU1ExponentGramScoreLimit
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g) (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (candidate : Q') (hcandidate : candidate ∈ atlas.candidates)
    (hcandidate1 : candidate < (1 : Q'))
    (coordinates : List ExponentGramCoordinate) : CReal :=
  u1ExponentGramDistanceLimit
    G g hg0 hg1 candidate
    (atlas.candidate_pos hcandidate) hcandidate1 coordinates

@[simp] theorem atlasU1ExponentGramScoreLimit_approx
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g) (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (candidate : Q') (hcandidate : candidate ∈ atlas.candidates)
    (hcandidate1 : candidate < (1 : Q'))
    (coordinates : List ExponentGramCoordinate)
    (K : Nat) :
    (atlasU1ExponentGramScoreLimit
      G g hg0 hg1 atlas candidate hcandidate hcandidate1
      coordinates).approx K =
        atlasU1ExponentGramScore
          G g (Q'.le_of_lt hg0) atlas K
          coordinates candidate := by
  rw [atlasU1ExponentGramScore_of_mem
    G g (Q'.le_of_lt hg0) atlas K
    coordinates candidate hcandidate]
  rfl

#print axioms u1ExponentGramDistanceModulus
#print axioms u1ExponentGramDistance_twoSided_of_modulus
#print axioms u1ExponentGramDistanceLimit
#print axioms u1ExponentGramDistanceSeq_converges
#print axioms u1ExponentGramDistanceLimit_equiv_of_converges
#print axioms atlasU1ExponentGramScoreLimit_approx

end YMGap.Continuum.BF4U1OuterCutoffScoreCRealLimit
