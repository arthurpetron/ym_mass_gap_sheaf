/-
# Choice-free completion of a `CReal`-valued squared seminorm

The established GNS completion is deliberately optimized for a `Q'`-valued
pre-Hilbert form.  A limiting Osterwalder--Schrader form, however, naturally
takes values in `CReal`.  This module isolates the smaller construction that
is actually needed in that situation.

The input is a constructive squared pseudometric.  Its triangle law is the
sqrt-free estimate

  d(x,z) <= 2 d(x,y) + 2 d(y,z),

stated in the transitive eventual order on `CReal`.  Null points are quotiented
first.  Cauchy sequences and asymptotic closeness carry explicit, Type-valued
moduli; the completion is the quotient by the resulting closeness relation.
Every nonexpansive map descends, and a pointwise seminorm semigroup descends to
an honest semigroup on the completion.

`null_congr` is the one genuinely seminorm-specific input: zero-distance
replacement must preserve distance.  For a positive bilinear form it is the
usual Cauchy--Schwarz radical lemma.  Keeping it visible prevents a hidden use
of choice or an illicit conversion of a `CReal` form to a rational one.

All constructions are intuitionistic.  The only quotient principle used is
`Quot.sound`.
-/

import YMGap.Continuum.HamiltonianScalar

namespace YMGap.Continuum.CRealSeminormCompletion

open YMGap.Constructive

/-! ## 1. A `CReal`-valued squared pseudometric -/

/-- Constructive squared-pseudometric data.  `distSq` is allowed to be
degenerate; `null_congr` is the radical descent law. -/
structure SquaredSeminorm where
  Carrier : Type
  distSq : Carrier -> Carrier -> CReal
  distSq_refl : forall x, CReal.Equiv (distSq x x) CReal.czero
  distSq_symm : forall x y, CReal.Equiv (distSq x y) (distSq y x)
  distSq_nonneg : forall x y, CReal.leEv CReal.czero (distSq x y)
  distSq_triangle : forall x y z,
    CReal.leEv (distSq x z)
      (CReal.add
        (CReal.add (distSq x y) (distSq x y))
        (CReal.add (distSq y z) (distSq y z)))
  null_congr : forall {x x' y y'},
    CReal.Equiv (distSq x x') CReal.czero ->
    CReal.Equiv (distSq y y') CReal.czero ->
    CReal.Equiv (distSq x y) (distSq x' y')

namespace SquaredSeminorm

variable (D : SquaredSeminorm)

/-- Zero squared distance. -/
def Null (x y : D.Carrier) : Prop :=
  CReal.Equiv (D.distSq x y) CReal.czero

private theorem four_zero_equiv_zero :
    CReal.Equiv
      (CReal.add
        (CReal.add CReal.czero CReal.czero)
        (CReal.add CReal.czero CReal.czero))
      CReal.czero := by
  rw [show CReal.czero = CReal.ofQ' 0 from rfl]
  rw [CReal.ofQ'_add]
  exact CReal.ofQ'_equiv_of_eqv
    (show (((0 : Q') + 0) + (0 + 0)).eqv 0 by decide)

theorem null_refl (x : D.Carrier) : D.Null x x :=
  D.distSq_refl x

theorem null_symm {x y : D.Carrier} (h : D.Null x y) : D.Null y x :=
  CReal.Equiv.trans (D.distSq_symm y x) h

/-- The sqrt-free triangle estimate is sufficient for transitivity at zero. -/
theorem null_trans {x y z : D.Carrier}
    (hxy : D.Null x y) (hyz : D.Null y z) : D.Null x z := by
  have hsum : CReal.leEv
      (CReal.add
        (CReal.add (D.distSq x y) (D.distSq x y))
        (CReal.add (D.distSq y z) (D.distSq y z)))
      (CReal.add
        (CReal.add CReal.czero CReal.czero)
        (CReal.add CReal.czero CReal.czero)) :=
    CReal.leEv_add
      (CReal.leEv_add (CReal.leEv_of_equiv hxy) (CReal.leEv_of_equiv hxy))
      (CReal.leEv_add (CReal.leEv_of_equiv hyz) (CReal.leEv_of_equiv hyz))
  have hupper : CReal.leEv (D.distSq x z) CReal.czero :=
    CReal.leEv_trans (D.distSq_triangle x y z)
      (CReal.leEv_trans hsum (CReal.leEv_of_equiv four_zero_equiv_zero))
  exact CReal.equiv_of_leEv_leEv hupper (D.distSq_nonneg x z)

def nullSetoid : Setoid D.Carrier where
  r := D.Null
  iseqv :=
    ⟨D.null_refl, @D.null_symm, @D.null_trans⟩

/-- The positive-definite carrier before completion. -/
def QuotSpace : Type := Quotient D.nullSetoid

/-- The descended squared distance, valued in the genuine real quotient. -/
def qdistSq : D.QuotSpace -> D.QuotSpace -> CReal.RC :=
  Quotient.lift₂
    (fun x y => Quotient.mk CReal.crealSetoid (D.distSq x y))
    (fun _ _ _ _ hx hy => Quotient.sound (D.null_congr hx hy))

@[simp] theorem qdistSq_mk (x y : D.Carrier) :
    D.qdistSq (Quotient.mk D.nullSetoid x) (Quotient.mk D.nullSetoid y) =
      Quotient.mk CReal.crealSetoid (D.distSq x y) := rfl

/-! ## 2. Explicit-modulus Cauchy data -/

/-- A Cauchy sequence for `distSq`, with a Type-level modulus. -/
structure Cauchy where
  seq : Nat -> D.Carrier
  modulus : Q' -> Nat
  isCauchy : forall (epsilon : Q'), (0 : Q') < epsilon ->
    forall m n, modulus epsilon <= m -> modulus epsilon <= n ->
      CReal.leEv (D.distSq (seq m) (seq n)) (CReal.ofQ' epsilon)

/-- Explicit asymptotic-closeness data between two Cauchy representatives. -/
structure Close (X Y : D.Cauchy) where
  modulus : Q' -> Nat
  close : forall (epsilon : Q'), (0 : Q') < epsilon ->
    forall n, modulus epsilon <= n ->
      CReal.leEv (D.distSq (X.seq n) (Y.seq n)) (CReal.ofQ' epsilon)

/-- Propositional relation used by `Quotient`; every witness still contains a
Type-level modulus. -/
def CompletionRel (X Y : D.Cauchy) : Prop := Nonempty (D.Close X Y)

private theorem czero_le_ofQ'_of_pos {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    CReal.leEv CReal.czero (CReal.ofQ' epsilon) :=
  CReal.leEv_of_le
    (CReal.ofQ'_le_ofQ' (Q'.le_of_lt hepsilon))

def closeRefl (X : D.Cauchy) : D.Close X X where
  modulus := fun _ => 0
  close := by
    intro epsilon hepsilon n hn
    exact CReal.leEv_trans (CReal.leEv_of_equiv (D.distSq_refl (X.seq n)))
      (czero_le_ofQ'_of_pos hepsilon)

def closeSymm {X Y : D.Cauchy} (h : D.Close X Y) : D.Close Y X where
  modulus := h.modulus
  close := by
    intro epsilon hepsilon n hn
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv (CReal.Equiv.symm (D.distSq_symm (X.seq n) (Y.seq n))))
      (h.close epsilon hepsilon n hn)

private def quarterTolerance (epsilon : Q') : Q' :=
  HalfPow.half * (HalfPow.half * epsilon)

private theorem quarterTolerance_pos {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < quarterTolerance epsilon :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon hepsilon)

private theorem four_quarters_le (epsilon : Q') :
    ((quarterTolerance epsilon + quarterTolerance epsilon) +
      (quarterTolerance epsilon + quarterTolerance epsilon)) <= epsilon := by
  apply Q'.le_of_eqv
  have hpair :
      (quarterTolerance epsilon + quarterTolerance epsilon).eqv
        (HalfPow.half * epsilon) :=
    ExpNeg.two_halves (HalfPow.half * epsilon)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hpair hpair)
    (ExpNeg.two_halves epsilon)

/-- The `epsilon/4` split closes transitivity for squared-distance triangle. -/
def closeTrans {X Y Z : D.Cauchy}
    (hXY : D.Close X Y) (hYZ : D.Close Y Z) : D.Close X Z where
  modulus := fun epsilon =>
    max (hXY.modulus (quarterTolerance epsilon))
      (hYZ.modulus (quarterTolerance epsilon))
  close := by
    intro epsilon hepsilon n hn
    have hquarter : (0 : Q') < quarterTolerance epsilon :=
      quarterTolerance_pos hepsilon
    have hnXY : hXY.modulus (quarterTolerance epsilon) <= n :=
      Nat.le_trans (Nat.le_max_left _ _) hn
    have hnYZ : hYZ.modulus (quarterTolerance epsilon) <= n :=
      Nat.le_trans (Nat.le_max_right _ _) hn
    have hXYn := hXY.close (quarterTolerance epsilon) hquarter n hnXY
    have hYZn := hYZ.close (quarterTolerance epsilon) hquarter n hnYZ
    have hsum : CReal.leEv
        (CReal.add
          (CReal.add
            (D.distSq (X.seq n) (Y.seq n))
            (D.distSq (X.seq n) (Y.seq n)))
          (CReal.add
            (D.distSq (Y.seq n) (Z.seq n))
            (D.distSq (Y.seq n) (Z.seq n))))
        (CReal.add
          (CReal.add
            (CReal.ofQ' (quarterTolerance epsilon))
            (CReal.ofQ' (quarterTolerance epsilon)))
          (CReal.add
            (CReal.ofQ' (quarterTolerance epsilon))
            (CReal.ofQ' (quarterTolerance epsilon)))) :=
      CReal.leEv_add
        (CReal.leEv_add hXYn hXYn)
        (CReal.leEv_add hYZn hYZn)
    have hconstant : CReal.leEv
        (CReal.add
          (CReal.add
            (CReal.ofQ' (quarterTolerance epsilon))
            (CReal.ofQ' (quarterTolerance epsilon)))
          (CReal.add
            (CReal.ofQ' (quarterTolerance epsilon))
            (CReal.ofQ' (quarterTolerance epsilon))))
        (CReal.ofQ' epsilon) := by
      rw [CReal.ofQ'_add]
      exact CReal.leEv_of_le
        (CReal.ofQ'_le_ofQ' (four_quarters_le epsilon))
    exact CReal.leEv_trans (D.distSq_triangle (X.seq n) (Y.seq n) (Z.seq n))
      (CReal.leEv_trans hsum hconstant)

theorem completionRel_refl (X : D.Cauchy) : D.CompletionRel X X :=
  ⟨D.closeRefl X⟩

theorem completionRel_symm {X Y : D.Cauchy}
    (h : D.CompletionRel X Y) : D.CompletionRel Y X := by
  rcases h with ⟨hdata⟩
  exact ⟨D.closeSymm hdata⟩

theorem completionRel_trans {X Y Z : D.Cauchy}
    (hXY : D.CompletionRel X Y) (hYZ : D.CompletionRel Y Z) :
    D.CompletionRel X Z := by
  rcases hXY with ⟨hXYdata⟩
  rcases hYZ with ⟨hYZdata⟩
  exact ⟨D.closeTrans hXYdata hYZdata⟩

def completionSetoid : Setoid D.Cauchy where
  r := D.CompletionRel
  iseqv :=
    ⟨D.completionRel_refl, @D.completionRel_symm,
      @D.completionRel_trans⟩

/-- The choice-free Cauchy completion carrier. -/
def Completion : Type := Quotient D.completionSetoid

/-! ## 3. Dense constants and null descent -/

def constant (x : D.Carrier) : D.Cauchy where
  seq := fun _ => x
  modulus := fun _ => 0
  isCauchy := by
    intro epsilon hepsilon m n hm hn
    exact CReal.leEv_trans (CReal.leEv_of_equiv (D.distSq_refl x))
      (czero_le_ofQ'_of_pos hepsilon)

def embedRep (x : D.Carrier) : D.Completion :=
  Quotient.mk D.completionSetoid (D.constant x)

def closeConstantsOfNull {x y : D.Carrier}
    (h : D.Null x y) : D.Close (D.constant x) (D.constant y) where
  modulus := fun _ => 0
  close := by
    intro epsilon hepsilon n hn
    exact CReal.leEv_trans (CReal.leEv_of_equiv h)
      (czero_le_ofQ'_of_pos hepsilon)

theorem embedRep_eq_of_null {x y : D.Carrier} (h : D.Null x y) :
    D.embedRep x = D.embedRep y :=
  Quotient.sound ⟨D.closeConstantsOfNull h⟩

/-- The constant embedding descends through the seminorm radical. -/
def embedQuot : D.QuotSpace -> D.Completion :=
  Quotient.lift D.embedRep (fun _ _ h => D.embedRep_eq_of_null h)

/-! ## 4. Descent of nonexpansive maps -/

/-- A map nonexpansive for the `CReal` squared distance. -/
structure Nonexpansive where
  toFun : D.Carrier -> D.Carrier
  contraction : forall x y,
    CReal.leEv (D.distSq (toFun x) (toFun y)) (D.distSq x y)

namespace Nonexpansive

variable {D : SquaredSeminorm} (T : D.Nonexpansive)

theorem maps_null {x y : D.Carrier} (h : D.Null x y) :
    D.Null (T.toFun x) (T.toFun y) := by
  have hupper : CReal.leEv
      (D.distSq (T.toFun x) (T.toFun y)) CReal.czero :=
    CReal.leEv_trans (T.contraction x y) (CReal.leEv_of_equiv h)
  exact CReal.equiv_of_leEv_leEv hupper
    (D.distSq_nonneg (T.toFun x) (T.toFun y))

def mapCauchy (X : D.Cauchy) : D.Cauchy where
  seq := fun n => T.toFun (X.seq n)
  modulus := X.modulus
  isCauchy := by
    intro epsilon hepsilon m n hm hn
    exact CReal.leEv_trans (T.contraction (X.seq m) (X.seq n))
      (X.isCauchy epsilon hepsilon m n hm hn)

def mapClose {X Y : D.Cauchy} (h : D.Close X Y) :
    D.Close (T.mapCauchy X) (T.mapCauchy Y) where
  modulus := h.modulus
  close := by
    intro epsilon hepsilon n hn
    exact CReal.leEv_trans (T.contraction (X.seq n) (Y.seq n))
      (h.close epsilon hepsilon n hn)

theorem map_completionRel {X Y : D.Cauchy}
    (h : D.CompletionRel X Y) :
    D.CompletionRel (T.mapCauchy X) (T.mapCauchy Y) := by
  rcases h with ⟨hdata⟩
  exact ⟨T.mapClose hdata⟩

/-- The descended nonexpansive map on the completed carrier. -/
def completionMap : D.Completion -> D.Completion :=
  Quotient.lift
    (fun X => Quotient.mk D.completionSetoid (T.mapCauchy X))
    (fun _ _ h => Quotient.sound (T.map_completionRel h))

@[simp] theorem completionMap_mk (X : D.Cauchy) :
    T.completionMap (Quotient.mk D.completionSetoid X) =
      Quotient.mk D.completionSetoid (T.mapCauchy X) := rfl

end Nonexpansive

/-! ## 5. Explicit-modulus continuous maps descend to the completion -/

/-- A map with a Type-level input tolerance for every positive output
tolerance.  This is the general completion interface needed for rational
scaling: multiplication by a large scalar is continuous but not
nonexpansive. -/
structure ModulusContinuous where
  toFun : D.Carrier -> D.Carrier
  tolerance : Q' -> Q'
  tolerance_pos : forall epsilon, (0 : Q') < epsilon ->
    (0 : Q') < tolerance epsilon
  contraction : forall epsilon, (0 : Q') < epsilon -> forall x y,
    CReal.leEv (D.distSq x y) (CReal.ofQ' (tolerance epsilon)) ->
      CReal.leEv (D.distSq (toFun x) (toFun y)) (CReal.ofQ' epsilon)

namespace ModulusContinuous

variable {D : SquaredSeminorm} (T : D.ModulusContinuous)

def mapCauchy (X : D.Cauchy) : D.Cauchy where
  seq := fun n => T.toFun (X.seq n)
  modulus := fun epsilon => X.modulus (T.tolerance epsilon)
  isCauchy := by
    intro epsilon hepsilon m n hm hn
    exact T.contraction epsilon hepsilon (X.seq m) (X.seq n)
      (X.isCauchy (T.tolerance epsilon)
        (T.tolerance_pos epsilon hepsilon) m n hm hn)

def mapClose {X Y : D.Cauchy} (h : D.Close X Y) :
    D.Close (T.mapCauchy X) (T.mapCauchy Y) where
  modulus := fun epsilon => h.modulus (T.tolerance epsilon)
  close := by
    intro epsilon hepsilon n hn
    exact T.contraction epsilon hepsilon (X.seq n) (Y.seq n)
      (h.close (T.tolerance epsilon)
        (T.tolerance_pos epsilon hepsilon) n hn)

theorem map_completionRel {X Y : D.Cauchy}
    (h : D.CompletionRel X Y) :
    D.CompletionRel (T.mapCauchy X) (T.mapCauchy Y) := by
  rcases h with ⟨hdata⟩
  exact ⟨T.mapClose hdata⟩

def completionMap : D.Completion -> D.Completion :=
  Quotient.lift
    (fun X => Quotient.mk D.completionSetoid (T.mapCauchy X))
    (fun _ _ h => Quotient.sound (T.map_completionRel h))

@[simp] theorem completionMap_mk (X : D.Cauchy) :
    T.completionMap (Quotient.mk D.completionSetoid X) =
      Quotient.mk D.completionSetoid (T.mapCauchy X) := rfl

end ModulusContinuous

/-! ## 6. Binary quadratic-Lipschitz operations descend to the completion -/

/-- A binary operation satisfying the sqrt-free squared-distance estimate

`d(op x y, op x' y') <= 2 d(x,x') + 2 d(y,y')`.

Addition on a seminormed vector carrier has exactly this bound.  Naming the
interface here lets addition descend to the explicit-modulus completion
without adding any choice or extracting quotient representatives. -/
structure BinaryQuadraticLipschitz where
  toFun : D.Carrier -> D.Carrier -> D.Carrier
  contraction : forall x x' y y',
    CReal.leEv
      (D.distSq (toFun x y) (toFun x' y'))
      (CReal.add
        (CReal.add (D.distSq x x') (D.distSq x x'))
        (CReal.add (D.distSq y y') (D.distSq y y')))

namespace BinaryQuadraticLipschitz

variable {D : SquaredSeminorm} (T : D.BinaryQuadraticLipschitz)

private theorem four_quarter_bounds
    {x x' y y' : D.Carrier} {epsilon : Q'}
    (hx : CReal.leEv (D.distSq x x')
      (CReal.ofQ' (quarterTolerance epsilon)))
    (hy : CReal.leEv (D.distSq y y')
      (CReal.ofQ' (quarterTolerance epsilon))) :
    CReal.leEv
      (CReal.add
        (CReal.add (D.distSq x x') (D.distSq x x'))
        (CReal.add (D.distSq y y') (D.distSq y y')))
      (CReal.ofQ' epsilon) := by
  have hsum : CReal.leEv
      (CReal.add
        (CReal.add (D.distSq x x') (D.distSq x x'))
        (CReal.add (D.distSq y y') (D.distSq y y')))
      (CReal.add
        (CReal.add
          (CReal.ofQ' (quarterTolerance epsilon))
          (CReal.ofQ' (quarterTolerance epsilon)))
        (CReal.add
          (CReal.ofQ' (quarterTolerance epsilon))
          (CReal.ofQ' (quarterTolerance epsilon)))) :=
    CReal.leEv_add (CReal.leEv_add hx hx) (CReal.leEv_add hy hy)
  have hconstant : CReal.leEv
      (CReal.add
        (CReal.add
          (CReal.ofQ' (quarterTolerance epsilon))
          (CReal.ofQ' (quarterTolerance epsilon)))
        (CReal.add
          (CReal.ofQ' (quarterTolerance epsilon))
          (CReal.ofQ' (quarterTolerance epsilon))))
      (CReal.ofQ' epsilon) := by
    rw [CReal.ofQ'_add]
    exact CReal.leEv_of_le
      (CReal.ofQ'_le_ofQ' (four_quarters_le epsilon))
  exact CReal.leEv_trans hsum hconstant

/-- Pointwise application of a binary quadratic-Lipschitz operation sends two
explicit-modulus Cauchy sequences to a Cauchy sequence. -/
def mapCauchy (X Y : D.Cauchy) : D.Cauchy where
  seq := fun n => T.toFun (X.seq n) (Y.seq n)
  modulus := fun epsilon =>
    max (X.modulus (quarterTolerance epsilon))
      (Y.modulus (quarterTolerance epsilon))
  isCauchy := by
    intro epsilon hepsilon m n hm hn
    have hquarter : (0 : Q') < quarterTolerance epsilon :=
      quarterTolerance_pos hepsilon
    have hmX : X.modulus (quarterTolerance epsilon) <= m :=
      Nat.le_trans (Nat.le_max_left _ _) hm
    have hnX : X.modulus (quarterTolerance epsilon) <= n :=
      Nat.le_trans (Nat.le_max_left _ _) hn
    have hmY : Y.modulus (quarterTolerance epsilon) <= m :=
      Nat.le_trans (Nat.le_max_right _ _) hm
    have hnY : Y.modulus (quarterTolerance epsilon) <= n :=
      Nat.le_trans (Nat.le_max_right _ _) hn
    exact CReal.leEv_trans
      (T.contraction (X.seq m) (X.seq n) (Y.seq m) (Y.seq n))
      (four_quarter_bounds (D := D)
        (X.isCauchy (quarterTolerance epsilon) hquarter m n hmX hnX)
        (Y.isCauchy (quarterTolerance epsilon) hquarter m n hmY hnY))

/-- Pointwise application preserves explicit asymptotic closeness in both
arguments. -/
def mapClose {X X' Y Y' : D.Cauchy}
    (hX : D.Close X X') (hY : D.Close Y Y') :
    D.Close (T.mapCauchy X Y) (T.mapCauchy X' Y') where
  modulus := fun epsilon =>
    max (hX.modulus (quarterTolerance epsilon))
      (hY.modulus (quarterTolerance epsilon))
  close := by
    intro epsilon hepsilon n hn
    have hquarter : (0 : Q') < quarterTolerance epsilon :=
      quarterTolerance_pos hepsilon
    have hnX : hX.modulus (quarterTolerance epsilon) <= n :=
      Nat.le_trans (Nat.le_max_left _ _) hn
    have hnY : hY.modulus (quarterTolerance epsilon) <= n :=
      Nat.le_trans (Nat.le_max_right _ _) hn
    exact CReal.leEv_trans
      (T.contraction (X.seq n) (X'.seq n) (Y.seq n) (Y'.seq n))
      (four_quarter_bounds (D := D)
        (hX.close (quarterTolerance epsilon) hquarter n hnX)
        (hY.close (quarterTolerance epsilon) hquarter n hnY))

theorem map_completionRel {X X' Y Y' : D.Cauchy}
    (hX : D.CompletionRel X X') (hY : D.CompletionRel Y Y') :
    D.CompletionRel (T.mapCauchy X Y) (T.mapCauchy X' Y') := by
  rcases hX with ⟨hXdata⟩
  rcases hY with ⟨hYdata⟩
  exact ⟨T.mapClose hXdata hYdata⟩

/-- The descended binary operation on the completed carrier. -/
def completionMap : D.Completion -> D.Completion -> D.Completion :=
  Quotient.lift₂
    (fun X Y => Quotient.mk D.completionSetoid (T.mapCauchy X Y))
    (fun _ _ _ _ hX hY => Quotient.sound (T.map_completionRel hX hY))

@[simp] theorem completionMap_mk (X Y : D.Cauchy) :
    T.completionMap
        (Quotient.mk D.completionSetoid X)
        (Quotient.mk D.completionSetoid Y) =
      Quotient.mk D.completionSetoid (T.mapCauchy X Y) := rfl

end BinaryQuadraticLipschitz

/-! ## 7. A nonexpansive semigroup descends to the completion -/

/-- Pointwise semigroup laws are requested only modulo the seminorm radical;
that is exactly the equality available before completing a degenerate form. -/
structure NonexpansiveSemigroup where
  op : Nat -> D.Nonexpansive
  zero_law : forall x, D.Null ((op 0).toFun x) x
  add_law : forall m n x,
    D.Null ((op (m + n)).toFun x) ((op m).toFun ((op n).toFun x))

namespace NonexpansiveSemigroup

variable {D : SquaredSeminorm} (S : D.NonexpansiveSemigroup)

/-- Pointwise null representatives are close with the constant zero modulus. -/
def closeOfPointwiseNull {X Y : D.Cauchy}
    (h : forall n, D.Null (X.seq n) (Y.seq n)) : D.Close X Y where
  modulus := fun _ => 0
  close := by
    intro epsilon hepsilon n hn
    exact CReal.leEv_trans (CReal.leEv_of_equiv (h n))
      (czero_le_ofQ'_of_pos hepsilon)

theorem completionMap_zero (x : D.Completion) :
    (S.op 0).completionMap x = x := by
  refine Quotient.inductionOn x (fun X => ?_)
  apply Quotient.sound
  exact ⟨closeOfPointwiseNull (D := D) (fun n => S.zero_law (X.seq n))⟩

theorem completionMap_add (m n : Nat) (x : D.Completion) :
    (S.op (m + n)).completionMap x =
      (S.op m).completionMap ((S.op n).completionMap x) := by
  refine Quotient.inductionOn x (fun X => ?_)
  apply Quotient.sound
  exact ⟨closeOfPointwiseNull (D := D) (fun k => S.add_law m n (X.seq k))⟩

end NonexpansiveSemigroup

end SquaredSeminorm

/-! ## Axiom gates -/

#print axioms SquaredSeminorm.null_trans
#print axioms SquaredSeminorm.qdistSq
#print axioms SquaredSeminorm.closeTrans
#print axioms SquaredSeminorm.Completion
#print axioms SquaredSeminorm.embedQuot
#print axioms SquaredSeminorm.Nonexpansive.maps_null
#print axioms SquaredSeminorm.Nonexpansive.completionMap
#print axioms SquaredSeminorm.ModulusContinuous.mapCauchy
#print axioms SquaredSeminorm.ModulusContinuous.mapClose
#print axioms SquaredSeminorm.ModulusContinuous.completionMap
#print axioms SquaredSeminorm.BinaryQuadraticLipschitz.mapCauchy
#print axioms SquaredSeminorm.BinaryQuadraticLipschitz.mapClose
#print axioms SquaredSeminorm.BinaryQuadraticLipschitz.completionMap
#print axioms SquaredSeminorm.NonexpansiveSemigroup.completionMap_zero
#print axioms SquaredSeminorm.NonexpansiveSemigroup.completionMap_add

end YMGap.Continuum.CRealSeminormCompletion
