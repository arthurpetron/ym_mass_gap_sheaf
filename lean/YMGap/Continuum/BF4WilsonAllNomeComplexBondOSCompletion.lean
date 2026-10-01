/-
# Complex completion of the ORIGINAL physical bond sources

Two existing real physical bond completions give the complex carrier. Its
Hermitian form consists of four ORIGINAL odd-window bond pairings. The
computed two-way isometry to the witnessed complex time-sector quotient
identifies the full represented carrier, not merely its finite sources.

Paired source rows supply density and Cauchy limits with explicit moduli.
No representative is selected from a quotient, and no new analytic premise
is assumed. This is fixed-nome/fixed-width bond reconstruction, not the
canonical continuum half-space OS root, physical calibration or full QFT.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
import YMGap.Continuum.BF4WilsonAllNomeComplexTimeSector

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.BF4WilsonAllNomeComplexification
  (ComplexValue valueConj)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion rowSetoid toSectorRep fromSectorRep fromSectorRep_limit
    bondCompletedInner bondCompletedDistance constantRows constantRows_limit
    constant_pairing constant_distance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_inner bondValue_distance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_ofState)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization
  (bondForm image denseExpression denseExpression_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

attribute [local irreducible] toSectorRep denseExpression

abbrev ComplexBondCompletion :=
  BondCompletion hw0 hw1 (width := width) × BondCompletion hw0 hw1 (width := width)

/-- Both physical Cauchy moduli remain Type-level input data. -/
abbrev Rows := BF4WilsonAllNomeBondOSCompletion.Rows hw0 hw1 (width := width) ×
  BF4WilsonAllNomeBondOSCompletion.Rows hw0 hw1 (width := width)

abbrev Source (width : Nat) := IntrinsicExpression width × IntrinsicExpression width

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "S" => BF4WilsonAllNomeComplexTimeSector.State hw0 hw1 (width := width)
local notation "VC" => BF4WilsonAllNomeComplexification.ComplexCarrier hw0 hw1 width
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

def value (x : H) : VC := (bondValue hw0 hw1 x.1,bondValue hw0 hw1 x.2)

theorem value_injective {x y : H} (h : value hw0 hw1 x = value hw0 hw1 y) : x = y := by
  apply Prod.ext
  · exact bondValue_injective hw0 hw1 (congrArg Prod.fst h)
  · exact bondValue_injective hw0 hw1 (congrArg Prod.snd h)

def ofState (x : S) : H :=
  (BF4WilsonAllNomeBondOSLinear.ofState hw0 hw1 x.1,
   BF4WilsonAllNomeBondOSLinear.ofState hw0 hw1 x.2)

theorem value_ofState (x : S) :
    value hw0 hw1 (ofState hw0 hw1 x) = BF4WilsonAllNomeComplexTimeSector.val hw0 hw1 x := by
  apply Prod.ext <;> exact bondValue_ofState hw0 hw1 _

def rowState (X : Rows hw0 hw1 (width := width)) : S :=
  (toSectorRep hw0 hw1 X.1,toSectorRep hw0 hw1 X.2)

def ofRows (X : Rows hw0 hw1 (width := width)) : H :=
  (Quotient.mk (rowSetoid hw0 hw1) X.1,Quotient.mk (rowSetoid hw0 hw1) X.2)

theorem value_ofRows (X : Rows hw0 hw1 (width := width)) :
    value hw0 hw1 (ofRows hw0 hw1 X) =
      BF4WilsonAllNomeComplexTimeSector.val hw0 hw1 (rowState hw0 hw1 X) := rfl

/-- Sample only each supplied state's actual original range witness. -/
def rowsOfState (x : S) : Rows hw0 hw1 (width := width) :=
  (fromSectorRep hw0 hw1 x.1,fromSectorRep hw0 hw1 x.2)

theorem ofRows_rowsOfState (x : S) :
    ofRows hw0 hw1 (rowsOfState hw0 hw1 x) = ofState hw0 hw1 x := by
  apply value_injective hw0 hw1
  rw [value_ofRows,value_ofState]
  apply Prod.ext <;> exact fromSectorRep_limit hw0 hw1 _

def SectorQuotient := Quotient
  (BF4WilsonAllNomeComplexTimeSector.stateSetoid hw0 hw1 (width := width))

def sectorValue : SectorQuotient hw0 hw1 (width := width) → VC :=
  Quotient.lift (BF4WilsonAllNomeComplexTimeSector.val hw0 hw1) (fun _ _ h => h)

theorem sectorValue_injective {x y : SectorQuotient hw0 hw1 (width := width)}
    (h : sectorValue hw0 hw1 x = sectorValue hw0 hw1 y) : x = y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro X Y h
  exact Quotient.sound h

/-- A paired quotient lift, not representative selection in either factor. -/
def toSector (x : H) : SectorQuotient hw0 hw1 (width := width) :=
  Quotient.lift₂
    (fun X Y => Quotient.mk (BF4WilsonAllNomeComplexTimeSector.stateSetoid hw0 hw1)
      (rowState hw0 hw1 (X,Y)))
    (fun _ _ _ _ h k => Quotient.sound (Prod.ext
      ((BF4WilsonAllNomeBondOSCompletion.close_iff_limit_eq hw0 hw1 _ _).mp h)
      ((BF4WilsonAllNomeBondOSCompletion.close_iff_limit_eq hw0 hw1 _ _).mp k))) x.1 x.2

def fromSector : SectorQuotient hw0 hw1 (width := width) → H :=
  Quotient.lift (ofState hw0 hw1) (fun x y h => by
    apply value_injective hw0 hw1
    rw [value_ofState,value_ofState]
    exact h)

theorem toSector_value (x : H) :
    sectorValue hw0 hw1 (toSector hw0 hw1 x) = value hw0 hw1 x := by
  rcases x with ⟨x,y⟩
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  rfl

theorem fromSector_value (x : SectorQuotient hw0 hw1 (width := width)) :
    value hw0 hw1 (fromSector hw0 hw1 x) = sectorValue hw0 hw1 x := by
  refine Quotient.inductionOn x ?_
  exact fun X => value_ofState hw0 hw1 X

theorem toSector_fromSector (x : SectorQuotient hw0 hw1 (width := width)) :
    toSector hw0 hw1 (fromSector hw0 hw1 x) = x := by
  apply sectorValue_injective hw0 hw1
  rw [toSector_value,fromSector_value]

theorem fromSector_toSector (x : H) :
    fromSector hw0 hw1 (toSector hw0 hw1 x) = x := by
  apply value_injective hw0 hw1
  rw [fromSector_value,toSector_value]

/-- The four original real physical pairings define the Hermitian form. -/
def inner (x y : H) : ComplexValue :=
  (RCadd (bondCompletedInner hw0 hw1 x.1 y.1) (bondCompletedInner hw0 hw1 x.2 y.2),
   RCsub (bondCompletedInner hw0 hw1 x.1 y.2) (bondCompletedInner hw0 hw1 x.2 y.1))

theorem inner_value (x y : H) : inner hw0 hw1 x y =
    BF4WilsonAllNomeComplexification.inner hw0 hw1 width (value hw0 hw1 x) (value hw0 hw1 y) := by
  simp only [inner,BF4WilsonAllNomeComplexification.inner,value,bondValue_inner]

def distance (x y : H) : RC :=
  RCadd (bondCompletedDistance hw0 hw1 x.1 y.1) (bondCompletedDistance hw0 hw1 x.2 y.2)

theorem distance_value (x y : H) : distance hw0 hw1 x y =
    RCadd (completedDist hw0 hw1 (value hw0 hw1 x).1 (value hw0 hw1 y).1)
      (completedDist hw0 hw1 (value hw0 hw1 x).2 (value hw0 hw1 y).2) := by
  simp only [distance,value,bondValue_distance]

def sectorDistance : SectorQuotient hw0 hw1 (width := width) →
    SectorQuotient hw0 hw1 (width := width) → RC :=
  fun x y => RCadd
    (completedDist hw0 hw1 (sectorValue hw0 hw1 x).1 (sectorValue hw0 hw1 y).1)
    (completedDist hw0 hw1 (sectorValue hw0 hw1 x).2 (sectorValue hw0 hw1 y).2)

theorem toSector_isometry (x y : H) :
    sectorDistance hw0 hw1 (toSector hw0 hw1 x) (toSector hw0 hw1 y) = distance hw0 hw1 x y := by
  rw [sectorDistance,toSector_value,toSector_value,distance_value]

def zero : H := (BF4WilsonAllNomeBondOSLinear.zero hw0 hw1,
  BF4WilsonAllNomeBondOSLinear.zero hw0 hw1)

theorem value_zero : value hw0 hw1 (zero hw0 hw1 (width := width)) =
    BF4WilsonAllNomeComplexification.complexZero hw0 hw1 width := by
  apply Prod.ext <;> exact BF4WilsonAllNomeBondOSLinear.bondValue_zero hw0 hw1

theorem inner_conj_symm (x y : H) : inner hw0 hw1 x y = valueConj (inner hw0 hw1 y x) := by
  rw [inner_value,inner_value]
  exact BF4WilsonAllNomeComplexification.inner_conj_symm hw0 hw1 width _ _

theorem inner_nonnegative (x : H) : RCnonneg (inner hw0 hw1 x x).1 := by
  rw [inner_value]
  exact BF4WilsonAllNomeComplexification.inner_nonnegative hw0 hw1 width _

theorem inner_posdef (x : H) :
    (inner hw0 hw1 x x).1 = RCzero ↔ x = zero hw0 hw1 := by
  rw [inner_value,BF4WilsonAllNomeComplexification.inner_posdef,← value_zero]
  exact ⟨value_injective hw0 hw1,congrArg (value hw0 hw1)⟩

/-- These are the four ORIGINAL normalized reflected source limits. -/
def sourceForm (x y : Source width) : ComplexValue :=
  (RCadd (bondForm hw0 hw1 x.1 y.1) (bondForm hw0 hw1 x.2 y.2),
   RCsub (bondForm hw0 hw1 x.1 y.2) (bondForm hw0 hw1 x.2 y.1))

def ofSource (x : Source width) : H :=
  (BF4WilsonAllNomeBondOSCompletion.ofSource hw0 hw1 x.1,
   BF4WilsonAllNomeBondOSCompletion.ofSource hw0 hw1 x.2)

theorem value_ofSource (x : Source width) :
    value hw0 hw1 (ofSource hw0 hw1 x) =
      BF4WilsonAllNomeComplexTimeSector.val hw0 hw1 (image hw0 hw1 x.1,image hw0 hw1 x.2) := by
  apply Prod.ext <;> exact constantRows_limit hw0 hw1 _

theorem source_pairing (x y : Source width) :
    inner hw0 hw1 (ofSource hw0 hw1 x) (ofSource hw0 hw1 y) = sourceForm hw0 hw1 x y := by
  simp only [inner,ofSource,sourceForm,constant_pairing]

/-- Physical source differences, not the ambient norm of a raw source. -/
theorem source_distance (x y : Source width) :
    distance hw0 hw1 (ofSource hw0 hw1 x) (ofSource hw0 hw1 y) =
      RCadd (BF4WilsonAllNomeBondOSCompletion.physicalDist hw0 hw1 x.1 y.1)
        (BF4WilsonAllNomeBondOSCompletion.physicalDist hw0 hw1 x.2 y.2) := by
  simp only [distance,ofSource,constant_distance]

private theorem half_budget (e : Q') :
    RCadd (rat (HalfPow.half*e)) (rat (HalfPow.half*e)) = rat e :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => ExpNeg.two_halves e))

def denseSource (X : Rows hw0 hw1 (width := width)) (e : Q') : Source width :=
  (denseExpression hw0 hw1 (rowState hw0 hw1 X).1 (HalfPow.half*e),
   denseExpression hw0 hw1 (rowState hw0 hw1 X).2 (HalfPow.half*e))

/-- An actual paired finite source, with no preimage or density hypothesis. -/
theorem denseSource_bound (X : Rows hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) :
    RCle (distance hw0 hw1 (ofSource hw0 hw1 (denseSource hw0 hw1 X e))
      (ofRows hw0 hw1 X)) (rat e) := by
  rw [distance_value,value_ofSource,value_ofRows]
  have h := RCadd_le_add
    (denseExpression_bound hw0 hw1 (rowState hw0 hw1 X).1 _ (ExpNeg.half_mul_pos _ he))
    (denseExpression_bound hw0 hw1 (rowState hw0 hw1 X).2 _ (ExpNeg.half_mul_pos _ he))
  rw [half_budget] at h
  exact h

/-- A sequence of REPRESENTED paired physical bond states, not a bare
quotient sequence with an implicitly chosen representative at each index. -/
structure CauchySequence where
  seq : Nat → Rows hw0 hw1 (width := width)
  modulus : Q' → Nat
  bound : ∀ e : Q', (0 : Q') < e → ∀ m n, modulus e ≤ m → modulus e ≤ n →
    RCle (distance hw0 hw1 (ofRows hw0 hw1 (seq m)) (ofRows hw0 hw1 (seq n))) (rat e)

def sectorSequence (C : CauchySequence hw0 hw1 (width := width)) :
    BF4WilsonAllNomeComplexTimeSector.CauchySequence hw0 hw1 (width := width) where
  seq := fun n => rowState hw0 hw1 (C.seq n)
  modulus := C.modulus
  bound := by
    intro e he m n hm hn
    have h := C.bound e he m n hm hn
    rw [distance_value,value_ofRows,value_ofRows] at h
    exact h

/-- Return actual physical rows for the limit, with both new range moduli. -/
def limitRows (C : CauchySequence hw0 hw1 (width := width)) : Rows hw0 hw1 (width := width) :=
  rowsOfState hw0 hw1 (BF4WilsonAllNomeComplexTimeSector.limit hw0 hw1 (sectorSequence hw0 hw1 C))

def limitRate (C : CauchySequence hw0 hw1 (width := width)) : Q' → Nat :=
  BF4WilsonAllNomeComplexTimeSector.limitRate hw0 hw1 (sectorSequence hw0 hw1 C)

theorem limit_bound (C : CauchySequence hw0 hw1 (width := width)) (e : Q')
    (he : (0 : Q') < e) (n : Nat) (hn : limitRate hw0 hw1 C e ≤ n) :
    RCle (distance hw0 hw1 (ofRows hw0 hw1 (C.seq n))
      (ofRows hw0 hw1 (limitRows hw0 hw1 C))) (rat e) := by
  rw [limitRows,ofRows_rowsOfState,distance_value,value_ofRows,value_ofState]
  exact BF4WilsonAllNomeComplexTimeSector.limit_bound hw0 hw1 (sectorSequence hw0 hw1 C) e he n hn

def limitCertificate (C : CauchySequence hw0 hw1 (width := width)) :
    Σ' X : Rows hw0 hw1 (width := width), Σ' rate : Q' → Nat,
      ∀ e : Q', (0 : Q') < e → ∀ n, rate e ≤ n →
        RCle (distance hw0 hw1 (ofRows hw0 hw1 (C.seq n)) (ofRows hw0 hw1 X)) (rat e) :=
  ⟨limitRows hw0 hw1 C,limitRate hw0 hw1 C,limit_bound hw0 hw1 C⟩

#print axioms value_injective
#print axioms value_ofState
#print axioms value_ofRows
#print axioms ofRows_rowsOfState
#print axioms toSector
#print axioms fromSector
#print axioms toSector_fromSector
#print axioms fromSector_toSector
#print axioms toSector_isometry
#print axioms inner_value
#print axioms distance_value
#print axioms value_zero
#print axioms inner_conj_symm
#print axioms inner_nonnegative
#print axioms inner_posdef
#print axioms value_ofSource
#print axioms source_pairing
#print axioms source_distance
#print axioms denseSource_bound
#print axioms sectorSequence
#print axioms limitRows
#print axioms limit_bound
#print axioms limitCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
