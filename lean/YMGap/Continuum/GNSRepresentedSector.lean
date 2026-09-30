/-
# Witnessed polynomial-sector completion inside the original GNS space

A sector witness supplies an existing Cauchy representative, membership of
each dense term, and its equality to the specified ORIGINAL completion
point. No representatives are extracted from quotient points or propositions.
The existing diagonal limit and dense-map extension preserve these witnesses.
This constructs a represented completion, not a new ambient Hilbert space
or a characterization as the fixed space of an unconstructed group action.
-/

import YMGap.Continuum.GNSDenseCompletionExtension
import YMGap.Continuum.HamiltonianScalar

namespace YMGap.Continuum.GNSRepresentedSector

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionExtension
open YMGap.Continuum.HamiltonianScalar

/-- Data witnessing a dense-sector approximation of a specified point of the
existing completion. The Cauchy representative retains its explicit modulus. -/
structure Representative (D : GNSData) (P : D.V → Prop)
    (x : GNSCompletionSpace D) where
  rep : CauchyGNS D
  terms : ∀ n, P (rep.seq n)
  pin : Quotient.mk (cauchySetoid D) rep = x

namespace Representative

variable {D : GNSData} {P : D.V → Prop}

def ofRep (X : CauchyGNS D) (hX : ∀ n, P (X.seq n)) :
    Representative D P (Quotient.mk (cauchySetoid D) X) := ⟨X, hX, rfl⟩

def ofDense (p : D.V) (hp : P p) : Representative D P (embedV D p) :=
  ofRep (constCauchy D p) (fun _ => hp)

/-- Transport the pin, not the representative or its modulus. -/
def transport {x y : GNSCompletionSpace D} (a : Representative D P x)
    (h : x = y) : Representative D P y := ⟨a.rep, a.terms, a.pin.trans h⟩

def add (hadd : ∀ p q, P p → P q → P (D.add p q))
    {x y : GNSCompletionSpace D} (a : Representative D P x) (b : Representative D P y) :
    Representative D P (D.cAdd x y) where
  rep := D.cAddCauchy a.rep b.rep
  terms n := hadd _ _ (a.terms n) (b.terms n)
  pin := (congrArg (fun z => D.cAdd z (Quotient.mk (cauchySetoid D) b.rep)) a.pin).trans
    (congrArg (D.cAdd _) b.pin)

def neg (hneg : ∀ p, P p → P (D.neg p))
    {x : GNSCompletionSpace D} (a : Representative D P x) :
    Representative D P (D.cNeg x) where
  rep := D.cNegCauchy a.rep
  terms n := hneg _ (a.terms n)
  pin := congrArg D.cNeg a.pin

def sub (hadd : ∀ p q, P p → P q → P (D.add p q))
    (hneg : ∀ p, P p → P (D.neg p))
    {x y : GNSCompletionSpace D} (a : Representative D P x) (b : Representative D P y) :
    Representative D P (D.cSub x y) := a.add hadd (b.neg hneg)

/-- Every term of the existing cofinal diagonal is literally a supplied
inner term, so no limit-closure assumption on the dense predicate is needed. -/
theorem lim_terms (X : GeneralCompletionCauchy D)
    (hX : ∀ n m, P ((X.pt n).seq m)) (n : Nat) : P (X.lim.seq n) :=
  hX (X.phi n) (X.reindex.Jidx n)

/-- Constructive sequential completeness with supplied representatives and
moduli. This never chooses representatives from propositional membership. -/
def limit (X : GeneralCompletionCauchy D) (hX : ∀ n m, P ((X.pt n).seq m)) :
    Representative D P (Quotient.mk (cauchySetoid D) X.lim) :=
  ofRep X.lim (lim_terms X hX)

/-- The already constructed extension has the SAME literal diagonal output. -/
def map (T : DenseMap D) (hT : ∀ p, P p → ∀ n, P ((T.toRep p).seq n))
    {x : GNSCompletionSpace D} (a : Representative D P x) :
    Representative D P (T.completionMap x) where
  rep := T.mapRep a.rep
  terms := lim_terms (T.mapOuter a.rep) (fun n m => hT _ (a.terms n) m)
  pin := congrArg T.completionMap a.pin

end Representative

/-- Rational scalar action on the same completion, with an explicit scaled
Cauchy modulus inherited from the existing scalar construction. -/
def smul (S : SmulGNSData) (P : S.toGNSData.V → Prop)
    (hsmul : ∀ c p, P p → P (S.toGNSData.smul c p))
    (c : Q') {x : GNSCompletionSpace S.toGNSData}
    (a : Representative S.toGNSData P x) :
    Representative S.toGNSData P (S.cSmul c x) where
  rep := S.cSmulCauchy c a.rep
  terms n := hsmul c _ (a.terms n)
  pin := congrArg (S.cSmul c) a.pin

#print axioms Representative.ofRep
#print axioms Representative.ofDense
#print axioms Representative.transport
#print axioms Representative.add
#print axioms Representative.neg
#print axioms Representative.sub
#print axioms Representative.lim_terms
#print axioms Representative.limit
#print axioms Representative.map
#print axioms smul

end YMGap.Continuum.GNSRepresentedSector
