/-
# OWN centering does not sign a spatially weighted temporal residue

An exact two-state diagnostic with the ORIGINAL FORM T=K*M_V and
ell_V(h)=H[V*h]: K=[[3/4,1/4],[1/4,3/4]], V=(2,3), a=T^0 1.
The kinetic kernel is strictly positive, symmetric and stochastic;
T is positive and symmetric in ell_V. Both chronological partitions are
computed, not identified. For Theta=V the residue
z*T(Theta*A)-v*Theta*a has both signs. Literal OWN centering still gives
a strictly POSITIVE integrated residue, so it cannot automatically be
discarded as nonpositive in a weighted noise/variance telescope.

This is NOT an SU(2) action, an original BF4 state, a counterexample at
positive filter depth, or a test of the COMPLETE Ward/Taylor combination.
It prunes only the generic favorable-sign inference from positivity,
weighted symmetry, chronological partitions and OWN centering. Its consumer
is the adaptive conditional-score audit, not a physical spectral-gap claim.
-/

import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.RationalWeightedTemporalResidueObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Constructive.SumOfSquares (q_mul_self_nonneg)

local infix:50 " ≈ " => Q'.eqv

def quarter : Q' := Q'.mkPos 1 4 (by decide)
def half : Q' := Q'.mkPos 1 2 (by decide)

def kinetic (i j : Bool) : Q' := (if i == j then 3 else 1)*quarter

def heat (f : Bool → Q') : Bool → Q'
  | false => quarter*(3*f false+f true)
  | true => quarter*(f false+3*f true)

def weight : Bool → Q'
  | false => 2
  | true => 3

def haar (f : Bool → Q') : Q' := half*(f false+f true)
def mass (f : Bool → Q') : Q' := haar (fun i => weight i*f i)
def pairing (f g : Bool → Q') : Q' := mass (fun i => f i*g i)
def transfer (f : Bool → Q') : Bool → Q' := heat (fun i => weight i*f i)

theorem kinetic_positive (i j : Bool) : (0 : Q') < kinetic i j := by
  cases i <;> cases j <;> decide

theorem kinetic_symmetric (i j : Bool) : kinetic i j ≈ kinetic j i := by
  cases i <;> cases j <;> decide

theorem kinetic_row_mass (i : Bool) : kinetic i false+kinetic i true ≈ 1 := by
  cases i <;> decide

theorem heat_kernel_pin (f : Bool → Q') (i : Bool) :
    heat f i ≈ kinetic i false*f false+kinetic i true*f true := by
  cases i
  · exact poly_identity_of_normal_eq
      (.mul (.var 2) (.add (.mul (.const 3) (.var 0)) (.var 1)))
      (.add (.mul (.mul (.const 3) (.var 2)) (.var 0))
        (.mul (.mul (.const 1) (.var 2)) (.var 1)))
      (by decide) (fun | 0 => f false | 1 => f true | _ => quarter)
  · exact poly_identity_of_normal_eq
      (.mul (.var 2) (.add (.var 0) (.mul (.const 3) (.var 1))))
      (.add (.mul (.mul (.const 1) (.var 2)) (.var 0))
        (.mul (.mul (.const 3) (.var 2)) (.var 1)))
      (by decide) (fun | 0 => f false | 1 => f true | _ => quarter)

/-- The actual weighted transfer is symmetric for ALL rational probes. -/
theorem transfer_symmetric (f g : Bool → Q') :
    pairing f (transfer g) ≈ pairing g (transfer f) := by
  exact poly_identity_of_normal_eq
    (.mul (.var 4) (.add
      (.mul (.const 2) (.mul (.var 0) (.mul (.var 5)
        (.add (.mul (.const 3) (.mul (.const 2) (.var 2))) (.mul (.const 3) (.var 3))))))
      (.mul (.const 3) (.mul (.var 1) (.mul (.var 5)
        (.add (.mul (.const 2) (.var 2)) (.mul (.const 3) (.mul (.const 3) (.var 3)))))))))
    (.mul (.var 4) (.add
      (.mul (.const 2) (.mul (.var 2) (.mul (.var 5)
        (.add (.mul (.const 3) (.mul (.const 2) (.var 0))) (.mul (.const 3) (.var 1))))))
      (.mul (.const 3) (.mul (.var 3) (.mul (.var 5)
        (.add (.mul (.const 2) (.var 0)) (.mul (.const 3) (.mul (.const 3) (.var 1)))))))))
    (by decide) (fun
      | 0 => f false | 1 => f true | 2 => g false | 3 => g true
      | 4 => half | _ => quarter)

/-- An explicit SOS certificate, retaining the actual weight on BOTH sides. -/
theorem transfer_square_pin (f : Bool → Q') :
    pairing f (transfer f) ≈ half*quarter*
      (2*((2*f false+3*f true)*(2*f false+3*f true))+
        (2*f false-3*f true)*(2*f false-3*f true)) := by
  exact poly_identity_of_normal_eq
    (.mul (.var 2) (.add
      (.mul (.const 2) (.mul (.var 0) (.mul (.var 3)
        (.add (.mul (.const 3) (.mul (.const 2) (.var 0))) (.mul (.const 3) (.var 1))))))
      (.mul (.const 3) (.mul (.var 1) (.mul (.var 3)
        (.add (.mul (.const 2) (.var 0)) (.mul (.const 3) (.mul (.const 3) (.var 1)))))))))
    (.mul (.mul (.var 2) (.var 3)) (.add
      (.mul (.const 2) (.mul
        (.add (.mul (.const 2) (.var 0)) (.mul (.const 3) (.var 1)))
        (.add (.mul (.const 2) (.var 0)) (.mul (.const 3) (.var 1)))))
      (.mul
        (.add (.mul (.const 2) (.var 0)) (.neg (.mul (.const 3) (.var 1))))
        (.add (.mul (.const 2) (.var 0)) (.neg (.mul (.const 3) (.var 1)))))))
    (by decide) (fun | 0 => f false | 1 => f true | 2 => half | _ => quarter)

theorem transfer_positive (f : Bool → Q') : (0 : Q') ≤ pairing f (transfer f) := by
  have hs := Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2)
      (q_mul_self_nonneg (2*f false+3*f true)))
    (q_mul_self_nonneg (2*f false-3*f true))
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ half*quarter) hs)
    (Q'.le_of_eqv (Q'.eqv_symm (transfer_square_pin f)))

def incoming : Bool → Q' := fun _ => 1
def outgoing : Bool → Q' := transfer incoming
def incomingPartition : Q' := pairing incoming incoming
def outgoingPartition : Q' := pairing outgoing outgoing

theorem chronological_pins :
    outgoing false ≈ Q'.mkPos 9 4 (by decide) ∧
    outgoing true ≈ Q'.mkPos 11 4 (by decide) ∧
    incomingPartition ≈ Q'.mkPos 5 2 (by decide) ∧
    outgoingPartition ≈ Q'.mkPos 525 32 (by decide) := by decide

def residue (i : Bool) : Q' :=
  incomingPartition*transfer (fun j => weight j*outgoing j) i-
    outgoingPartition*weight i*incoming i

theorem residue_both_signs : residue false < 0 ∧ (0 : Q') < residue true := by decide

def ownMean : Q' := Q'.mkPos 6 17 (by decide)
def probe : Bool → Q' | false => 1 | true => 0
def ownCentered (i : Bool) : Q' := probe i-ownMean
def edgeMass : Q' := mass (fun i => incoming i*outgoing i)

/-- Mean of the SAME chronological incoming edge law; no unweighted mean. -/
theorem own_mean_pin :
    (0 : Q') < edgeMass ∧
    edgeMass*ownMean ≈ mass (fun i => incoming i*outgoing i*probe i) ∧
    mass (fun i => incoming i*outgoing i*ownCentered i) ≈ 0 := by decide

theorem own_variance_positive :
    (0 : Q') < mass (fun i => incoming i*outgoing i*ownCentered i*ownCentered i) := by decide

def centeredResidue : Q' := mass (fun i => incoming i*ownCentered i*ownCentered i*residue i)

theorem centered_residue_pin : centeredResidue ≈ Q'.mkPos 3045 9248 (by decide) := by decide
theorem centered_residue_positive : (0 : Q') < centeredResidue := by decide

/-- The actual conditional determinant, before dividing by the output density. -/
def noise (i : Bool) : Q' :=
  outgoing i*transfer (fun j => incoming j*ownCentered j*ownCentered j) i-
    transfer (fun j => incoming j*ownCentered j) i*
      transfer (fun j => incoming j*ownCentered j) i

theorem noise_pin (i : Bool) : noise i ≈ Q'.mkPos 9 8 (by decide) := by
  cases i <;> decide

def weightedTimeDifference : Q' :=
  incomingPartition*(mass (fun i => weight i*noise i)+
    mass (fun i => weight i*transfer (fun j => incoming j*ownCentered j) i*
      transfer (fun j => incoming j*ownCentered j) i))-
  outgoingPartition*mass (fun i => weight i*(incoming i*ownCentered i)*(incoming i*ownCentered i))

/-- BOTH chronological partitions and the complete noise are retained. -/
theorem weighted_time_difference_pin : weightedTimeDifference ≈ centeredResidue := by decide
theorem weighted_time_difference_positive : (0 : Q') < weightedTimeDifference := by decide

end YMGap.Continuum.RationalWeightedTemporalResidueObstruction

#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.transfer
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.kinetic_positive
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.kinetic_symmetric
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.kinetic_row_mass
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.heat_kernel_pin
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.transfer_symmetric
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.transfer_square_pin
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.transfer_positive
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.chronological_pins
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.residue_both_signs
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.own_mean_pin
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.own_variance_positive
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.centered_residue_pin
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.centered_residue_positive
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.noise_pin
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.weighted_time_difference_pin
#print axioms YMGap.Continuum.RationalWeightedTemporalResidueObstruction.weighted_time_difference_positive
