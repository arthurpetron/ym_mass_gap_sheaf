#!/usr/bin/env python3
"""Regenerate checkpoint data and finite arithmetic Lean checker inside this project."""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
from math import lcm
import hashlib
import json
import sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from computations.cube_cutoff_one_checkpoint import (
    EDGES,FACES,CYCLES,FACE_MASKS,CYCLE_INDEX,spatial_matrix,transfer,
    matvec,dot,encode,normalized_pair_escape,haar_loops)


def clear(values):
    denom=lcm(*(x.denominator for x in values))
    return denom,[x.numerator*(denom//x.denominator) for x in values]


def build():
    r=F(1,8);A=spatial_matrix(r)
    one=tuple(F(i==0) for i in range(32))
    p=tuple(F(i==CYCLE_INDEX[FACE_MASKS[0]]) for i in range(32))
    u=transfer(A,r,one); f=transfer(A,r,p)
    escape=normalized_pair_escape(A,r)
    G=[[F(*x) for x in row] for row in escape['marginal_gram']]
    c=[F(*x) for x in escape['dual_coefficients']]
    b=[matvec(A,f)[i] for i in escape['basis_indices']]
    gd,gi=clear([x for row in G for x in row]); cd,ci=clear(c);bd,bi=clear(b)
    grow=[gi[i*8:(i+1)*8] for i in range(8)]
    rows=[sum(grow[i][j]*ci[j] for j in range(8)) for i in range(8)]
    norm=sum(ci[i]*rows[i] for i in range(8));pair=sum(x*y for x,y in zip(bi,ci))
    assert rows[:7]==[0]*7 and norm>0 and pair>0
    moments=[]
    for d in range(5):
        ud,fd=one,p
        for _ in range(d):ud,fd=transfer(A,r,ud),transfer(A,r,fd)
        Z=dot(one,matvec(A,ud));J=dot(p,matvec(A,fd));L=dot(one,matvec(A,fd));R=dot(p,matvec(A,ud))
        assert L==R
        moments.append({'separation':d,'Z':encode(Z),'left':encode(L),'right':encode(R),
                        'joint':encode(J),'connected':encode((Z*J-L*R)/Z**2)})
    data={'scope':'Exact six-face SU(2) cube cutoff-one diagnostic. Local Lean gates and global original-carrier pin pending.',
          'w':encode(F(1,2)),'r':encode(r),'kernel_cutoff':1,
          'one_factor_pointwise_floor':encode(1-4*r),
          'edges':EDGES,'faces':FACES,'cycles':CYCLES,
          'spatial_matrix':[[encode(x) for x in row] for row in A],
          'original_window_moments':moments,'normalized_pair_escape':escape,
          'integer_certificate':{'gram_denominator':gd,'gram_numerators':grow,
            'dual_denominator':cd,'dual_numerators':ci,'source_pairing_denominator':bd,
            'source_pairing_numerators':bi,'weighted_norm_numerator':norm,'pairing_numerator':pair},
          'lean_verification':'NOT RUN','original_cube_matrix_pin':'NOT FORMALIZED',
          'no_continuum_or_uniform_gap_claim':True}
    target=ROOT/'audits/CHECKPOINT-01-CUBE-TRANSFER-2026-09-18.json'
    target.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    def ilist(xs):return '['+', '.join(str(x) for x in xs)+']'
    header='''/-
# Exact arithmetic check of the finite-cube normalized-pair diagnostic

STATUS: candidate for local Lean verification. Not imported by YMGap.lean.

This checks the displayed INTEGER certificate: seven weighted orthogonality
relations, positive dual norm and a positive full-weight pairing numerator.
The integers were generated using exact SU(2) Haar contractions. Their pin to
`transferStep`/the full original weighted window is NOT a theorem of this file.
In particular, a successful check is NOT a physical or continuum gap proof.
No canonical statement is edited and no analytic premise is introduced.

Consumer: reject a plaquette-span closure shortcut only after the separate
original-cube moment pin has been proved. The source-level mathematical
interpretation and exact Python checks are in the associated audit.
-/

import Init

namespace YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck
set_option autoImplicit false

'''
    text=header
    text+=f'def gramDenominator : Nat := {gd}\n'
    text+=f'def dualDenominator : Nat := {cd}\n'
    text+=f'def sourceDenominator : Nat := {bd}\n'
    text+='def gram : List (List Int) := [\n  '+',\n  '.join(ilist(row) for row in grow)+']\n'
    text+='def dual : List Int := '+ilist(ci)+'\n'
    text+='def sourcePairing : List Int := '+ilist(bi)+'\n\n'
    text+='''def dot : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | a::xs, b::ys => a*b + dot xs ys

def rowPairing (i : Nat) : Int := dot (gram.getD i []) dual

def normNumerator : Int := dot dual ((List.range 8).map rowPairing)
def pairingNumerator : Int := dot sourcePairing dual

-- Shape guards prevent truncated list operations from hiding missing entries.
theorem shapes : gram.length = 8 ∧ dual.length = 8 ∧
    sourcePairing.length = 8 ∧ (gram.all (fun row => row.length == 8)) = true := by decide

theorem denominators_positive : 0 < gramDenominator ∧
    0 < dualDenominator ∧ 0 < sourceDenominator := by decide

'''
    names=['shapes','denominators_positive']
    for i in range(7):
        name=f'weighted_orthogonality_{i}'
        names.append(name);text+=f'theorem {name} : rowPairing {i} = 0 := by decide\n'
    text+='\ntheorem weighted_norm_positive : 0 < normNumerator := by decide\n'
    text+='theorem source_pairing_positive : 0 < pairingNumerator := by decide\n'
    names+=['weighted_norm_positive','source_pairing_positive']
    zn,zd=escape['original_partition']
    text+=f'\ndef partitionNumerator : Int := {zn}\n'
    text+=f'def partitionDenominator : Int := {zd}\n'
    text+='theorem normalized_norm_below_one :\n    normNumerator * partitionDenominator <\n      (gramDenominator : Int) * (dualDenominator : Int)^2 * partitionNumerator := by decide\n'
    text+='theorem connected_covariance_lower :\n    (sourceDenominator : Int) * (dualDenominator : Int) * partitionNumerator <\n      (2500000 : Int) * partitionDenominator * pairingNumerator := by decide\n'
    text+='theorem connected_covariance_upper :\n    (2000000 : Int) * partitionDenominator * pairingNumerator <\n      (sourceDenominator : Int) * (dualDenominator : Int) * partitionNumerator := by decide\n'
    names+=['normalized_norm_below_one','connected_covariance_lower','connected_covariance_upper']
    text+='\nend YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck\n\n'
    for name in names:text+=f'#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.{name}\n'
    dest=ROOT/'lean/YMGap/Continuum/BF4CubeNormalizedPairEscapeCheck.lean'
    dest.write_text(text,encoding='utf-8')
    print('Generated',target.relative_to(ROOT),dest.relative_to(ROOT))
    print('Integer certificate checks:',len(names),'PENDING local Lean')
    print('Exact normalized weighted escape:',float(F(*escape['full_weight_pairing_with_transferred_source'])))
    print('Original source-to-matrix Lean pin: NOT FORMALIZED')

if __name__=='__main__': build()
