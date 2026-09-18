#!/usr/bin/env python3
"""Focused exact tests; no random seeds, numerical eigensolvers, or global writes."""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as F
from itertools import product, permutations, combinations
from pathlib import Path
import json
import math
import sys
import time
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from computations.cube_cutoff_one_checkpoint import *


def sphere_moment(exponents):
    if any(e % 2 for e in exponents): return F(0)
    halves=[e//2 for e in exponents]
    numerator=math.prod(math.prod(range(1,2*k,2)) for k in halves)
    denominator=math.prod(4+2*j for j in range(sum(halves)))
    return F(numerator,denominator)


def entry_terms(row,col,forward):
    # Independent polynomial implementation, including an explicitly written inverse.
    if forward:
        return { (0,0):((0,1,0),(1,0,1)), (0,1):((2,1,0),(3,0,1)),
                 (1,0):((2,-1,0),(3,0,1)), (1,1):((0,1,0),(1,0,-1))}[(row,col)]
    return { (0,0):((0,1,0),(1,0,-1)), (0,1):((2,-1,0),(3,0,-1)),
             (1,0):((2,1,0),(3,0,-1)), (1,1):((0,1,0),(1,0,1))}[(row,col)]


def polynomial_entry_moment(directions,indices):
    total_real,total_imag=F(0),F(0)
    for terms in product(*(entry_terms(indices[2*i],indices[2*i+1],forward)
                           for i,forward in enumerate(directions))):
        exponents=[0]*4; re,im=1,0
        for coordinate,a,b in terms:
            exponents[coordinate]+=1
            re,im=re*a-im*b,re*b+im*a
        moment=sphere_moment(exponents)
        total_real+=re*moment;total_imag+=im*moment
    return total_real,total_imag


def vertex_map(v,perm,flip):
    return sum(((v>>i)&1)<<perm[i] for i in range(3)) ^ flip


class CubeCheckpointTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.r=F(1,8);cls.A=spatial_matrix(cls.r)
        cls.data=json.loads((ROOT/'audits/CHECKPOINT-01-CUBE-TRANSFER-2026-09-18.json').read_text())

    def test_geometry_and_complete_even_support_census(self):
        self.assertEqual((len(EDGES),len(FACES),len(CYCLES)),(12,6,32))
        self.assertEqual(Counter(m.bit_count() for m in CYCLES),{0:1,4:6,6:16,8:9})
        for m in CYCLES:
            self.assertEqual(len(FILLINGS[m]),2)
            a,b=FILLINGS[m];self.assertEqual(a^b,63)
            self.assertEqual(boundary(a),m)

    def test_all_quadratic_and_quartic_entries_against_sphere_polynomials(self):
        checked=0
        for degree in (2,4):
            for directions in product((False,True),repeat=degree):
                tensor,denom=edge_tensor(directions)
                for indices in product((0,1),repeat=2*degree):
                    re,im=polynomial_entry_moment(directions,indices)
                    self.assertEqual(im,0)
                    self.assertEqual(re,F(int(tensor[indices]),denom))
                    checked+=1
        self.assertEqual(checked,4160)

    def test_full_cycle_basis_haar_orthonormality(self):
        for i in range(32):
            for j in range(i,32):
                self.assertEqual(haar_loops(CYCLE_LOOPS[i]+CYCLE_LOOPS[j]),F(i==j))

    def test_normalization_and_schur_factor(self):
        self.assertEqual(haar_loops(FACES),F(1,16))
        for p,q in combinations(range(6),2):
            if FACE_MASKS[p]&FACE_MASKS[q]:
                loops=(FACES[p],FACES[q])+components(FACE_MASKS[p]^FACE_MASKS[q])
                self.assertEqual(haar_loops(loops),F(1,2))
        self.assertEqual(self.A[0][0],1+(2*self.r)**6/F(16))

    def test_all_cube_automorphisms(self):
        for perm in permutations(range(3)):
            for flip in range(8):
                edge_map=[EDGE_INDEX[tuple(sorted((vertex_map(a,perm,flip),vertex_map(b,perm,flip))))]
                          for a,b in EDGES]
                remap=[CYCLE_INDEX[sum(1<<edge_map[e] for e in range(12) if m & (1<<e))]
                       for m in CYCLES]
                for i in range(32):
                    for j in range(32):
                        self.assertEqual(self.A[i][j],self.A[remap[i]][remap[j]])

    def test_stored_matrix_is_reproducible(self):
        actual=[[encode(x) for x in row] for row in self.A]
        self.assertEqual(actual,self.data['spatial_matrix'])

    def test_both_spatial_weights_in_transfer_pairing(self):
        # Explicit A D A versus the same expression with the source/target interchanged.
        for i,j in ((0,1),(3,17),(5,21),(7,31)):
            expected=sum((self.A[i][k]*self.r**CYCLES[k].bit_count()*self.A[k][j]
                          for k in range(32)),F(0))
            e=tuple(F(k==j) for k in range(32))
            self.assertEqual(matvec(self.A,transfer(self.A,self.r,e))[i],expected)
            self.assertEqual(expected,sum((self.A[j][k]*self.r**CYCLES[k].bit_count()*self.A[k][i]
                                          for k in range(32)),F(0)))

    def test_normalized_pair_escape_with_same_marginal(self):
        witness=normalized_pair_escape(self.A,self.r)
        self.assertEqual(witness,self.data['normalized_pair_escape'])
        Z=F(*witness['original_partition'])
        pairing=F(*witness['full_weight_pairing_with_transferred_source'])
        norm=F(*witness['dual_squared_norm'])
        self.assertTrue(0 < norm/Z < 1)
        self.assertTrue(F(1,2500000)<pairing/Z<F(1,2000000))
        self.assertEqual(witness['weighted_pairings_with_constant_and_plaquettes'],[[0,1]]*7)
        self.assertEqual(F(*witness['connected_determinant']),Z*pairing)

    def test_integer_certificate_clears_actual_rationals(self):
        C=self.data['integer_certificate']; W=self.data['normalized_pair_escape']
        gram=[[F(n,C['gram_denominator']) for n in row] for row in C['gram_numerators']]
        dual=[F(n,C['dual_denominator']) for n in C['dual_numerators']]
        self.assertEqual(gram,[[F(*x) for x in row] for row in W['marginal_gram']])
        self.assertEqual(dual,[F(*x) for x in W['dual_coefficients']])
        self.assertEqual(matvec(gram,dual)[:7],(F(0),)*7)
        self.assertEqual(dot(dual,matvec(gram,dual)),F(*W['dual_squared_norm']))

    def test_admissible_cutoff_one_positivity_and_rejected_domains(self):
        self.assertEqual(1-4*self.r,F(1,2))
        for r in (F(-1,8),F(1,4),F(1,2)):
            with self.assertRaises(ValueError):spatial_matrix(r)
        with self.assertRaises(ValueError):edge_tensor((True,)*6)
        with self.assertRaises(ValueError):solve_exact([[0]],[1])

    def test_original_observable_held_fixed_in_recorded_windows(self):
        e=tuple(F(i==0) for i in range(32))
        p=tuple(F(i==CYCLE_INDEX[FACE_MASKS[0]]) for i in range(32))
        for stored in self.data['original_window_moments']:
            u,f=e,p
            for _ in range(stored['separation']):u,f=transfer(self.A,self.r,u),transfer(self.A,self.r,f)
            Z=dot(e,matvec(self.A,u));L=dot(e,matvec(self.A,f));R=dot(p,matvec(self.A,u))
            J=dot(p,matvec(self.A,f));self.assertEqual(L,R)
            self.assertEqual(encode((Z*J-L*R)/Z**2),stored['connected'])
            self.assertGreater(Z,0)


if __name__=='__main__':
    start=time.monotonic()
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(CubeCheckpointTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    report={'tests_run':result.testsRun,'failures':len(result.failures),'errors':len(result.errors),
            'success':result.wasSuccessful(),'runtime_seconds':time.monotonic()-start,
            'independent_one_link_moment_comparisons':4160,'cube_automorphisms':48,
            'arithmetic':'exact signed int64 with overflow guard and fractions.Fraction',
            'arithmetic_rounding_error':'0',
            'cutoff_and_continuum_approximation_error':'not bounded by this checkpoint',
            'lean_verification':'NOT RUN','original_source_to_matrix_pin':'NOT FORMALIZED'}
    (ROOT/'audits/CHECKPOINT-01-TEST-RESULTS-2026-09-18.json').write_text(json.dumps(report,indent=2)+'\n')
    sys.exit(0 if result.wasSuccessful() else 1)
