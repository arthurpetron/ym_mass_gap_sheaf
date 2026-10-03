"""Focused exact diagnostic tests; no generated writes or Lean claims."""
from fractions import Fraction as F
import unittest
from unittest.mock import patch

from computations.cube_cutoff_one_checkpoint import (
    CYCLES, CYCLE_LOOPS, FACE_MASKS, FACES, FILLINGS, encode, face_loops,
    haar_loops,
)
from computations.cube_cutoff_one_signed_gain import (
    MAX_POLYNOMIAL_DEGREE, bent_loop, canonical, compute_pilot,
    compute_polynomial_pilot, insertion_matrix, kinetic, poly_eval, poly_mul,
    poly_shift, polynomial_report, report,
)


def quadratic(left, matrix, right):
    """Independent explicit bilinear reconstruction, not matvec/dot."""
    return sum((left[i]*matrix[i][j]*right[j]
                for i in range(32) for j in range(32)), F(0))


class CubeSignedGainTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pilot = compute_pilot()
        cls.polynomial = compute_polynomial_pilot()

    def test_geometry_full_basis_and_literal_bent_loop(self):
        p = self.pilot
        pair, index = bent_loop()
        self.assertEqual((len(p.spatial), len(p.insertion), len(p.one)), (32, 32, 32))
        self.assertTrue(all(len(row) == 32 for row in p.spatial+p.insertion))
        self.assertEqual((pair, index), (p.adjacent_faces, p.cycle_index))
        self.assertEqual(CYCLES[index], FACE_MASKS[pair[0]] ^ FACE_MASKS[pair[1]])
        self.assertEqual(CYCLES[index].bit_count(), 6)
        self.assertEqual(len(CYCLE_LOOPS[index]), 1)
        self.assertEqual(p.reference, F(1, 8)**6)

    def test_inserted_matrix_keeps_exact_original_haar_contractions(self):
        p = self.pilot
        for i, j in ((0, 0), (0, p.cycle_index), (3, 17), (12, 31)):
            parity = CYCLES[i] ^ CYCLES[j] ^ CYCLES[p.cycle_index]
            expected = sum(((2*p.r)**s.bit_count()*haar_loops(
                CYCLE_LOOPS[i]+CYCLE_LOOPS[p.cycle_index]+CYCLE_LOOPS[j]+face_loops(s))
                for s in FILLINGS[parity]), F(0))
            self.assertEqual(p.insertion[i][j], expected)
        self.assertTrue(all(p.insertion[i][j] == p.insertion[j][i]
                            for i in range(32) for j in range(32)))

    def test_own_mean_uses_original_odd_partition_not_even_partition(self):
        p = self.pilot
        Z = quadratic(p.one, p.spatial, p.terminal_message)
        mean_num = quadratic(p.observable, p.spatial, p.terminal_message)
        E = quadratic(p.terminal_message, p.spatial, p.terminal_message)
        self.assertEqual(p.odd_partition, Z)
        self.assertEqual(p.even_partition, E)
        self.assertGreater(Z, 0)
        self.assertGreater(E, 0)
        self.assertNotEqual(Z, E)
        self.assertEqual(p.own_mean, mean_num/Z)
        self.assertEqual(mean_num-p.own_mean*Z, 0)

    def test_centered_message_literal_heat_reconstruction(self):
        p = self.pilot
        psi = tuple(p.observable[j]-p.own_mean*p.one[j] for j in range(32))
        direct = tuple(p.r**CYCLES[i].bit_count()*sum(
            (p.spatial[i][j]*psi[j] for j in range(32)), F(0)) for i in range(32))
        self.assertEqual(p.centered_message, direct)
        self.assertEqual(p.centered_message, tuple(
            v-p.own_mean*u for v, u in zip(p.observed_message, p.terminal_message)))
        self.assertEqual(p.observed_message, kinetic(p.r, tuple(
            p.insertion[i][0] for i in range(32))))

    def test_original_signed_pairings_and_favorable_candidate_sign(self):
        p = self.pilot
        C1 = quadratic(p.terminal_message, p.insertion, p.centered_message) - \
            p.own_mean*quadratic(p.terminal_message, p.spatial, p.centered_message)
        C2 = quadratic(p.centered_message, p.spatial, p.centered_message)
        self.assertEqual(p.first_cross, C1)
        self.assertEqual(p.second_square, C2)
        self.assertEqual(p.gain, C2-p.reference*C1)
        self.assertGreater(C2, 0)
        # A falsifiable finite diagnostic expectation, NOT an analytic premise.
        self.assertGreater(p.gain, 0)

    def test_uncentered_regression_does_not_replace_own_center(self):
        p = self.pilot
        C1raw = quadratic(p.terminal_message, p.insertion, p.observed_message)
        C2raw = quadratic(p.observed_message, p.spatial, p.observed_message)
        self.assertEqual(p.uncentered_first_cross, C1raw)
        self.assertEqual(p.uncentered_second_square, C2raw)
        self.assertEqual(p.uncentered_gain, C2raw-p.reference*C1raw)
        self.assertNotEqual(p.own_mean, 0)
        self.assertNotEqual(p.gain, p.uncentered_gain)

    def test_unchanged_engine_and_domain_guards(self):
        with self.assertRaises(ValueError):
            insertion_matrix(F(1, 4), self.pilot.cycle_index)
        with self.assertRaises(ValueError):
            insertion_matrix(F(-1, 8), self.pilot.cycle_index)
        with self.assertRaises(ValueError):
            insertion_matrix(F(1, 8), 32)
        with self.assertRaises(ValueError):
            kinetic(F(1, 8), (F(1),))
        with self.assertRaises(ValueError):
            haar_loops((FACES[0],)*6)
        with self.assertRaises(ValueError):
            haar_loops(((0, 1, 0),))
        # Odd incidence must return zero before asking for a tensor contraction.
        with patch("computations.cube_cutoff_one_checkpoint.edge_tensor",
                   side_effect=AssertionError("Odd term reached tensor engine")):
            self.assertEqual(haar_loops((FACES[0],)*7), 0)

    def test_stdout_report_preserves_proof_scope_and_exact_data(self):
        p = self.pilot
        data = report(p)
        self.assertEqual(data["original_source_to_matrix_pin"], "NOT FORMALIZED IN LEAN")
        self.assertFalse(data["completed_gain_or_uniform_scaling_claim"])
        self.assertEqual(data["G_raw"], encode(p.gain))
        self.assertEqual(data["G_over_same_even_partition"], encode(p.gain/p.even_partition))
        self.assertEqual(data["own_odd_mean"], encode(p.own_mean))
        self.assertEqual(data["original_own_center_residual"], [0, 1])
        self.assertIn("no cached", data["matrix_provenance"])
        self.assertTrue(data["headCutoff_guard"].startswith("FAILED:"))

    def test_polynomial_matrices_reconstruct_actual_haar_entries(self):
        p, polynomial = self.pilot, self.polynomial
        for i in range(32):
            self.assertEqual(poly_eval(polynomial.terminal_message[i], p.r), p.terminal_message[i])
            for j in range(32):
                self.assertEqual(poly_eval(polynomial.spatial[i][j], p.r), p.spatial[i][j])
                self.assertEqual(poly_eval(polynomial.insertion[i][j], p.r), p.insertion[i][j])

    def test_cleared_polynomial_preserves_full_own_center_and_gain(self):
        p, polynomial = self.pilot, self.polynomial
        Z = poly_eval(polynomial.odd_partition, p.r)
        n = poly_eval(polynomial.odd_mean_numerator, p.r)
        self.assertEqual(Z, p.odd_partition)
        self.assertEqual(n, p.own_mean*Z)
        self.assertEqual(tuple(poly_eval(v, p.r) for v in polynomial.cleared_centered_message),
                         tuple(Z*v for v in p.centered_message))
        self.assertEqual(poly_eval(polynomial.cleared_gain, p.r), Z*Z*p.gain)

    def test_polynomial_leading_term_and_full_signed_remainder_bound(self):
        polynomial = self.polynomial
        P = polynomial.cleared_gain
        self.assertLessEqual(len(P)-1, MAX_POLYNOMIAL_DEGREE)
        self.assertTrue(all(c == 0 for c in P[:10]))
        self.assertEqual(P[10], 2)
        tail = sum((abs(P[i])*F(1, 8)**(i-10) for i in range(11, len(P))), F(0))
        self.assertEqual(tail, polynomial.tail_majorant_at_one_eighth)
        self.assertEqual(polynomial.candidate_interval_floor, 2-tail)
        # Falsifiable regression for the calculated bound, not an analytic premise.
        self.assertLess(tail, F(1, 2))
        self.assertGreater(polynomial.candidate_interval_floor, F(3, 2))
        data = polynomial_report(polynomial, self.pilot)
        self.assertEqual(data["candidate_floor_strictly_positive"], 2-tail > 0)
        self.assertTrue(data["interval_conclusion_available"])
        for r in (F(1, 8), F(1, 16), F(1, 32)):
            self.assertGreaterEqual(poly_eval(P, r)/r**10, 2-tail)

    def test_polynomial_caps_reject_overflow_without_truncation(self):
        self.assertEqual(canonical([0, 1, 0, 0]), (F(0), F(1)))
        with self.assertRaises(ValueError):
            canonical([0]*(MAX_POLYNOMIAL_DEGREE+1)+[1])
        with self.assertRaises(ValueError):
            poly_mul(poly_shift((F(1),), 41), poly_shift((F(1),), 40))
        with self.assertRaises(ValueError):
            poly_shift((F(1),), -1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
