#!/usr/bin/env python3
"""Sensitivity (not the rule input): re-run step34 (5-u Wilson-flow stopping-rule analysis) with the step-2 Wilson-flow measurements (prod4 *_z1p9/_z2p4/_z2p9
NAME.csv, eps 0.1; the Zeuthen NAME.zeu.csv stays excluded) pooled into the (L, beta) ensembles.  usage: step2_pooled_wilson.py OUTPREFIX [NBOOT]"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import step34 as S
S.EXC = ('_cold', '_tau', '.alt', '.zeu', 'bad_')
S.main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 400, S.DIRS, False)
