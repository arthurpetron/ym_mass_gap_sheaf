Model: rel. err(g2) = 0.075/sqrt(N); s0 = 0.0644; test slope k1 = 0.0027 (exact two-loop: s(1.54)=0.0685, s(2.41)=0.0710; its series slope 2 ln2 b1 = 0.00252, k2 ~ 0.00010).
Check vs existing: model 3-pair continuum error at u=2.41, 1.54 with N24=300 / existing: 0.0015, 0.0021 / 0.0015, 0.0021 (E_forms.md, c=0.3).

| plan | u values | continuum error per u | sigma(k1), k2 = 0 fixed | sigma(k1), k2 free | k1=0.0027 vs k1=0 (sigma, k2 fixed) | (k2 free) |
|---|---|---|---|---|---|---|
| P0 current (2 u, 300 meas L=24) | 1.54, 2.41 | 0.0021, 0.0015 | 0.00055 | undetermined (2 points) | 4.9 | - |
| P1 4x L=24 (1200 meas) at the 2 beta | 1.54, 2.41 | 0.0019, 0.0013 | 0.00050 | undetermined (2 points) | 5.4 | - |
| P1' = P1 + 4x L=12 (2400 meas) | 1.54, 2.41 | 0.0016, 0.0011 | 0.00041 | undetermined (2 points) | 6.6 | - |
| P2 = P1' + 12->24 at u=1.0, 1.9, 2.9 (300 meas L=24, 1200 L=12; 6->12, 8->16 at existing quality) | 1.54, 2.41, 1, 1.9, 2.9 | 0.0016, 0.0011, 0.0033, 0.0017, 0.0011 | 0.00026 | 0.00160 | 10.2 | 1.7 |
| P3 = P2 + 16->32 at the 2 original u (300 meas L=32, 2000 L=16) | 1.54, 2.41, 1, 1.9, 2.9 | 0.0015, 0.0009, 0.0033, 0.0017, 0.0011 | 0.00025 | 0.00152 | 10.8 | 1.8 |
| P2x4 = P2 with 4x all statistics (all pairs, all u) | 1.54, 2.41, 1, 1.9, 2.9 | 0.0008, 0.0005, 0.0016, 0.0009, 0.0005 | 0.00013 | 0.00080 | 20.4 | 3.4 |
| P2x16 = P2 with 16x all statistics | 1.54, 2.41, 1, 1.9, 2.9 | 0.0004, 0.0003, 0.0008, 0.0004, 0.0003 | 0.00007 | 0.00040 | 40.9 | 6.8 |

## Re-run with the ACTUAL measured errors (items 1-2 final data, `S3_final.json`, errors: nominal)

Ensembles entering the primary (lin3) k1 fits: 30 (interpolated old-u pairs counted as 2 pseudo-ensembles each); their CPU cost at the measured rates: 49.6 CPU-h.

| plan | sigma(k1) c=0.3, k2 free | c=0.4, k2 free | c=0.3, k2=0 | c=0.4, k2=0 | extra CPU-h (est.) |
|---|---|---|---|---|---|
| A0 actual (items 1-2 done) | 0.00218 | 0.00345 | 0.00037 | 0.00059 | 0 |
| A2x: 2x statistics on every ensemble | 0.00154 | 0.00244 | 0.00026 | 0.00042 | 50 |
| A4x: 4x statistics on every ensemble | 0.00109 | 0.00172 | 0.00019 | 0.00030 | 149 |
| A16x: 16x statistics on every ensemble | 0.00055 | 0.00086 | 0.00009 | 0.00015 | 745 |
| uniform factor needed for sigma(k1) <= 0.0009 at BOTH c (k2 free): 14.7x | | | | | 679 |
| A-16->32 (P3/"item 3"): 16->32 at u=1.54, 2.41 (300 meas L=32, 2000 L=16), lin over 6,8,12,16 | 0.00206 | 0.00295 | 0.00034 | 0.00048 | ~40 |
| A-16->32 (P3/"item 3"): 16->32 at u=1.54, 2.41 (300 meas L=32, 2000 L=16), lin over finest 3 = 8,12,16 at those u | 0.00390 | 0.00491 | 0.00063 | 0.00076 | ~40 |
| optimal allocation to sigma(k1) <= 0.0009 at both c, k2 free (water-filling) | 0.00057 | 0.00090 | | | 249 |
|   largest extra: L=16 J1.54: 8323 -> 128340 meas (133 CPU-h); L=12 J1.54: 17235 -> 126068 meas (39 CPU-h); L=8 J1.54: 8323 -> 616813 meas (29 CPU-h); L=16 3.19: 400 -> 17923 meas (19 CPU-h); L=6 J1.54: 17235 -> 779388 meas (7 CPU-h); L=12 3.08: 600 -> 16299 meas (6 CPU-h) | | | | | |
| best within the 70 CPU-h cap, k2 free | 0.00096 | 0.00151 | | | 70 |
| optimal allocation to sigma(k1) <= 0.0009 at both c, k2 = 0 (water-filling) | 0.00037 (k2=0 fit) | 0.00059 | | | 0 |
|   largest extra:  | | | | | |
| best within the 70 CPU-h cap, k2 = 0 | 0.00016 | 0.00025 | | | 70 |

Reading: statistical only, fixed continuum form (lin3) and fixed u set; extrapolation-form spread and c=0.3/0.4 disagreement are NOT reduced by statistics in this model.
