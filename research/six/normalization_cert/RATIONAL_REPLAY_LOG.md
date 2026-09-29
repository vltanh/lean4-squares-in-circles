# Normalization certificate execution log
Python: 3.13.5; backend: independent exact-dyadic intervals, 96-bit units (NOT Arb).
This log records local execution, not Lean kernel acceptance or a downstream A2 audit.
Predicate inputs: Q0=142559/50000; genuine Seven label; specified central domains.
Lemma A uses the hand CE/OWN exclusions for cx>c0; the face cx=c0 is NOT excluded.
Each source file used in this execution is identified below by SHA-256.

## Direct certificates
| certificate | result | boxes | unresolved | elapsed | closure reasons |
|---|---|---:|---:|---|---|
| L1 chart bounds, axial label, no SEC | CERTIFIED | 83679 | 0 | 8.67s | claim: 11464, infeasible:chart: 60, infeasible:contain: 20230, infeasible:disjoint: 10086 |
| L2 five pins, margin 1/100 | CERTIFIED | 3747 | 0 | 0.39s | infeasible:chart: 24, infeasible:contain: 646, infeasible:disjoint: 662, pin:D: 166, pin:E: 66, pin:N: 66, pin:S: 122, pin:W: 122 |
| L3-E windows and separators | CERTIFIED | 2097 | 0 | 0.14s | claim: 51, infeasible:chart: 13, infeasible:contain: 441, infeasible:disjoint: 499, pin-outside: 45 |
| L3-N windows and separators | CERTIFIED | 2097 | 0 | 0.24s | claim: 51, infeasible:chart: 13, infeasible:contain: 441, infeasible:disjoint: 499, pin-outside: 45 |
| L3-W windows and separators | CERTIFIED | 2505 | 0 | 0.28s | claim: 62, infeasible:chart: 13, infeasible:contain: 473, infeasible:disjoint: 602, pin-outside: 103 |
| L3-D windows and separators | CERTIFIED | 1567 | 0 | 0.20s | claim: 108, infeasible:chart: 10, infeasible:contain: 158, infeasible:disjoint: 372, pin-outside: 136 |
| L3-S windows and separators | CERTIFIED | 2505 | 0 | 0.32s | claim: 62, infeasible:chart: 13, infeasible:contain: 473, infeasible:disjoint: 602, pin-outside: 103 |
| L3-prime E/OWN | CERTIFIED | 2359 | 0 | 0.16s | claim: 61, infeasible:contain: 533, pin-outside: 42, sep-fails: 544 |
| L3-prime E/CE | CERTIFIED | 1931 | 0 | 0.13s | claim: 60, infeasible:chart: 12, infeasible:contain: 344, pin-outside: 12, sep-fails: 538 |
| L3-prime N/OWN | CERTIFIED | 2359 | 0 | 0.16s | claim: 61, infeasible:contain: 533, pin-outside: 42, sep-fails: 544 |
| L3-prime N/CN | CERTIFIED | 1931 | 0 | 0.16s | claim: 60, infeasible:chart: 12, infeasible:contain: 344, pin-outside: 12, sep-fails: 538 |
| L3-prime W/OWN | CERTIFIED | 2143 | 0 | 0.17s | claim: 53, infeasible:contain: 427, pin-outside: 100, sep-fails: 492 |
| L3-prime W/CW | CERTIFIED | 9097 | 0 | 0.89s | claim: 525, infeasible:chart: 16, infeasible:contain: 1394, pin-outside: 56, sep-fails: 2558 |
| L3-prime S/OWN | CERTIFIED | 2143 | 0 | 0.37s | claim: 53, infeasible:contain: 427, pin-outside: 100, sep-fails: 492 |
| L3-prime S/CS | CERTIFIED | 9097 | 0 | 0.74s | claim: 525, infeasible:chart: 16, infeasible:contain: 1394, pin-outside: 56, sep-fails: 2558 |
| L3-prime D/OWN | CERTIFIED | 855 | 0 | 0.08s | claim: 68, infeasible:contain: 48, pin-outside: 162, sep-fails: 150 |
| L3-prime D/CW | CERTIFIED | 3619 | 0 | 0.29s | claim: 193, infeasible:chart: 9, infeasible:contain: 498, pin-outside: 142, sep-fails: 968 |
| L3-prime D/CS | CERTIFIED | 3619 | 0 | 0.27s | claim: 193, infeasible:chart: 9, infeasible:contain: 498, pin-outside: 142, sep-fails: 968 |
| L6 cap piercing, margin 1/30 | CERTIFIED | 2767 | 0 | 0.12s | claim: 288, infeasible:cap: 756, infeasible:contain: 340 |
| L7 own moving pin, margin 1/20 | CERTIFIED | 1937 | 0 | 0.17s | claim: 86, infeasible:contain: 333, not-own: 499, pin-E-outside: 51 |
| W/D order, all four pair axes | CERTIFIED | 5239 | 0 | 1.18s | D-contain: 208, D-disjoint-C: 232, D-pin-out: 62, W-contain: 170, W-disjoint-C: 72, W-pin-out: 100, order-ok: 549, pair-overlap: 1227 |
| A1 forbidden arc (-99/100,61/50), cx>c0 | CERTIFIED | 2927 | 0 | 0.46s | infeasible:chart: 8, infeasible:contain: 518, infeasible:disjoint: 605, marker-outside-arc: 333 |
| A2 forbidden arc (-27/50,39/25), 36 central boxes, cx>c0 | CERTIFIED | 25780 | 0 | 2.39s | |

## Scalar obligations
| id | interval result | sampled diagnostic minimum | tested intervals | statement |
|---|---|---:|---:|---|
| S1 | PASS | 0.00911817441 | 1 | B(2/5)<3/2-rho0 |
| S1a | PASS | 0.0993792816 | 1 | t1<2/5 |
| S2 | PASS | 0.1128524 | 1 | cap frame is primary |
| S3 | PASS | 0.026601831 | 1 | near corner is inside central disk |
| S4 | PASS | 0.204331867 | 1 | piercing lower normal margin |
| S5 | PASS | 0.0730955363 | 23 | piercing G(t,h)>Q0 |
| S5a | PASS | 0.0666484887 | 1 | rho0 sin(2/5)<1/2 |
| S6 | PASS | 0.0372412225 | 1 | U0<1/2 |
| S7 | PASS | 0.0299355782 | 1 | B(1/4)<1/2 |
| S7a | PASS | 0.0506207184 | 1 | 1/4<t1 |
| S8a | PASS | 0.025229315 | 7 | tilt budget on [t1,2/5] |
| S8b | PASS | 0.279049394 | 1 | tilt budget Taylor coefficient |
| S9 | PASS | 0.0235786924 | 1 | OWN-E exclusion with diagonal tolerance |
| S10a | PASS | 0.00218258938 | 1 | 177/200<2-rho0 |
| S10b | PASS | 0.00218258938 | 1 | rho0<223/200 |
| S10c | PASS | 0.00524122246 | 1 | U0<117/250 |
| S11a | PASS | 0.317932876 | 1 | linear maximizer lies left of a=2-rho0 |
| S11b | PASS | 0.20819545 | 1 | 9a+11u<2pi+7 |
| S12 | PASS | 0.37769331 | 1 | secondary separators fail |
| S13 | PASS | 0.124551602 | 1 | A1 forbidden arc exceeds 2pi/3 |
| S14 | PASS | 0.0164012244 | 1 | A2 forbidden arc exceeds 2pi/3 |
| S15 | PASS | 0.260432633 | 3 | CN theta<0: positive derivative |
| S16 | PASS | 0.0498299691 | 13 | OWN-N theta<0: positive derivative |
| S17a | PASS | 0.0797739561 | 1 | a_N increasing |
| S17b | PASS | 0.0646457939 | 1 | a_N(5X0/4)>rho0 |
| S18 | PASS | 1.18376444 | 1 | OWN-N theta>=0: positive derivative |
| S19a | PASS | 0.00316320683 | 1 | u>=1/2 implies label>=5/8 |
| S19b | PASS | 0.226581201 | 1 | N secondary: |theta|<5/8 |
| S20 | PASS | 0.00962625067 | 27 | A1 OWN-S theta>=0: positive derivative |
| S21 | PASS | 1.54041404 | 1 | A1 OWN-S theta<0: positive derivative |
| S22 | PASS | 0.297284739 | 3 | A1 CS: derivative positive on [0,3/10] |
| S22b | PASS | 0.233672568 | 1 | A1 CS: value positive on [3/10,2/5] |
| S23a | PASS | 0.0464180801 | 1 | a_S1(5U0/4)>rho0 |
| S23b | PASS | 0.0942893706 | 1 | a_S1(pi/4)>rho0 |
| S23c | PASS | 0.178448472 | 1 | 2/5<5U0/4 |
| S23d | PASS | 0.0941974773 | 1 | 1/4<5X0/4 |
| S24 | PASS | 0.225669811 | 1 | E quadrant: CN impossible |
| S25 | PASS | 0.159572654 | 1 | E quadrant: SEC+ impossible |
| S26 | PASS | 0.0797986976 | 1 | A1 E quadrant: SEC- impossible |
| S27 | PASS | 0.23934661 | 1 | N SEC- and S SEC+ impossible |
| S28 | PASS | 0.525928454 | 5 | A2 OWN-N theta>=0: positive derivative |
| S29 | PASS | 0.0198612975 | 33 | A2 OWN-S marker bound |
| S30 | PASS | 0.0560809942 | 77 | A2 CS in S quadrant, b>0 |
| S31 | PASS | 0.0501798187 | 7 | A2 E SEC-/CS, theta>=0 |
| S32a | PASS | 0.088509654 | 43 | A2 E CS theta<0, b<=0 |
| S32b | PASS | 0.1043764 | 1 | A2 E CS theta<0, b>0 |
| S35 | PASS | 0.259203769 | 1 | CE: q_E normal |
| S36 | PASS | 0.39882 | 1 | CE: q_E transverse |
| S37 | PASS | 0.0971815358 | 1 | CW: q_W normal |
| S38 | PASS | 0.0782409788 | 9 | CW: q_D normal when q_W transverse fails |
| S39 | PASS | 0.0559726941 | 1 | CW: lower q_W transverse failure infeasible |
| S40 | PASS | 0.141663134 | 9 | OWN-E: q_E transverse |
| S40a | PASS | 0.210181349 | 1 | OWN-E: q_E normal |
| S41a | PASS | 0.0126109373 | 1 | a_E(3/10)>rho0 |
| S41b | PASS | 0.00110255536 | 1 | a_E(-5/12)>rho0 |
| S41c | PASS | 0.0145154145 | 1 | a_E(-pi/4)>rho0 |
| S42a | PASS | 0.000649355503 | 1 | a_W(-2/3)>rho0 |
| S42b | PASS | 0.0145154145 | 1 | a_W(-pi/4)>rho0 |
| S43a | PASS | 0.214421805 | 1 | OWN-W negative: q_W normal |
| S43 | PASS | 0.148984322 | 7 | OWN-W: q_W transverse lower |
| S44 | PASS | 0.0894192416 | 7 | OWN-W subcase ii: q_W normal |
| S45a | PASS | 0.00201589651 | 1 | OWN-W iii: q_D normal can fail only below -1/30 |
| S45b | PASS | 0.134737034 | 3 | OWN-W iii: q_W transverse upper |
| S45c | PASS | 0.256515833 | 1 | OWN-W iii: q_W normal |
| S47 | PASS | 0.121214403 | 1 | q_E not in OWN-N |
| S47b | PASS | 0.181113584 | 1 | q_E not in OWN-S |
| S48 | PASS | 0.00862666549 | 9 | W upper window 5/8 |
| S49 | PASS | 0.0490803885 | 3 | q_W not in OWN-N, theta>=0.17 |
| S49b | PASS | 0.0105274517 | 1 | q_W normal excludes theta_N<=0.17 |
| S50 | PASS | 0.097558869 | 5 | q_W not in OWN-S, theta_S<=0 |
| S51 | PASS | 0.21299264 | 1 | D OWN-W: theta>-2/5 |
| S52a | PASS | 0.970796327 | 1 | E<N |
| S52b | PASS | 0.487462993 | 1 | N<W |
| S52c | PASS | 0.160398163 | 1 | D<S |
| S52d | PASS | 0.487462993 | 1 | S<E+2pi |
| S53 | PASS | 0.0773276194 | 1 | W/D primary-axis exclusion |
| S54a | PASS | 0.301625656 | 1 | own moving pin normal |
| S54 | PASS | 0.0569297288 | 15 | own moving pin transverse |

The four identities are algebraic; the following are numerical sanity checks only.
- I1: PASS; cap branches agree at t1
- I2: PASS; 9/4+(X0+1/2)^2=Q0
- I3: PASS; (5/2-rho0)^2+(U0+1/2)^2=Q0
- I4: PASS; (rho0+1/2)^2+1/4=Q0

## Source hashes
`bnb.py`: `405f56ec4d27ea488d6d1ab0d6e51876fe8bf80c51f58b697dbc41f2182aeb35`
`cert_cone.py`: `82df0a970760c0d6a96388866fcb9ffea7ae12b4a6e9f0b86f22694acf971111`
`cert_main.py`: `3404a9e05c61192fabbafaa2cf24f23babcb0c4b2f5b43a51585df3ba56196df`
`cert_main2.py`: `4b855c55ad49886ace5405c0de40541dbe3ddb486c9a14d46bbc6b7d8b52dc99`
`cert_scalars.py`: `8685df9ed6a9559cb5416d5bb05fca5612bd14a2eb3ea60c95789400c01a7e64`
`cert_wd.py`: `97279e2780ffc692877451aa86a02ddf453b25ae2edcca6058f2146256b34e57`
`ia.py`: `136fbde30ca3bc8a456f15609e866c81e2c194a5b44ecf5adf9d8e4f0d8abd16`
`rational_arb_compat.py`: `689e0272d77d56340bb8c715e8c69a5b86da348165be1c5c08e947752169fbf2`
`replay_rational.py`: `7c41ad9cc611354fbe59f9787267039f5d1384002fbe630686f58bdaec34305c`
`run_all.py`: `0e342a1101675033c38ade7df2974b12326e5926b0809bb4d3e33348d4839d49`
`sharpness.py`: `7b2a6fb6c91d59e6764e6d9508517cbd3493060b7b0af95e0f6e4e5fee969f9e`
`test_replay.py`: `be364630bb94523ff32bb01425f786db0e449473a48de662ccbb60f63b4e5b65`

OVERALL: ALL CERTIFIED; 78 scalar inequalities, 4 identity sanity checks, 23 direct groups.
