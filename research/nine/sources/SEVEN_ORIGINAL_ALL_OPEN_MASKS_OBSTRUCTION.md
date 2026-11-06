# Every open mask has a subcritical seven-original realization

> Retained mathematical source. Reproduction commands, checker reports and implementation notes below refer to the [archived version](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/SEVEN_ORIGINAL_ALL_OPEN_MASKS_OBSTRUCTION.md); the current task is the [pen-and-paper roadmap](../PROOF_PLAN.md).

This is an exact obstruction to a proposed proof route, not a new mask
closure. It shows that the five marked comparisons and the complete physical
constraints on the seven selected originals cannot exclude any of the 24
open masks. At least some information involving an omitted original is
necessary. It does not show that each of the two omitted originals is
individually indispensable.

No Lean, Lake or CI. Numerical optimization suggested the rows below;
the certificate and its proof use rational arithmetic only.

## Statement and encoding

For each of the 24 masks whose main bits have at least one weak outer link,
there are seven independently framed unit squares A,B,C,D,E,F,G, pairwise
strictly separated, with every corner strictly inside the disk of squared
radius 17/4. They satisfy all five center-cone comparisons strictly and
have exactly the prescribed actual/weak bits. Since

    1105/256 - 17/4 = 17/256 >0,

these are strictly subcritical configurations of the selected-seven
relaxation. They are not nine-square configurations and cannot be
counterexamples to the intended theorem.

A table entry (X,Y,T) denotes

    c=(1006X/1000000,1003Y/1000000),  t=T/1000,
    u=((1-t^2)/(1+t^2),2t/(1+t^2)),  v=(-u_y,u_x).

All values are rational, and u,v are exactly orthonormal. The entries have
|T|<=414, so u_x>=|u_y| and the coordinate halfwidth is
h=(u_x+|u_y|)/2. Column order gives the original labels; the marked edges
are AB,BC,CD,EF,FG.

## Fourteen explicit representatives


| Mask | A | B | C | D | E | F | G |
|---|---|---|---|---|---|---|---|
| 001/00 | (-1477,-4,0) | (-477,-974,0) | (523,-1266,0) | (1436,-353,-121) | (-888,996,0) | (112,1227,0) | (1112,752,0) |
| 001/01 | (-1478,0,0) | (-478,-257,0) | (522,-1257,0) | (1438,-342,-117) | (-882,1000,0) | (118,1444,0) | (1090,769,-117) |
| 001/10 | (-1477,0,0) | (-477,-966,0) | (523,-1211,0) | (1449,-286,-98) | (-890,993,-65) | (10,138,-63) | (1070,802,1) |
| 001/11 | (-1478,0,0) | (-478,-391,0) | (522,-1258,0) | (1437,-343,-118) | (-890,993,-59) | (132,1126,-59) | (1096,760,-59) |
| 011/00 | (-1323,-233,0) | (-323,-303,0) | (534,-1160,-334) | (1360,-334,-121) | (-1001,767,0) | (-1,1400,0) | (999,771,0) |
| 011/01 | (-1324,-230,0) | (-324,-303,0) | (533,-1160,-337) | (1359,-334,-121) | (-998,770,0) | (2,1399,0) | (990,775,-61) |
| 011/10 | (-1323,-234,0) | (-323,-303,0) | (534,-1160,-334) | (1360,-334,-121) | (-1000,769,3) | (-4,1399,3) | (999,770,0) |
| 011/11 | (-1334,-210,0) | (-334,-336,0) | (520,-1190,414) | (1357,-352,-128) | (-982,793,3) | (15,1396,3) | (1003,762,-74) |
| 101/00 | (-1420,-352,110) | (-501,-1271,0) | (499,-1272,0) | (1419,-352,-109) | (-1109,745,0) | (-109,1355,0) | (1098,937,-414) |
| 101/01 | (-1415,-7,-86) | (-483,-939,0) | (517,-1263,0) | (1431,-349,-120) | (-961,930,-86) | (200,1443,-91) | (1091,758,-91) |
| 101/11 | (-1425,-284,99) | (-500,-1209,0) | (500,-641,0) | (1425,284,99) | (-897,1098,-414) | (-116,438,393) | (649,1194,399) |
| 111/00 | (-949,-958,414) | (-242,-251,-414) | (465,-958,-414) | (1319,-105,0) | (-1301,360,-136) | (-186,1003,0) | (814,895,0) |
| 111/01 | (-1333,-208,-4) | (-334,-336,-4) | (520,-1190,414) | (1357,-352,-128) | (-986,789,-4) | (18,1398,0) | (1003,762,-73) |
| 111/11 | (-967,-863,392) | (-260,-155,392) | (448,-863,392) | (1156,-155,392) | (-1113,430,412) | (-392,1123,412) | (857,955,412) |

## Finite hand verification table

The following bounds apply to all entries in the associated row. K/1000
is an upper bound on every squared corner norm. P/10^6 is a lower bound on
the exhibited physical separating-axis reserve of each of the 21 pairs;
C/10^6 bounds every cone reserve dx-|dy|; and B/10^6 bounds every marked
bit reserve (dx-h_i-h_j for a zero bit, h_i+h_j-dx for a one bit).
Every entry is positive, and every K is less than 4250.

The axis word has 21 digits in lexicographic pair order
AB,AC,AD,AE,AF,AG,BC,BD,BE,BF,BG,CD,CE,CF,CG,DE,DF,DG,EF,EG,FG.
For pair i,j, a digit 0, 1, 2, 3 selects u_i,v_i,u_j,v_j respectively.
Its reserve is

    |n dot (c_j-c_i)|
      -( |n dot u_i|+|n dot v_i|+|n dot u_j|+|n dot v_j| )/2.

A positive reserve explicitly separates the two closed original squares.
No inset-only or center-disk relaxation is substituted for physical
separation. The corner checks use all four vectors c+(s*u+t*v)/2,
with s,t in {-1,1}. Each line is checked by substitution and clearing
positive denominators; the adjacent standalone checker prints the exact
minimum reserves and verifies the displayed bounds.

| Mask | K | P | C | B | Axis word |
|---|---:|---:|---:|---:|---|
| 001/00 | 4201 | 3000 | 2739 | 6000 | 000100001113111003000 |
| 001/01 | 4198 | 3000 | 3000 | 6000 | 000100001103113031002 |
| 001/10 | 4195 | 3416 | 3781 | 6000 | 000302001313111003002 |
| 001/11 | 4198 | 3300 | 2745 | 6000 | 000300001303113003000 |
| 011/00 | 3894 | 3000 | 2478 | 6000 | 020110201101033003000 |
| 011/01 | 3890 | 3000 | 2478 | 6000 | 020110201101033003002 |
| 011/10 | 3894 | 2487 | 2478 | 4005 | 020110203101033003022 |
| 011/11 | 3901 | 2264 | 1508 | 2999 | 030110303100133033002 |
| 101/00 | 4171 | 2489 | 2757 | 6000 | 122330001133111001000 |
| 101/01 | 4178 | 2501 | 2742 | 6000 | 000130001333113003000 |
| 101/11 | 4100 | 3892 | 2775 | 6000 | 120322021122231203022 |
| 111/00 | 3705 | 3000 | 2121 | 6000 | 002130022311033201220 |
| 111/01 | 3901 | 2408 | 1508 | 2973 | 030110301100133033202 |
| 111/11 | 3529 | 4028 | 1118 | 157709 | 000122103120312331001 |

## Exact reversal and coverage

Negate both coordinates and both frame vectors, and relabel

    (A,B,C,D;E,F,G) -> (D,C,B,A;G,F,E).

This is a half-turn of the seven physical squares followed by a permutation.
It preserves their exact unit frames, all 28 corner norms, all 21 physical
pairs and the five cone inequalities. The mask abc/de becomes cba/ed.
The 14 printed representatives and their reversals are exactly the 24
five-bit strings whose first or third bit is 1. No constraints on the
unprinted eighth and ninth originals have been asserted or checked.

The table covers 14 representatives: four each for main 001 and 011, and
three each for self-reversing main 101 and 111 (short 01 and 10 are partners).
Main 001/011 reversals supply 100/110. Therefore every open mask's
selected-seven relaxation is feasible, with all boundaries avoided.

## Evidence and consequence

[computer_assisted/seven_original_all_open_masks_table.json](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/computer_assisted/seven_original_all_open_masks_table.json) is the complete rational table.
[computer_assisted/verify_seven_original_table.py](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/computer_assisted/verify_seven_original_table.py) is an independent, standalone arithmetic
reader of that table; it imports neither the numerical search nor the
producer's geometry code. It verifies 882 rational assertions, including
the 56 displayed summary bounds, and the exact 24-mask reversal union.
[computer_assisted/seven_original_table_exact_report.json](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/computer_assisted/seven_original_table_exact_report.json) records that successful replay.
The root integrator independently reran the standalone checker and obtained
the same successful arithmetic result. The SHA-256 inventory binds the exact
source, table, report and this hand/table document. This is computational
arithmetic checking accompanying the explicit hand/table proof; no human
or proof-kernel verification is claimed.

The consequence is a deliberate route restriction: switching to another
open mask cannot make a proof that discards both extras sound. Continue
with full-original-nine constraints or a valid global extraction. This
result changes zero mask, positional-root or roadmap counts.
