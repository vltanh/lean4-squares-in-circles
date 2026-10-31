# The last vertical-endpoint source form in LSLSLD is impossible

**Status:** complete hand argument with a printed finite rational certificate,
checked in this session. No independent agent review or Lean verification is
claimed. This closes a whole support row inside LSLSLD, not the whole cycle
signature or a master-ledger entry.

Use the both-unique-D-endpoint branch of
[ONE_DIAGONAL_TWO_SIDE_COMMON_SOURCE_EDGE.md](ONE_DIAGONAL_TWO_SIDE_COMMON_SOURCE_EDGE.md).
The [vertical-source table](ONE_DIAGONAL_VERTICAL_SOURCE_SIDE_EXCLUSION.md)
and [torque exclusions](ONE_DIAGONAL_VERTICAL_SOURCE_TORQUE_EXCLUSIONS.md)
already remove all forms with a vertical S direction at A except source
row V_V with radial-side C. We exclude precisely that remaining form,
retaining both circle-load coefficients of C and every endpoint contact
slide. Reflection gives the same conclusion for a vertical direction at B.

## 1. A complete two-variable necessary parameter family

Let e=(a,b) point along C's common inner edge and m=(-b,a) point into C.
The exact common-edge classification gives

```text
a^2+b^2=1,       0<b<a,
C=[-1/2,1/2]*e+[L,L+1]*m,
Q_A=-e/2+L*m,       Q_B=e/2+L*m,
R^2=(L+1)^2+1/4,       9/10<L<17/16.
```

A's S direction is (0,1), while B's is (-r,s), with

```text
r^2+s^2=1,       0<r<s,       b<r.
```

The last strict inequality follows from the common-edge support inequality
`r*a-s*b>0`: since a,b,r,s are positive unit coordinates in their first
quadrants, it is equivalent to b<r. At A the horizontal-side contact slide
is alpha in [0,1). At B the support is its strict upper inner corner.
Put d=sqrt(2) and K=2+d. Matching the two actual S endpoint contacts gives

```text
alpha=r+a-d>=0,
U=1+d-r-a/2,       W=2+b/2,
u=U+L*b,          H_A=W-L*a,
v=1+r+a/2-L*b,    H_B=1+s-L*a-b/2.                 (1)
```

For example, the A contact after its unit S step is
`(1-u-alpha,2-H_A)=(-a/2-L*b,-b/2+L*a)`, and the B contact is
`(v-1-r,1-H_B+s)=(a/2-L*b,b/2+L*a)`. This verifies every identity in (1)
and also u+v=K. No contact slide has been fixed to zero.

Both D endpoints are geometrically circle-loaded, so
`u^2+H_A^2=v^2+H_B^2=R^2`. Substituting (1) cancels the L^2 terms and yields

```text
L=L_A=(U^2+W^2-5/4)/(2*(W*a+1-U*b)),
L=L_B=(2+2*(r+s)+a*(1+r)-b*(1+s))
       /(2*(1+b*(1+r)+a*(1+s))).                    (2)
```

The first denominator is positive. In fact a>7/10, b<3/4, U<43/20 and
W>=2 give `W*a+1-U*b>63/80`; the second is plainly positive.
These bounds follow from a>1/sqrt(2), b<1/sqrt(2), d<3/2 and r>0.

Normalize the positive D force magnitude to one and write h for its
common strict side-interior height. A's vertical-contact torque gives

```text
-h=H_A*(L*b+a/2)/u.
```

B's torque gives `(h+H_B)*(v*s-H_B*r)=H_B*(s-r)`. Eliminating h and
multiplying by the positive u therefore forces

```text
T=(u*H_B-H_A*(L*b+a/2))*(v*s-H_B*r)
  -u*H_B*(s-r)=0.                                  (3)
```

Thus (1)--(3), alpha>=0, b<r and r<s are necessary for every realization.
No force equation or circle-weight ratio at C was used. In particular a
zero coefficient at either one of C's geometric circle vertices is retained.

## 2. Rational domain and exact interval operations

Use half-angle variables

```text
x=b/(1+a),       y=r/(1+s),
a=(1-x^2)/(1+x^2),       b=2x/(1+x^2),
s=(1-y^2)/(1+y^2),       r=2y/(1+y^2).
```

Every actual realization lies in the closed rectangle

```text
X=[0,5/12],       Y=[1/5,5/12],                      (4)
```

and satisfies x<y and r<s. Indeed both frame angles are below pi/4,
so x,y<sqrt(2)-1<5/12. Also alpha>=0 and a<=1 give
`r>=sqrt(2)-1>2/5`, whence `y=r/(1+s)>r/2>1/5`.
The map `z -> 2z/(1+z^2)` is strictly increasing for 0<=z<1, proving
b<r equivalent to x<y.

Throughout the table enclose d by

```text
140/99<sqrt(2)<99/70,
140^2<2*99^2,       99^2>2*70^2.                    (5)
```

Evaluate formulas (1)--(3) and (2) by exact rational interval arithmetic.
Addition and subtraction use endpoint sums/differences; multiplication
takes the minimum and maximum of the four endpoint products. Division
by a positive interval [l,u] multiplies by [1/u,1/l]. These operations
enclose all simultaneous actual values even when variables repeat.
Only boxes with a strictly positive interval lower bound for the first
L_A denominator are evaluated further. All other division intervals
are positive. When L_A and L_B intervals overlap, restrict L to their
intersection with [9/10,17/16] before evaluating (1) and (3).

## 3. Rejection rules and complete coverage

The certificate uses only these rules. A margin is the displayed exact
interval quantity, bounded below in the table in units of 1/10^9.

| Rule | Interval contradiction | Margin |
| --- | --- | --- |
| N | lower(x)>=upper(y), contradicting x<y | lower(x)-upper(y) |
| S | lower(r)>=upper(s), contradicting r<s | lower(r)-upper(s) |
| A | upper(alpha)<0, contradicting alpha>=0 | -upper(alpha) |
| L- | upper(L_A)<9/10 | 9/10-upper(L_A) |
| L+ | lower(L_A)>17/16 | lower(L_A)-17/16 |
| G- | upper(L_A-L_B)<0 | -upper(L_A-L_B) |
| G+ | lower(L_A-L_B)>0 | lower(L_A-L_B) |
| T | lower(T)>0, contradicting T=0 | lower(T) |

Start with rectangle (4). At each split bisect its longer interval,
choosing x in a tie. The two closed children retain the midpoint. A
path's 0 means the lower child and 1 the upper child. Thus each printed
binary path specifies one exact closed rational rectangle with no
floating-point convention.

The table is a complete binary-tree frontier: a node is either a listed
leaf or has both listed descendant branches. There are 248 leaves,
247 splits and 495 nodes in all, with maximum path length 15. The exact
checker reconstructs this tree, checks every child and witness, rejects
uncovered rectangles and prefix-overlapping leaves, and verifies
`sum_leaf 2^(-path_length)=1`. Therefore every point of (4), including all
subdivision boundaries, is covered by at least one rejected closed leaf.

All printed margins are positive; the smallest is 104178/10^9. The two
weak-comparison rules N and S would also permit zero, since their physical
inequalities are strict, but zero is not needed here. Counts by rule are
N:1, S:2, A:4, L-:5, L+:2, G-:36, G+:78 and T:120.

The full rational data are in
[radial_vertical_source_exclusion.json](radial_vertical_source_exclusion.json).
The self-contained
[checker](check_radial_vertical_source_exclusion.py) reconstructs all
intervals, formulas, coverage and printed bounds. Its builder fails if
any cell remains unresolved; its default verification checks the saved
certificate and the table below without numerical optimization. The
finite interval calculations are the proof certificate, and the program
is a reproducibility check for them.

| Row | Closed-cell path | Rejection | Margin / 10^9 |
| ---: | --- | --- | ---: |
| 0 | `0000000` | L- | 7108686 |
| 1 | `0000001` | G- | 2372226 |
| 2 | `000001` | G- | 39600139 |
| 3 | `00001000` | A | 8895032 |
| 4 | `000010010` | T | 99633973 |
| 5 | `0000100110` | A | 1173997 |
| 6 | `0000100111` | T | 44422823 |
| 7 | `00001010` | A | 15617340 |
| 8 | `0000101100` | A | 4865648 |
| 9 | `0000101101` | T | 29388375 |
| 10 | `000010111` | G+ | 27237381 |
| 11 | `000011000` | G- | 22208613 |
| 12 | `000011001` | T | 27458217 |
| 13 | `00001101` | T | 27939112 |
| 14 | `0000111000` | T | 12345212 |
| 15 | `00001110010` | T | 72980589 |
| 16 | `00001110011` | T | 69664959 |
| 17 | `000011101` | G+ | 3459844 |
| 18 | `0000111100` | T | 4605125 |
| 19 | `0000111101` | T | 35166025 |
| 20 | `0000111110` | T | 10259527 |
| 21 | `00001111110` | T | 51593293 |
| 22 | `00001111111` | G+ | 8079631 |
| 23 | `00010` | L- | 6427647 |
| 24 | `0001100` | G- | 12458924 |
| 25 | `000110100` | T | 16859954 |
| 26 | `00011010100` | T | 35533224 |
| 27 | `00011010101` | T | 51420922 |
| 28 | `00011010110` | T | 60230210 |
| 29 | `00011010111` | T | 35549461 |
| 30 | `000110110` | G- | 9159066 |
| 31 | `00011011100` | T | 87277324 |
| 32 | `00011011101` | T | 25235043 |
| 33 | `0001101111` | T | 21240461 |
| 34 | `0001110` | L- | 1303708 |
| 35 | `000111100` | G- | 30271145 |
| 36 | `000111101` | T | 2412297 |
| 37 | `00011111` | G- | 3127868 |
| 38 | `001000` | G+ | 31105190 |
| 39 | `0010010` | G+ | 2240119 |
| 40 | `0010011` | G+ | 80727136 |
| 41 | `00101` | G+ | 120925530 |
| 42 | `0011000000` | G+ | 12343919 |
| 43 | `0011000001` | G+ | 1210505 |
| 44 | `001100001` | G+ | 36254878 |
| 45 | `00110001000` | T | 36278592 |
| 46 | `00110001001` | G+ | 14294312 |
| 47 | `00110001010` | T | 21474125 |
| 48 | `00110001011` | G+ | 3433039 |
| 49 | `001100011` | G+ | 14091274 |
| 50 | `0011001` | G+ | 34532592 |
| 51 | `00110100000` | T | 17707254 |
| 52 | `00110100001` | T | 23041214 |
| 53 | `00110100010` | T | 43016768 |
| 54 | `00110100011` | T | 9288453 |
| 55 | `0011010010` | G+ | 8160683 |
| 56 | `00110100110` | G+ | 2082451 |
| 57 | `00110100111` | G+ | 22122785 |
| 58 | `00110101000` | T | 66952934 |
| 59 | `00110101001` | T | 9287177 |
| 60 | `0011010101` | T | 3684192 |
| 61 | `00110101100` | T | 11621169 |
| 62 | `00110101101` | G+ | 11672584 |
| 63 | `001101011100` | T | 29804587 |
| 64 | `001101011101` | T | 23309454 |
| 65 | `00110101111` | G+ | 1384499 |
| 66 | `00110110` | G+ | 22479174 |
| 67 | `00110111` | G+ | 1517028 |
| 68 | `00111` | G+ | 26025573 |
| 69 | `01000` | L- | 49186880 |
| 70 | `0100100` | L- | 23347566 |
| 71 | `0100101` | G- | 12343051 |
| 72 | `010011` | G- | 36659407 |
| 73 | `0101` | G- | 25966762 |
| 74 | `0110000000` | T | 26620489 |
| 75 | `0110000001` | G- | 5068267 |
| 76 | `01100000100` | T | 123441 |
| 77 | `01100000101` | T | 1914266 |
| 78 | `01100000110` | T | 22460255 |
| 79 | `011000001110` | T | 19674684 |
| 80 | `011000001111` | T | 13662659 |
| 81 | `011000010` | G- | 9209878 |
| 82 | `01100001100` | T | 43511126 |
| 83 | `011000011010` | T | 10708282 |
| 84 | `011000011011` | T | 20955960 |
| 85 | `01100001110` | G- | 8240874 |
| 86 | `01100001111` | T | 11312383 |
| 87 | `0110001000` | G+ | 6581735 |
| 88 | `01100010010` | G+ | 1341129 |
| 89 | `01100010011` | G+ | 21543642 |
| 90 | `011000101` | G+ | 31215090 |
| 91 | `011000110000` | T | 22784228 |
| 92 | `011000110001` | T | 16827918 |
| 93 | `01100011001` | G+ | 11667425 |
| 94 | `011000110100` | T | 11076779 |
| 95 | `011000110101` | T | 5528822 |
| 96 | `01100011011` | G+ | 1953445 |
| 97 | `011000111` | G+ | 11353906 |
| 98 | `011001000` | G- | 28051919 |
| 99 | `0110010010` | T | 3880013 |
| 100 | `0110010011` | G- | 2289634 |
| 101 | `011001010` | G- | 46286066 |
| 102 | `011001011` | G- | 5372203 |
| 103 | `011001100000` | T | 1462233 |
| 104 | `011001100001` | T | 9115119 |
| 105 | `011001100010` | G+ | 104178 |
| 106 | `011001100011` | T | 9184280 |
| 107 | `011001100100` | T | 18705045 |
| 108 | `011001100101` | T | 27992735 |
| 109 | `011001100110` | T | 3880525 |
| 110 | `0110011001110` | T | 20890284 |
| 111 | `0110011001111` | T | 28149601 |
| 112 | `0110011010` | G+ | 7624815 |
| 113 | `01100110110` | G+ | 3221784 |
| 114 | `01100110111` | G+ | 23593832 |
| 115 | `01100111000` | T | 18215847 |
| 116 | `0110011100100` | T | 26032218 |
| 117 | `0110011100101` | T | 22726491 |
| 118 | `0110011100110` | T | 34869356 |
| 119 | `0110011100111` | T | 17499173 |
| 120 | `01100111010` | G- | 4428955 |
| 121 | `011001110110` | T | 5923733 |
| 122 | `011001110111` | T | 14582764 |
| 123 | `011001111000` | G+ | 1641270 |
| 124 | `011001111001` | T | 2826152 |
| 125 | `01100111101` | G+ | 14289202 |
| 126 | `0110011111000` | T | 19419823 |
| 127 | `0110011111001` | G+ | 5147182 |
| 128 | `0110011111010` | T | 14397431 |
| 129 | `0110011111011` | G+ | 626835 |
| 130 | `01100111111` | G+ | 5145809 |
| 131 | `011010` | G+ | 5701567 |
| 132 | `01101100` | G+ | 21644131 |
| 133 | `01101101` | G+ | 2990880 |
| 134 | `0110111` | G+ | 71580893 |
| 135 | `0111000` | G- | 2032718 |
| 136 | `01110010000` | G- | 13328570 |
| 137 | `01110010001` | T | 5286464 |
| 138 | `01110010010` | G- | 22074792 |
| 139 | `01110010011` | G- | 1556109 |
| 140 | `0111001010000` | T | 12644047 |
| 141 | `0111001010001` | T | 16390401 |
| 142 | `0111001010010` | T | 20866615 |
| 143 | `0111001010011` | T | 11566411 |
| 144 | `011100101010` | G+ | 3831277 |
| 145 | `0111001010110` | G+ | 1906914 |
| 146 | `0111001010111` | G+ | 12148498 |
| 147 | `0111001011000` | T | 28809179 |
| 148 | `0111001011001` | T | 6929834 |
| 149 | `011100101101` | T | 1112592 |
| 150 | `0111001011100` | T | 13619458 |
| 151 | `0111001011101` | G+ | 7729339 |
| 152 | `0111001011110` | T | 8987110 |
| 153 | `0111001011111` | G+ | 3349656 |
| 154 | `0111001100` | G- | 5560855 |
| 155 | `0111001101` | G- | 14042685 |
| 156 | `011100111000` | T | 8903284 |
| 157 | `011100111001` | T | 16424003 |
| 158 | `0111001110100` | T | 4538905 |
| 159 | `0111001110101` | T | 11087903 |
| 160 | `0111001110110` | T | 6857406 |
| 161 | `0111001110111` | T | 6640220 |
| 162 | `01110011110` | T | 7370397 |
| 163 | `0111001111100` | T | 14232374 |
| 164 | `0111001111101` | T | 2373313 |
| 165 | `0111001111110` | T | 21343537 |
| 166 | `01110011111110` | T | 9557032 |
| 167 | `01110011111111` | T | 11451244 |
| 168 | `0111010` | G- | 35017392 |
| 169 | `011101100` | G- | 15595255 |
| 170 | `01110110100` | G- | 6387443 |
| 171 | `0111011010100` | G- | 1907585 |
| 172 | `0111011010101` | T | 7008727 |
| 173 | `011101101011` | T | 1982817 |
| 174 | `01110110110` | G- | 14582285 |
| 175 | `011101101110` | T | 8714037 |
| 176 | `011101101111` | G- | 1431676 |
| 177 | `011101110` | G- | 31624275 |
| 178 | `01110111100` | G- | 22627814 |
| 179 | `01110111101` | G- | 1961329 |
| 180 | `0111011111` | G- | 5018919 |
| 181 | `0111100000` | G+ | 11294722 |
| 182 | `0111100001` | G+ | 2448061 |
| 183 | `011110001` | G+ | 36756065 |
| 184 | `011110010000` | G+ | 6672920 |
| 185 | `011110010001` | G+ | 2366567 |
| 186 | `01111001001` | G+ | 19536844 |
| 187 | `0111100101000` | G+ | 684154 |
| 188 | `0111100101001` | G+ | 10962403 |
| 189 | `0111100101010` | T | 4506195 |
| 190 | `0111100101011` | G+ | 6722171 |
| 191 | `01111001011` | G+ | 10956693 |
| 192 | `011110011` | G+ | 19183981 |
| 193 | `0111101` | G+ | 34683332 |
| 194 | `0111110000000` | T | 413330 |
| 195 | `0111110000001` | G+ | 2520903 |
| 196 | `01111100000100` | T | 7364699 |
| 197 | `01111100000101` | T | 5509577 |
| 198 | `0111110000011` | T | 2565293 |
| 199 | `01111100001` | G+ | 2534043 |
| 200 | `01111100010000` | T | 7482117 |
| 201 | `01111100010001` | T | 10780561 |
| 202 | `01111100010010` | T | 9384598 |
| 203 | `01111100010011` | T | 7367894 |
| 204 | `0111110001010` | T | 6447435 |
| 205 | `01111100010110` | T | 5393874 |
| 206 | `01111100010111` | T | 3462232 |
| 207 | `011111000110` | G+ | 1868194 |
| 208 | `0111110001110` | G+ | 425530 |
| 209 | `0111110001111` | G+ | 10742242 |
| 210 | `011111001` | G+ | 2255282 |
| 211 | `0111110100000` | T | 12790187 |
| 212 | `01111101000010` | T | 1621750 |
| 213 | `01111101000011` | T | 3279080 |
| 214 | `0111110100010` | G- | 1623860 |
| 215 | `01111101000110` | T | 6390572 |
| 216 | `01111101000111` | T | 9441272 |
| 217 | `01111101001000` | G+ | 157128 |
| 218 | `01111101001001` | T | 5479556 |
| 219 | `0111110100101` | G+ | 6678680 |
| 220 | `01111101001100` | T | 3583177 |
| 221 | `01111101001101` | T | 1728286 |
| 222 | `0111110100111` | G+ | 2653503 |
| 223 | `0111110101000` | G- | 5593999 |
| 224 | `0111110101001` | T | 5242815 |
| 225 | `011111010101` | T | 139858 |
| 226 | `011111010110000` | T | 8694558 |
| 227 | `011111010110001` | T | 11554687 |
| 228 | `011111010110010` | T | 11280249 |
| 229 | `011111010110011` | T | 9655313 |
| 230 | `01111101011010` | G+ | 2447969 |
| 231 | `01111101011011` | G+ | 465009 |
| 232 | `011111010111000` | T | 14176255 |
| 233 | `011111010111001` | T | 7796884 |
| 234 | `01111101011101` | S | 986002 |
| 235 | `01111101011110` | T | 1912777 |
| 236 | `01111101011111` | S | 986002 |
| 237 | `0111110110` | G+ | 1166381 |
| 238 | `011111011100` | G+ | 6281860 |
| 239 | `011111011101` | G+ | 2328260 |
| 240 | `01111101111` | G+ | 19373148 |
| 241 | `0111111` | G+ | 469976 |
| 242 | `100` | G+ | 82337114 |
| 243 | `101` | N | 4166666 |
| 244 | `1100` | G+ | 38131425 |
| 245 | `11010` | G+ | 25549314 |
| 246 | `11011` | L+ | 35018433 |
| 247 | `111` | L+ | 120414761 |

## 4. Consequence and scope

No point of the full parameter domain satisfies every necessary condition.
The radial-C/V_V source with a vertical A endpoint is therefore impossible.
Reflection excludes the analogous vertical B form.

Together with the two previously proved vertical-source exclusions, every
LSLSLD realization whose two D endpoints have unique circle vertices must
have strict inner-corner S support at both D endpoints. Its remaining C
supports are the three common-edge rows E_A, E_B and V_V. Both complete
S-transmitter slide intervals still remain free, and the radial-D-endpoint
branch has separate obligations. Whole-case completion is not inferred.

This certificate completes the 30 unresolved cells preserved in
[RADIAL_VERTICAL_SOURCE_RESEARCH_HANDOFF.md](RADIAL_VERTICAL_SOURCE_RESEARCH_HANDOFF.md).
This local theorem changes no master status because the whole LSLSLD
signature is still open.
