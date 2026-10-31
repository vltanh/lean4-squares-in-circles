# Uniform capacity of a radial-D three-square core

**Status:** complete capacity argument with an explicit finite rational
table, checked in this single-agent session using separate 44-bit and
60-bit integer interval backends. The logical capacity predicates are
shared. No independent agent review or Lean verification is claimed.

## 1. A theorem independent of the remaining contact graph

Let 79/40<=R<=3/sqrt(2), and put K=2+sqrt(2).
Suppose three interior-disjoint unit squares in the containing disk have
the following normalized geometry:

```text
A=[-u,1-u] x [-1/2,1/2],       R^2=u^2+1/4,
B=[v-1,v] x [-H,1-H],         v=K-u, H=sqrt(R^2-v^2),
D: center (K/2-u,h), with square axes (1,1)/sqrt(2),(-1,1)/sqrt(2),
-1/2<h<1-H,                  H>5/4.
```

Thus A is radial, B has its unique lower outer circle vertex, and D is
the diagonal unit transmitter touching their facing sides. No other
contact, force, orientation or graph hypothesis is needed.

**Theorem.** Every packing containing this three-square core has at most
nine unit squares, including these three.

The [same-sign normalization](ONE_DIAGONAL_TWO_SIDE_SAME_SIGN_NORMALIZATION.md)
proves these hypotheses, after reflection if needed, for the entire
radial-D-endpoint class of LSLSLD. The theorem is also available whenever
another family supplies the same three-body geometry. It does not
classify the surrounding graph one loaded count at a time.

## 2. One compact two-parameter domain covers every core

The exact identity

```text
H^2=2*K*(u-2)+9/4
```

and h lying strictly in both endpoint side intervals imply H<3/2,
hence u<2. The imported lower window gives

```text
u^2=R^2-1/4 >=5841/1600 > (191/100)^2,
u>191/100>19/10.
```

Write

```text
tau=(h+1/2)/(3/2-H),       0<tau<1,
h=-1/2+tau*(3/2-H).
```

Every physical core is consequently covered by
19/10<=u<=2, 0<=tau<=1. The boundary u=2 gives H=3/2 and h=-1/2;
it may be retained in the capacity cover even though it is not a strict
D side-interior contact.

For any unit-square center z in the disk, the farthest vertex bound gives

```text
R^2 >= |z|^2+|z|+1/2,
(|z|+1/2)^2 <= R^2-1/4 = u^2,
|z| <= u-1/2.
```

This sharper center-radius bound keeps its dependence on u. Replacing it
with a single larger radius unnecessarily enlarges the uncovered domain.

The three center boxes on any parameter rectangle are the outward
interval evaluations of

```text
c_A=(1/2-u,0),
c_B=(K-u-1/2,1/2-H),
c_D=(K/2-u,-1/2+tau*(3/2-H)).
```

Their orientations remain fixed, including D's diagonal axes.

## 3. Exact physical-square and slot exclusions

For a candidate center z, distance strictly below 1/2 from one of the
three existing closed physical squares is impossible: the added square's
open inscribed disk of radius 1/2 would meet that square's interior.

For an axis-aligned existing square centered at c, this distance squared
is

```text
max(|z_x-c_x|-1/2,0)^2 + max(|z_y-c_y|-1/2,0)^2.
```

For D first use the two fixed diagonal coordinates
((z_x-c_x)+(z_y-c_y))/sqrt(2) and
((z_y-c_y)-(z_x-c_x))/sqrt(2). The same formula applies.

For a closed candidate rectangle and a closed core center box, bound
each absolute coordinate by its largest endpoint value. If the sum of
the two truncated squares is strictly below 1/4, the entire candidate
rectangle is excluded uniformly for every actual center in that core box.
Interval bounds for the diagonal-coordinate factor 1/sqrt(2) are rounded
outward. Losing the correlation between the two coordinates only weakens
an exclusion.

Each retained slot is a disk of radius 499/1000, and hence diameter
998/1000<1. It contains at most one added unit-square center, because
distinct packed squares have disjoint open inscribed disks and center
distance at least one.

Thus a finite cover by excluded cells and six such slots proves the
theorem: at most six further squares can join the three existing ones.

## 4. Complete parameter and center tables

Let S=2^44=17592186044416. Parameter paths start from

```text
u in [33425153484390/S,2],       tau in [0,1].
```

The lower endpoint rounds 19/10 outward. At each path step bisect u if
10*width(u)>=width(tau), otherwise bisect tau. Take the integer midpoint
rounded downward in units 1/S. A 0 selects the lower closed child and
a 1 the upper closed child. Closed children share their bisecting boundary.

The complete frontier consists of the 42 capacity rows below and one
radius-impossible row. The paths are prefix-free and form a full binary
tree, maximum depth ten. In the sole excluded row, path
`0101101010`, u's upper endpoint is below 191/100. Section 2 excludes
every physical parameter in it. No unresolved parameter row remains.

In the following table u and tau endpoints are integers divided by S;
each slot pair is divided by 1000. All six disks in a row have radius
499/1000. The final column gives the number of center-cover leaves.

| Parameter path | u endpoints / S | tau endpoints / S | Six slot centers / 1000 | Cover cells |
| --- | --- | --- | --- | ---: |
| `0000` | [33425153484390,33864958135500] | [0,4398046511104] | (-591,992) (1037,370) (330,1163) (373,477) (-150,1019) (882,865) | 142 |
| `000100` | [33425153484390,33645055809945] | [4398046511104,6597069766656] | (1037,416) (-637,1041) (229,1083) (408,497) (838,1038) (-187,1088) | 149 |
| `000101` | [33645055809945,33864958135500] | [4398046511104,6597069766656] | (1037,416) (-637,1041) (229,1083) (408,497) (838,1038) (-187,1088) | 138 |
| `00011` | [33425153484390,33864958135500] | [6597069766656,8796093022208] | (680,1141) (-1025,-1025) (-647,1126) (1150,481) (502,390) (0,1084) | 140 |
| `0010` | [33864958135500,34304762786611] | [0,4398046511104] | (739,952) (-663,1178) (120,1302) (1150,435) (600,450) (-87,800) | 137 |
| `00110` | [33864958135500,34084860461055] | [4398046511104,8796093022208] | (-148,1108) (1112,396) (853,1051) (450,375) (258,1033) (-662,1010) | 221 |
| `00111` | [34084860461055,34304762786611] | [4398046511104,8796093022208] | (-148,1108) (1112,396) (853,1051) (450,375) (258,1033) (-662,1010) | 166 |
| `0100` | [33425153484390,33864958135500] | [8796093022208,13194139533312] | (680,1141) (-1025,-1025) (-647,1126) (1150,481) (502,390) (0,1084) | 149 |
| `010100` | [33425153484390,33645055809945] | [13194139533312,15393162788864] | (58,1131) (-800,-1125) (1100,504) (-623,1171) (706,1066) (530,520) | 112 |
| `010101` | [33645055809945,33864958135500] | [13194139533312,15393162788864] | (58,1131) (-800,-1125) (1100,504) (-623,1171) (706,1066) (530,520) | 127 |
| `01011000` | [33425153484390,33535104647167] | [15393162788864,16492674416640] | (58,1131) (-800,-1125) (1100,504) (-623,1171) (706,1066) (530,520) | 111 |
| `01011001` | [33535104647167,33645055809945] | [15393162788864,16492674416640] | (58,1131) (-800,-1125) (1100,504) (-623,1171) (706,1066) (530,520) | 105 |
| `0101101000` | [33425153484390,33480129065778] | [16492674416640,17042430230528] | (58,1131) (-800,-1125) (1100,504) (-623,1171) (706,1066) (530,520) | 111 |
| `0101101001` | [33480129065778,33535104647167] | [16492674416640,17042430230528] | (58,1131) (-800,-1125) (1100,504) (-623,1171) (706,1066) (530,520) | 110 |
| `0101101011` | [33480129065778,33535104647167] | [17042430230528,17592186044416] | (58,1131) (-800,-1125) (1100,504) (-623,1171) (706,1066) (530,520) | 109 |
| `01011011` | [33535104647167,33645055809945] | [16492674416640,17592186044416] | (58,1131) (-800,-1125) (1100,504) (-623,1171) (706,1066) (530,520) | 112 |
| `010111` | [33645055809945,33864958135500] | [15393162788864,17592186044416] | (58,1131) (-800,-1125) (1100,504) (-623,1171) (706,1066) (530,520) | 126 |
| `011` | [33864958135500,34304762786611] | [8796093022208,17592186044416] | (680,1141) (-1025,-1025) (-647,1126) (1150,481) (502,390) (0,1084) | 191 |
| `100` | [34304762786611,34744567437721] | [0,8796093022208] | (-148,1108) (1112,396) (853,1051) (450,375) (258,1033) (-662,1010) | 227 |
| `101` | [34744567437721,35184372088832] | [0,8796093022208] | (-199,1010) (1125,278) (903,937) (429,346) (227,1192) (-681,1151) | 256 |
| `110000` | [34304762786611,34524665112166] | [8796093022208,10995116277760] | (-148,1108) (1112,396) (853,1051) (450,375) (258,1033) (-662,1010) | 189 |
| `110001` | [34524665112166,34744567437721] | [8796093022208,10995116277760] | (-148,1108) (1112,396) (853,1051) (450,375) (258,1033) (-662,1010) | 196 |
| `1100100` | [34304762786611,34524665112166] | [10995116277760,12094627905536] | (-148,1108) (1112,396) (853,1051) (450,375) (258,1033) (-662,1010) | 247 |
| `11001010` | [34304762786611,34414713949388] | [12094627905536,13194139533312] | (-148,1108) (1112,396) (853,1051) (450,375) (258,1033) (-662,1010) | 233 |
| `11001011` | [34414713949388,34524665112166] | [12094627905536,13194139533312] | (-148,1108) (1112,396) (853,1051) (450,375) (258,1033) (-662,1010) | 184 |
| `110011` | [34524665112166,34744567437721] | [10995116277760,13194139533312] | (-148,1108) (1112,396) (853,1051) (450,375) (258,1033) (-662,1010) | 204 |
| `11010000` | [34304762786611,34414713949388] | [13194139533312,14293651161088] | (680,1141) (-1025,-1025) (-647,1126) (1150,481) (502,390) (0,1084) | 130 |
| `11010001` | [34414713949388,34524665112166] | [13194139533312,14293651161088] | (-148,1108) (1112,396) (853,1051) (450,375) (258,1033) (-662,1010) | 186 |
| `11010010` | [34304762786611,34414713949388] | [14293651161088,15393162788864] | (680,1141) (-1025,-1025) (-647,1126) (1150,481) (502,390) (0,1084) | 129 |
| `11010011` | [34414713949388,34524665112166] | [14293651161088,15393162788864] | (-148,1108) (1112,396) (853,1051) (450,375) (258,1033) (-662,1010) | 305 |
| `110101` | [34524665112166,34744567437721] | [13194139533312,15393162788864] | (-148,1108) (1112,396) (853,1051) (450,375) (258,1033) (-662,1010) | 266 |
| `11011000` | [34304762786611,34414713949388] | [15393162788864,16492674416640] | (680,1141) (-1025,-1025) (-647,1126) (1150,481) (502,390) (0,1084) | 133 |
| `110110010` | [34414713949388,34469689530777] | [15393162788864,16492674416640] | (680,1141) (-1025,-1025) (-647,1126) (1150,481) (502,390) (0,1084) | 131 |
| `110110011` | [34469689530777,34524665112166] | [15393162788864,16492674416640] | (425,370) (-725,1225) (1113,253) (231,1226) (950,940) (-217,1017) | 238 |
| `11011010` | [34304762786611,34414713949388] | [16492674416640,17592186044416] | (680,1141) (-1025,-1025) (-647,1126) (1150,481) (502,390) (0,1084) | 132 |
| `110110110` | [34414713949388,34469689530777] | [16492674416640,17592186044416] | (680,1141) (-1025,-1025) (-647,1126) (1150,481) (502,390) (0,1084) | 131 |
| `110110111` | [34469689530777,34524665112166] | [16492674416640,17592186044416] | (425,370) (-725,1225) (1113,253) (231,1226) (950,940) (-217,1017) | 313 |
| `11011100` | [34524665112166,34634616274943] | [15393162788864,16492674416640] | (425,370) (-725,1225) (1113,253) (231,1226) (950,940) (-217,1017) | 247 |
| `11011101` | [34634616274943,34744567437721] | [15393162788864,16492674416640] | (425,370) (-725,1225) (1113,253) (231,1226) (950,940) (-217,1017) | 187 |
| `11011110` | [34524665112166,34634616274943] | [16492674416640,17592186044416] | (425,370) (-725,1225) (1113,253) (231,1226) (950,940) (-217,1017) | 314 |
| `11011111` | [34634616274943,34744567437721] | [16492674416640,17592186044416] | (425,370) (-725,1225) (1113,253) (231,1226) (950,940) (-217,1017) | 189 |
| `111` | [34744567437721,35184372088832] | [8796093022208,17592186044416] | (792,944) (-652,1121) (1238,371) (134,1373) (-62,737) (675,350) | 381 |

The complete corner inequalities and every center-leaf path are in
[radial_diagonal_three_body_certificate.json](radial_diagonal_three_body_certificate.json).
There are **7,604 center leaves** in total, maximum binary depth 22.
For each row, take the center-domain square [-rho,rho]^2,
rho=u_upper-1/2. Bisect the longer coordinate interval, x first on ties.
The paths cover its entire closed square. A leaf is assigned to:

* Outside: its minimum squared norm exceeds rho^2.
* Physical square A, B or D: the uniform distance bound from Section 3
  is strictly below 1/4.
* One of the six slot disks: its maximum squared distance from that
  rational slot center is strictly below 249001/1000000.

Every comparison is a strict integer inequality after clearing positive
powers of S and rational denominators. Core center boxes are recorded
and independently recomputed. The data includes every chosen slot,
parameter endpoint, box and leaf; an optimizer supplies none of the
proof premises.

All additional centers lie in the appropriate row's six disks. Therefore
the total is at most 3+6=9, proving the theorem uniformly over the whole
parameter domain and all orientations of every additional square.

## 5. Reproduction and arithmetic scope

```text
node research/ten/check_radial_diagonal_three_body.mjs
node research/ten/check_radial_diagonal_three_body_60bit.mjs
```

Both arithmetic/checking bodies were executed in the session's V8 runtime
and verify all 42 capacity rows, the excluded radius row, all 7,604 strict
leaf inequalities and both levels of coverage. The unavailable execution
workspace prevented running the Node entry points.

The primary backend uses 44-bit direct quotient intervals and integer
square roots. The second uses 60-bit reciprocal intervals and a separately
implemented integer square root. The logical predicates are shared.
Coverage uses Kraft/prefix arithmetic and full binary tries respectively.
The second backend reconstructs the recorded 44-bit subdivision exactly
before lifting endpoints, so integer midpoint rounding cannot change the
geometry represented by a path. Numerical proposals are not premises.

## 6. Whole LSLSLD closure

At most one D endpoint can be radial, by the same-sign normalization.
The two endpoint-circle classes are exhaustive:

| D endpoint circle features | Exclusion |
| --- | --- |
| Both unique | [Complete source closure](STRICT_VERTEX_SOURCE_CAPACITY_CLOSURE.md), including E_A/E_B and every V_V source circle feature |
| One radial | This three-body capacity theorem, after reflection and relabeling |

Both retain all S slides and all nonnegative radial circle-load splits.
Thus every ambient ten-square completion of the whole signature LSLSLD
is excluded. The stable entry **C20-M06-L03-B02-T02** is closed by this
assembly. The fixed master becomes **277/336 hand closed; 59 open**;
the cycle subledger becomes **250/279 closed; 29 open**.

This does not prove the unrestricted n=10 lower bound. The 59 remaining
fixed families and the separate equality/Lean gates remain as recorded
in the master ledger.


## 7. Shared corollary: no radial endpoint on any loaded-to-loaded D path

The conclusion is independent of endpoint degree and the rest of the graph.

**Corollary.** In the jointly selected certificate of a hypothetical
strictly subcritical ten-packing, every D transmitter whose two neighbors
are loaded has unique geometric circle vertices at both neighbors.
This includes every loaded count and every allowed branching count.
It excludes a geometric two-circle endpoint even if one of its two circle
coefficients is zero.

By Section 4 of
[generic normal selection](GENERIC_CONTACT_NORMAL_SELECTION.md), both D
contacts are relative interiors of the neighbor sides. Those neighbor
frames are therefore parallel and the strip normalization u+v=K applies,
without requiring either neighbor to have degree two.

The endpoints' horizontal centers have strict opposite signs: containment
gives u,v<=sqrt(R^2-1/4)<33/16 and hence u,v>K-33/16>4/3.
Thus a geometric two-circle endpoint must have its two circle vertices on
its outer vertical side, rather than a horizontal side whose center would
have horizontal coordinate zero.

Suppose the left endpoint is radial. Then
u=sqrt(R^2-1/4)>19/10, while v=K-u<61/40.
Both endpoints cannot be radial, since that would give u+v>19/5>K.
The right endpoint has

```text
H^2=R^2-v^2 > ((79)^2-(61)^2)/1600=63/40>25/16.
```

Reflect vertically so its unique circle vertex is lower.
The common D height belongs strictly to both loaded sides, so
-1/2<h<1-H and H<3/2. All hypotheses of Section 1 hold.
Its capacity bound contradicts the ambient ten-packing.
Relabeling covers a radial right endpoint.

The corollary does not apply when a D path has an unloaded retained
neighbor. No count is claimed closed solely because this shared
multiplicity class has disappeared.


The subsequent [opposite-sign capacity theorem](OPPOSITE_DIAGONAL_CAPACITY.md)
now also excludes every loaded D pair with unique circle vertices of
opposite transverse signs. Every selected loaded-to-loaded D path therefore
has unique same-sign endpoint circle vertices. Endpoint degrees and the
remaining graph stay unrestricted.
