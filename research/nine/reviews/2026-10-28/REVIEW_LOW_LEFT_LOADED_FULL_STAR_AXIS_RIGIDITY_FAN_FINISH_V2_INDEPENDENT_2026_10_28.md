# Independent review: low-left loaded full-star axis rigidity

Date: October 28, 2026 UTC. Reviewer: fan_finish_v2.

**Verdict: PASS for the entire stated arbitrary-degree theorem.**
This is a full independent mathematical review of the frozen source,
not a review of a numerical sample, an application to one selected
pose, or a declaration that a graph family is closed. The target was
not edited.

## 1. Exact source and complete direct-read ledger

The reviewed source is
`LOW_LEFT_LOADED_FULL_STAR_TWO_AXIS_NORMALS_FORCE_ALIGNED_UNIT.md`,
9147 bytes, 267 lines, SHA256
`2fae45df2a6736976a899f8502049b761fecba7d6fcdbde5cd9c42bae0e92b95`.

I read every section of that source and the complete contents of both
of its direct inputs:

| Direct input | SHA256 | Reviewed operative use |
| --- | --- | --- |
| LOADED_TWO_APPLICATION_FULL_STAR_BOUNDARY_FREE_CONCURRENCE_DICHOTOMY.md | 3808b2b767a9e15c7270b50c4fbbb434ae0d69fe42c567d4da01f7d167f7fa78 | Complete physical corner classification, arbitrary-degree grouping at two identical actual application values, nonparallel proper concurrence, and the inside conclusion only in the unique physical-corner row |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original positive contact forces and actual support applications, complete force and torque balances, and all original circle coefficients |

The first input has 23353 bytes and 555 lines; the second has 17993
bytes and 399 lines. The declared radius lies strictly between
sqrt(2) and 1+sqrt(2), as required by the concurrence theorem: the
lower endpoint has R squared equal to 17/4, and the upper bound
1105/256 is less than (1+sqrt(2)) squared.

## 2. Statement and original-object audit

The theorem assumes one actual loaded unit T in the original packing,
with max x=epsilon and max y=-f, where

    0<=epsilon<1/60, 89/120<f<1,
    R^2=(2+epsilon)^2+1/4<=1105/256.

Every original positive pair normal is North or East, with a positive
total in each direction. The true degree is arbitrary. Those are
strong, explicit hypotheses on the whole original star, not merely
on two selected contacts.

The conclusion is the complete actual aligned square

    [epsilon-1,epsilon] times [-f-1,-f]

and its unique physical boundary corner identity. No neighbor is
deleted, no circle load is suppressed, and no virtual force is
introduced. All other units and all neighbor degrees and loads remain
unrestricted. I checked that the proof uses arbitrary-degree grouping
only when a tilted square makes all East applications literally the
same vertex Q and all North applications literally the same vertex P.
It makes no such assertion in the final aligned case.

## 3. Complete two-corner physical-mask exclusion

In the two-physical-corner row the full mask classification gives the
actual radial square [d,d+1]e+[-1/2,1/2]Je. Its center coordinates are
strictly negative from the stated maxima, so e=(-s,-c), with c,s>0.
The exact maxima give

    epsilon=c/2-d*s, f=d*c-s/2,
    c+s=(f-epsilon)/(d-1/2),
    c-s=(f+epsilon)/(d+1/2).

Both denominator estimates have the correct direction:
f-epsilon>29/40 and d-1/2<31/60 yield c+s>87/62>7/5;
f+epsilon>89/120 and d+1/2<91/60 yield c-s>89/182>12/25.
The resulting lower bound 1369/625 for
(c+s)^2+(c-s)^2 contradicts its exact value 2.

This argument is entirely physical geometry. It excludes the whole
two-corner mask before any inside-concurrence claim, including both
individual circle-coefficient-zero endpoints. It does not confuse a
one-point load mask with a one-corner physical mask.

## 4. Tilted full-star concurrence and exhaustive unique corner cover

Every nonaligned unit with the two stated maxima has the frame

    Q=(epsilon,-f-s), u=(-c,s), v=(-s,-c),
    P=Q+u, c,s>0, c^2+s^2=1.

The North and East supports are the unique actual P and Q. Their full
positive sums alpha and beta have nonparallel directions, and the
unchanged force equation is F_T=(-beta,-alpha). The nonparallel
arbitrary-degree clause of the direct concurrence theorem therefore
gives the actual intersection

    K=(epsilon-c,-f-s)=t*F_T, t>0.

In particular c>epsilon. Since the entire two-corner mask has already
been excluded, the legitimate unique-corner inside clause yields
K=theta*Z with 0<theta<=1. Thus the proof neither imports the false
general inside-concurrence assertion for a two-corner mask nor applies
a true-degree-two lemma to a higher-degree object.

I checked the exhaustive physical corner cover: Q.v is positive
because it equals c*f+(c-epsilon)*s. Orthogonality gives the same
strict increase on adding v from Q+u. Hence neither Q nor Q+u can be
the physical circle corner; the only possibilities are the actual
Z_0=Q+v and Z_1=Q+u+v. No reflection or frame reselection removes a
mask row.

## 5. Independent audit of both continuous corner rows

For Z_0, the two coordinates of K=theta*Z_0 give precisely

    (s-c)*(f+s)=c*(c-epsilon)>0.

This forces s>c. If c<=1/2, then
1-c^2-s*c>c^2, because 2c^2<=1/2 and s*c<c<=1/2.
The displayed identity is consequently impossible in that interval.
Thus 1/2<c<s, so c+s>(1+sqrt(3))/2>27/20. The actual vertical
coordinate of Z_0 exceeds 251/120 in magnitude, hence exceeds 25/12.
The exact reserve (25/12)^2-1105/256=55/2304 is positive. This excludes
the full Z_0 row.

For Z_1, the radial identity is

    s*(f+c+s-epsilon)=c*(c-epsilon),
    theta=(f+s)/(f+c)<=1.

The second relation forces s<=c. If c<=9/10, the normalized arc
c in [1/sqrt(2),9/10] gives s>2/5 and c+s>13/10. Together with
f-epsilon>29/40, the left side exceeds 81/100, whereas the right
side is at most c^2<=81/100. Thus c>9/10.

If s<=1/3, the right side exceeds 8/9-1/60=157/180, while the left
side is less than 7/9. Hence s>1/3; combining this with c>9/10 also
makes s<c strict. These are whole-interval deductions, not numerical
angle samples.

For f>=4/5, normalization gives c+s>(sqrt(8)+1)/3>5/4. The actual
corner therefore has |x|>37/30 and |y|>17/10. Their squared sum is
397/90, whose exact excess over 1105/256 is 1091/11520.

For f<=4/5, s<=3/8 would make the right side of the radial identity
greater than 809/960 and its left side less than 783/960. Thus s>3/8,
and c+s>(sqrt(55)+3)/8>13/10. The actual corner has |x|>77/60 and
|y|>197/120. Their squared sum is 62525/14400, whose exact excess
over 1105/256 is 59/2304.

Both contradictions are strict, and both f intervals contain f=4/5.
The split therefore leaves no gap at its shared endpoint. These two
rows exhaust every tilted unit after the complete mask classification.

## 6. Aligned conclusion, endpoints, and scope

After excluding all tilts, the prescribed actual coordinate maxima
give the claimed aligned square exactly. Its center coordinates are
both strictly negative, so its unique farthest corner is
(epsilon-1,-f-1). The original circle load has positive total, hence
that physical corner lies on the original circle. This proves the
stated identity R^2=(1-epsilon)^2+(1+f)^2 without normalizing away any
circle coefficient.

The review covers epsilon=0, the full half-open epsilon interval,
every allowed f, both physical mask types, individual zero circle
weights in the excluded two-corner type, all actual support means,
and arbitrary true positive degree. The source makes no conclusion
about a whole graph family or any computational-certificate count.

**Adoption recommendation:** accept the frozen target as a complete
local arbitrary-degree rigidity theorem, subject to the separate root
review. This review used hand algebra and full source reading only;
no Lean/Lake run, computational certificate, numerical pose search,
CI, source modification, metadata change, staging, commit, or remote
action was performed.
