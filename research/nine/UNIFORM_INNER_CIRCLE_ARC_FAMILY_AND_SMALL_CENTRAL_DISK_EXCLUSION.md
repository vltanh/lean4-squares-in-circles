# A continuous inner-circle arc theorem and a smaller central-disk obstruction

Date: October 28, 2026 UTC. Author: root continuation.
Read base: `eff516e8751adb49ef7d2b2ce51064021a003dd1`.

**Status: complete proposed force-free hand theorem, submitted for a
separate full independent review. No original gate is changed.**

The argument covers a continuous interval of inner-circle radii at once.
It distinguishes an angular-measure statement, which includes a weak
clearance endpoint, from a connected-arc statement, which requires strict
clearance. This distinction matters when the circle is tangent to an
outer side of the square. No physical normal, force, mean, or square is
changed, and no computational exclusion certificate is a premise.

## 1. Exact statements

Put

    Q = 1105/256,
    v = sqrt(Q/2),
    r_- = (v-1)/sin(pi/8)
        = sqrt(2*(2+sqrt(2)))*(v-1),
    r_+ = 1/(2*sin(pi/8)).

The constants satisfy

    6/5 < r_- < 157/128 < 13/10 < r_+ < 4/3.             (1)

Let r be any one radius in the entire open interval

    r_- < r < r_+,       h = r-1.                         (2)

Let E be any actual closed unit square contained in D_sqrt(Q), with
arbitrary orientation and actual center c. All distances and circles
below refer to the original common origin O.

**Theorem A, including the weak clearance endpoint.** If

    dist(O,E) >= h,

then the angular measure of `int(E) intersect {|p|=r}` is strictly
greater than pi/4. This actual intersection need not be connected at
the weak clearance endpoint.

**Theorem B, with connectedness.** If `dist(O,E)>h`, the same actual
intersection is one connected open arc longer than pi/4. It contains
the radial center point `r*c/|c|` in E's open interior.

There is no boundary-contact, load, degree, stress, owner, selected
normal, or graph premise. In particular E may be any original completion
unit. The same r is used for every unit in a packing comparison.

**Theorem C, uniform consequences for retained physical units.**

1. At most seven interior-disjoint units in D_sqrt(Q) can have
   distance at least h from O.
2. Every nine-unit packing in that disk has at least two distinct
   actual units at distance strictly less than h from O.
3. No actual square in such a nine-unit packing can contain the entire
   closed disk D_h, even with tangencies on its own sides.

In particular all these conclusions hold with the explicit rational
choice

    r = 157/128,       h = 29/128.                        (3)

Thus the central-disk obstruction improves the older radius 1/4 to
29/128. It is a necessary condition for every original packing, not a
claim that one of its unresolved graph/load families is excluded.

**Theorem D, the exact critical clearance.** The three packing
conclusions of Theorem C also hold at

    h_* = r_- - 1.

At this one inner-circle radius, a single square can have arc length
exactly pi/4, so Theorem A's strict single-square statement does not
extend. Section 11 classifies all such equality squares and proves
that eight of them cannot coexist. In particular every original
nine-unit packing has two distinct actual units with distance strictly
less than h_*, and no actual unit contains the closed disk D_(h_*).

## 2. Exact constant comparisons

Write `E_*=(2+sqrt(2))*(v-1)^2`, so `r_-^2=2*E_*`.
The elementary bounds used throughout are

    7/5 < sqrt(2) < 99/70 < 3/2,
    1/sqrt(2) > 7/10,
    117/80 < v < 2351/1600 < 3/2.

The relevant positive squared reserves are

    2-(7/5)^2 = 1/25,
    (99/70)^2-2 = 1/4900,
    Q/2-(117/80)^2 = 247/12800,
    (2351/1600)^2-Q/2 = 2201/2560000.

Consequently

    E_* > (17/5)*(37/80)^2 = 23273/32000,
    r_-^2 > 23273/16000 > 36/25,

where the last reserve is 233/16000. On the other hand

    E_* < (239/70)*(751/1600)^2 < (157/128)^2/2,

whose final reserve is exactly 11919/716800000. This proves the
first three comparisons in (1). The comparison 157/128<13/10 is
immediate.

For the two comparisons involving r_+, use

    sin(pi/8)^2 = (2-sqrt(2))/4.

First `sin(pi/8)<5/13`, because `sqrt(2)>238/169`; the latter
follows by squaring, with reserve 478/28561. Hence r_+>13/10.
Second `sin(pi/8)>3/8`, because `sqrt(2)<23/16`, with squared
reserve 17/256. Hence r_+<4/3. All quantities being squared are
positive. This completes (1) without decimal estimates.

Two more comparisons will be useful:

    E_* > (17/5)*(9/20)^2 = 1377/2000 > 933/1600,       (4)
    cos(pi/8) < 3/4 + 1/(4*sqrt(2)).                    (5)

For (4), `v>29/20` follows from `v>117/80>29/20`;
the final rational reserve is 843/8000. For (5), both sides are
positive and the difference of their squares is

    (3-2*sqrt(2))/32 > 0.

## 3. The complete own-frame domain

Use E's own two axes, reflect them, and exchange them if necessary
so the coordinates of its actual center satisfy x>=y>=0. These
coordinate choices are made separately for each actual square; no
common orientation of different squares is inferred. Set

    a=x+1/2, b=y+1/2, A=a-1, B=b-1,
    E=[A,a] times [B,b],
    a>=b>=1/2, q=a^2+b^2<=Q.                            (6)

The last inequality is exactly the farthest-corner containment
condition. The nearest point to O has coordinates

    (max(A,0),max(B,0)).                                 (7)

The following cases exhaust (6): a>r; a<=r with B>0; and the
possible weak-clearance residue a<=r with B<=0.

## 4. The whole inner-face case a>r

Here A>r-1>1/5. The full domain gives

    0<A<41/40,          -1/2<=B<1/2,
    A^2+B^2 < 2081/1600 < 36/25 < r^2.                  (8)

For the upper A bound use
`a<=sqrt(Q-1/4)=sqrt(1041)/16<81/40`; the last squared
reserve is 219/6400. For B use b<=v<3/2.

### 4.1. One fixed-q convexity argument covers every orientation

Define

    E_0 = A^2+B^2+sqrt(2)*A*B.

At fixed q, with t=a+b, direct expansion gives

    E_0 = (1-1/sqrt(2))*q + t^2/sqrt(2)
          -(2+sqrt(2))*t + 2+sqrt(2).                   (9)

This is convex in t. Over the complete fixed-q interval
`a>=b>=1/2`, its maximum occurs at one of b=1/2 or a=b.
Enlarging to that entire interval is legitimate even when an
endpoint does not itself satisfy a>r or the clearance premise.

At b=1/2, put `A_0=sqrt(q-1/4)-1`. Since the original a>r,

    1/5 < A_0 < 41/40.

Therefore

    E_0 = A_0^2+1/4-A_0/sqrt(2)
        < A_0^2+1/4-(7/10)*A_0 <= 933/1600 < E_*.

The quadratic is convex; its endpoint values are 3/20 and
933/1600. The final comparison is (4).

At a=b=w=sqrt(q/2), the original q>r^2+1/4 and r>6/5
give `3/4<w<=v`. Consequently

    E_0=(2+sqrt(2))*(w-1)^2 <= (2+sqrt(2))*(v-1)^2=E_*.

Indeed `(w-1)^2` is convex on [3/4,v], and its upper-end
value is larger because v>29/20>5/4. Thus (9), both endpoints,
and (2) prove uniformly

    E_0 <= E_* = r_-^2/2 < r^2/2.                       (10)

This single continuous comparison is independent of any force
or contact-feature partition.

### 4.2. The actual connected arc has length greater than pi/4

Set

    alpha=acos(A/r), beta=asin(B/r),
    gamma=asin(min(b/r,1)).

Because E lies in the positive x half-plane, a>r, and (8)
holds, its actual closed circle intersection is exactly the interval

    [beta, min(alpha,gamma)].                            (11)

The corresponding open-interior intersection is the open interval.
In particular beta>-alpha, and no omitted second component exists.

Inequality (10) is equivalent to

    (sqrt(2)*A+B)^2 < r^2-B^2.

It follows that

    A < r*cos(beta+pi/4).

The comparison is valid even if sqrt(2)*A+B is negative.
Since |B|<=1/2 and r>6/5, one has |beta|<pi/4, so cosine
is decreasing on the relevant interval. Thus

    alpha-beta > pi/4.                                  (12)

If b<=r, the other possible interval length satisfies

    gamma-beta = asin(b/r)-asin((b-1)/r)
               >= 2*asin(1/(2*r)) > pi/4.               (13)

The difference is nondecreasing for b>=1/2, since
`b>=|b-1|`; a derivative comparison proves this on the interior
and continuity includes b=r. The final strict comparison is
exactly r<r_+.

If b>r, then gamma=pi/2 and beta<pi/4, again giving (13).
Both candidates in (11) therefore give one open arc longer than
pi/4. No clearance assumption was used within this case.

## 5. The whole outer-face case a<=r with B>0

Here

    0<B<=A<=h=r-1<1/3,
    k^2=A^2+B^2 >= h^2,

where the weak inequality is precisely the assumed clearance.
The actual closed intersection is the interval

    [max(acos(a/r),asin(B/r)),
     min(acos(A/r),asin(b/r))].                          (14)

We prove that all four candidate upper-minus-lower differences
exceed pi/4; this also proves that the interval exists and is
the entire intersection. The two opposite-face differences have
the strip bound (13). The inner-inner difference is at least

    pi/2-2*asin(h/r) > pi/4,

because r<4/3 gives h/r<1/4<sin(pi/8).

For the remaining outer-outer difference define

    L(A,B)=asin((1+A)/r)+asin((1+B)/r)-pi/2.

At fixed k^2, vary from A=B=k/sqrt(2) to the actual A>=B.
This entire analytic path remains in 0<A,B<=h. In its interior,
the derivative's sign is that of

    (A-B)*[(A+B-h)^2+(k^2-h^2)*(A+B+1)],                 (15)

which is nonnegative. To check (15) explicitly, compare the
positive derivative terms and square. Their difference has factor

    (A-B)*[(A+B)^2+(k^2-2*h-h^2)*(A+B)+k^2],

and the bracket is exactly the one in (15). This uses
`r^2=1+2*h+h^2`. Continuity includes A=h or B=h, where an
individual derivative may be infinite. Hence

    L(A,B) >= 2*asin((1+k/sqrt(2))/r)-pi/2
           >= 2*asin((1+h/sqrt(2))/r)-pi/2.              (16)

The final argument equals

    (1+h/sqrt(2))/r
      = 1/sqrt(2)+(1-1/sqrt(2))/r
      > 3/4+1/(4*sqrt(2)) > cos(pi/8),                  (17)

by r<4/3 and (5). Thus (16) is strictly greater than pi/4,
even when k=h. All inverse-sine arguments belong to [0,1]
because k/sqrt(2)<=h; all comparisons use its increasing branch.

The four strict comparisons prove that the open version of (14)
is one connected arc longer than pi/4, including the weak
clearance endpoint in this case.

## 6. The exact tangent-side residue at weak clearance

Suppose a<=r and B<=0. Formula (7) and the clearance premise
give

    r-1 <= dist(O,E)=max(A,0) <= r-1.

Since r>1, this forces

    a=r, A=r-1=h, -1/2<=B<=0, b=B+1 in [1/2,1].        (18)

This is impossible under strict clearance, and it is the only
additional case needed by Theorem A.

For (18), put beta=asin(B/r) and gamma=asin(b/r). The inner
x face does not cut the interval between these two angles, since

    h^2+b^2 < 1/9+1=10/9 < (6/5)^2 < r^2.

The outer face x=r is tangent to the circle at angle zero.
Consequently the actual open-interior intersection is exactly

    (beta,gamma) with the point 0 removed if it belongs. (19)

When B=0, zero is already an endpoint. When B<0, removing it
does split the interval into two open arcs. No connectedness is
claimed in that subcase. A single point has zero angular measure,
so (13) gives the full measure of (19) as

    gamma-beta >= 2*asin(1/(2*r)) > pi/4.                (20)

This proves the weak-endpoint assertion without incorrectly
assigning a tangent point to the open square or taking a limit
of connected intersections.

## 7. The radial center point under strict clearance

Sections 4--6 already prove Theorem A and the connected-arc part
of Theorem B. Suppose now dist(O,E)>h. The nearest-point support
of this convex unit has distance dist(O,E), and its projection
halfwidth is at least 1/2. Thus

    |c| > h+1/2 = r-1/2.                                (21)

Every contained unit also satisfies

    |c|^2+|c|+1/2 <= Q,
    |c| < 91/60,

because the farthest own corner gives the first inequality and
the excess at 91/60 is 31/57600. Since r>6/5, this implies
`|c|<r+1/2`. Together with (21),

    ||c|-r| < 1/2.

The point `r*c/|c|` therefore lies in the actual open incircle
of E, hence in the unique open arc already proved. This step
does not assert that the whole arc is centered at c.

## 8. Count, central disk, and the original radius-window consequence

For different interior-disjoint units, their actual open-interior
intersections with one fixed circle are disjoint measurable subsets.
If eight such units all had distance at least h, Theorem A would
give total angular measure strictly greater than `8*(pi/4)=2*pi`,
impossible. This proves Theorem C(1), and C(2) follows for nine
units by counting their actual distinct bodies. Connectedness is
not needed in this summation, so (19) causes no exception.

Suppose one actual unit K in a nine-unit packing contained the
closed disk D_h. Its open interior contains the open disk of
radius h, including when a side of K is tangent to D_h. Every
other closed unit avoids int(K): a point of another closed unit
inside int(K) has arbitrarily nearby interior points of that unit,
contradicting interior nonoverlap. Hence each of the other eight
units has distance at least h. The preceding count excludes them.
This proves C(3) at the full weak central-disk containment endpoint.

In the entire original radius window `79/40<=R<=sqrt(Q)`, any
physical boundary unit has distance at least `R-sqrt(2)` from O,
using one of its actual circle corners and its unit diameter.
In particular

    dist(O,E) >= R-sqrt(2) > 79/40-3/2=19/40>h,

since h<1/3. Thus the two near units in C(2) are both physically
circle-clear. If the original selected force certificate is also
present, they consequently have zero total circle load. This is
an implication from proved physical clearance; zero selected load
is not being substituted for physical clearance.

The explicit rational choice (3) is valid by (1). It yields

    at least two actual units meeting the open disk D_(29/128),
    no actual unit containing the closed disk D_(29/128).

Both statements apply simultaneously to every original graph,
all physical masks and all force selections, with all nine units
retained. A smaller positive component alone cannot borrow the
nine-unit conclusion after its completing units are removed.

## 9. Why both radius endpoints are genuine obstructions

The interval (2) has actual unit-square obstructions at both of
its endpoints, not just failures of a polynomial estimate.

At r=r_-, take the contained square

    E=[v-1,v] times [v-1,v].

Its far corner lies on the circle of squared radius Q. Because
`r_-<157/128<7/5<v`, neither outer face cuts its inner-circle
intersection. The intersection is the single open arc

    (asin((v-1)/r_-), acos((v-1)/r_-))
      = (pi/8, 3*pi/8),

of length exactly pi/4. Its distance from O is
`sqrt(2)*(v-1)>1/2>r_--1`; for example v>29/20 and
sqrt(2)>7/5 give the first comparison. Thus even strict clearance
does not restore the strict arc inequality at this endpoint.

At r=r_+, take

    E=[1/2,3/2] times [-1/2,1/2].

It lies in the smaller disk of squared radius 5/2, and has
distance 1/2 from O, greater than r_+-1 because r_+<4/3.
Its inner-circle intersection has exact angular length

    2*asin(1/(2*r_+))=pi/4.

The inner x face and outer x face do not cut this interval.
Indeed r_+>13/10 implies `sqrt(r_+^2-1/4)>1/2`, and
r_+<4/3<3/2. This verifies the second endpoint obstruction.

These examples show that neither endpoint can be added to the
stated continuous strict-arc family. They do not claim that the
near-unit count or the sharp nine-square packing theorem is attained
by either single-square example.

## 10. Literal relation to the existing uniform kernels

The older `GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md`, Section 1,
proves a connected open radius-5/4 arc longer than pi/4 for every
actual unit with distance strictly greater than 1/4. Its conclusion
is exactly the r=5/4 instance of Theorem B, since (1) gives
`r_-<5/4<r_+`. Its original force-free domain and radial-center
conclusion are preserved. Its original source bytes and historical
review pins remain unchanged; this manuscript is a stronger additional
kernel, not a silent source substitution.

Section 2 of that source proves height greater than 3/10 for every
actual width-one channel in its exact entire positive-cycle scope.
Its whole extra squares therefore satisfy Theorem B simultaneously
for every r in `[157/128,13/10]`. In particular its exact original
channel callers may use the radius-13/10 circle while retaining the
same strict clearance. Any bound on the available free interval still
requires that caller's full occupied-crosscut routing; this theorem
does not supply a pocket-capacity bound by itself.

The previous central-quarter-disk obstruction follows immediately
from C(3), while (3) improves its excluded central disk by the exact
amount `1/4-29/128=3/128`. No rooted origin-location hypothesis,
missing contact, or true degree equation is inferred merely from
this improved metric constant. No whole original fine or coarse gate
is credited without its separate complete caller.

The mathematical proof above is self-contained. The following source
is referenced only to identify the exact older exports and literal
channel premises that the stronger kernel preserves:

| Existing source | SHA256 | Exact relation |
|---|---|---|
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb | Its Section 1 is the r=5/4 strict-clearance instance; its Section 2 supplies h>3/10 at its unchanged actual channel hypotheses |

There is no numerical angle mesh, pose exclusion, coefficient table,
inverse-angle evaluation, changed normal, dropped force, Lean build,
CI, workflow, remote mutation, or original-ledger edit in this source.

## 11. Equality rigidity extends the packing obstruction to the exact critical radius

This section is a subsequent complete extension by the same author.
The first independent review pinned the version without Theorem D;
that old review is not a review of the extended bytes. The extension
requires a fresh current-source review before adoption.

Set r=r_- and h=h_*=r_--1. Keep the same full actual unit domain
and assume dist(O,E)>=h. Every constant comparison in Sections 2--7
still holds except the final strict inequality in (10), which becomes

    E_0 <= E_* = r^2/2.                                  (21)

The two strip bounds remain strict because r_-<r_+. The whole
outer-face argument remains strict because r_-<4/3. The tangent-side
residue still has strict angular measure greater than pi/4. The
inner-face argument now gives angular measure at least pi/4.
Consequently every actual unit of clearance at least h_* has

    angular measure of int(E) intersect {|p|=r_-} >= pi/4. (22)

### 11.1. Complete equality classification in the one-unit bound

If equality holds in (22), the preceding strict cases force a>r.
The strip candidate in (11) is also strictly longer than pi/4.
Hence equality requires

    alpha-beta=pi/4,
    E_0=E_*.

The fixed-q endpoint b=1/2 has E_0<E_* by (4). The quadratic
in t in (9) is strictly convex, so any interior t between the
two distinct fixed-q endpoints is strictly below the larger
endpoint value. Therefore E_0=E_* can occur only at a=b=w.
In that case

    (w-1)^2=(v-1)^2,       3/4<w<=v.

Since v>29/20, the alternative w=2-v is less than 3/4 and
is impossible. Thus w=v. Conversely the actual square

    S_0=[A,v] times [A,v],       A=v-1,

does have equality, as proved in Section 9. Therefore every
equality unit is a rigid rotation about O of this exact square.
Its actual open radius-r_- intersection is the single arc
`(pi/8,3*pi/8)` in that square's displayed coordinates. Its
arc midpoint is its radial center direction. Reflections produce
the same rotated family and no additional geometry.

This classifies equality in the entire one-unit measure theorem,
including all original orientations and the weak clearance endpoints.

### 11.2. Eight equality units cannot coexist

Suppose eight actual interior-disjoint units all had distance at
least h_*. Their actual circle intersections are disjoint, and
(22) assigns each measure at least pi/4. Their total measure
cannot exceed 2*pi. Thus every unit has equality in (22), and
all eight are the classified rotations of S_0.

Each of their single open arcs has length pi/4. Their eight
midpoint directions have successive cyclic gaps at least pi/4;
otherwise two open arcs overlap. The gaps sum to 2*pi, so
every gap is exactly pi/4. Rotate all actual data about O to
make one unit S_0. Its clockwise adjacent unit is then precisely
`Rot(-pi/4) S_0`, because the equality square is fixed by its
radial midpoint direction.

Put K=1+sqrt(2) and consider the actual point

    P=(K*A,A).

The inequalities

    A < K*A < v                                         (23)

hold. The first is immediate. For the second, `K*(v-1)<v`
is equivalent to `v<1+1/sqrt(2)`, which follows from
`v<3/2<1+1/sqrt(2)`.

Consequently P lies in the relative interior of the bottom
side of S_0. In the own coordinates of the clockwise rotated
unit, obtained by rotating P back by pi/4, it has coordinates

    ((P_x-P_y)/sqrt(2), (P_x+P_y)/sqrt(2))
       = (A,K*A).

By (23), this is in the relative interior of that unit's left
side. These two actual sides are not parallel. More explicitly,
for all sufficiently small positive eta, the point

    P + eta*(2,1)

is inside both actual units: its second S_0 coordinate increases
from A, while its first rotated coordinate increases from A by
eta/sqrt(2); all other coordinate margins in (23) stay strict.
This contradicts interior nonoverlap.

Thus eight far units at the critical clearance cannot coexist.
Any larger family would contain such an eight-unit subfamily.
There are at most seven actual units with distance at least h_*.

### 11.3. Exact critical near-unit and central-disk consequences

Counting the original nine physical bodies now gives at least
two distinct units with distance strictly less than h_*. If an
actual unit contained the closed disk D_(h_*), all eight other
closed units would avoid its open interior and have distance at
least h_*, exactly as in Section 8. The just-proved eight-unit
obstruction excludes this possibility, including tangent sides
of the alleged central unit.

In the original radius window the two near units are physically
circle-clear, since the unchanged boundary-distance estimate in
Section 8 is strictly greater than h_*<1/3. All nine original
units and their masks remain; no selected-force equation is used.

Theorem D therefore strengthens the rational radius-29/128
obstruction to the exact constant

    h_* = sqrt(2*(2+sqrt(2)))*(sqrt(1105/512)-1)-1.

The single-square equality at r_- remains real. The packing
count survives that endpoint because the entire equality geometry
is incompatible across eight actual squares, not because a weak
arc inequality was mislabeled strict. No numerical pose cover or
extra computational certificate is introduced by this endpoint
argument, and it gives no whole original graph/load closure on
its own.
