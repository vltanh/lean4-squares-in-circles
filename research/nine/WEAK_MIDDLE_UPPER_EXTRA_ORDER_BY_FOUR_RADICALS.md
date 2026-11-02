# An upper central extra cannot lie below P: a four-radical reduction

November 2, 2026. Physical reduction for a complete finite hand/table
proof in the original `010/11` caller. **The complete finite forest has passed independent exact replay.**
Its sixteen roots cover all eight original sign charts and both left
position intervals. Floating optimization is not a proof premise.
No Lean, Lake, or CI.

## 1. Original caller and the ordering target

Retain all nine original physical units A,B,C,D,L,P,R,F,G in the closed
disk of squared radius Q=1105/256, with disjoint open interiors. Retain
the actual outer main comparisons A/B and C/D, the weak main middle
comparison B/C, the two weak short comparisons L/P and P/R, all five
original horizontal center-cone comparisons, and all independent frames.

Use the unconditional upward routing of
`WEAK_MIDDLE_TWO_WEAK_SHORT_ROUTING_AND_HIGH_FLOOR.md`. Thus P is above
both inner mains, L is above B, and R is above C. Suppose P has whole
floor at most 1/10. The desired conclusion is:

> If any original unit U distinct from P is central, |xU|<=29/60, and
> is above both inner mains, then yU>yP. This includes U=L or U=R
> whenever that selected shoulder is central.

The existence of such a U and the good-floor consequence for U are
separate obligations. Neither is assumed in this reduction. In
particular U is never assigned a new cone comparison with L or R.
If U=L, its original L/P pair may appear both in the two-step height
argument and in the later selected-pair rows. Both are necessary
consequences of that same original pair. The minimization below bounds
the actual U before removing its parameters; it does not choose a
replacement frame. No step requires U distinct from L or R.

Reflect horizontally, reversing the two marked chains together if
needed, so x=xP>=0. Write zL=-xL and zR=xR. Every outsider has absolute
horizontal center less than 13/12. Each marked cone gap is larger than
707/1000: the two disjoint radius-one-half center disks give center
distance at least one, hence a cone's horizontal gap at least 1/sqrt(2),
and (707/1000)^2<1/2. Consequently

    0<=x<1129/3000, zR>=7/10, zL>19/60.             (1)

All bounds used below are closed enlargements. Equal heights yU=yP are
impossible because

    |xU-xP|<=29/60+1129/3000=2579/3000<1.

Thus a counterexample has the strict ordering yM<yU<yP for either inner
main M. Choose M on U's own horizontal half-plane, with either choice
allowed at xU=0. Put

    h=hM, g=1/(4h), eta=h+g-1, p=hP, ell=29/60.

The outer-link endpoint reserve and main-center bands give

    1/2<=h<13/20, eta<=V<1/30,
    g-1/60<|xM|<61/60-h,
    yM>m(h):=g-199/120+(32/9)eta.                 (2)

The same original M supplies h, g, eta, its center band and its lower
height. Nothing here uses an actual middle edge or the old inner-width
bound 31/60.

## 2. Eliminate the position and frame of U analytically

Write z=|xU| and u=hU. The two true horizontal gaps obey

    |xU-xM|<=d1(z):=max(z-g+1/60,61/60-h-z),
    |xP-xU|<=d2(z):=x+z.                           (3)

At physical points the interval for |xM| is nonempty, so d1 is
nonnegative. Throughout the complete parameter range,
d1<=31/60 and d2<=2579/3000<1.

For any two physical unit squares of coordinate halfwidths v,w, the
smaller support of every genuine separating side axis is at least
1+|v-w|. This is the accepted physical support inequality used in
`WEAK_MIDDLE_UPPER_CENTRAL_WHOLE_FLOOR.md`, Section 2. It therefore
implies their center distance is at least 1+|v-w|, for every pair of
independent chiralities. Applied to the original M/U and U/P pairs in
their strict vertical order, it yields

    yP > m(h)
         +sqrt((1+|h-u|)^2-d1(z)^2)
         +sqrt((1+|p-u|)^2-d2(z)^2).               (4)

This pair consequence includes all physical separator owners; it does
not assert vertical projection separation or a new center cone.

First fix u. At physical points the two affine arguments
z-g+1/60 and 61/60-h-z have sum 1/30-eta>0. Their maximum therefore
equals the maximum of their absolute values. Thus the first radical in
(4) is the minimum of the two concave functions obtained by using the
squares of these two affine arguments. Their absolute values are below
one, so the radicals are defined on the full interval. A minimum of
concave functions is concave. The second radical is also concave in z.
Thus their sum has its minimum at z=0 or z=ell.

Next fix either endpoint z. Below min(h,p), both support arguments
1+|h-u| and 1+|p-u| decrease as u increases; above max(h,p), both
increase as u increases. Hence a minimum occurs in the interval
between h and p. On that interval both support arguments are affine
in u, and s -> sqrt(s^2-D^2) has second derivative
-D^2/(s^2-D^2)^(3/2)<=0. The sum is therefore concave in u there and
has its minimum at u=h or u=p. This reasoning covers h=p and either
zero horizontal gap.

Some points in the eventual closed h root have eta>1/30, for which the
inner-center band would be inverted and this concavity identity need
not describe a physical pair. Formula (5) is merely a harmless scalar
extension at those nonphysical points; the separate necessary row
1/30-eta already rejects them. The geometric implication above is used
only with the original nonempty physical band.

Set Delta=|h-p|. The original U has therefore been eliminated: define

    d1e=max(e-g+1/60,61/60-h-e), d2e=x+e,

    T0(e)=sqrt(1-d1e^2)+sqrt((1+Delta)^2-d2e^2),
    T1(e)=sqrt((1+Delta)^2-d1e^2)+sqrt(1-d2e^2),

    Pminus=m(h)+min(T0(0),T1(0),T0(ell),T1(ell)).  (5)

Every counterexample satisfies yP>=Pminus. Every radical in (5) has a
strictly positive radicand on the complete root. Since the bound was
derived from the actual two pairs before minimizing, no replacement U
or independently chosen pair frame has entered the physical caller.

## 3. Complete seven-scalar necessary system

Keep exactly the original P,L,R frames and the original endpoint
resources in Sections 2, 4, 5 and 6 of
`WEAK_MIDDLE_TWO_WEAK_SHORT_MAINHEIGHT_QUARTER.md`. The variables are

    (tP,tL,tR,x,zL,zR,h),

with tP,tL,tR in [0,1], x in [0,1129/3000], zR in
[7/10,13/12], h in [1/2,13/20], and zL in [19/60,3/5] or
[3/5,13/12]. Retain all eight independent sign triples. These are
sixteen complete closed roots, including all shared faces and all
aligned original frames.

Use (5) for P's initial lower height. Its initial upper height is

    Pplus=min(p+1/10, UsP(x,p,kP)).                 (6)

The two signed corner bounds, original endpoint lower contributions
AL,AR, the five endpoint/shoulder resource rows, the raised original
endpoint rectangles, and the two shoulder lower heights are unchanged
from that common reduction. In the lower zL root the valid lower
height is -9/20; in the raised root use its original inset-axis formula.
For R use the raised formula throughout. In particular one retained
P frame occurs in both original L/P and P/R comparisons.

One may apply the following necessary interval contractions before
forming the pair rows. They only use the two original cones:

    DL=zL+x, DR=zR-x,
    Pminus=max(Pminus,Lminus-DL,Rminus-DR),
    Pplus=min(Pplus,Lplus+DL,Rplus+DR),
    Lminus=max(Lminus,Pminus-DL),
    Lplus=min(Lplus,Pplus+DL),
    Rminus=max(Rminus,Pminus-DR),
    Rplus=min(Rplus,Pplus+DR).                    (7)

The updates in (7) are in the displayed order. They remain valid when
an already necessary height interval is empty; such a point is rejected
by its height row.

The 21 necessary scalar rows are:

* Pplus-Pminus, Lplus-Lminus, Rplus-Rminus;
* 1/30-eta;
* the five original endpoint/shoulder resource rows;
* the six original physical pair rows for L/P;
* the six original physical pair rows for P/R.

The pair rows use 707/1000 in place of the weaker 7/10 lower cone span
in the common reduction. Every pair still keeps the exact original
relative-frame support, all four actual owner axes with both directions,
the original weak-bit halfwidth bound, and the original inset cone span.
All inequalities are necessary, so a complete strict negative cover of
these rows proves the ordering target without additional hypotheses.

## 4. Complete exact forest and accepted arithmetic

The separate directed-integer checker reconstructs every original rational
root, midpoint and necessary scalar. The completed forest has
**16,294,696 strict leaves**, **32,589,376 nodes**, maximum depth **51**,
and no unresolved frontier. Its least positive reserve is

    3186498 / 2^48 > 0.

The complete per-chart counts are:

| (sP,sL,sR) | Left interval [19/60,3/5] | Left interval [3/5,13/12] |
|---|---:|---:|
| (−,−,−) | 120,521 | 1,089,753 |
| (−,−,+) | 33,127 | 527,791 |
| (−,+,−) | 89,663 | 647,895 |
| (−,+,+) | 28,681 | 263,900 |
| (+,−,−) | 40,031 | 529,905 |
| (+,−,+) | 127,069 | 7,941,874 |
| (+,+,−) | 49,841 | 393,012 |
| (+,+,+) | 243,565 | 4,168,068 |

The canonical lossless certificate is
`computer_assisted/upper_extra_order_cover.json.gz`, with SHA-256

    87ddb6261f35520aff9c63cdad27272302e15eec52883d4b8e9bd85420d29cab.

Its decompressed JSON SHA-256 is

    975608457d51a20609156b1b6efa1ebc0b2b1db059abfc961b2ba5efdfb8bfaf.

The standalone `verify_upper_extra_order_exact.cpp` and its Python wrapper
import no producer arithmetic. They reconstruct exact rational box
coordinates and enclose every operation using directed integer intervals
with denominator 2^48, signed 128-bit products, and integer square roots.
The physical caller and concavity eliminations were separately reviewed
in `UPPER_EXTRA_ORDER_INDEPENDENT_PHYSICAL_REVIEW.md`. That review's
then-pending arithmetic obligation is discharged by the complete replay
record `upper_extra_order_cover_independent_exact_replay.json`.

The replay was performed on the complete raw JSON. The saved gzip
identity record proves exact byte equality with that replayed payload;
compression introduces no additional arithmetic assumption. The raw
replay, byte-binding record and rejection controls are retained. The
current checker and certificate hashes match those acceptance records.
No repeated replay or human/kernel verification is claimed here.

Every original counterexample to the ordering statement supplies a point
of a complete root with all 21 scalars nonnegative. Its strict interval
leaf excludes that point. Therefore every original upper central unit
U distinct from P is strictly higher than P, including a central selected
L or R. The theorem does not assert that U has a good whole floor; that
requires a separate proof preserving every needed original pair.
