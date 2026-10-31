# Full independent review of the aligned-low LTAC.S upper-C placement

Date: October 28, 2026. Reviewer: triangle_bridges.

**Decision: ACCEPTED, unchanged, for the entire original C-upper/A-lower
placement, including its full exact continuous two-target certificate.**
I read the entire root-authored proof and code, rederived the complete
physical segment argument, checked every operative input at its literal
degree and force scope, reproduced the author certificate, and separately
reconstructed every terminal box with exact Fraction arithmetic and
128-bit outward radicals. No correction is requested.

| Reviewed source | SHA-256 |
| --- | --- |
| `HOUSE_LOWER_TAC_S_ALIGNED_UPPER_C_EXCLUSION.md` | `b773da381ac721c0f3c06083c9da6258ea1142353fd4a6e000edaff1d8398125` |
| `certificates/aligned_low_s_upper_c_visibility_separation.py` | `d57e7506d4f6e1dd92c991c8579fcfcd03377703863b0d42d50f417267fe2c4c` |

This is a full separate independent review of a root-authored source.
It does not count the root author's computation as an independent
acceptance. The repeated degree-free x>t calculation was also used
in the complementary upper-A proof; I independently rederived it in
my complete 98355c7e review and again checked its exact use here.
No lower A2 equation is substituted for the original A3.

## 1. Original graph and exact local-input transfers

The source retains the original edges

    AT, DT, AD, AB, BC, CD, BL,

with the genuine S leaf at B and positive house loads exactly at
T,A,C. The actual degrees remain B3,A3,D3,T2,C2,L1. In particular
B is physically clear, A retains its third force, and D retains
its roof force. The physical argument uses D as an actual convex
unit square; it never changes D into a degree-two transmitter.
All nine original physical units remain, and the uniform R>2
input has its literal same-nine scope.

The complete aligned strict-low chart is

    2<R<sqrt(17)/2, 14/15<d<1, a=1-d,
    B=[-a,d] times[-g,h], g=1-h,
    29/50<h<2/3, 1/3<g<21/50,
    P_C=(-a,h), n=(-c,s), j=(-s,-c),
    c,s>0, c^2+s^2=1, c/s=(x+a)/h,
    P_A=(x,-g), 3/10<x<=d.

The original B-to-A normal is South, and C owns its incoming n.
I reread the full local Sections 1--6 of 02fd37d9 while auditing
both original placements. Their true-root force and torque cover,
physical lower tilt, and finite singleton ownership selection use
only the actual three-force root and boundary status of its two
neighbors. They do not need degree two at A or an all-boundary
cycle. The later whole-C5 path is not imported. The reflection is
of the entire actual packing and keeps this placement's labels.

I also checked the complete force-free Sections 1--3 of c32b99ad.
They give, at arbitrary lower degree,

    A=(x,-g)+[0,1](b,-t)+[0,1](-t,-b),
    b,t>0, b^2+t^2=1,
    Z_A=(x+b-t,-g-b-t)=(X,-Y), X^2+Y^2=R^2.

Every other physical lower corner is strictly inside the original
circle. No b/t ordering is part of that physical input. Its later
loaded-two continuation is correctly not used at A. Thus every
physical mask, including a potentially zero individual weight,
has been covered before the unique-corner conclusion.

## 2. The whole lower A is east of O, without an A2 hypothesis

The X>0 calculation is valid for all b,t. If X<=0, then t>b and
|X|<t-b because x>0. Using b^2+t^2=1,

    R^2<(t-b)^2+(g+b+t)^2
       =2+2g(b+t)+g^2
       <2+297/250+441/2500<4.

The final strict reserve is 1589/2500. If x<=t instead, X>0
gives X<=b. The largest eigenvalue of b^2+(b+t)^2 is
(3+sqrt(5))/2<21/8. The resulting upper radius comparison is

    R^2<21/8+297/250+441/2500=4-53/5000.

Therefore x>t. I checked both radical bounds and both exact
reserves. This proof uses only the actual frame, circle point and
root geometry; it establishes the whole-square facts

    every point of A has x-coordinate at least x-t>0,
    every point of A has y-coordinate at most -g.

In particular x+b>t+b>1>d, since b,t are strictly positive and
b^2+t^2=1. The actual lower edge therefore crosses the real
leaf's inner line and gives the unchanged screen

    (d-x)t >= (h-1/2)b.

This excludes x=d. The source's uniform t>2/25 proof is complete
without ordering b and t: b<7/10 gives t>sqrt(51)/10>7/10;
otherwise the screen with d-x<7/10 and h-1/2>2/25 gives
t>2/25. The scalar's enlarged domain thus includes both lower
tilts, including the cases t>b omitted by the other placement's
C2-specific argument.

## 3. The full upper C2 star and both unchanged return points

The upper physical frame is

    C=P_C+[0,1]n+[-rho,1-rho]j,
    N=ac+hs, K=hc-as=xs,
    W=K+rho, delta=1-rho,
    R^2=(N+1)^2+W^2.

The unique upper circle corner and its radius equation are physical
consequences of the local chart. The rho>7/8 radius-triangle proof
in 843e9afc precedes any upper degree-two equation. Its premise
N^2+K^2=a^2+h^2<101/225 is literal here. The full upper C2
equation then has a circle resultant with strictly negative j
component, while its incoming B normal is -n. Hence the outgoing
C-to-D normal has positive j component and is nonparallel to the
incoming force. Conditional Lemma 1.1 of 7d0c4092 applies at
exactly this scope, with no requirement that D be boundary.

The original radial concurrence has unchanged coordinates

    (N+lambda,-K),
    lambda=(K-N*rho)/(K+rho)>=0.

The full near/owned/far feature cover of 843e9afc now applies
literally to C2. I checked its complete far-return proof: the actual
minimum support would exceed 27/25>d, so that feature fails for
every contained neighbor. The source does not import that theorem's
later boundary-neighbor-only return exclusions. The complete two
survivors have the original applications

    Q(u)=P_C+u*n+delta*j,
    u=0 at the near vertex,
    u=lambda for the whole owned-j side mean.

The owned-side coordinate is forced by the unchanged proper line.
Neither a positive proper length nor a nonzero lambda is assumed;
lambda=0 and delta=0 are retained throughout.

The new uniform concurrence bound is sound. Since x<=d<1,
K=xs<h<2/3, and N>=hs=(h/x)K>=(29/50)K. Therefore

    lambda<=(197/400)*K/(K+7/8)
            <=197/925<1/4.

I independently computed 1-(29/50)(7/8)=197/400, the value
at K=2/3, and the final strict gap 137/3700. These are comparison
bounds on the original lambda, not choices of its value.

## 4. Complete actual segment obstruction, with all crossing endpoints

For either actual Q define

    A0=a+x-t>0,
    L=u*c+delta*s>=0,
    H=1+u*s-delta*c>7/8.

The exact point is Q=(-a-L,H-g). Let P be D's original AD
application. The whole-square A bounds give P_x>=x-t>0 and
P_y<=-g. Both P and Q belong to the same actual unit D, so
their closed segment is in D and their distance is at most sqrt(2).
The segment cannot enter int(B): any point of a full-dimensional
closed square in that open set has nearby interior square points
there. This applies even if the segment is an edge of D and needs
no stress assumption at D.

I checked the complete crossing argument separately from the scalar:

* If L=0, positivity of c,s implies u=delta=0, so Q=(-a,h).
  Every segment from Q to the allowed P immediately enters int(B).
  This excludes the coincident corner endpoint directly.
* If L>0, the segment crosses x=-a strictly between Q and P.
  When Q_y<=h, that crossing is strictly below h because P_y<=-g.
  A crossing above -g would immediately enter int(B), so it must
  be at or below the lower-left root corner.
* When Q_y>h and P_x>=d, the horizontal displacement is at least
  1+L and the vertical displacement is greater than one. Their
  squared sum exceeds two, contradicting the original unit diameter.
  Thus P_x<d in this case. A crossing at or above the top root
  edge then necessarily crosses y=h with x strictly between -a
  and d before reaching P. This also enters int(B). A crossing
  between the two horizontal edges is already forbidden. Again it
  must be at or below y=-g.

These cases include a contact exactly at either left root corner,
P on an A side endpoint, Q on the original owned C side endpoint,
and a segment tangent to the lower-left corner. No assumed D frame
or shorter force equation is hidden in this necessity.

Writing the crossing parameter as L/(P_x+a+L), its allowed height
is exactly equivalent to

    (P_x+a+L)H <= L(Q_y-P_y).

Since Q_y>P_y and their distance is at most sqrt(2), and since
P_x+a>=A0, every actual D must satisfy

                         (A0+L)H<=sqrt(2)*L.

The directions of both inequalities and the signs of H,L are
correct. This is the only geometric necessity passed to the
continuous certificate.

## 5. Complete scalar domain, operations and safe restrictions

I read the full closed enlargement in the manuscript and checked its
literal caller. It retains d in[14/15,1], h in[29/50,2/3],
t in[2/25,1], b=sqrt(1-t^2), the strict R^2>4 condition,
and both actual circle equations. It also retains

    3/10<=x<=d, x>=t,
    (d-x)t>=(h-1/2)b,
    rho in[7/8,1], lambda in[0,197/925].

There is no b>=t premise. The positive denominators are the actual
normal length, X and W; positivity is certified before division.
The dependent X identity is only intersected with another enclosure
of the same actual X. No mean or circle equation is replaced by a
free scalar interval disconnected from its original formula.

The author code uses only exact Fraction arithmetic and integer
square root. Its addition, sign, product, square and reciprocal
rules are outward enclosures for all signs. The 48-bit dyadic
radical floor and ceiling are correct, including exact-square and
formal-negative-lower-bound endpoints. A nonpositive upper X^2
bound excludes the explicit X>0 premise. A negative upper W^2
bound excludes a real radical; a denominator not yet positive
causes subdivision. The R^2 upper-bound rejection correctly retains
the original strict R^2>4 domain and excludes only boxes wholly
outside it.

The other rejection guards are exactly the stated x interval,
x>=t, actual leaf screen, upper mean and proper-concurrence ranges.
The screen rejects only when its entire upper bound is negative,
so a true leaf-corner equality remains. All rho and lambda endpoints
are retained by closed intersections. The author's equivalent
positive normal formulas c=1/sqrt(1+(h/w)^2) and its reflection
for s are valid on the entire positive domain.

## 6. Both targets and the complete quadratic lower envelope

For either original u in{0,lambda}, the target is

    G(u)=(A0+u*c+delta*s)(1+u*s-delta*c)
                     -(99/70)(u*c+delta*s).

My separate sparse polynomial expansion gives exactly

    G(u)=G(0)+B0*u+c*s*u^2,
    B0=s*A0+(1-99/70)c+delta(s^2-c^2).

The alternative product/factorized forms in the code are identical.
Taking the greater of their interval lower endpoints is therefore
valid. If g0,b0,q0 bound G(0),B0,c*s below, then q0>0 and
u>=0 give the whole-interval lower polynomial
g0+b0*u+q0*u^2. Its minimum on the retained lambda interval is
at the vertex -b0/(2q0), clipped to that closed interval. This
establishes a lower bound for every actual lambda, rather than
testing a configuration at the minimizer. Both coefficients whose
lower bounds are multiplied by u or u^2 have nonnegative multipliers.
The code finally takes the lesser of its certified bounds for G(0)
and G(lambda); neither original return point is omitted.

The initial success test is positive. The final exact run separately
checks that every successful terminal bound is greater than the
claimed 1/1000000. This check is present and passes. No weaker
positive conclusion is silently used as the uniform bound.

## 7. Author reproduction and separate full 128-bit verification

Running the exact frozen author checker reproduces the entire tree:

| Certificate quantity | Exact reproduced value |
| --- | ---: |
| Visited nodes | 38,701 |
| Terminal boxes | 19,351 |
| Strict two-target certificates | 17,438 |
| Radius exclusions | 234 |
| Proper-concurrence exclusions | 226 |
| Actual leaf-screen exclusions | 1,024 |
| Actual x-interval exclusions | 359 |
| Upper physical mean exclusions | 70 |
| Maximum binary depth | 18 |
| Unresolved boxes | 0 |

Its canonical terminal digest is exactly
`c8abdb83f97e69fd9445b3733df9fd2fcd77eaf357a69eea23fe63d3800397ad`.
The full minimum fraction, not a rounded decimal, is preserved in
the copied author output and compared strictly to 1/1000000.

My separate checker imports no author code or peer arithmetic.
It accepts only the terminal binary paths and claimed margins as
data to verify. A new trie rejects duplicate leaves, a leaf with
descendants and any missing sibling. Starting at the full original
box, it independently reconstructs every normalized-width midpoint
split and verifies both closed children have the exact parent
endpoints. Thus the paths are proved to cover the entire rectangle,
including every splitting plane. The node identity and the exact
Kraft sum one are also checked.

The independent arithmetic uses an immutable interval class, exact
Fractions and 128-bit outward radicals. Its c,s enclosure uses the
two monotonic component endpoints: the first component increases
with its own positive argument and decreases with the other one.
This is mathematically the same exact normal as the source but a
separately implemented enclosure, without an imported normalization
helper. At every leaf the checker recomputes both circles, every
original guard, all actual means, both target expressions and the
complete lower quadratic.

All 19,351 leaves certify again with the same counts of admissible
targets and exclusion reasons. Every independent target margin is
at least its author counterpart, and the independent uniform minimum
is strictly greater than 1/200000, hence greater than 1/1000000.
All 38,701 nodes and depth 18 are independently reconstructed. This
is a complete continuous check of every original terminal, not a
sampling argument or a verification only of the successful leaves.

The full independent data, including every exact margin, are saved:

| Independent artifact | SHA-256 |
| --- | --- |
| `certificates/review_lower_tac_upper_c_visibility_triangle_bridges.py` | `417a832c7ba660850b1a2f9abf92dd2ea68b5504536875d772f41ad168575180` |
| `checkpoints/triangle_bridges_lower_tac_upper_c_independent_scalar_2026_10_28.json` | `6753484f79acdf7ffaeabb3d9b738f13496eca37ce5383aff17a4981637a7745` |
| `checkpoints/triangle_bridges_lower_tac_upper_c_physical_checks_2026_10_28.json` | `c62068ade4a9a81a0fceabc24e38133d050702f0306bfae2ae8e814f5c073281` |
| `checkpoints/triangle_bridges_lower_tac_upper_c_author_reproduction_2026_10_28.json` | `a960dd73c0ed3084e4dfe4cf34a3f749e2a2ca2fef962e247c46cc3ffc405691` |

The physical record also independently checks all nine literal
input pins, nine exact rational values and both polynomial identities.

## 8. Complete contradiction and precise accepted scope

For either original return point the full certificate gives
G(u)>1/1000000. Because L>=0 and sqrt(2)<99/70, with exact
squared reserve 1/4900,

    (A0+L)H>(99/70)L>=sqrt(2)L.

This contradicts the actual D segment necessity. The L=0 case
already has its separate physical exclusion, and is also consistent
with the strict scalar inequality. Both actual C return points,
every original side mean and proper-distance endpoint, both lower
A tilt directions and every D frame are covered. A remains true
loaded3, D true unloaded3, T true loaded2, and every original
physical unit and corner mask remains.

The complete root-authored upper-C placement is independently
accepted unchanged. This record does not itself assert a whole
LTAC.S parent or change an original fine/coarse flag. No canonical
movement, post-extraction selection, shortened force star, numerical
pose, Lean/CI, shared ledger edit or remote mutation was used.
