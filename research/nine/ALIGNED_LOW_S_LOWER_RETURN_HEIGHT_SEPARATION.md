# The actual low aligned S-root boundary returns have separated heights

Date: October 28, 2026. Author: rooted_blocks.

**Status: complete exact scalar theorem, frozen for full independent
review.** Root supplied the first continuous rational interval proof
of the target inequality while I developed the physical caller. The
checker below is a separate reconstruction, with different interval
representations, normal enclosures and radical precision. This
contribution is explicit; root's verification is not substituted for
the requested separate peer reviews.

The theorem concerns the two original circle equations and actual
means. There is no sampled configuration or numerical maximization
premise.

## 1. Entire enlarged scalar domain

Let

    14/15 <= d <= 1,       29/50 <= h <= 2/3,
    a=1-d, g=1-h,         2/25 <= t <= 5/7,
    b=sqrt(1-t²),         b>=t.

Define the actual radius value and the lower far-corner coordinates by

    R²=(d+1)²+1/4,
    Y=g+b+t,
    X=sqrt(R²-Y²)>0,
    x=X-b+t.

Require the complete following restrictions:

    3/10 <= x <= d,       x>=t,
    (d-x)t >= (h-1/2)b.                              (1)

Put

    w=x+a,  ell=sqrt(w²+h²),
    c=w/ell, s=h/ell,
    N=ac+hs, K=xs,
    W=sqrt(R²-(N+1)²),
    rho=W-K,             7/8 <= rho <= 1,
    delta=1-rho,
    tau=b(xY/X-g),        0 <= tau <= 1.              (2)

The square roots in (2) are required to be real. In fact W>0
follows from rho>=7/8 and K>0. Every denominator is positive:
h>=29/50, w>=3/10, ell>0 and X>0.

**Theorem.** Throughout this entire closed enlargement of the actual
physical domain,

                    tau*b-delta*c > 1/25000 > 0.     (3)

The original physical caller uses strict d<1, h<2/3, x<d,
x>t, rho>7/8 and 0<tau<1. Those stricter facts are not needed
by this scalar theorem. The two coupled circle equations in (2)
are retained. A lower-circle estimate alone is not asserted to
imply (3).

## 2. Exact interval operations

The full arithmetic proof is the standalone file

`certificates/aligned_low_s_lower_return_height_separation.py`

SHA-256

`bd92d1895f240805a78ea5160b0b7ed56f6948a4ec6ce88ff870bb55a6472f15`.

It uses only Python integers, Fraction, and integer square root for
mathematical operations. There are no floating-point numbers in the
code. An interval is an immutable pair of rational endpoints. Addition
and negation use endpoint arithmetic; multiplication uses the minimum
and maximum of all four endpoint products. Squaring uses zero as the
lower bound exactly when the interval contains zero. Division is used
only for a strictly positive denominator interval, via its reversed
reciprocal endpoints. Intersections preserve every common real value.

For a nonnegative rational z and S=2^64, the lower square-root
endpoint is

    floor(sqrt(z*S²))/S,

computed by integer square root after exact integer division. The
upper endpoint is the same rational when its square is exactly z,
and otherwise one lattice step larger. Thus each radical interval
contains the full real radical range. If a formal radicand interval
straddles zero, its lower endpoint is clamped to zero; the actual
nonnegative radicand remains included.

These operations are outward enclosures. Correlation is never used
to shrink an interval without an explicitly retained identity or
inequality from (1)--(2).

## 3. Safe enclosures and every possible rejection

Start from the full parameter rectangle

    [14/15,1] times [29/50,2/3] times [2/25,5/7]       (4)

in the order (d,h,t). Each box is processed as follows.

1. Enclose b=sqrt(1-t²), and intersect its interval with
   [t_lower,1]. This retains b>=t. An empty intersection
   cannot contain an admissible point.

2. Enclose R²,Y and X²=R²-Y². If its upper bound is nonpositive,
   the required X>0 is impossible. Otherwise enclose its positive
   square root, clamping only a possibly negative formal lower
   endpoint to zero.

3. Enclose x=X-b+t and intersect with
   [max(3/10,t_lower),d_upper]. These are necessary consequences
   of (1). Then intersect the current X interval with the enclosure
   of x+b-t. This uses the original exact identity and is valid
   after the previous contraction of x. Any empty intersection
   excludes only inadmissible points.

4. Enclose the left side minus the right side of the actual leaf
   screen in (1). A strictly negative upper bound excludes the
   whole box from the admissible domain. No weak equality is
   rejected by that test.

5. Use the direct common normalization ell=sqrt(w²+h²) and
   enclose c=w/ell,s=h/ell, then N,K and W². A negative upper
   bound for W² excludes the box. Otherwise enclose W and
   intersect W-K with [7/8,1]. An empty intersection violates
   the actual upper mean range.

6. Enclose delta and tau from (2), intersecting tau with [0,1].
   An empty intersection excludes the original mean range; both
   endpoints are kept. Enclose tau*b-delta*c. A strictly positive
   lower bound certifies that box. The final full run checks that
   every such lower bound is, in fact, greater than 1/25000.

If a needed denominator interval is not yet strictly positive, or no
rejection or strict target bound has been obtained, the box is split.
No assertion about the sign of an actual denominator is substituted
for a certified interval denominator during arithmetic.

For clarity, a contraction such as x>=t_lower is only a necessary
bound; it does not identify x with t or impose a point value for
either parameter. Using independent interval copies of c and s can
only enlarge the later enclosures. All exact normal and circle
relations hold for every original point in the retained domain.

## 4. Whole-rectangle coverage and the exact finite result

An unresolved box is bisected at the rational midpoint of the
coordinate with greatest width divided by that coordinate's original
width in (4). Ties use the first coordinate. Both closed children
are retained, so their union is the entire parent, including the
splitting plane. A binary path records each child choice.

The exact run terminates with

| Quantity | Exact result |
| --- | --- |
| Visited nodes | 3,135 |
| Terminal boxes | 1,568 |
| Leaf-screen exclusions | 374 |
| Strict target certificates | 1,194 |
| Maximum binary depth | 15 |
| Unresolved boxes | 0 |

The other safe rejection guards remain in the checker but are not
needed as terminal reasons in this final partition. The total number
of nodes is exactly twice the number of leaves minus one.

The checker independently validates complete coverage from the
terminal path set: at each greatest path length, every terminal
sibling pair 0/1 must be present, and it replaces the pair by its
parent. Repeated replacement ends at the single empty root path.
No duplicate path is allowed. This proves a finite complete prefix
partition of (4), independent of the evaluation of the inequalities.

The canonical JSON serialization of the terminal paths, terminal
reasons and exact rational margins has SHA-256

`3e16224eccf7d9f4b93cd98f0b49901d15ac6ff1aa0decfff4620c6e282f9662`.

Its smallest positive lower bound is exactly

    18956496404463990827204268332919517456616691594803600945518049471507298635035616009529115650121242132577493180859511
    /
    402169494448028657470437288087932018112536386033276568006664944962647528099822910355958034676910115411275627154636800000.

The exact comparison of this fraction with 1/25000 is strict and
is asserted in the checker. Thus each admissible point lies in a
certified target box, and its actual value is at least that box's
lower endpoint, which is greater than 1/25000. This proves (3).

The root's separately implemented initial cover uses Fraction
objects, reciprocal normal formulas and 48-bit radical endpoints;
it closes the same domain in 1,290 leaves. That calculation prompted
this independent reconstruction but is not an additional hypothesis
of the present complete code and interval argument.

## 5. Literal physical interpretation and limits

For the actual aligned low S-root caller, c,s are the upper boundary
unit's original axes, and rho is its original incoming side mean.
The upper unit's lowest physical height is h-delta*c. The lower
loaded-two unit's actual return mean has height -g-tau*b. Therefore
(3) says that even adding one full vertical unit to that return
height stays strictly below the upper unit:

    1-g-tau*b < h-delta*c-1/25000,

because g=1-h. The physical caller must separately establish its
actual contact feature and that the connecting square's height
above that port is at most one. No such feature is assumed for an
arbitrary square by this scalar theorem.

No original contact mean is replaced by an extremal point. No
degree-two equation at an upper degree-three body or connecting
degree-three body is present. No numerical pose, approximate
minimum, unverified search region, omitted completion square,
Lean compilation, CI, ledger change or remote mutation is used.
