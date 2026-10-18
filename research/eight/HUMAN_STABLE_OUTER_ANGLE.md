# Stable outer-center angular separation at the eight-square ceiling

**Status.** A hand-proof quantitative corollary of
HUMAN_SHARP_OUTER_PAIR_SECTOR.md. It applies to every pair of unit
squares of arbitrary orientations; no actual-contact or stress premise
is used. The result does **not** close the unrestricted n=8 bound.

## Theorem

Let two interior-disjoint unit squares lie in a disk of squared radius

    q <= q_plus := 9789/2500.

If both center norms are at least one, their smaller angular separation
satisfies

    delta > pi/4 - 1/500.                               (1)

Consequently this bound holds for every pair of 'outer' squares in the
eight-square sharp-radius search region, even if they do not touch.

## 1. The circle-ceiling perturbation costs less than 7/15000

Put

    q0=5/2+sqrt(2),   Delta=q_plus-q0
      =3539/2500-sqrt(2).

This is positive and

    0<Delta<7/5000,                                    (2)

because 7071/5000<sqrt(2)<3539/2500; both comparisons follow by
squaring positive rationals.

For a unit square with center p of norm r>=1 and relative frame
angle beta in [0,pi/4], write L=cos(beta)+sin(beta).
Its farthest squared vertex norm equals

    r^2+L*r+1/2.                                       (3)

Let m(beta) be the positive solution of

    m^2+L*m+1/2=q0.                                    (4)

The previously proved sector theorem establishes m(beta)>5/4 for
all beta in the full interval. If r<=m, leave the square fixed.
If r>m, translate the square's center radially inward to norm m,
without rotating the square. Its farthest vertex norm is now q0,
and its center norm remains >1. The translation distance is

    r-m = [(r^2+L*r)-(m^2+L*m)]/(r+m+L)
        <= Delta/(2*m+L) < Delta/3 < 7/15000.          (5)

Thus *every* square with center norm at least one at q_plus can be
radially translated by less than

    eps := 7/15000                                     (6)

into D_sqrt(q0), while retaining its center direction, frame and
center-norm-at-least-one condition. No simultaneous non-overlap
preservation is asserted for these translated squares.

## 2. A uniform interior margin in the narrower sector

Put t=pi/8, lambda=(2+sqrt(2))/3 and
w=lambda*(1,0). Set

    t_new=t-1/1000.

Claim: every square S in D_sqrt(q0), with center norm >=1 and
center angle |phi|<=t_new, contains the closed disk

    D(w,1/1500)                                         (7)

in its **open** interior.

We use the point-in-square inequalities of
HUMAN_SHARP_OUTER_PAIR_SECTOR.md, displaying the uniform margins
rather than re-proving its derivative identities. In that note write
the center-frame coordinates of w-p as

    A=lambda*cos(phi+alpha)-r*cos(alpha),
    B=-lambda*sin(phi+alpha)+r*sin(alpha).

A disk of radius 1/1500 about w is contained in the square's open
interior if |A|,|B|<1/2-1/1500.

The longitudinal bounds in sections 1--2 of that note are uniform
for |phi|<=t, and give

    A< (4-sqrt(2))/6 < 1/2-1/1500,
    -A<349/700 <1/2-1/1500.                            (8)

For the transverse coordinate, reflection and monotonicity in phi
reduce to bounding -B at phi=t_new. When alpha>=0, section 3 gives

    -B < sqrt(2341/10000) <1/2-1/1500.                (9)

When alpha=-beta<=0, section 4 proves at the old endpoint phi=t:

    G(beta):=lambda*sin(t-beta)+m(beta)*sin(beta)
            <=1/2

for every beta in [0,pi/4], by strict concavity.
Replacing t by t_new decreases the bound by

    lambda*[sin(t-beta)-sin(t_new-beta)]
       =lambda*integral_(t_new)^t cos(v-beta) dv.

In the entire integration domain, |v-beta|<=pi/4, so
cos(v-beta)>=1/sqrt(2)>2/3; also lambda>1.
The integral interval has length 1/1000, hence the decrease is

    > 1/1500.                                         (10)

It follows that -B<1/2-1/1500 also in this last branch. Reflection
covers the other sign of B. This establishes the common closed disk
(7) with a strict margin, for **all** orientations and center radii.

All elementary margins used above are rational:
349/700<749/1500; sqrt(2341/10000)<749/1500
by squaring; and (4-sqrt(2))/6<749/1500
already follows from sqrt(2)>1.

## 3. Perturb back and contradict disjointness

Suppose two original squares in D_sqrt(q_plus), with center norms at
least one, had angular gap at most

    2*t_new=pi/4-1/500.

Rotate their angular bisector to the horizontal axis. Apply section 1
to each square separately. Their radially translated squares both
satisfy the sector condition |phi|<=t_new, so section 2 gives a closed
disk of radius 1/1500 centered at the same point w inside each.

Each translation in section 1 has length strictly less than

    7/15000 < 1/1500.

Translating a square back by a vector shorter than 1/1500 cannot
remove w from its open interior when its translated copy contains
D(w,1/1500) in its open interior. Therefore w lies in the *open*
interiors of both original squares, contradicting disjointness.

This proves (1), including the endpoint q=q_plus and the weak
hypothetical angular inequality. The argument uses no numerical
sampling, interval-box verification, or configuration classification.

## 4. Why this does not finish n=8

The candidate contains six squares with center norm at least one and
a noncentral exterior square whose center norm is below one.
An outer-center pair gap of pi/4-1/500 does not control the seventh
exterior center, does not force the actual outer contact graph to be
a single path, and does not assign every square to the central cap
hypotheses. The seven-outer-cycle and outer-path-with-inner-attachments
cases in HUMAN_OUTER_GRAPH_REDUCTION.md remain open at the sharp radius.

The result strengthens the previously proved generic pi/7 exterior
center spacing *for the outer subset only*. Neither bound implies
the five projected inequalities needed for R8>=Rhat.
