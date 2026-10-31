# An oblique return at an aligned long endpoint has a strict section bound

**Date:** October 30, 2026 UTC. **Status:** complete proposed force-free
local theorem and continuous tangent proof, awaiting full independent
review. All earlier frozen sources remain unchanged.

This manuscript treats every actual contact type at the upper-inner
corner of an aligned boundary endpoint. A return square either stays
above the endpoint's upper side, in which case it is genuinely tilted,
or owns the original oblique contact normal at a side-interior point.
In the latter case it may extend below that side, but its section at
height 5/4 still satisfies the same strict bound as a unit above the
original floor. Every side parameter and both section-edge alternatives
are retained. No endpoint force or torque equation is used.

## 1. Exact actual scope and conclusions

Let actual closed unit squares have disjoint open interiors and lie in
the disk centered at the unchanged origin, with squared radius

    q<=Q=1105/256.

One actual physically boundary square is

    B=[x,x+1] x [h-1,h],
    59/60<x<61/60, 3/8<=h<=1/2.                        (1)

Consequently its actual containing circle has

    q=(x+1)^2+(1-h)^2.                                  (2)

At h=1/2 the two outer B corners are both physical circle corners;
no load is prescribed at either. Let C be a distinct actual physically
boundary unit wholly in the open halfplane y>0. The actual contact
point is B's upper-inner vertex

    p=(x,h).

Retain an original common unit support normal from B toward C of the
form

    n=(-alpha,beta), alpha>0, beta>0,
    alpha^2+beta^2=1.                                  (3)

Thus C minimizes n at this same actual p. Its true degree, all forces,
circle weights and other contacts are unrestricted. Set

    rho=5/4,
    f(h)=sqrt(Q-(h+1)^2)-1.                            (4)

**Theorem.** Exactly the following exhaustive alternatives are needed:

1. C is wholly in y>=h, and its own axes are not parallel to the
   coordinate axes.
2. p lies in the relative interior of a side of C. The normal n in
   (3) is C's actual inward own axis, and for the perpendicular own
   axis v=(beta,alpha),

       C=p+[0,1]n+[-r,1-r]v, 0<r<1.                  (5)

   The whole original slider r is retained. C crosses y=rho, and
   the left endpoint ell of its nondegenerate section there obeys

       ell<f(h).                                      (6)

The second alternative is precisely the possible below-floor case:
its vertex p-rv has height h-r alpha<h. The first alternative does
not require that p is a relative side-interior contact. In fact the
proof shows it occurs at a return-square vertex.

The theorem does not by itself import a section estimate for arbitrary
above-floor tilted squares. It supplies the complete contact-type
reduction and proves (6) on the whole below-floor branch. Combining it
with a separately proved strict section theorem for nonzero tilts above
floor h covers all oblique direct joins. No such input is silently
assumed in the proof below.

Reflection in the y axis gives the corresponding strict lower bound
on the right section endpoint for the left long endpoint.

## 2. The inward halfplane cannot contain a boundary return

Write B in its outward own frame, reflecting only the vertical
coordinate, as

    B=[kappa-1,kappa] x [ell0-1,ell0],
    kappa=x+1, ell0=1-h,
    kappa>=ell0>=1/2, kappa^2+ell0^2=q.

The original horizontal direction and the disk origin do not move.
Here

    kappa-ell0=x+h>163/120>1.                          (7)

I repeat the complete local inner-face lemma to keep this contact
cover self-contained. Suppose a unit T lies in the closed halfplane
X<=kappa-1 and meets the inner B face. A maximal-X vertex of T lies
on the overlapping supporting intervals. If T's support is an entire
side, its vertical interval and B's interval both have length one;
their nonempty overlap contains an endpoint of T's interval. Thus this
vertex assertion covers all shared-side and endpoint contacts.

Write that actual vertex as P=(kappa-1,y), with
`ell0-1<=y<=ell0`, so |y|<=ell0. Its inward unit side directions,
after labeling, are

    w1=(-cos theta,sin theta),
    w2=(-sin theta,-cos theta), 0<=theta<=pi/2.

The two adjacent corners have squared norm at most

    (kappa-1)^2+ell0^2+1+2ell0
      =q-2kappa+2ell0+2<q.

Since `P.(w1+w2)<=-(kappa-1)+ell0`, the opposite corner has squared
norm at most

    (kappa-1)^2+ell0^2+2-2(kappa-1)+2ell0
      =q-4kappa+2ell0+5<q.

The last strict comparison follows from
`4kappa-2ell0-5>2ell0-1>=0`. The original vertex has squared norm
at most `(kappa-1)^2+ell0^2<q` as well. All four actual corners
therefore lie strictly inside the containing circle.

**Inner-halfplane exclusion.** No actual physical-boundary return C
meeting p can be wholly in X<=x. This conclusion concerns physical
circle contact and actual geometry; it uses no equation, load, owner
selection or degree assumption at either unit.

## 3. Complete vertex/side classification at the original point

The actual contact p cannot lie in int C, since points of int B
approach p. If it is a C vertex, its inward tangent cone is a right
angle. It cannot meet the open southeast quadrant, which is the local
interior cone of B at p.

Parameterize the C inward edge directions in circular order by angles
`theta,theta+pi/2` avoiding that open quadrant. They may be represented
with `0<=theta<=pi`. If `0<=theta<=pi/2`, both edges have nonnegative
y-components, so the whole C lies in y>=h. If
`pi/2<=theta<=pi`, both have nonpositive x-components, so the whole
C lies in X<=x, forbidden by Section 2. The shared endpoint case
is included. Thus every allowed vertex contact has the asserted floor.

Such a return cannot be axis-aligned. An axis-aligned vertex cone above
p is either the northeast or northwest quadrant. The northeast choice
does not minimize the original strict normal (-alpha,beta), because
moving along its positive-x edge decreases that functional. The
northwest choice is wholly in X<=x and is forbidden by Section 2.
This proves the nonzero-tilt statement in alternative 1.

If p is in the relative interior of a C side, that side has the unique
original inward unit normal n. Its perpendicular direction may be
chosen as v=(beta,alpha). The unit-square chart is exactly (5), with
0<r<1 because the point is a genuine side-interior point. The actual
normal is not reassigned, the side mean is not moved, and its full
slider is not replaced by a corner. Its bottom vertex has height
h-r alpha<h, so the two alternatives exhaust all physical contacts
and separate the actual below-floor branch.

## 4. The below-floor return must cross the section line

Assume (5). Put

    k=rho-h, 3/4<=k<=7/8,
    l=1-r in (0,1).

The actual bottom and top heights of C are

    h-r alpha, h+beta+l alpha.

Since C contains p with h<rho, its bottom is below rho. I prove its
top is strictly above rho, rather than assuming a high section exists.
Suppose instead

    beta+l alpha<=k.                                  (8)

Then beta<=k and

    l beta<=beta*(k-beta)/sqrt(1-beta^2)
           <=k^2/(4*sqrt(1-k^2))
           <=49/(32*sqrt(15))<2/5.                    (9)

The final strict comparison follows from `245^2<64^2*15`, namely
60025<61440. Hence the full x-range of C obeys

    x_max=x+l beta<61/60+2/5=17/12,
    x_min=x-alpha-r beta>59/60-sqrt(2)>-1/2.            (10)

The whole actual C lies in y>0 by hypothesis. Under (8) it would
therefore have every point of squared norm strictly less than

    (17/12)^2+(5/4)^2=257/72.                          (11)

But its actual containing radius is fixed by the physical boundary
unit B in (2), and

    q>(119/60)^2+1/4=15061/3600,
    15061/3600-257/72=737/1200>0.                      (12)

Equations (11)--(12) contradict C's physical circle contact. This
proves that its top is above rho. The horizontal line y=rho thus
crosses the open interior of C, giving a nondegenerate closed section
with two genuine endpoints.

## 5. The two exact active edges of the left section endpoint

Write an arbitrary point of C in its actual chart as

    p+u n+v0 v, 0<=u<=1, -r<=v0<=1-r.

At height rho it obeys `u beta+v0 alpha=k`. Its x-coordinate
is decreasing in u, because eliminating v0 gives

    X=x+(beta/alpha)*k-u/alpha.

The largest allowed u is `min(1,(k+alpha*r)/beta)`. Consequently
the left section endpoint has exactly these two alternatives:

* **Opposite-n-face active:** u=1 and

      ell=x+(beta*k-1)/alpha.                         (13)

* **Bottom-v-edge active:** v0=-r and

      ell=x-(alpha*k+r)/beta.                         (14)

The equality case where the two descriptions meet is included in
either formula. Existence proved in Section 4 supplies all remaining
interval constraints; no other active edge is omitted.

## 6. The opposite-n-face case has a uniform strict margin

For 0<k<1 and alpha^2+beta^2=1, positive squaring gives

    (1-beta*k)^2-alpha^2*(1-k^2)=(beta-k)^2>=0.

Both sides before squaring are positive, so (13) gives

    ell<=x-sqrt(1-k^2).                                (15)

Consider

    G(h)=sqrt(Q-(h+1)^2)+sqrt(1-(rho-h)^2).

It is strictly increasing on [3/8,1/2]. Its derivative is positive
exactly when `Q*(rho-h)^2>(h+1)^2`; this follows from Q>4,
`rho-h>=3/4` and `h+1<=3/2`. All square-root denominators are
positive, so the derivative comparison uses valid positive squares.

At the lower endpoint,

    G(3/8)=sqrt(621)/16+sqrt(15)/8
          >249/160+77/160=163/80.

The two rational radical bounds follow from
`(249/10)^2<621` and `(77/20)^2<15`. Since x<61/60,
(15) therefore yields the uniform strict reserve

    f(h)-ell >163/80-121/60=1/48.                     (16)

This closes the entire opposite-face case without any angular or
normal-force hypothesis beyond the original chart (5).

## 7. The bottom-v-edge case: tangent contradiction over the entire slider

Assume (14) and suppose for contradiction that ell>=f(h). Define

    B0=h+1, A0=sqrt(Q-B0^2), F=A0-1=f(h),
    K=x+1, d=x-F=K-A0, k=9/4-B0,
    r0=beta*d-alpha*k.

Equation (14) gives `r0>=r>0`. The full parameter ranges are

    11/8<=B0<=3/2,
    23/16<=A0<=sqrt(621)/16,
    119/60<K<121/60,
    3/4<=k<=7/8.

Moreover

    d<121/60-23/16=139/240<3/5,
    alpha/beta<d/k<4/5,
    beta>3/4.                                          (17)

The bound on beta follows directly by normalization; for example
`beta>5/sqrt(41)>3/4`. Positivity of r0 supplies the strict first
ratio bound, so no small-angle premise is inserted.

Let z0=(A0,B0), so |z0|^2=Q. The original upper corner of C is

    Z=p+n+(1-r)v.

For comparison only, put `Z0=p+n+(1-r0)v`. Because r0>=r and
`z0.v=A0 beta+B0 alpha>0`,

    z0.Z>=z0.Z0.                                       (18)

Z0 is an algebraic comparison point, not a moved physical application
or a substituted square. The point Z in (18) remains the actual corner.

Using `alpha^2+beta^2=1` and `1-beta=alpha^2/(1+beta)`, direct expansion
gives the exact identity

    (z0.Z0-Q)/alpha
      =(B0-A0)+(9*A0/4-B0*K)*beta
        +alpha*[A0*K+9*B0/4-Q-(A0+B0)/(1+beta)].       (19)

I prove both displayed terms strictly positive on the full parameter
box, retaining the exact coupled circle relation for A0,B0.

### 7.1 The first term is positive

Its beta coefficient satisfies

    9*A0/4-B0*K >=9*(23/16)/4-(3/2)*(121/60)
                 =67/320>0.

Thus (17) gives

    (B0-A0)+(9*A0/4-B0*K)*beta
      >(11/16)*A0+B0*(1-3*K/4)
      >=(11/16)*(23/16)-(41/80)*(3/2)
       =281/1280>0.                                   (20)

The negative coefficient of B0 is treated with its upper bound,
not its lower bound.

### 7.2 The bracket multiplying alpha is positive

For fixed K>=119/60, the relevant first part is bounded below by

    J(B0)=(119/60)*sqrt(Q-B0^2)+9*B0/4-Q.

This is concave on [11/8,3/2], since the square-root second derivative
is strictly negative. Its minimum is therefore bounded below by the
smaller endpoint value. At B0=11/8, the rational radical bound already
used in Section 6 gives

    J(11/8)>11929/6400>37/20,
    11929/6400-37/20=89/6400>0.

At B0=3/2, its exact value is

    J(3/2)=7333/3840>37/20,
    7333/3840-37/20=229/3840>0.

Also `A0+B0<=sqrt(2Q)<3`, and beta>3/4. Consequently

    A0*K+9*B0/4-Q-(A0+B0)/(1+beta)
      >37/20-12/7=19/140>0.                           (21)

Equations (19)--(21), with alpha>0, imply z0.Z0>Q and hence z0.Z>Q.
But Z is an actual contained corner and |z0|=sqrt(Q), so Cauchy's
inequality gives `z0.Z<=|z0|*|Z|<=Q`. This contradiction proves
ell<f(h) throughout the second case. The proof retains every r in
(0,1), including its approach to either endpoint; no slider optimizer
or angular sample is used.

Together with Section 6 this proves the complete below-floor conclusion
(6), and Sections 2--3 establish the full contact-type theorem.

## 8. Literal aligned-long-endpoint application and remaining input

After the complete two-endpoint alignment theorem, a right long endpoint
has the actual aligned pose

    B=[s+1,s+2] x [y_B-1/2,y_B+1/2],
    |s|<1/60.

Its above-side boundary return normals have positive global y component.
The full endpoint force equation therefore forces a negative y-component
in its total circle resultant. If y_B>0, the unique physical circle
corner would have positive y coordinate, which is impossible. Hence
`y_B<=0`; the radial y_B=0 case retains both physical circle weights.
The coupled endpoint height bound gives `-1/8<=y_B<=0`.

Thus `x=s+1` and `h=y_B+1/2` satisfy (1). The complete previously
proved contact-locus theorem leaves either a vertical upper-side normal
or an oblique normal at the upper-inner vertex. In the latter case its
original normal satisfies (3), and the whole actual return unit is above
y>0 by the original return-side localization. Every hypothesis of the
local theorem is now literal. The left endpoint is its x-reflection,
with its own independent height and mean.

A separate complete theorem for units wholly above floors in
[3/8,1/2] can be combined with the first alternative of Section 1.
The source here supplies the entire below-floor alternative and proves
that an above-floor oblique return has a nonzero tilt. It does not
assume that a neighbor-owned square is above the endpoint's side, nor
that C and D share an own frame. No full opposite-C7 closure or
original coarse-cell credit is assigned by this manuscript alone.

## 9. Source boundary and verification

The inner-owned-face lemma is already proved in
`C7_HIGH_CENTER_CONTACT_TYPES.md`, Section 1, and reconstructed in the
frozen
`LONG_ENDPOINT_RETURN_CONTACT_LOCUS_FORCE_LINE_SIGN_AND_TILTED_VERTEX_REDUCTION_2026_10_30.md`
(SHA256 `cf942c1069e451ad043c80c8075fd67c85d2b71faa05c29b9baa3dae32f66fe3`).
Its full proof is repeated in Section 2 above; none of the former
source's all-owned graph or radius-three-halves premises is imported.

The literal Section 8 caller uses the completed endpoint alignment
source
`SEPARATED_BOUNDARY_RETURN_NEIGHBORS_FORCE_ALIGNED_LONG_ENDPOINTS_2026_10_30.md`
(SHA256 `9c7f47ce87b5a7d548ec76c33f5912adae870211770ea578f15621a78104ca06`)
and the unchanged endpoint/return-side estimates already listed there.
The local Sections 1--7 theorem itself needs no stress, topology,
normal selection or extra body equations.

All comparisons are exact over the stated continuous parameter domains.
Both actual contact-type alternatives and both active section edges are
covered, including their shared equality. Every original unit remains.
No numerical pose search, finite angle table, root relocation, shorter
star, new application mean, Lean compilation, CI, original ledger edit,
metadata change or remote publication is used or asserted.

