# A deep support band forces axis alignment for a loaded full star with at most two actual applications

Date: October 29, 2026 UTC. Author: far-vertex continuation.

**Status: complete proposed arbitrary-degree hand theorem and whole
original far-C alignment reduction, frozen for separate independent
review.** The general result applies to the complete original loaded
star whenever it has at most two distinct actual application points.
At a chosen application its direction is the normalized exact group
sum. For a true degree-two unit with distinct applications this is
exactly its unchanged original pair normal.

If that support point has transverse coordinate of absolute value at
most one half and depth greater than `R-sqrt(2)`, the actual square
must have sides parallel to the support direction. A pointwise radius
inequality proves the entire tilted alternative impossible at once.
The proof covers coincident applications, physical two-corner masks
and zero individual circle coefficients before making any
unique-mask concurrence-containment inference.

In the whole remaining original Type II far-return side row, the
previous uniform C height and tangent bounds satisfy this band.
Consequently **every remaining actual C is aligned with the original
frame `(d0,n)`**, including the previously unclassified C masks when B
is radial. Its exact two-coordinate chart and its genuine shared DC
port follow with the original mean unchanged. The aligned feature is
retained; the entire far-return row is not declared closed here.

## 1. Complete full-star statement and the exact aggregate direction

Let K and every actual positive pair neighbor of K be closed unit
squares contained in the same unchanged disk `D_R` about `O=0`, with
pairwise disjoint open interiors. Assume

    sqrt(2)<R<1+sqrt(2).                                  (1)

K is genuinely loaded and retains its whole original positive star,
of any positive finite true degree. Write its full force and moment as

    F+sum_i mu_i*n_i=0,
    sum_i mu_i*det(P_i,n_i)=0,
    F=2*sum_j lambda_j*Z_j,
    mu_i>0, lambda_j>=0, sum_j lambda_j>0.                (2)

Here `n_i` is the original outward unit support normal of K toward
its actual neighbor, and `P_i` is its unchanged original actual
application in the entire physical intersection. At a shared side it
is the original full mean. The `Z_j` are all actual physical circle
corners, with `|Z_j|=R`; a physically present corner may have zero
coefficient. No positive pair term or actual unit is removed.

Suppose the entire original set of applications has at most two
distinct actual values. Choose one such value Q and form only the
exact algebraic sum of all original terms there:

    G_Q=sum_(P_i=Q) mu_i*n_i,
    n=G_Q/|G_Q|.                                        (3)

This sum is nonzero and supports the same actual K at Q. Indeed all
the outward normals at a side interior are its side axis; at a vertex
they lie in its closed outward quadrant. Their positive sum has
strictly positive projection onto that quadrant's bisector. Thus

    n.(X-Q)<=0 for every X in K.                         (4)

The direction n is not a new selected contact normal or a new physical
neighbor. It is the exact group direction in (3). The theorem does not
assert that an arbitrary individual normal in a multiple-term group
has the same line as this sum. For true degree two with distinct
applications, each group has exactly one original term and n is that
term's original normal.

Let d0 be either unit tangent perpendicular to n and write the actual
point relative to the unchanged circle origin as

    Q=x*d0-h*n,
    h>0, |x|<=1/2.                                      (5)

**Support-band theorem.** If the sides of K are not parallel to
`(d0,n)`, then necessarily

    R^2>=x^2+(h+sqrt(2))^2.                             (6)

In particular either of the following complete band conditions forces
K to be aligned with `(d0,n)`:

    h>R-sqrt(2), |x|<=1/2;                              (7)

    h>=R-sqrt(2), 0<|x|<=1/2.                           (8)

All transverse endpoints in (7),(8) are included. At the joint boundary
`h=R-sqrt(2), x=0`, inequality (6) alone is noncontradictory;
that boundary is not silently included in an exclusion.

## 2. A tilted support point forces a unique physical circle corner

If needed reverse the tangent d0, as a change of coordinates for all
the same actual data, so that `0<=x<=1/2`. This changes no square,
normal, force or mean. Suppose K is tilted relative to `(d0,n)`.
Then n is not parallel to an own side axis, so Q is its unique actual
maximum-n vertex. Its two outward own axes can be written

    r=cos(phi)*d0+sin(phi)*n,
    m=-sin(phi)*d0+cos(phi)*n,
    0<phi<pi/2,
    K=Q-[0,1]r-[0,1]m.                                 (9)

These are the actual two axes at Q, with their ordering and signs
chosen only to express the whole square. The original point obeys

    Q.r=x*cos(phi)-h*sin(phi)<1/2,
    Q.m=-x*sin(phi)-h*cos(phi)<0<1/2.                   (10)

Both inequalities are strict even at `x=0` or `x=1/2`, since h>0
and both trigonometric components are positive. For each own
coordinate separately, its lower endpoint is strictly farther from
zero: if that upper endpoint is a, the difference of the two squared
coordinates is `(a-1)^2-a^2=1-2a>0`. The unique farthest actual
corner of K is therefore

    Z=Q-r-m=(x+s)*d0-(h+c)*n,
    s=sin(phi)-cos(phi),
    c=sin(phi)+cos(phi)>0,
    s^2+c^2=2, c<=sqrt(2).                              (11)

Because K is genuinely loaded and contained in `D_R`, this unique
farthest corner is its entire physical circle mask and `|Z|=R`.
No other circle corner with zero coefficient has been suppressed:
(10) proves strict physical uniqueness before using any force weight.
A nonvertex cannot be on the circle because the disk is strictly
convex. Consequently the full circle resultant is

    F=kappa*Z, kappa>0.                                 (12)

## 3. The complete finite/parallel application cover after uniqueness

Apply the complete boundary-free full-star theorem at SHA256
`3808b2b767a9e15c7270b50c4fbbb434ae0d69fe42c567d4da01f7d167f7fa78`
to the unchanged original star (2), grouping only equal actual
applications as in (3). Its radius hypothesis is exactly (1), and its
complete group directions are the same ones used here.

If all original applications equal Q, that theorem gives the actual
point `q=Q`, which lies in K and is a positive multiple of F. Its
proper ray at Q has length zero. This includes arbitrary true degree
without deleting or splitting any original contact term.

If there are two distinct actual applications and their exact group
sums are nonparallel, the theorem gives their proper concurrence,

    q=Q-ell*n=t*Z,
    ell>=0, t>0, q in K.                                (13)

Here the positive radial coefficient has absorbed kappa from (12).
The containment `q in K` is the theorem's **one physical circle
corner** conclusion, justified here by (10)--(12). Its physical
two-corner nonparallel alternatives can have exterior concurrence;
no containment claim has been made for those alternatives.

If there are two distinct actual applications and parallel group
sums, that complete theorem gives exactly a physically radial square
with two distinct physical circle corners and equal positive corner
weights. This contradicts the physical uniqueness already established
in Section 2. Thus this entire parallel alternative is excluded here
before assigning any finite concurrence to it.

Consequently (13) holds in every remaining tilted case, also with
`ell=0` in the one-application alternative. Since q belongs to the
same actual square in `D_R`, `|Z|=R` and t>0 imply

    0<t<=1.                                             (14)

All original force groups, side endpoints, full shared means and both
physical masks have now been covered. In particular (14) was not
inferred for a two-physical-corner exterior concurrence.

## 4. A single pointwise radius inequality excludes the whole tilt

Take the two original-frame coordinates in (13):

    x=t*(x+s),
    h+ell=t*(h+c).                                      (15)

If x>0, (14) and the first equality give `s>=0`. The second gives
`t*(h+c)>=h`. Substituting `t=x/(x+s)>0` and multiplying
positive denominators yields

    x*c>=h*s.

Since s>=0 and c>0, it follows that

    x*s+h*c
       >=h*s^2/c+h*c
        =2h/c
       >=sqrt(2)*h.                                    (16)

If x=0, the first equality in (15) and t>0 instead give `s=0`.
Equation (11) then gives `c=sqrt(2)`, so (16) again holds, now
with equality. This handles the whole closed transverse interval
without dividing by x at its zero endpoint.

Finally (11),(16) and the unchanged physical circle corner give

    R^2=|Z|^2
       =x^2+h^2+2+2*(x*s+h*c)
       >=x^2+(h+sqrt(2))^2.

This proves (6). Under (7), the last squared quantity is strictly
larger than R^2. Under (8), its addition of x^2 is strictly larger
than R^2. Both contradictions prove their complete alignment
conclusions. The proof is pointwise in the full original data and
requires no orientation partition, sampled angle or packing search.

## 5. A closed band throughout the original sharp radius window

For the original window

    79/40<=R<=sqrt(1105)/16,                              (17)

condition (1) holds. The already used exact comparisons are

    (206/99)^2-1105/256=33511/2509056>0,
    2-(140/99)^2=2/9801>0.

They give

    R-sqrt(2)<206/99-140/99=2/3<65/96.                   (18)

Thus throughout (17) the complete closed support band

    h>=65/96, |x|<=1/2                                 (19)

forces alignment by (7), including x=0 and both transverse endpoints.
This is only a corollary of the radius-dependent general theorem;
the general theorem has no dependence on the special nine-square
upper radius or on the Type II graph.

## 6. Entire unchanged far-return entry and the strict C tangent sign

Now retain the complete original Type II far-A-vertex D-owned return
row in D02.L135, with literal labels and graph

    A=0,V=1,D=2,C=3,N=4,B=5,
    rim A--V--D--C--N--B--A, chord AD.

A,D are unloaded true degree three; V,B,C are genuinely loaded true
degree two. N is the actual unloaded true degree-two side transmitter.
All six core units and all three actual completing units remain in
the original disk, with disjoint open interiors and every original
positive pair term, selected normal, application or full shared mean,
physical circle corner and individual zero coefficient. The same
original conditional common-selection entry remains explicit.

The previously proved complete diagonal, parallel-endpoint and
coincident-C exclusions retain their precise original scopes. In the
remaining side form the unchanged actual points satisfy

    T in B, U in C, T-U=d_N, |d_N|=1,
    d_N.d0<0, d_N.n>0.                                  (20)

The full proper C endpoint is finite with distinct applications
`Q_C!=U`. Its unchanged outward pair normals are n at Q_C and
d_N at U. With their original positive magnitudes p_C,gamma, the
full circle resultant and the exact proper concurrence are

    F_C=-p_C*n-gamma*d_N,
    p_C,gamma>0,
    q_C=Q_C-ell_C*n=t_C*F_C,
    ell_C>=0, t_C>0.                                    (21)

Equation (21) holds across both physical masks. In a physically
two-corner case q_C may be exterior; no C-containment assertion is
needed for the following sign. Taking the d0 coordinate gives

    x:=Q_C.d0=t_C*(-gamma*d_N.d0)>0.                     (22)

The complete current uniform tangent theorem at SHA256
`ed6a592db738a3fa31c87244415efc668180fbff9397b4511052e8fb3e3269c2`
gives, over this entire original domain,

    x<1/2.                                              (23)

The complete preceding height theorem at SHA256
`c803a178538c87924d866ee65ed95a7c2403a35203d5a7f5bf85bbc794ccc93c`
gives, with the actual original D point P,

    Q_C.n=P.n-1<-65/96,
    h:=1-P.n>65/96.                                    (24)

Neither imported inequality replaces the original D mean or omits
any V/A/D equation. Their whole scalar domain and all positive
denominator and radius conditions remain as proved in those sources.

## 7. The entire actual C is aligned, for every physical mask

The actual C and both its actual neighbors D,N satisfy the complete
full-star premises of Section 1. Its true degree is two with two
distinct applications, so the direction n in (21) is exactly the
normalized original single-term group at Q_C. It is an actual
maximum-n support of the whole C, with

    Q_C=x*d0-h*n,
    0<x<1/2, h>65/96.

Equations (17)--(19) therefore apply. The general support-band theorem
proves that **every actual C in this remaining original far-side
domain has sides parallel to `(d0,n)`**.

This conclusion includes the C configurations in which B is already
physically radial. No radial hypothesis on C, original ownership by C,
interior-side mean at C or unique-circle hypothesis on C was inserted
to obtain it. Under a supposition of tilt, the theorem first derives
physical uniqueness and only then uses unique-mask concurrence
containment. Thus the physically two-corner exterior-concurrence
possibilities have not been silently discarded.

## 8. The full aligned C chart and its genuine original shared port

Because Q_C maximizes n and C is aligned, there is an actual scalar
a_C such that

    C=[a_C-1,a_C]*d0+[-h-1,-h]*n,
    Q_C=x*d0-h*n.                                      (25)

Since h>0, every farthest corner is on the lower side `n=-h-1`.
If a_C<1/2, the transverse center is negative and every physical
circle corner has the negative transverse coordinate a_C-1.
Its full nonnegative circle combination of positive total would then
have negative d0 component. This contradicts (20),(21). Hence

    a_C>=1/2.                                          (26)

The actual lower-right corner is farthest and, as C is genuinely
loaded, it is an actual circle corner. Thus the exact radial equation is

    a_C^2+(h+1)^2=R^2.                                 (27)

For a_C>1/2 this is the unique physical circle corner. For a_C=1/2
the two actual lower corners are the full physical circle mask,
including any allowed individual zero coefficient. Equation (27)
does not impose equal weights in that two-corner case.

By (20), the actual maximum-d_N support of this C is the strict
upper-left vertex

    U=(a_C-1)*d0-h*n.                                  (28)

Since Q_C belongs to C, `x>=a_C-1`; since Q_C!=U, the inequality
is strict. Equations (23),(26) give the other strict inequality:

    a_C-1<x<1/2<=a_C.                                  (29)

Thus Q_C is a genuine relative-interior point of C's original top
side. This is a conclusion about the unchanged mean, not a choice of
a new mean or an earlier extra ownership premise.

The full original D chart, in these same coordinates, is

    D=P-[0,1]n+[t_D-1,t_D]d0,
    0<t_D<1,
    Q_C=P-n-delta_D*d0,
    0<delta_D<v<1-t_D.                                 (30)

Its original D mean therefore lies strictly inside D's back side:

    P.d0+t_D-1<x<P.d0+t_D.

That side and C's top side are both on the unchanged line `n=-h`.
By (29),(30), their two actual intervals contain an open subinterval
about the same original Q_C. Their physical intersection has positive
length, and Q_C remains the original full shared-side mean. The
actual entire DC contact is consequently shared, with n an own C
axis as well as the already original D axis. No fresh normal
selection or re-extraction of multipliers has occurred.

## 9. Exact remaining scope and complete direct sources

The whole tilted-C feature is excluded over the entire original
far-return side domain. The original remainder has precisely the
aligned chart (25)--(30), the original full forces and moments, its
original D mean, and the complete one- or two-physical-circle masks.
The previous B/C mask alternative and every unused equation still
apply. This source does not assert that the aligned C cases are
inconsistent; it does not close the entire far-return row, Type II,
either D02 parent, loaded N in L1345, the unrestricted nine-square
bound or equality classification.

| Complete direct source | SHA256 | Exact use |
| --- | --- | --- |
| LOADED_TWO_APPLICATION_FULL_STAR_BOUNDARY_FREE_CONCURRENCE_DICHOTOMY.md | 3808b2b767a9e15c7270b50c4fbbb434ae0d69fe42c567d4da01f7d167f7fa78 | Entire original arbitrary-degree, at-most-two-actual-application cover; exact groups, one-application case, proper positive concurrence, unique-mask containment and full physical-two parallel exception |
| TYPE_II_FAR_SIDE_UNIFORM_C_TANGENT_BOUND_AND_COMPLETE_RADIAL_C_AXIS_REDUCTION_2026_10_29.md | ed6a592db738a3fa31c87244415efc668180fbff9397b4511052e8fb3e3269c2 | Whole original strict upper tangent bound, at its current exact full scope and original-domain conditions |
| TYPE_II_FAR_SIDE_RETURN_COMPLETE_COINCIDENT_C_APPLICATION_EXCLUSION_2026_10_29.md | c803a178538c87924d866ee65ed95a7c2403a35203d5a7f5bf85bbc794ccc93c | Entire height bound h>65/96, distinct-C applications, complete physical-mask cover and exact radius comparisons |
| TYPE_II_FAR_RETURN_SIDE_CHANNEL_EXCLUDES_BOTH_PARALLEL_LOADED_ENDPOINTS_2026_10_29.md | e573ec4e567bb3e255ddbc9348b24dd4780651beebd1f3ea713e949930929b68 | Whole original far-side entry, true degrees, full finite endpoint cover, strict transmitter cone and all actual means |
| UNIVERSAL_UNIT_SQUARE_CAP_AND_COMPLETE_TYPE_II_FAR_RETURN_DIAGONAL_EXCLUSION_2026_10_29.md | f4f2f293e038ea9f42dc8572cb8f216c9b9718a8fb14c4ac215232efcaf34e3c | Entire original D chart, unchanged genuine v and full delta_D mean, original selection and owner scope |

All five complete direct sources were read. The root continuation
suggested the clean radius-dependent support-band statement (7),(8)
and supplied the full aligned chart/genuine-port consequence for
independent reconstruction. The far-vertex continuation supplied the
tilted-corner radius proof, the exact at-most-two-application aggregate
extension, and the complete all-mask C join. Both also contributed
to prior scalar inputs as those sources disclose. A separate
noncontributor review of this entire new source and its direct inputs
is required before adoption; contributor validation is not represented
as that independent review.

Every new estimate is the pointwise norm identity (6), its complete
finite/parallel cover and the exact rational comparisons (18). No
numerical pose search, angle mesh, sampled packing, geometric
certificate, changed mean, shortened star, altered physical mask,
omitted square, new normal, Lean/Lake invocation, CI/workflow dispatch,
remote mutation or merge was used.
