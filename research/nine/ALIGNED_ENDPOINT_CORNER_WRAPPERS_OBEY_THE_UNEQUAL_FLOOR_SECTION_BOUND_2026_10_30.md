# Aligned-endpoint corner wrappers obey the same unequal-floor section bound

**Date:** October 30, 2026 UTC.
**Status:** complete proposed continuous geometric family theorem, awaiting
full independent review. Earlier frozen sources remain unchanged.

Put `Q=1105/256`, `z=5/4`, and

    g(Y)=sqrt(Q-Y^2), C_f=g(f+1).

The proof treats the actual return square even when it crosses below the
top side of an aligned endpoint. It does not replace that square by a
convex hull, impose a new floor on it, or alter its original force normal.

## 1. The complete oblique supporting-side statement

Let `0<=q<=Q`, and suppose

    59/60<x<61/60, 3/8<=f<=1/2,
    (x+1)^2+(1-f)^2<=q.                               (1)

Let an actual closed unit square C lie in `D_q`, physically touch its
containing circle, and have the exact representation

    p=(x,f),
    n=(-alpha,beta), u=(beta,alpha),
    alpha>0, beta>0, alpha^2+beta^2=1,
    C=p+[0,1]n+[r-1,r]u, 0<=r<=1.                    (2)

Thus p is an actual point of C's supporting side with inward own normal n.
The entire support side, its endpoint cases and all rotations of this form
are included. No order between alpha and beta is assumed.

**Theorem 1.** The line `y=z` cuts strictly between C's lower and upper
horizontal supports. Its actual left section endpoint satisfies

    ell<C_f-1.                                        (3)

In particular the same left-section bound holds strictly for every
oblique side of a return square meeting an aligned endpoint's upper-inner
corner, whether or not the return square stays above height f.

## 2. The section is present even for a square crossing below the floor

Equation (1) already implies

    q>15061/3600>4.                                   (4)

Indeed `x+1>119/60` and `1-f>=1/2`.
The bottom and top heights of the square in (2) are

    f+(r-1)*alpha, f+r*alpha+beta.

Its bottom is at most `f<=1/2<z`. Suppose for contradiction that its
top were at most z. Put `k=z-f`, so `3/4<=k<=7/8`. Then

    beta<=k, alpha>=sqrt(15)/8>7/16,
    r<= (k-beta)/alpha.

Consequently its rightmost x coordinate obeys

    x+r*beta
      <=x+beta*(k-beta)/alpha
      <61/60+(49/256)/(7/16)
      =349/240<3/2.                                  (5)

The inequality `beta*(k-beta)<=k^2/4<=49/256` covers the whole
closed permitted beta interval. Its leftmost x coordinate is greater than

    59/60-(alpha+beta)>=59/60-sqrt(2)>-1/2.

Every y coordinate is at least `f-alpha>=-5/8` and, under the supposed
top bound, at most `5/4`. Thus every actual corner has squared norm
strictly less than

    (3/2)^2+(5/4)^2=61/16<4<q.

Every corner is strictly inside the disk, contradicting physical boundary
contact. Hence the top is strictly above z. This proves the nondegenerate
interior-section assertion without assuming a positive floor for C.

## 3. The two actual left endpoints

At height z let `k=z-f`. The two lower bounds on the x coordinate,
obtained from the u and n side coordinates of (2), are

    ell_1=x+(r-1-alpha*k)/beta,
    ell_2=x+(beta*k-1)/alpha.

By Section 2 the section is nonempty, and its actual left endpoint is

    ell=max(ell_1,ell_2).                              (6)

Both candidates will be bounded separately, without an active-edge
assumption. Let

    d=C_f-1.

Throughout the stated floor interval,

    7/16<=d<9/16, z=5/4.                              (7)

The lower endpoint follows from `g(3/2)=23/16`, and the upper
endpoint from `g(11/8)=sqrt(621)/16<25/16`.

## 4. The first candidate: a whole-domain squared inequality

Retain the actual corner

    P=p+r*u+n.

Its own coordinates satisfy

    n.P=1-alpha*x+beta*f=:E,
    u.P=u.p+r.

Since P belongs to the original disk,

    beta*ell_1=u.P-1-alpha*z
       <=sqrt(Q-E^2)-1-alpha*z.                       (8)

The radical is defined by the actual contained corner. It remains to
compare it with the positive quantity `1+alpha*z+beta*d`.
Direct expansion, using `alpha^2+beta^2=1` and
`C_f^2+(f+1)^2=Q`, gives

    [1+alpha*z+beta*d]^2+[1-alpha*x+beta*f]^2-Q
      =alpha * {
          2(z-x)+2(zd-xf)*beta
          +alpha*[z^2+x^2-d^2-f^2-2(d+f)/(1+beta)]
        }.                                           (9)

Every sign in (9) is uniform over both angular halves. The following
coarse rational estimates are sufficient:

    2(z-x)>7/15,
    zd-xf>=(5/4)(7/16)-(61/60)(1/2)=37/960>0,
    z^2+x^2-d^2-f^2>31/16,
    2(d+f)/(1+beta)<17/8.

For the third inequality the reserve after substituting the worst
displayed bounds is

    (5/4)^2+(59/60)^2-(9/16)^2-(1/2)^2-31/16
       =1471/57600>0.

The bracket multiplying alpha inside braces is therefore greater than
`-3/16`. Since `0<alpha<=1`, the full braces in (9) are strictly
greater than

    7/15-3/16=67/240>0.

Thus the left side of (9) is positive. Squaring positive quantities in
(8) is legitimate and gives

    sqrt(Q-E^2)<1+alpha*z+beta*d,
    ell_1<d=C_f-1.                                   (10)

The bound neither assumes a preferred side owns the original certificate
normal nor drops any physical corner. It uses one actual corner of C.

## 5. The second candidate: the endpoint's actual outer corner supplies the correlation

Put

    K_f=g(1-f), D=x+1-C_f.

Equation (1) gives `x+1<=K_f`, so

    0<D<=K_f-C_f=4f/(K_f+C_f).                        (11)

The strict positivity of D follows already from `x+1>119/60` and
`C_f<25/16`. The sum `K_f+C_f` decreases with f: its derivative is

    (1-f)/K_f-(1+f)/C_f<0,

since `K_f>C_f>0` and `1-f<1+f`. Therefore

    K_f+C_f >= [sqrt(1041)+23]/16
              >55/16>24/7.

Substituting in (11) yields `D<7f/6`. The quadratic

    (7f/6)^2+(5/4-f)^2

is convex in f. Its endpoint values on `[3/8,1/2]` are respectively
`245/256` and `65/72`, with the former larger. Hence

    D^2+k^2<245/256<1.                               (12)

By the Cauchy inequality for the actual unit pair `(alpha,beta)`,

    alpha*D+beta*k<=sqrt(D^2+k^2)<1.

Rearranging exactly gives

    ell_2=x+(beta*k-1)/alpha<x-D=C_f-1.                (13)

Equations (6), (10) and (13) prove Theorem 1. The correlation in (11)
comes from the original aligned endpoint's outer corner; the separate
coarse ranges of x and f would not suffice for (12).

## 6. Exhaustive geometric contact cover at an aligned boundary endpoint

Let the actual aligned endpoint be

    B=[x,x+1] x [f-1,f]

with (1), physically touching the circle of squared radius q. Let C be
another physical-boundary unit with interior disjoint from B. Suppose an
actual contact of this pair lies on the top side of B, excluding its outer
endpoint. This is precisely the return-contact locus supplied by the frozen
long-endpoint theorem once B is aligned.

There are exactly two sufficient alternatives for the section estimate:

1. C is wholly in `y>=f`. The complete unequal-floor section theorem
   applies to its original square directly.
2. C has the representation (2) at the upper-inner corner `p=(x,f)`,
   with an oblique inward own side normal. Theorem 1 applies strictly.

Here is the full geometric justification, including vertex/vertex cases.
A contact in the relative interior of B's top side has the unique common
normal pointing vertically upward, so C is wholly above f. If C is not
wholly above f, the contact must therefore be at p.

At p, B's outward supporting normals form the closed upper-left quadrant.
No common normal can point horizontally left: it would put C in `x<=x`
and make C a boundary neighbor of B's inner own face. The exact inner-face
lemma excludes this. In its notation the parameters are

    kappa=x+1, ell=1-f,
    kappa^2+ell^2=q, kappa-ell=x+f>1, ell>=1/2.

These are the complete hypotheses of Section 1 of
`C7_HIGH_CENTER_CONTACT_TYPES.md`, also fully reconstructed in the frozen
long-endpoint contact-locus source. No all-owned selection is imported.

If p is a vertex of C, its inward normal cone is another closed angular
interval of length ninety degrees. Two intersecting such intervals contain
at least one endpoint direction of the first interval in the second: lift
their overlapping arcs to intervals on the line and compare their equal
lengths. Applied to B's quadrant, either the vertical-up or horizontal-left
axis is a common supporting normal. The latter has just been excluded;
the former puts C wholly above f. Thus a vertex/vertex contact cannot
evade the first alternative.

In the remaining case p lies in the relative interior of an actual side
of C. The common normal is uniquely that side's own inward axis. It belongs
to B's upper-left quadrant, and neither boundary axis remains in the
non-above-floor branch. Hence it has the form `(-alpha,beta)` with both
components strictly positive. Taking the perpendicular own axis
`(beta,alpha)` and its actual side parameter r gives exactly (2).

This is an exhaustive geometric cover. It does not replace an original
force normal or select a new stress. In the vertex/vertex branch the
auxiliary axis only proves an actual whole-square halfplane inclusion.
In the genuine side-interior branch the actual common normal is already
the own axis used in (2).

## 7. Section consequence and source boundary

The complete unequal-floor profile is
`UNIFORM_UNEQUAL_FLOOR_SECTION_PROFILE_AND_TWO_UNIT_CAP_METRIC_2026_10_30.md`,
SHA256 `abfb4887037851d2715c8ff746ff11dc238109692b2cc0fbc42598bb4dae9d94`.
It gives `ell<=C_f-1` for every actual square wholly above f and
proves that the section at z is nondegenerate. Theorem 1 gives the same
inequality strictly for every remaining oblique-side wrapper from Section 6.
Reflection gives the corresponding right endpoint bound at a left aligned
endpoint. These statements use actual horizontal sections of the original
return squares, so an actual set-distance lower bound can be applied on
that common line without assuming a common short-channel normal.

The frozen return-contact locus used in the geometric caller is
`LONG_ENDPOINT_RETURN_CONTACT_LOCUS_FORCE_LINE_SIGN_AND_TILTED_VERTEX_REDUCTION_2026_10_30.md`,
SHA256 `cf942c1069e451ad043c80c8075fd67c85d2b71faa05c29b9baa3dae32f66fe3`.
The original local face source has SHA256
`68e94d3f80274c07f3a4f6c0d01eab753733b1e808838c6abf6e4448cfc481b8`.
The direct calculation in Sections 1--5 is self-contained and does not
depend on either source; they enter only for the complete contact cover
and the above-floor alternative.

This manuscript supplies the previously missing wrapper section estimate
and its geometric contact cover. A whole-cycle sharp theorem must still
join these statements to its actual endpoint height bounds, two section
ordering possibilities, and the actual return-square set distance. No
nine-square global closure is declared here.

The proof contains exact continuous inequalities only. No finite pose
search, stress optimization, original ledger mutation, Lean compilation,
CI run, certificate alteration, discarded packing unit or remote publication
is used.
