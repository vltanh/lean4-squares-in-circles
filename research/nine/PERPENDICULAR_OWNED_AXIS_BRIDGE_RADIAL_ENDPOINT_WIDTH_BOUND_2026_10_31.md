# A radial endpoint gives an exact width bound for every perpendicular owned-axis bridge

Date: October 31, 2026 UTC.

**Status: complete hand theorem.** With two actual perpendicular exterior
own axes, a channel parallel to either one forces an exact bound on its
length and the common circle radius. For a unit side channel the bound
is incompatible with R>2. For a diagonal unit channel with the original
side-interior applications, it gives d<1, excluding the entire R>=sqrt(17)/2
sector at once. All original support means and both physical circle weights
are retained.

## 1. General original full-star setting

Let two actual unit squares B,C lie in the same disk centered at O, have
disjoint interiors, and be loaded with their complete original positive
degree-two stars. Let b,c be perpendicular unit vectors. Assume that B
owns its original exterior inward normal b at a minimum-b support point
or full mean K, while C owns its exterior inward normal -c at a maximum-c
support point or full mean L.

Keep the complete original two incoming forces and circle resultants:

    G_B=p*b+g*n,
    G_C=-q*c-g*n,
    p,q,g>0.                                      (1)

Here the actual channel applications T in B and U in C have their original
minimum-n and maximum-n support meanings, respectively, and the original
channel equations give

    T-U=lambda*n, lambda>0.                       (2)

No endpoint degree is shortened to obtain (1). Further physical contacts,
including zero-force contacts, remain. Every actual physical circle corner
and its original nonnegative coefficient remains in G_B,G_C; each full
resultant is nonzero. The common radius is R>2, and put

    d=sqrt(R^2-1/4)-1,
    R^2=(d+1)^2+1/4.                             (3)

Condition on either original direction n=b or n=c. These are the cases
of the theorem; no freely chosen replacement channel direction is used.

**Theorem 1.1.** Under these hypotheses,

    d <= lambda/2+1/(lambda+2).                   (4)

The inequality is strict if, in the n=b case, T is in the relative
interior of B's minimum-b side or U is in the relative interior of C's
maximum-b side. For n=c use the corresponding two support-side interiors
after interchanging B,C as in Section 4.

The only local force hypotheses are the two full stars (1). All other
actual squares remain present and arbitrary.

## 2. The parallel full star forces the same physical radial B

First take n=b and use (b,c) as an orthonormal coordinate frame. B's
complete circle resultant is (p+g)b. Because b is an actual own axis,
this forces the entire actual physical position

    B=[d,d+1]*b+[-1/2,1/2]*c.                    (5)

Here is a direct proof including every physical mask. If the transverse
coordinate of the B center were positive, every farthest vertex would
have positive c coordinate; hence every physical circle corner and its
nonzero resultant would have positive c coordinate. A negative center
coordinate gives the negative version. Both contradict the zero c
component of G_B. Thus the transverse center coordinate is zero.

The b coordinate of the center cannot be negative, since then every
physical circle corner would have negative b coordinate. If it were zero
as well, the square would be centered at O and its circle vertices would
have radius 1/sqrt(2), contrary to R>2 and positive circle load. It is
therefore positive. Its two far-side vertices have transverse coordinates
plus or minus 1/2 and the same positive b coordinate. The radius equation
puts that coordinate at d+1, proving (5).

This is a conclusion about the original B and original full circle force.
The two physical corners are retained. Any equalities of their weights
that follow from the zero transverse resultant are derived equalities,
not a preliminary restriction on a physical-two mask.

Since T is still on the original minimum-b side, (2),(5) give

    T.b=d, -1/2<=T.c<=1/2,
    U.b=d-lambda, U.c=T.c.                       (6)

All weak side-mean endpoints are present in (6).

## 3. The opposite complete force fixes a physical far corner

In the same frame, C's complete resultant is -g*b-q*c. Both components
are strictly negative. A positive center coordinate in either own axis
would make that coordinate positive at every physical circle vertex,
which contradicts this full resultant. Therefore both center coordinates
of C are nonpositive. A zero coordinate is allowed and is not reclassified
as physical uniqueness.

The original maximum-b side through U and maximum-c side through L
describe the same complete square as

    C=[d-lambda-1,d-lambda]*b+[l-1,l]*c,
    l=L.c.                                       (7)

The nonpositive c-center coordinate gives l<=1/2. Since U is an actual
point of the same maximum-b side, its transverse coordinate is at most l.
Together with (6),

    -1/2<=T.c=U.c<=l<=1/2.                       (8)

If either of the two side-interior hypotheses in Theorem 1.1 holds,
the first-to-last comparison yields l>-1/2. In detail, an interior T
has T.c>-1/2, while an interior U has U.c<l; either provides strictness.

Because both center coordinates in (7) are nonpositive, the bottom-left
vertex

    Z=(d-lambda-1)*b+(l-1)*c

is an actual farthest vertex of C. The positive circle load implies that
its distance is exactly R. This remains true if one center coordinate is
zero and Z is one of two physical circle corners. Hence (8) gives

    R^2=(d-lambda-1)^2+(l-1)^2
       <=(d-lambda-1)^2+9/4,                    (9)

strictly when l>-1/2. Substitute the original same-circle identity (3):

    (lambda+2)*(2*d-lambda)<=2.                 (10)

The factor lambda+2 is strictly positive. Division proves (4), with
the asserted strict version. No torque is omitted from an original star;
only the full force equations and actual side supports are needed for
this stronger geometric bound.

## 4. The other parallel direction and both unit transmission lengths

If the original n=c, interchange the entire actual B,C data and use

    b'=-c, c'=-b, n'=-n=b',
    T'=U, U'=T.

The same full equations become exactly (1)--(2) in the primed labels,
with the original positive magnitudes interchanged. Thus Sections 2--3
apply literally. The radius, physical corners, original means and all
other units are unchanged. This proves the second direction of the
theorem without assuming a fresh normal or reflection of only one square.

For an original unloaded unit side transmitter lambda=1, even the weak
mean version of (4) gives

    d<=1/2+1/3=5/6.

It contradicts R>2, which gives d>sqrt(15)/2-1>14/15>5/6.
Thus the complete perpendicular-own-axis side channel with n parallel
to either exterior own axis is impossible, including all original
transverse means and either physical circle-weight endpoint.

For an original unloaded unit diagonal transmitter lambda=sqrt(2),
the initial incident-diagonal avoidance makes T,U relative-side-interior
points of B,C. The strict form of (4) becomes

    d<sqrt(2)/2+1/(2+sqrt(2))=1.                (11)

Thus every such diagonal feature is impossible whenever d>=1, equivalently
R>=sqrt(17)/2. The joining endpoint is included in the exclusion.

## 5. Literal West/strict opposite-return application

Retain the complete original owner chart of

`WEST_STRICT_OPPOSITE_RETURN_HAND_APERTURE_MASK_COVER_AND_UNIQUE_CENTRAL_EXCLUSION_2026_10_31.md`,

Sections 1--3, with its strict support-cone identity. The same original
B,C own the nonparallel exterior axes b_ext,c_ext. If N is the original
unloaded true2 diagonal channel, the already common incident-diagonal
avoidance makes both endpoints own n. Hence their actual square frames
are parallel. Their own axes b_ext,c_ext must be parallel or perpendicular;
the strictly negative determinant in that source rules out parallelism.
They are perpendicular.

The full loaded-endpoint cone theorem

`LOADED_ENDPOINTS_FORCE_TRANSMITTER_CONE_AND_PHYSICAL_CORNER_CAP_2026_10_29.md`

applies to the original strict positive combination Delta=K-L of those
same exterior axes. It retains both whole loaded B2,C2 stars and the
original channel force and torque. It puts n in their closed positive
cone. Of the four common own-axis directions plus or minus b_ext and
plus or minus c_ext, only b_ext and c_ext lie in that cone. The two
remaining diagonal directions are precisely the two cases of Section 4.

Consequently the entire West/strict opposite diagonal feature is excluded
for d>=1. No generated projection-gap certificate is needed in this
whole radius sector. Any diagonal survivor must satisfy the stricter
same-nine-square window

    14/15<d<1,
    2<R<sqrt(17)/2.

The hand R>2 invocation in this caller is the same explicit measure path
printed in the companion monotonicity source, through
`NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md`,
`NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md`, and
`ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md`, Section 3. No historical
checker is used.

The remaining diagonal interval d<1, nonparallel side directions, the
whole two-unique side feature, and the original D02 parent remain separate
obligations. This manuscript changes no original flag and asserts no
closure from a numerical sample. Every inequality above is a printed
whole-domain physical-square or full-force argument; no mathematical
script, generated certificate, shortened star, reselected normal,
Lean/Lake build or CI is a proof dependency.

