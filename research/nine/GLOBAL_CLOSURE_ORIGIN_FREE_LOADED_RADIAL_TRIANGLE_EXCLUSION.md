# An origin-free radial triangle cannot have a true loaded degree-two third vertex

Date: October 27, 2026.

**Status: complete proposed uniform local theorem and complete terminal-fan
application, pending full root and separate independent review.** No
original gate or shared ledger is changed.

Retain all actual interior-disjoint unit squares in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60,
    M_*=91/60.

Every contained center has norm less than M_*. A unit contained beyond
an actual support of height h requires h<=d. Distinct unit centers
are at distance at least one. These are the exact bounds in
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md Section 1.

## 1. Complete local statement and unchanged force scope

Let H,X,K be three distinct actual pairwise-touching unit squares,
each avoiding O even on its boundary. Require:

* X has precisely its two positive pair edges to H,K and positive
  total circle load.
* K physically touches the containing circle, with arbitrary other
  forces and any full actual circle-weight system.
* The physical H-K contact is radial: an actual common point p and
  common separating unit normal have determinant zero.
* H retains arbitrary other actual positive forces and circle atoms.

The radial H-K pair need not have positive stress. No H or K
degree-two equation is imposed.

**Radial-triangle theorem.** This entire configuration is impossible.

The proof uses the actual two-force equation only at X. It does not
split a higher-degree body's circle force or infer radiality for an
arbitrary physical contact.

## 2. The radial edge and the complete H-pair cover

The contact point is nonzero because all three units avoid O.
The pure radial-contact geometry in
ROOTED_ORIGIN_FREE_RADIAL_CONTACT_EXCLUSIONS.md Section 1 makes
the inner unit physically circle-clear. Since K is boundary, H
must be inner. Orient the radial direction e toward K, so

    p=t e,       1<t<=d,
    H subset {e.x<=t},       K subset {e.x>=t}.        (1)

The strict t>1 follows from origin avoidance of the inner H.
If d<=1 this already contradicts (1). No later proof assumes
such radii have been silently removed.

Let n be the original H-to-X unit normal with positive magnitude
mu, and let m be the original X-to-K normal with magnitude nu.
Let G be X's full original positive circle resultant. Its exact
force equation is

    G=mu n-nu m.                                     (2)

The H pair n,e cannot be opposite parallel normals: its two
neighbors X,K would then lie beyond opposite supporting faces
of H, separated by positive width, and could not touch.
If n=e, both X,K lie beyond the same support e.x=t>1.
Their actual centers have e projection greater than 3/2 and norm
less than M_*. The corresponding cap rectangle has squared diameter

    (M_*-3/2)^2+4(M_*^2-9/4)=29/144<1,

contradicting their center separation. Thus n and e are nonparallel.

The purely physical triangle proper-port theorem, with every actual
mean retained, gives the H concurrence

    q_H=h e,                       h<=t.              (3)

This is the intersection of the original HX line and the specified
physical radial HK line. Properness at their actual HK application
is exactly t-h>=0. It uses no external moment premise at H.

Because X is truly loaded degree two and has the actual boundary
neighbor K, TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md Lemma 2.1
gives a nonparallel pair at X and

    q_X=s G,                       s>0,               (4)

with both original X ports proper. Both physical circle masks
and zero individual corner-weight endpoints remain. In particular,
q_X need not be inside a physical two-corner X.

At K, either its two triangle lines are nonparallel, giving

    q_K=k e,                       k>=t>1,             (5)

or they are parallel with the same outward sign, giving m=e.
The opposite-sign K pair would separate its touching neighbors
H,X and is impossible. These are geometric statements about
the two triangle lines, not K's full force equation.

## 3. The actual H concurrence lies strictly behind O

First suppose K's triangle pair is nonparallel. Properness on the
HX and XK edges gives

    q_X-q_H=ell n,       q_K-q_X=eta m,
    ell,eta>=0.                                      (6)

We show G and e are independent. If they were parallel, all
three concurrences would lie on the e line. A nonzero first
difference in (6) would make n parallel to e, already excluded.
A nonzero second difference would make K's pair parallel.
Hence all three concurrences coincide. Equations (3),(5) then
force that common point to be p=t e. Every proper coefficient
in (6) vanishes, so both original X ports also equal p.

By (4), G is a positive multiple of e. The two nonparallel
outward X normals at p have positive sum -G. A side-interior
normal cone is one-dimensional, so p must be an X vertex.
The positive sum of two independent normals in its right-angle
normal cone lies strictly inside that cone. Thus e points
strictly into X from p: p+rho e belongs to int X for sufficiently
small rho>0.

But e is an inward support normal of the actual outer K at p.
The square support-point inward-segment fact puts p+rho e in
closed K for sufficiently small rho>0, even at an endpoint.
A point of closed K inside int X implies interior overlap nearby.
This contradiction proves independence.

Both ell,eta in (6) are now strictly positive. Substitute (6)
and q_X=sG into (2). Comparing the independent e coefficient gives

    (mu/ell)h+(nu/eta)k=0.

Since k>0, this yields h<0.

If K's triangle pair is parallel, m=e. Equation (2) becomes
mu n=G+nu e; because n,e are independent, so are G,e.
The first relation of (6) still holds, with ell>0. Comparing
the e coefficient in

    sG-h e=ell n=(ell/mu)(G+nu e)

gives h=-ell*nu/mu<0. Thus in every actual K alternative,

    q_H=-sigma e,                    sigma>0.         (7)

The only force equation used in these coefficient comparisons is
the complete true equation (2) at X.

## 4. Both actual boundary neighbors enter the same strict center cap

Since H avoids O, choose and reflect an actual own axis u so
H has interval [a,a+1] with a>0 on that axis. Write its other
own interval as [b,b+1], and put A_0=a+1>1.

The real radial support point p=t e belongs to H. Its u coordinate
is positive, so e_u>0. It therefore maximizes the u coordinate:

    p_u=A_0=t e_u,
    e_u=A_0/t>1/d>60/61,
    |e_v|<11/61.                                     (8)

In particular p_v belongs to [b,b+1].

Write P for the original HX port. Pure triangle properness and (7)
give

    P=q_H+z n=-sigma e+z n,            z>=0.

Its u coordinate is at least a>0 while (q_H)_u<0.
Hence z>0,n_u>0, so P lies on H's same far own side:

    P_u=A_0.

The exact slope identity is

    n_v/n_u=(P_v+sigma e_v)/(A_0+sigma e_u).           (9)

This is a positive weighted mean of P_v/A_0 and e_v/e_u.
The latter is p_v/A_0, by (8), and is within the actual
far-side transverse interval.

If n_v>0, P_v=b+1, so (9) gives n_v/n_u<=P_v/A_0.
If n_v<0, P_v=b, so it gives n_v/n_u>=P_v/A_0.
For n_v=0 the following comparison is immediate as well.
Multiplying by the correctly signed n_v yields

    P_v n_v>=A_0 n_v^2/n_u,
    h_H(n)=A_0 n_u+P_v n_v>=A_0/n_u>1/n_u.           (10)

No own-side mean was replaced; the axis case retains P_v exactly.
The actual contained neighbor X requires h_H(n)<=d. Therefore

    n_u>60/61,       |n_v|<11/61,       h_H(n)>1.      (11)

For X's real center c_X, its halfwidth in direction n is at least
1/2, so c_X.n>3/2. Its transverse component is less than
sqrt(181)/60<27/120. Resolving along the actual own axis u,

    c_X.u>(3/2)(60/61)-(27/120)(11/61)
                =3501/2440=:L_*.                    (12)

The actual K center satisfies c_K.e>=t+1/2>3/2.
Equations (8) and the same transverse bound give c_K.u>L_* too.
Thus these two distinct actual centers belong to one cap rectangle
whose squared diameter is

    (M_*-L_*)^2+4(M_*^2-L_*^2)
        =52124381/53582400<1.                         (13)

This contradicts their distance at least one. The radial-triangle
theorem is proved, including every parallel-K, coincident-port,
side-axis and two-corner concurrence endpoint.

## 5. A whole terminal five-body fan cannot lie outside an origin-interior unit

Let the actual positive fan consist of a hub H and path

    1-2-3-4,

with all four H spokes. Allow arbitrary further original forces
only at H. The path endpoints retain their true degree two;
the inner vertices retain their true degree three. Suppose a
distinct actual unit E outside the fan contains O in its open
interior. Then all five closed fan units avoid O.

The two endpoints are loaded because each has touching neighbors.
At either internal path vertex, its hub neighbor touches both
other path neighbors. The full radius-free
NO_UNLOADED_DIAMOND_HUB.md therefore forces that actual degree-three
vertex loaded. All four private path units are physical boundary
units, with their complete original circle systems.

Let h_i be the actual weighted origin moment of the spoke directed
H to i. Let k_i be that of the path edge i to i+1. The unchanged
private moment equations, whose circle terms are radial, give

    k_0=0, k_4=0,
    h_i=k_i-k_(i-1)                for i=1,2,3,4.      (14)

Every actual k_1,k_2,k_3 is nonzero: a zero would make a physical
contact between two boundary units radial, contrary to the pure
radial-contact clearance theorem.

If a nonzero k_i is a strict positive local maximum of the
sequence k_0,...,k_4, then

    h_i>0,      k_i>0,      -h_(i+1)>0.

The three actual geometric line moments around the physical triangle
H-i-(i+1)-H have those same signs, since original magnitudes are
positive. The complete geometric triangle moment-circuit theorem
excludes that triangle beside the actual origin-interior E.
The same argument, with signs reversed, excludes every strict
negative local minimum.

There must therefore be an adjacent nonzero plateau among
k_1,k_2,k_3. To see this, if any value is positive, take the
largest positive value. A maximal block on which it is attained
cannot have length one, which would give the forbidden strict
local maximum; the endpoints k_0,k_4 are zero. If all values are
negative, apply the same argument to their minimum. Hence either

    k_1=k_2, so h_2=0,
    or k_2=k_3, so h_3=0.                             (15)

In the first case the physical H-2 contact is radial. Vertex 2
is boundary, vertex 1 is genuinely loaded degree two with exactly
the neighbors H,2, and all three units avoid O. Sections 1--4
exclude the physical triangle H-1-2.
In the second case use the actual triangle H-4-3 instead.
Thus the entire terminal hub-rooted fan is impossible beside E.

This whole-family result retains every original H force and imposes
no isolated-fan equilibrium at H. It uses only the unchanged private
circle moments in (14); it neither deletes a chord nor turns a
degree-three private vertex into a transmitter.

In C3.335.b0 with a middle triangle and a terminal hub-rooted fan,
the intact opposite triangle supplies exactly such an E. This
therefore excludes that whole original rooted fan case. In the
two-intact-petal common-hub bouquet, the separate seven-boundary-
neighbor theorem excludes the same rooted fan, because its hub
touches eight physical boundary units.

The other rooted five-body graphs and root orbits remain separate
obligations. No coarse closure, new fine gate, numerical pose,
Lean compilation, CI, remote action or shared-ledger edit is
asserted by this source.
