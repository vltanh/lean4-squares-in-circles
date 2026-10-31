# A radial triangle with a zero-moment opposite pair, and every outside-origin fan

Date: October 27, 2026.

**Status: complete proposed uniform geometric theorem and whole-fan
assembly, pending full root and separate independent review.**
Mathematical text is frozen for audit. No original gate, shared ledger,
Lean file, workflow, or remote branch is changed.

Keep the original actual interior-disjoint unit squares in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60,       M=91/60.

Every contained center has norm less than M. A contained unit beyond
a unit support of height h requires h<=d. These are the exact bounds
of `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md`, Section 1.

## 1. A geometric two-port statement with its exact coefficient scope

Let I,J,K be three distinct pairwise-touching actual unit squares.
Suppose a specified physical I-J contact has common point p and
separating unit normal e with

    p=t e,       t>0,
    I subset {x:e.x<=t},       J subset {x:e.x>=t},
    O not in the closed I.                               (1)

The direction is chosen so I is the inner endpoint. Let n be a
specified actual common unit normal from I to K, with common point P,
and m a specified actual common unit normal from K to J, with common
point Q. Retain every original selected normal and aggregate mean
when these are positive certificate edges.

Assume there exist positive numbers mu,nu such that

    -mu det(P,n)+nu det(Q,m)=0.                         (2)

**Geometric radial-triangle theorem.** These hypotheses are impossible.

No degree, circle-load, or other-force hypothesis is imposed on K.
It may contain O. No force equation is imposed on I or J. The numbers
mu,nu may be the original positive magnitudes when their two K
moments cancel. More generally, the conclusion is a geometric one
for positive algebraic coefficients satisfying (2). Such auxiliary
coefficients are never asserted to be a new physical stress or
assigned to original circle atoms.

For the proof abbreviate

    F=mu n-nu m.

This is just the negative of the displayed weighted outward K pair.
If mu,nu are the original magnitudes, F is its complete balancing
external resultant whenever that actual external system is kept.
Neither interpretation adds a boundary or positive-circle premise.

## 2. Radial geometry and the nonparallel pair at I

The pure radial-contact geometry in
`ROOTED_ORIGIN_FREE_RADIAL_CONTACT_EXCLUSIONS.md`, Section 1, gives

    1<t<=d,       dist(O,J)=t.                           (3)

For completeness, choose and reflect an own I axis u whose closed
interval is [a,a+1] with a>0. The positive radial point on that axis
has positive e component, and its support maximum is a+1>1.
Therefore t>1. The upper bound in (3) is the contained-neighbor
support bound. The actual segments p-[0,1]e in I and p+[0,1]e in J
are retained: each is an inward normal segment of a unit square.

The two actual I normals n,e are nonparallel. Opposite signs would
separate the touching neighbors J,K beyond opposite I supports.
Equal signs would put both J and K beyond the same height t>1.
Their centers would have e-coordinate greater than 3/2 and norm
less than M; the corresponding cap rectangle has squared diameter

    (M-3/2)^2+4(M^2-9/4)=29/144<1,

contradicting their disjoint open radius-1/2 incircles.

The complete physical triangle proper-port theorem in
`RADIAL_TRIANGLE_CONCURRENCE.md`, Section 1, hence gives

    q_I=h e,       h<=t.                                (4)

That theorem is geometric: each original port is behind its outward
normal from the genuine concurrence, with a nonnegative coefficient.
It applies to arbitrary actual normal owners, shared means and
coincident ports. No shortened equation at I or J is used.

## 3. Every nonparallel K pair forces h<0

Suppose n,m are nonparallel, so K has a genuine concurrence q_K.
Equation (2) gives

    det(q_K,F)=0,       F!=0.                            (5)

No sign of the proportionality in (5) is assumed.

### 3.1. The J pair is nonparallel

Its concurrence is q_J=j e with j>=t>1. Properness on the two
remaining actual edges gives

    q_K-h e=lambda n,       j e-q_K=eta m,
    lambda,eta>=0.                                      (6)

First q_K cannot be collinear with e. Otherwise independence of n,e
forces lambda=0, and independence of m,e forces eta=0. Thus
q_K=q_I=q_J=p=t e, and every proper length on both K edges vanishes.
Both actual K applications P,Q equal p.

The two independent outward K normals at that vertex are -n and m.
Their positive weighted sum is -F, strictly inside the actual vertex
normal cone. Hence F points strictly into K from p. Equations (5)
and p=t e make F a nonzero multiple of e. If it is a positive
multiple, p+rho e lies in int K for sufficiently small rho>0 and
in the actual closed J. If it is a negative multiple, p-rho e lies
in int K and the actual closed I. Either produces open-interior
overlap: interior points of the latter square approach its displayed
closed point inside the open K. This excludes both signs, without
using the origin location or circle load of K.

Therefore q_K and e are independent and lambda,eta>0. Substituting
(6) into the definition of F gives the exact identity

    F=(mu/lambda+nu/eta)q_K
          -[(mu/lambda)h+(nu/eta)j]e.                   (7)

Equation (5) and the independence now force the coefficient of e
to vanish. Thus

    (mu/lambda)h+(nu/eta)j=0,

and h<0 because j>0. In fact (7) also proves that q_K is a positive
multiple of F; this sign is a conclusion, not a boundary or leaf
assumption at K.

### 3.2. The J pair is parallel

Its outward normals cannot have opposite signs because its two
neighbors I,K touch. Equal signs give m=e. Properness on IK still
gives q_K=h e+lambda n with lambda>=0. Using (2),(5) and
F=mu n-nu e, with independent e,n, yields

    mu h+nu lambda=0.                                  (8)

If lambda=0, then h=0 and q_K=q_I=O. The total proper length on
the actual IK edge is zero, so its actual application is O. This
contradicts the closed-origin avoidance of I. Consequently
lambda>0, and (8) gives h<0 here too. No concurrence or two-force
equation was assigned to the parallel J.

## 4. The complete parallel K case

Opposite outward K normals would separate its touching neighbors
I,J, so both have the same sign. In the displayed orientation this
means m=-n. The pair at I is already nonparallel, so e,n are
independent. The J pair, with outward normals -e and n, is also
nonparallel. Write its proper concurrence as q_J=j e, j>=t>1.

The original actual K ports, viewed at I and J, have the forms

    P=h e+a n,       Q=j e+b n,       a,b>=0.

Both outward K normals equal -n. Its exact moment condition (2)
therefore gives

    0=det(mu P+nu Q,n)=(mu h+nu j)det(e,n).

The last determinant is nonzero, whence h=-nu j/mu<0. This proof
uses the entire original positive mean in (2); it assumes neither
a radial S/D form nor any particular circle force at K.

Sections 3--4 establish in every case

    q_I=-sigma e,       sigma>0.                       (9)

## 5. The original two neighbors enter one impossible center cap

Retain the fixed own axis u and interval [a,a+1] of I from Section 2,
and put A=a+1>1. Let v be its other own axis, with transverse interval
[b,b+1]. The actual radial point p=t e maximizes the u coordinate, so

    p.u=A=t(e.u),       e.u>60/61,
    |e.v|<11/61.                                       (10)

The actual IK port has P=-sigma e+z n, z>=0, by properness and (9).
Since P.u>=a>0 and the concurrence has negative u coordinate,
z>0 and n.u>0. Consequently P.u=A. Its exact normal slope is

    (n.v)/(n.u)=(P.v+sigma(e.v))/(A+sigma(e.u)).          (11)

This is a positive weighted mean of (P.v)/A and (p.v)/A. The latter
belongs to the real transverse side interval. If n.v>0, P is its
upper endpoint and (11) is at most (P.v)/A; if n.v<0, P is its
lower endpoint and the inequality reverses. The zero case keeps
the original side mean. Multiplying by the correctly signed
vertical component gives in every case

    P.n>=A/(n.u)>1/(n.u).

The unchanged contained K requires P.n<=d. Thus

    n.u>60/61,       |n.v|<11/61,       P.n>1.           (12)

The two actual centers c_J,c_K have projections greater than 3/2
along e,n respectively and total norm less than M. Each transverse
component is less than sqrt(181)/60<27/120. Resolving both in the
same fixed u direction with (10),(12) gives

    c_J.u,c_K.u > (3/2)(60/61)-(27/120)(11/61)
                   =3501/2440=:L.

Their common cap rectangle has squared diameter

    (M-L)^2+4(M^2-L^2)=52124381/53582400<1.

This contradicts center separation and proves the entire geometric
radial-triangle theorem. Only the inner I had to avoid O; K's own
origin position, full degree, original loads and other forces remain
unrestricted throughout.

## 6. A geometric triangle with one zero directed moment

Let three actual pairwise-touching units all avoid O. Retain their
actual common points and common separating normals around one cyclic
orientation. Suppose one directed geometric line moment is zero and
the other two are nonzero with the same sign.

The zero-moment contact is radial and nonzero. Orient its endpoints
as I inner and J outer; both avoid O. At the opposite body K, the
two outward geometric moments have opposite nonzero signs. Choose
positive algebraic coefficients mu,nu to make their sum zero, for
example by taking the reciprocal of each absolute moment. All
hypotheses (1)--(2) then hold, so Sections 1--5 exclude the triangle.

These coefficients serve only the geometric proof. No original pair
magnitude, circle weight, normal, or mean is modified. No independent
physical triangle stress is asserted. If all three directed moments
are zero, the same contradiction follows with any positive mu,nu
at the opposite pair of any radial edge.

Together with `ROOTED_GEOMETRIC_TRIANGLE_MOMENT_CIRCUIT_EXCLUSION.md`,
this excludes a directed physical triangle beside an outside actual
origin-interior unit whenever all three moments are strictly the
same sign, or exactly one is zero and the other two have that sign,
or all three are zero. The case of exactly two zero moments and one
nonzero moment is not claimed by this statement.

## 7. Any complete fan with zero external moments excludes an outside origin unit

Let an actual positive fan have hub H and path 1,...,s, with s>=2.
Retain every spoke H-i and every path edge i-(i+1). Its vertices
may have arbitrary further actual forces and original circle loads,
provided the complete system external to this displayed fan has
zero origin moment at every vertex. No endpoint degree-two or
boundary-neighbor premise is imposed.

Suppose a distinct actual unit E outside the fan has O in int E.
Every closed fan body then avoids O. Write h_i for the original
weighted moment of H-to-i and k_i for that of i-to-(i+1), with
k_0=k_s=0. The unchanged full vertex moment equations give

    h_i=k_i-k_(i-1),       i=1,...,s.                    (13)

If all k_i vanish, every moment on any actual fan triangle vanishes,
contrary to Section 6.

Otherwise choose a largest positive value among the k_i if one
exists; if none exists choose a smallest negative value and reverse
all moment signs in the following argument. Consider one maximal
contiguous occurrence interval of that positive maximum M_0>0.
It lies among indices 1,...,s-1 because the two endpoint values
are zero. Let l be its first index.

If the interval has length one, (13) gives three strictly positive
directed moments around the actual triangle H-l-(l+1)-H:

    h_l=M_0-k_(l-1)>0,       k_l=M_0>0,
    -h_(l+1)=M_0-k_(l+1)>0.

The accepted strict geometric moment-circuit theorem excludes it
beside E. If the interval has length at least two, those same
three directed moments instead have the signs positive, positive,
zero. Section 6 excludes this whole alternative. A negative
minimum gives the identical contradiction after reversing the
triangle orientation.

Every possible original moment sequence is therefore impossible.
This proves the full fan theorem, without imposing degree two at
an attachment endpoint or rescaling any physical fan stress.

## 8. Exact terminal-block and C3.335 applications

For a genuine terminal fan block, the required external origin
moment at its attachment root is zero. Sum the unchanged origin
moment equations over all original bodies outside that block:
outside internal pair moments cancel at their actual applications,
every circle moment is zero, and the remaining cut moments sum to
zero. Their reversal supplies the root's complete external pair
moment. Its circle system also has zero moment. Every other
terminal fan vertex has only its original circle system outside
the fan. The same argument applies separately to outside branches
at multiple articulations of an actual fan block.

Thus any such actual fan block is impossible whenever a distinct
outside actual unit contains O openly. In particular, for the
C3.335.b0 chain whose middle block is a triangle and whose opposite
end block is an intact triangle at A, the accepted intact-end
theorem gives O in int A outside the terminal five-body fan.
Section 7 excludes all three genuine terminal-fan root orbits:
hub, inner path vertex, and endpoint. The endpoint case retains
its true extra forces; it is the new whole original root-family
exit beyond the earlier private-endpoint source.

For a common-root bouquet, the origin-interior articulation belongs
to the fan itself and is not the outside E required in Section 7.
That complete bouquet is not declared closed here. The local
radial-triangle theorem can still apply to a specific radial edge
with origin-free inner endpoint and a verified opposite pair
moment, even when its third body is the bouquet root. A separate
argument must establish that actual radial edge in every claimed
caller. No such edge is silently inferred from bouquet pressure.

No complete C3.335 coarse-cell closure is asserted here. All other
original graph types, loads, true degrees and circle masks retain
their separate obligations. No numerical pose, sampled angle,
post-extraction normal change, physical motion, Lean compilation,
CI, workflow, remote mutation or shared-ledger edit is used.
