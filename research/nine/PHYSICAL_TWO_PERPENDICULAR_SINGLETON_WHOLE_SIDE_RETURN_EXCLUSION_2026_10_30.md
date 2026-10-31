# The entire perpendicular-singleton side return has no unloaded bridge

Date: October 30, 2026. **Complete proposed hand-and-exact-certificate theorem;
independent audit and Lean compilation are deferred.**

This closes the whole remaining **D-owned exterior-side return** in the
physical-two West/strict, A-owned perpendicular-singleton feature of
`M6.B6.HEXAGON.D02.L135`. It includes the whole original continuous angle,
radius and mean domain, all physical circle masks at B and C, and either
individual zero circle coefficient at V. The corresponding opposite-D-vertex
return remains separate. This is not closure of the original D02 load row.

The two new ingredients are a radius-free diagonal-bridge lemma and a finite
exact interval cover of the full original side-return domain. The interval
cover has 7,545 nodes, 3,773 leaves and maximum depth 26; its data is about
150 kB, with one shared 200-line checker rather than expanded tactic cases.
It proves two whole-domain support inequalities, not infeasibility inferred
from a floating-point search. All arithmetic in generation and replay is
integer arithmetic with explicitly outward rounding.

## 1. Original geometry, complete stars and inherited whole exits

Retain the actual nine contained unit squares, the same original physical
force-and-torque certificate, all contact normals, original applications or
full side means, circle masks and individual coefficients. The exact stars are

    A:{V,D,B}, D:{V,A,C}, V:{A,D},
    B:{A,N}, C:{D,N}, N:{B,C}.

A and D are unloaded true degree three; V,B,C are loaded true degree two;
N is unloaded true degree two. The other three actual squares remain present.
No selected normal, original mean, positive edge or circle coefficient is
changed. The same initially selected incident-diagonal avoidance is retained.

**Reusable full-star scope.** The displayed B2/C2 stars identify the literal
L135 caller, but neither their degree-two equations nor their loads are used
anywhere in this proof. The theorem also holds with arbitrary original true
degrees, loads and additional forces at B,C, provided the full original
A3,D3,V2,N2 stars and the stated actual contact feature are retained. The
inherited c, b and return-ratio exits have exactly this arbitrary-endpoint
scope: their proofs use actual B/C support spans and the real unit N, not a
truncated endpoint force equation. Every additional edge at B or C remains
present. Consequently this is one exclusion of the same actual six-unit
configuration inside positive components of sizes six through nine, including
attachments at B,C; it is not restricted to an isolated simple component.

Use the complete chart of
`PHYSICAL_TWO_WEST_STRICT_PERPENDICULAR_SINGLETON_ADJACENT_RETURN_EXCLUSION_AND_COMPLETE_RESIDUAL_2026_10_29.md`
and its full-star sequel
`PERPENDICULAR_SINGLETON_FULL_STAR_OPPOSITE_LARGE_COMPONENT_AND_RETURN_RATIO_EXCLUSION_2026_10_29.md`:

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, 9/10<d<61/60,
    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-t), H=t+1/2, 0<t<=1/2,
    h=(c,-s), e=(s,c), c,s>0, c^2+s^2=1,
    A=P+[-1,0]h+[-l,1-l]e,
    W=P-x*h-l*e, 0<x,l<1,
    v=W-Q=-a*h+b*e=(-u,y),
    w=-b*h-a*e=(-y,-u),
    a,b,u,y>0, a^2+b^2=u^2+y^2=1,
    a=Hs+x, b=Hc-l, u=ac-bs, y=as+bc,
    D=Q+[0,1]v+[0,1]w.

The original AV,DV,AD magnitudes are mu,nu,gamma>0. Define

    D0=1-x=1-a+Hs>0, N0=1-l=1-Hc+b>0,
    r=gamma/mu=N0/D0,
    q=gamma/nu,
    M=d*s+c/2>0.

The actual A-to-B force and support point are

    F_B=-mu*h+gamma*e,
    K=P-h+N0*e,
    f=F_B/|F_B|=(-D0*h+N0*e)/sqrt(D0^2+N0^2).

The full V torque is nu*t=mu*M. In the D-owned exterior-side row,
the complete D force and torque give exactly

    q=u/b,
    L=Q+w+z*v,
    z=u*a/c, 0<z<1.                                      (1)

The full initial closed side-mean interval is retained before this deduction;
the strict bounds on z are consequences of the original equations. C has its
actual minimum support at L in inward direction

    f_C=F_C/|F_C|=(-y,-u).                                 (2)

Indeed F_C=-nu*East-gamma*e and, using q=u/b,

    1+q*s=c*y/b, q*c=c*u/b.

The unchanged full V,A,D equations now imply the **polynomial equality**

    b*(H-1/2)*N0 = (d*s+c/2)*u*D0.                       (3)

The already complete whole-feature exits let us restrict a putative survivor
to c>3/4, b<16/25, y>3/11 and q<18/5. The first and second restrictions are
from the original complete perpendicular-singleton and upper-return
compensation sources. The y restriction is from
`ACTUAL_UNIT_PROJECTION_BRIDGE_AND_PERPENDICULAR_SINGLETON_RETURN_INTERVALS_2026_10_29.md`.
The q restriction is Section 4 of the full-star sequel. That theorem retains
the actual B--N--C unit bridge and applies to either load of N. These are
whole-domain exits, not sampled bounds. In fact the generated certificate
below uses no low-y leaf, so the y restriction is dispensable for this result.

## 2. A general diagonal-bridge obstruction with a weaker vertical hypothesis

Let (h0,e0) be an orthonormal frame. Let B have an actual minimum-support point
K in unit direction f=-A*h0+B0*e0, where A,B0>0 and A^2+B0^2=1. Let C have
an actual minimum-support point L in direction -e0. Suppose

    K-L=-E*h0+G*e0, E>=0, G>sqrt(2), |K-L|^2>3.           (4)

Keep an actual unloaded true-degree-two square N between them with its full
force and torque equations and the same incident-diagonal avoidance. Then
**N cannot be a diagonal transmitter.** This assertion does not yet exclude
a side transmitter.

Here is a full proof, including all support ties. The elementary support-span
bound gives min_B e0 >= K.e0-A and max_C e0=L.e0. For the actual N applications
T in B and U in C, therefore (T-U).e0>=G-A>0. If N is diagonal, its entire
two-force equations give

    T-U=sqrt(2)*n, n=u0*h0+v0*e0, v0>0.

Incident-diagonal avoidance forces T and U to be relative-side-interior points
in B and C. Thus both B and C own n; their actual frames are parallel.

If u0>0, put w0=-v0*h0+u0*e0. L is the joint maximum-n/maximum-w0 vertex
of C, so U=L-alpha*w0 for 0<alpha<1. Since f.w0=A*v0+B0*u0>0, an arbitrary
actual minimum-f point or side mean of B has

    K=T+xi*n-beta*w0, 0<=xi<=1, 0<beta<1.

Consequently (K-L).h0=(sqrt(2)+xi)*u0+(alpha+beta)*v0>0,
contradicting (4). This covers either sign of f.n and its exact zero tie.

If u0=0, then f.n=B0>0. K and T are on B's same minimum-n side, and L and U
are on C's same maximum-n side. Hence (K-L).e0=sqrt(2), contradicting (4).
The arbitrary original L and K side means are harmless in this vertical case.

If u0<0, f.n=-A*u0+B0*v0>0. Again K and T share B's minimum-n side and L
and U share C's maximum-n side. With w0=-v0*h0+u0*e0, L is now the minimum-w0
endpoint of that C side. Write

    U=L+alpha*w0, 0<alpha<1,
    K=T+eta*w0, -1<eta<1.

The last strict bounds hold for every point on B's side because T is in its
relative interior. They also include any full original mean at K. Thus

    K-L=sqrt(2)*n+zeta*w0, zeta=alpha+eta>-1.

By |K-L|^2>3, zeta^2>1. Therefore zeta>1. Its e0 component is then
G=sqrt(2)*v0+zeta*u0<sqrt(2), another contradiction. All signs of u0 have
been covered. This proves the diagonal obstruction at its stated general
scope, without a radius, degree or load restriction at B,C.

## 3. Exact interval cover proves two useful inequalities simultaneously

Set

    W0=D0^2+N0^2, X=-c*D0+s*N0, Y=s*D0+c*N0,
    Kx=d-c+s*N0, Ky=1/2+s+c*N0,
    J=Kx*X+Ky*Y,
    L0=c*(H+s+c*N0+u-y-1)-a*u*y,
    G=1+a-b*D0.

For every original side-return survivor the finite exact cover proves

    Y>0, W0>0, c>0,
    L0*sqrt(W0)>c*|X|,
    G>0, G^2>2.                                            (5)

The root domain is the closed rational box

    0<=s<=2/3, 0<=b<=16/25,
    1/2<=H<=1, 9/10<=d<=61/60,
    a=sqrt(1-b^2), c=sqrt(1-s^2).

It contains every original survivor; endpoints are kept even when an original
strict hypothesis makes them impossible. No division by s, b, a force or a
matrix determinant is used in the cover.

Every leaf is one of the following exact alternatives:

| Leaf | Complete justification | Count |
| --- | --- | ---: |
| `return_ratio` | 5u-18b>=0, hence the already excluded q>=18/5 | 23 |
| `full_torque` | The interval for the left-minus-right side of (3) misses zero | 1,254 |
| `B_support` | J>d*sqrt(W0), contradicting the original contained-neighbor support bound | 305 |
| `B_point` | (Kx^2+Ky^2+1-R^2)*sqrt(W0)+2J>0 | 875 |
| `bridge_exclusion` | All inequalities in (5) hold on the entire box | 1,316 |

For `B_support`, every unit contained in the same disk has center norm at most
d+1/2 and directional halfwidth at least 1/2. Since B lies beyond A's actual
minimum-f contact K, K.f<=d. Here K.f=J/sqrt(W0), with W0>0.

For `B_point`, K+f belongs to the **actual B**, regardless of its force degree,
circle mask or owner. At a minimizing vertex, the two inward own components
of f belong to [0,1], so this unit segment lies in B; at a minimizing side it
is the normal segment to the opposite side. Thus |K+f|^2<=R^2. Multiplication
by sqrt(W0)>0 gives exactly the negation of the displayed leaf inequality.
The checker uses R^2=(d+1)^2+1/4, the original physical-two mask identity.

The certificate and its complete generation/replay program are

    certificates/physical_two_perpendicular_side_return.json
    ../../scripts/n9_physical_two_side_certificate.py.

### 3.1. Arithmetic and coverage soundness

An interval [lo,hi] in the checker represents the real interval
[lo/2^40,hi/2^40]. Rational constants are rounded down/up by integer division.
Addition and subtraction are exact. Multiplication takes the minimum and
maximum of its four endpoint products, rounded outwards by division by 2^40.
Squaring uses zero as its lower bound when the interval contains zero.
For a nonnegative interval, square-root endpoints are respectively
floor(sqrt(lo*2^40)) and ceil(sqrt(hi*2^40)); `isqrt` supplies the exact integer
floor and a squared comparison supplies the possible upper increment.
Absolute value uses the analogous exact endpoint rule. Each operation therefore
encloses every real value of that expression on the full original input box.

The certificate fixes a binary split coordinate at each internal node. Its two
children are the closed intervals [lo,mid] and [mid,hi], with all other
coordinates unchanged. Their union covers the parent, including the midpoint.
Replay recomputes every leaf inequality, rejects repeated/unvisited nodes,
and traverses both children of every split from the stated root. Structural
induction on this finite tree proves its whole closed-domain conclusion.

The exact tree has 7,545 nodes and 3,773 leaves. Both rational endpoints and
all singular-looking boundary faces are included in the cover; the proof
never concludes emptiness from reaching a subdivision limit. The generator
would print `UNRESOLVED` and produce no certificate if it failed to cover
the domain. Here generation and a separate full replay both terminate
successfully, using no floating-point comparison.

## 4. The whole side transmitter is excluded

Because f has positive world vertical component Y/sqrt(W0), the whole-square
support-span inequality gives

    min_B North >= Ky-|X|/sqrt(W0).

By (2), the same inequality in the opposite direction gives

    max_C North <= L.North+y.

The unchanged original side mean in (1) has L.North=-t-u+(a*u/c)*y.
Consequently their actual whole-square gap is at least

    H+s+c*N0+u-y-(a*u/c)*y-|X|/sqrt(W0)
      =1+L0/c-|X|/sqrt(W0)>1                           (6)

by (5). Every possible original T in B and U in C has vertical difference
greater than one. The side alternative T-U=n with |n|=1 is impossible.
This excludes the full side-transmitter alternative without any equation
at B or C beyond their actual unchanged support directions.

## 5. The whole diagonal transmitter is excluded

Use the actual D frame

    h0=-v=a*h-b*e, e0=-w=b*h+a*e.

Then C's inward direction is -e0. The inward B direction is

    f=-A0*h0+B0*e0,
    A0=(a*D0+b*N0)/sqrt(W0)>0,
    B0=(a*N0-b*D0)/sqrt(W0)>0.

To check the second strict sign over the **whole** domain, note b<16/25 and
a^2+b^2=1 imply 0<b<a. Also H<=1 and ac+bs<=1. Thus

    a*N0-b*D0=a-b+2ab-H(ac+bs)>=a-b+2ab-1>0.

For the last step, use a-1=-b^2/(1+a) and

    (2a-1)(1+a)-b=1-2b^2+a-b>0.

Writing j=1-z>0, the exact original support difference is

    K-L=-(D0+a*j-b)*h+(1+a+b*j)*e
        =-E*h0+G*e0,
    E=a*D0+b+j>0,
    G=1+a-b*D0>sqrt(2).                                (7)

Here the final inequality is (5). Moreover a^2>369/625>9/16, so a>3/4 and

    |K-L|^2 >= (1+a+b*j)^2 > (7/4)^2 > 3.             (8)

Equations (7),(8) give every premise of the general diagonal obstruction in
Section 2, retaining the same actual applications and the same initially
selected incident-diagonal avoidance. The complete diagonal alternative of
N is therefore impossible as well.

The unloaded true-degree-two force/torque theorem allows exactly the side
and diagonal alternatives. Sections 4 and 5 eliminate both. Hence the entire
original D-owned side return in this physical-two perpendicular-singleton
L135 feature is impossible.

## 6. Scope, transfer and reproducibility

The proof is uniform over every physical mask and full true degree of B,C
consistent with the displayed original supports; their loaded true-two
equations were never shortened or needed. It keeps the three completing
units and proves a contradiction already among A,V,D,B,C,N. The whole-data
reflection exchanges the two physical circle-weight endpoints at V and
transports every original square, force and mean, so it is included too.

N's **unloaded** full two-force equations are essential in Sections 2,4,5.
No conclusion is asserted for loaded N in D02.L1345. The opposite-D-vertex
return, other original AD owners and the other physical-two inner-face chart
also keep their separate obligations. No original fine or coarse flag changes:
the canonical D02 load row requires their union, not just this complete feature.

Run, from the repository root:

    python scripts/n9_physical_two_side_certificate.py \
      --verify research/nine/certificates/physical_two_perpendicular_side_return.json

The exact data may be regenerated with `--output` and a node limit of 20,000.
The full check takes under one second in the current environment. This is
ordinary integer/rational certificate evidence plus the explicit hand
soundness argument; it is not yet a compiled Lean proof. A future Lean replay
must prove the common interval operations and binary split soundness once,
then check this finite data with ordinary kernel-replayable proof terms.
