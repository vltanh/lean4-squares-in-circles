# Five-corner reduction and an exactly isolated candidate

This is a theorem about a specified projected contact chain. It is not yet a
reduction of every eight-square packing to that chain. The missing global
implication is kept explicit below.

## 1. The projected chain

Let five points P1,...,P5 lie in the closed disk of radius R<2 about the origin.
Let 0<=t<=pi/4, e=(cos t,sin t), and f=(-sin t,cos t). Suppose

    (P2-P1).y >= 2,
    (P2-P3).x >= 3,
    (P3-P4).y >= 2,
    f dot (P4-P5) >= 1+sin t,
    e dot (P1-P5) >= 2+cos t.                 (1)

These are precisely the five projected corner constraints of the candidate
family. Their numbers come from chains of unit-square widths, not sampled
point distances. The first three involve the common orientation of six squares;
the last two involve the second orientation of the two-square chain.

Put q=R^2 and y=P1.y. Define successively

    x1=sqrt(q-y^2),              x2=sqrt(q-(y+2)^2),
    x3=x2-3,                    y3=sqrt(q-x3^2),
    y4=y3-2,                    x4=-sqrt(q-y4^2),
    h1=cos(t)*x1+sin(t)*y-2-cos(t),
    h2=-sin(t)*x4+cos(t)*y4-1-sin(t).

A necessary condition for (1) is

    F(q,y,t):=h1^2+h2^2-q <= 0.              (2)

### Proof, including the directions of all inequalities

Since P2.y>=y+2 and P2.y<=R<2, y<0. Also y>=-R>-2, so
P2.y>=y+2>0. Disk containment gives P1.x<=x1 and P2.x<=x2.
Thus P3.x<=x2-3=x3<0, and P3.y<=y3. The radicand defining y3 must be
nonnegative: |P3.x|>=3-x2, while P3 is in the disk. Next
P4.y<=y3-2=y4<R-2<0. Feasibility of P4 implies y4>=-R and hence the
last radicand is nonnegative.

For z in [-R,0], the upper bound on f dot P for points with P.y=z is

    psi(z)=sin(t)*sqrt(q-z^2)+cos(t)*z.

This function is increasing. In the interior,
psi'(z)=cos(t)-sin(t)*z/sqrt(q-z^2)>0; continuity covers the endpoints.
Consequently f dot P4<=psi(y4)=-sin(t)*x4+cos(t)*y4.
Likewise e dot P1<=cos(t)*x1+sin(t)*y.

The last two inequalities of (1) therefore imply e dot P5<=h1 and
f dot P5<=h2. Both upper bounds are negative:

    h1 <= R-2-cos(t) < 0,
    h2 <= sin(t)*R-1-sin(t) < 0.

For the second line use y4<0, -x4<=R, sin(t)<=1, and R<2. Squaring the
negative projections increases their magnitudes, so

    q >= |P5|^2 = (e dot P5)^2+(f dot P5)^2 >= h1^2+h2^2.

This proves (2). No active-contact equality was assumed in this implication.

Conversely, if the radicands are nonnegative and (2) holds, the five points

    P1=(x1,y), P2=(x2,y+2), P3=(x3,y3), P4=(x4,y4),
    P5=h1*e+h2*f

belong to the disk and satisfy all five inequalities in (1) with equality.
Thus (2), with its radicand domains, exactly describes this projected-chain
feasibility problem. It is not just a local approximation to it.

## 2. Rationalize the tilt

Use z=tan(t/2). Then

    cos(t)=(1-z^2)/(1+z^2),  sin(t)=2z/(1+z^2).

The function F is now algebraic in q,y,z, with only four positive square roots.
Stationarity in t is equivalent to stationarity in z, since dt/dz>0.
The candidate is specified exactly by

    F(q,y,z)=0,    F_y(q,y,z)=0,    F_z(q,y,z)=0.        (3)

No decimal value is adopted as an exact solution of these equations.

## 3. A proved root enclosure

The standard-library script `verify_candidate_stationary.py` verifies a
contraction on the rational box whose center is

    q0 = 3.91553413751747532652,
    y0 = -0.92065667800760613175,
    z0 = 0.06189741100766035970,

and whose radius is 1/10^16 in each coordinate. Here the terminating decimals
are exact rational box data, not floating-point evaluations.

Let H=(F,F_y,F_z). The verifier uses the nonsingular rational matrix

    C = [ -0.270621      0          0       ]
        [ -0.226289      0.416268   0.226498]
        [ -0.129681      0.226498   0.180945].

It proves, with outward-rounded integer interval arithmetic,

    ||I-C DH(X)||_infinity < 1/100,
    x0-C H(x0)+(I-C DH(X))(X-x0) subset interior(X).

All radicands and denominators in this box are strictly positive. The map
T(x)=x-C H(x) is therefore a contraction mapping X into itself. The contraction
mapping theorem gives exactly one fixed point in X; nonsingularity of C makes
it exactly one solution of (3) in X. This establishes existence and isolation,
not merely convergence of Newton iteration.

The interval evaluator represents endpoints as integers divided by 2^110.
Addition is exact; multiplication/division use integer floor/ceiling; square
roots use integer square roots with outward rounding. First and second
partial derivatives are propagated by the product and chain rules. No
floating-point operation can accept an interval assertion.

Executed result: contraction norm is less than 1/100 and every image interval
lies strictly inside its original coordinate interval. The rational matrix
need not be an exact inverse: the verifier checks the property it uses.

## 4. Full-square construction at the isolated root

The points and centers are those of CANDIDATE_RECONSTRUCTION.md. Choosing the
remaining two axis-parallel heights as 7/20 and 27/20 avoids unnecessary
boundary equations. The following exact identities provide the zero-margin
separators:

- A/B and D/E have vertical center distance 1.
- B/C, B/T, C/D and T/D have horizontal center distance 1.
- C/T have vertical center distance 1.
- G/H have center difference e.
- e dot (A-G)=(1+cos(t)+sin(t))/2.
- f dot (E-H)=(1+cos(t)+sin(t))/2.

The five circle equalities are the outer corners P1,P2,P3,P4,P5. All other
corners and every pair not on the displayed zero-margin list have strictly
positive containment/separation slack at the isolated root. These remaining
inequalities can be checked over the whole root enclosure; the equalities
must be used symbolically rather than pretending a tiny interval containing
zero is a positive margin.

## 5. Exact limit of this result

We now have an exact, uniquely isolated stationary candidate, and an exact
scalar description of its projected-chain problem. To prove the eight-square
optimum still requires BOTH:

1. minimize F over the full projected-chain domain, not just the small root box;
2. prove that every sufficiently small eight-square packing produces this
   chain, or certify all other separating-axis/contact structures impossible.

The central-square and 2,2,2,1 marker-count reductions do not by themselves
prove the second item. Neither numerical stationarity nor the five-corner
construction is presented as an unrestricted optimality proof.
