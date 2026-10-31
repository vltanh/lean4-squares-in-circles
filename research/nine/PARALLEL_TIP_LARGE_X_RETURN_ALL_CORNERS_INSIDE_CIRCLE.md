# A large left-circle coordinate makes every actual parallel-tip return corner interior

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed continuous hand theorem, submitted for full independent review.** This is a self-contained all-four-corner geometric inequality. It retains the entire closed side-parameter interval and the equal-angle endpoint. Its original-force corollaries are stated explicitly; the actual physical chart must still be proved by a caller.

## 1. Full scalar and geometric theorem

Let

    x>=1, y>=1/2,
    a,b>0, a<=b, a^2+b^2=1,
    0<=r<=1,
    R^2=x^2+y^2>=4.

Define the actual reference point and unit square

    E=(1-x,y-1+r*b),
    u=(a,-b), v=(b,a),
    W=E+[0,1]u+[0,1]v.                              (1)

Assume either of the following complete alternatives:

* y<=x, with no upper radius restriction and no additional scalar inequality;
* y>=x, R^2<=5, and

      r*a*y<=x*(1-r*b).                              (2)

**Theorem.** Every corner of W has norm strictly less than R. Therefore the whole closed W lies strictly inside the disk D_R.

The equality y=x is covered by the first alternative without needing (2). The entire intervals r in [0,1], x>=1, y>=1/2, and the endpoint a=b are retained. Both R^2=4 and R^2=5 are included when they occur in the relevant alternative.

The strict open-frame assumption a>0 is essential. It is not widened to the aligned limit a=0: for example a=0,b=1,r=1,x=1 gives a W corner (1,y) with the same norm as (-1,y). Every intended nonparallel-W caller has a,b>0.

No force, torque, normal-selection or physical-circle-mask assertion is an input to this theorem. It applies to an actual W of the form (1), whatever W's degree, other contacts, load, circle weights or own-frame farthest-corner mask might have been.

## 2. Exact deficits of all four corners

Put

    B=1-r*b, 1-b<=B<=1,
    Z=(-x,y), |Z|=R.

Since 0<a<=b<1, one has B>0. Name the four actual W corners

    C_00=E,
    C_10=E+u,
    C_01=E+v,
    C_11=E+u+v.

Relative to Z their coordinates are

| Corner | Horizontal increment | Downward vertical increment |
| --- | --- | --- |
| C_00 | 1 | B |
| C_10 | 1+a | B+b |
| C_01 | 1+b | B-a |
| C_11 | 1+a+b | B+b-a |

Thus a corner with increments A,D has exact squared-radius deficit

    Delta=R^2-|C|^2=A*(2x-A)+D*(2y-D).              (3)

We prove strict positivity separately for every actual corner. No presumed W circle corner is selected.

For C_00, B in (0,1] and 2y>=1 give

    Delta_00=(2x-1)+B*(2y-B)>=1>0.                  (4)

For C_10 put A_1=1+a and D_1=B+b in [1,1+b]. If y>=1, then

    A_1*(2x-A_1)>=1-a^2=b^2,

and concavity of D_1*(2-D_1) on its closed interval gives

    D_1*(2y-D_1)>=D_1*(2-D_1)>=1-b^2=a^2.

Therefore

    Delta_10>=1>0.                                  (5)

If 1/2<=y<1, then R^2>=4 implies x>sqrt(3)>3/2. Consequently

    A_1*(2x-A_1)>(1+a)*(2-a),

while D_1>=1 and 2y>=1 give

    D_1*(2y-D_1)>=D_1*(1-D_1)>=-b-b^2.

The sum is

    Delta_10>1+a-b>0.                               (6)

This proves both first corners throughout the whole theorem, including every r endpoint.

## 3. The C_01 corner when y<=x: no torque inequality is needed

Put

    A=1+b,
    k=r*b+a-1=a-B.

Its deficit is

    Delta_01=A*(2x-A)-2y*k-k^2.                     (7)

If k<=0, then A*(2x-A)>=A*(2-A)=a^2>0. Also -k=B-a<1 and 2y>=1, so

    -2y*k-k^2=(-k)*(2y+k)>=0.

Thus Delta_01>0 in this case, without (2).

Suppose k>0 and y<=x. Since r<=1,

    0<k<=j:=a+b-1.

The quantity j is positive because a,b>0 and a^2+b^2=1. Also x>=sqrt(2), since x>=y and x^2+y^2>=4. Equation (7) gives

    Delta_01
      >=2x*(A-j)-A^2-j^2
      >=2sqrt(2)*(2-a)-A^2-j^2.                    (8)

Here A-j=2-a>0. Expanding the final expression, using 2ab<=1, and completing a square gives

    2sqrt(2)*(2-a)-A^2-j^2
      =4sqrt(2)-4+a^2-2ab+2a*(1-sqrt(2))
      >=6sqrt(2)-8+(a-(sqrt(2)-1))^2
      >0.                                          (9)

The last strict sign follows from sqrt(2)>4/3.

This proves the whole C_01 corner whenever y<=x, for every R>=2, every r in [0,1], and every permitted a,b. No force inequality or upper radius bound was used.

## 4. The C_11 corner when y<=x

Its squared norm is a convex quadratic function of r, because its r-dependent displacement is the vertical vector r*b. It is therefore enough to check both closed endpoints r=0 and r=1.

At r=0 its exact deficit simplifies to

    Delta_11(0)
      =2[(x+y-2)(1+b)+(x-y)a].                      (10)

When y<=x, both terms are nonnegative and x+y>2: indeed x,y>0 and x^2+y^2>=4. Hence (10) is strictly positive.

At r=1 the increments are

    A_3=1+a+b<=1+sqrt(2),
    D_3=1-a in (0,1).

As x>=sqrt(2),

    2x>=2sqrt(2)>1+sqrt(2)>=A_3,

and 2y>=1>D_3. Both terms in (3) are strictly positive.

Thus Delta_11 is strictly positive at both endpoints. Convexity of the squared norm, equivalently concavity of the deficit, proves positivity for every r in [0,1].

Together with Sections 2--3, this proves the theorem's entire first alternative. In particular this whole alternative is independent of (2) and has no upper-radius bound.

## 5. The C_01 corner when y>=x: the whole maximal-parameter comparison

Assume y>=x, 4<=R^2<=5, and (2). Since x>=1, here y>=1. If the actual k in (7) is nonpositive, the argument before (8) already proves Delta_01>0.

For the remaining case, rewrite (2) as

    r<=r_*:=x/(a*y+b*x).                             (11)

The denominator is positive. Since y>=x and a+b>1,

    0<r_*<=1/(a+b)<1.

For the fixed actual x,y,a,b, the upper comparison parameter gives

    K:=a-1+b*r_*
      =a-a*y/(a*y+b*x).                             (12)

Thus k<=K, and if the actual k>0 then K>0. On the positive k interval the expression (7) strictly decreases with k. It is consequently enough to prove

    D(x):=(1+b)*(2x-1-b)-2y*K-K^2>0,                 (13)

where R,a,b are fixed, y=sqrt(R^2-x^2), and

    1<=x<=R/sqrt(2).

The comparison r_* is only a scalar upper bound. No actual mean, W pose, or force equation is replaced.

Write

    L=a*y+b*x,
    J=a*b*R^2/L^2.

Direct differentiation along this fixed-radius interval gives

    y'=-x/y,
    K'=a*b*R^2/(y*L^2)>0,
    D'/2=[y*(1+b-J)+K*(x-J)]/y.                    (14)

The elementary square (a*y-b*x)^2>=0 gives

    L^2>=4abxy,
    J<=R^2/(4xy)
       =(y/x+x/y)/4.

Here 1<=y/x<=2: use x>=1 and y^2=R^2-x^2<=4. Since t+1/t increases for t>=1,

    J<=5/8.                                         (15)

Whenever K>0, (14)--(15) show D'>0, because 1+b>1 and x>=1.

If K<=0, one has K>a-1>-1 and

    D(x)>=(1+b)*(1-b)+(-K)*(2y+K)>0.                (16)

Thus only the left endpoint x=1 of a possible positive-K interval requires a separate check. Since K'>0, the set K>0 is an interval. If it begins after x=1, its initial limiting value has K=0 and is already positive by (16); then (14) keeps D positive. If it includes x=1, Section 6 proves the needed initial positivity.

This is a whole continuous derivative argument. No values of x or r are sampled.

## 6. Exact positivity at x=1

At x=1 put y=sqrt(R^2-1), so

    sqrt(3)<=y<=2.

If K<=0, (16) applies. Suppose K>0. By (12),

    K=a*[b-(1-a)y]/(a*y+b)>0.

Thus b>(1-a)y>0. Since y>=sqrt(3), squaring gives

    1-a^2>3*(1-a)^2,

and therefore

    1/2<a<=1/sqrt(2).                               (17)

At x=1, expand (13). The exact factorization is

    D(1)=a*y*P(y)/(a*y+b)^2,                         (18)

where

    P(y)=2a(1-a)y^2
         -(2a-1)(2b-a)y
         -2b(b-a).                                  (19)

Here is a uniform positive bound on the whole interval (17).

First, P increases for every y>=sqrt(3). Indeed

    P'(y)=4a(1-a)y-(2a-1)(2b-a).

On (17),

    a(1-a)>1/5,
    y>=sqrt(3)>5/3,
    2a-1<1/2,
    2b-a<5/4.

The first comparison follows from a(1-a)>=(sqrt(2)-1)/2>1/5. The last uses b<sqrt(3)/2<7/8 and a>1/2. Hence

    P'(y)>4/3-5/8=17/24>0.                          (20)

It remains to bound P(sqrt(3)). Its positive term satisfies

    6a(1-a)>=3*(sqrt(2)-1).                          (21)

For its first negative term, sqrt(3)<7/4 and 2b-a<5/4 give

    sqrt(3)*(2a-1)*(2b-a)
      <(35/16)*(2a-1).                              (22)

For the second, b<2a and a<=b imply

    2b(b-a)
      =[2b/(a+b)]*(1-2a^2)
      <=(4/3)*(1-2a^2).                             (23)

Define the single comparison quadratic

    H(a)=(35/16)*(2a-1)+(4/3)*(1-2a^2).

Its derivative is

    H'(a)=35/8-(16/3)a>3/8>0,

because a<3/4. Therefore, throughout (17),

    H(a)<=H(1/sqrt(2))
         =(35/16)*(sqrt(2)-1).                      (24)

Combining (21)--(24),

    P(sqrt(3))
      >(13/16)*(sqrt(2)-1)>0.                        (25)

Equations (20),(25) prove P(y)>0 for every y>=sqrt(3) in the actual domain. All factors outside P in (18) are strictly positive. This proves D(1)>0.

Sections 5--6 prove the whole C_01 corner in the second alternative, including x=1, R^2=4 or 5, a=b, and equality in (2).

## 7. The C_11 corner when y>=x and a>=1/4

This section does not need (2) or the upper-radius bound.

The actual center of W has u-coordinate

    E.u+1/2
      =1/2-[a(x-1)+b(y-1)]-r*b^2.                  (26)

We prove

    a(x-1)+b(y-1)>1/2                               (27)

whenever x>=1, y>=x, x^2+y^2>=4, and 1/4<=a<=b.

For 1<=x<=sqrt(2), the radius bound gives y>=sqrt(4-x^2). The function

    a(x-1)+b*(sqrt(4-x^2)-1)

is concave in x, so its minimum on that entire interval is at an endpoint. The two endpoint values are

    b*(sqrt(3)-1),

and

    (a+b)*(sqrt(2)-1).

The first exceeds 1/2 because b>=1/sqrt(2) and

    sqrt(3)>1+1/sqrt(2).

That radical inequality follows by squaring from sqrt(2)<3/2.

For the second, a+sqrt(1-a^2) increases on [1/4,1/sqrt(2)], so

    a+b>=(1+sqrt(15))/4.

Consequently the second endpoint exceeds 1/2: this is equivalent to

    sqrt(15)>1+2sqrt(2),

which again follows by squaring from sqrt(2)<3/2.

If x>=sqrt(2), use y>=x directly to obtain the same strict lower bound

    a(x-1)+b(y-1)>=(a+b)*(sqrt(2)-1)>1/2.

This proves (27) throughout the whole domain.

Equation (26) is thus strictly negative for every r in [0,1]. The two actual corners C_01 and C_11 differ by u, so

    |C_11|^2-|C_01|^2=2*(E.u+1/2)<0.                (28)

The entire C_01 proof already gives |C_01|<R. Therefore C_11 is strictly inside as well. This retains the equal-angle endpoint a=b.

## 8. The C_11 corner when y>=x and 0<a<1/4

Again its squared norm is convex in r, so check r=0 and r=1.

At r=0, equation (10) can be rewritten as

    Delta_11(0)
      =4(x-1)(1+b)+2(y-x)(1+b-a)>0.                 (29)

The two terms are nonnegative; they cannot both vanish under x^2+y^2>=4 and x>=1.

At r=1 set

    A_3=1+a+b<9/4,
    D_3=1-a in (3/4,1).

One also has A_3>2, since a+b>1, and y>=sqrt(2), since y>=x and x^2+y^2>=4. Thus

    A_3*(2x-A_3)>=A_3*(2-A_3)>-9/16.

The function t*(2sqrt(2)-t) increases on 0<t<=1, so

    D_3*(2y-D_3)
      >=D_3*(2sqrt(2)-D_3)
      >(3/4)*(2sqrt(2)-3/4)
      >123/80,

where the last comparison uses sqrt(2)>7/5. Hence

    Delta_11(1)>-9/16+123/80=39/40>0.               (30)

Both endpoints are strictly inside, so convexity covers every r in [0,1]. Equations (28)--(30) exhaust the complete a interval.

All four actual corners have now been proved strictly inside in both theorem alternatives. Since the squared norm is convex and the square is the convex hull of its four corners, its maximum on W occurs at a corner. The whole closed W lies in the open disk. This completes the theorem.

## 9. Exact original unique-mask corollary

The theorem applies directly to the following unchanged physical chart.

Let the actual positively loaded V be true pair degree two and have

    V=[-x,1-x] x [y-1,y],
    x>1/2, y>1/2,
    R^2=x^2+y^2.

Its unique physical circle corner is (-x,y). Let its original neighbor U lie across its bottom side and W lie across its right side. Let their original positive magnitudes be mu,nu, so full V force gives the full circle resultant

    F_V=(-nu,mu)=Lambda*(-x,y), Lambda>0.             (31)

Suppose the actual W is exactly (1), with its original V-W application E, and suppose the unchanged original U-V application is

    P=(p,y-1),
    r*a-x<=p<=1-x.                                  (32)

The entire interval in (32), including either endpoint and an arbitrary original shared-side mean, is retained.

The original true V2 torque about the unchanged circle origin is exactly

    mu*p+nu*(y-1+r*b)=0.                            (33)

Equation (31) gives mu=Lambda*y and nu=Lambda*x. Substitute (32) into (33) to obtain

    p=-x*(y-1+r*b)/y>=r*a-x,

or precisely

    r*a*y<=x*(1-r*b).                               (34)

No strict inequality is needed. No coefficient of an individual circle atom is divided out except the positive total unique-corner coefficient Lambda.

If x>=1 and 4<=R^2<=5, the whole theorem therefore applies, using either alternative according to the actual x,y. It makes every actual W corner strictly inside the circle. An actual physical-boundary W cannot satisfy this.

Consequently any actual unique-mask caller with (1),(31)--(33), physical-boundary W, and 4<=R^2<=5 must have

    x<1.                                            (35)

This corollary uses the full original V2, not a counterfactual force equation at a higher-degree body. It uses no force or torque equation at W.

The theorem does not itself derive the actual chart (1), the original interval (32), or a<=b from a graph. Those are explicit caller obligations. In particular it does not replace the real U-W application Q=E+r*u by E.

## 10. Exact full horizontal physical-two corollary

Suppose instead the actual V in the same global frame has the horizontal physical-two mask

    y=1/2,
    V=[-x,1-x] x [-1/2,1/2],
    x=sqrt(R^2-1/4),
    R>=2.

Its two physical circle corners are (-x,-1/2),(-x,1/2). Retain the complete original resultant

    F_V=Lambda*(-x,xi),
    Lambda>0, -1/2<=xi<=1/2.                         (36)

If the incoming and outgoing actual V forces have the signs in (31), the full force equation merely forces xi>0. No particular value of xi, equal weights, or positive coefficient at both physical corners is assumed.

In fact no V force equation is needed for the geometric exit. One has

    x>=sqrt(15)/2>1,
    y=1/2<x.

Thus the theorem's entire first alternative applies to every actual W of the form (1), with a,b>0,a<=b and every r in [0,1]. It proves W strictly inside the circle for every R>=2, without an upper radius bound or the torque inequality (34).

This excludes the whole horizontal physical-two V mask of this actual chart. Every individual zero circle coefficient and the entire resultant interval remain covered.

The vertical physical-two mask x=1/2 is outside this large-x conclusion. Its treatment, and the actual placement, support-owner cover and closing-pocket allocation of a complete original family, require the caller's separate arguments. No original whole-family checkbox is changed here.

## 11. Dependencies, endpoints, and verification boundary

The all-four-corner theorem in Sections 1--8 is self-contained. It uses only the printed exact coordinate expansions, elementary convexity/concavity, the full fixed-radius derivative, and the explicit monotone quadratic estimate. It requires no imported numerical certificate or geometric case reduction.

For the meaning of the unchanged force and torque data in Sections 9--10, the operative source is:

| Source | SHA-256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original radial circle forces, complete positive neighborhoods, actual shared means and origin torque convention in the two corollaries |

Every new scalar and corner comparison is printed above.

The theorem explicitly retains r=0, r=1, a=b, x=1, y=1/2, y=x, R^2=4, and R^2=5 whenever they satisfy its actual alternative. Equality in the unique-mask interval or in (34) is retained. The only strict frame requirement is a,b>0; the aligned a=0 counterexample is not hidden.

The intended nine-square upper radius satisfies 1105/256<5, so the whole original radius window lies inside the second alternative's scalar range. The first alternative and horizontal physical-two corollary have no upper radius restriction.

No sampled pose, angle mesh, optimized orientation, finite exclusion certificate, new normal choice, original-mean replacement, dropped force, changed true degree, artificial tip, Lean compilation, CI, workflow, commit, remote write, ledger change or whole-row credit is used.

