# Nonnegative return pressure forces positive contact projection in the upper-left ABC prefix

Date: October 25, 2026.

**Status: complete hand implication; independent full saved-source,
direct-prerequisite and exact-arithmetic review passed on October 25,
2026. See REVIEW_UNIQUE_RETURN_GEOMETRY_2026_10_25.md. The remaining
whole UUU block-pressure/return exit is open; no gate or ID changes.**

Keep the actual H--A--B--C--H cycle, intact HXY petal, genuine
H4/A2/B2/C2 equations, all original positive magnitudes and application
means, all nine physical squares, and all three completion squares.
A,B,C are physically unique and have positive original circle loads;
H is physically circle-clear. Use the original negative-A, H-owned HA,
B-owned upper-left AB chart. The common selected certificate is unchanged.
In particular

    6241/1600 <= q=R^2 <= 1105/256,
    z_A=(a,b), a>b>3/5, a^2+b^2=q,
    x=a-1, P=(x,b-1), T=(x,b),
    f=(s,c), g=(-c,s), c,s>0, c^2+s^2=1,
    rho=c/[c+s*(a/b-1)],
    v=1/sqrt(1+rho^2), u=rho*v,
    n=(u,v), j=(-v,u),
    H=P+[-1,0]n+[r-1,r]j, 0<r<1,
    c_H=P-n/2+(r-1/2)j,
    c_H dot z_A<0.

The original physical B circle corner is

    z_B=T+tau*f+epsilon*g,
    0<tau<1, epsilon in {0,1}.                    (1)

Both actual alternatives and their full original domains are retained.
There is no restriction on the BC support feature or HC ownership in
the following implication.

Here (1) is the whole-prefix result in
NEGATIVE_H_OWNED_UPPER_LEFT_NEAR_VERTEX_EXCLUSION.md, Section 1,
before its outgoing support fan or near-vertex specialization.
Explicitly, the B-owned AB singleton puts the actual T in the relative
interior of B's minimum-g side, so

    B=T+[0,1]g+[-delta,1-delta]f, 0<delta<1.

True B2 proper concurrence with its physical boundary neighbor A gives
q_B=T+ell*g=kappa_B*z_B in B, with kappa_B>0. Hence
z_B dot f=(T dot f)/kappa_B>0. Containment and the physically unique
circle corner make its f-coordinate the unique far endpoint of B's
f-interval; its positive sign makes it the maximum endpoint.
Thus tau=1-delta is in (0,1). The two possible g endpoints give exactly
epsilon in {0,1}. This derivation assumes no outgoing BC feature and
no HC owner, force equation or mean.

**Theorem.** If the actual C circle pressure is nonnegative,

    c_H dot F_C>=0,

then

    N:=P dot n>0.                                (2)

In particular this applies to the entire C-owned far BC singleton and
the entire genuinely shared BC side, by
ABC_RETURN_OWNER_NONNEGATIVE_ENDPOINT_PRESSURE.md. A strict B-owned
BC singleton is not silently added to the scope of that separate
pressure input. The theorem itself only assumes the displayed actual
C pressure and leaves every original normal and mean unchanged.

## 1. Consequences of a nonpositive N

Suppose N<=0. Since a>b and a^2+b^2>=6241/1600>2, we have a>1 and x>0.
Also b>3/5 and q<=1105/256 give

    a^2<1105/256-9/25=25321/6400<4,

so x<1. From N=xu+(b-1)v<=0 we obtain b<1. Set

    y=1-b, 0<y<2/5.

Then

    rho<=y/x.                                    (3)

The radius lower bound gives the stronger simple estimate

    x>7/10+(9/20)y=:x0(y).                        (4)

Indeed, if x<=x0(y), positivity of a=x+1 gives

    q=a^2+b^2
      <=(17/10+(9/20)y)^2+(1-y)^2
      =389/100-(47/100)y+(481/400)y^2.

This convex quadratic has its maximum on [0,2/5] at an endpoint.
Its two endpoint values are 389/100 and 2434/625, both less than
6241/1600; the smaller strict reserve at the latter endpoint is
249/40000. This contradicts the original radius lower bound.
In particular x>7/10>y.

The ordinary first coordinate of the actual H center satisfies

    (c_H)_x=x-u/2-(r-1/2)v
      >x-(u+v)/2
      >=x-(1+rho)/2
      >=x-(1+y/x)/2.                             (5)

The last expression is positive. To check it, the polynomial
2x^2-x-y increases in x for x>=7/10, and at x0(y) it equals

    7/25-(19/100)y+(81/200)y^2
      >=7/25-(19/100)(2/5)=51/250>0.

Thus (c_H)_x>0. Since a,b>0 and c_H dot z_A<0, necessarily

    (c_H)_y<0.                                    (6)

## 2. A complete exact inequality gives c<x

Combining (3) with the original A2 identity for rho gives

    (x-y)c <= [y(x+y)/(1-y)]s.

All quantities divided by below are positive, so

    c/s <= y(x+y)/[(1-y)(x-y)].                   (7)

Define

    F(x,y)=x^2(1-y)^2(x-y)^2
             -y^2(x+y)^2(1-x^2).

We prove F(x,y)>0 throughout the enlarged domain

    0<=y<=2/5, x>=x0(y).

The exact expansion is

    F=x^4(1-2y+2y^2)+x^3(-2y+4y^2)
       +x^2(-2y^3+2y^4)-2xy^3-y^4.             (8)

On 0<=y<=2/5 its first three coefficient bounds are

    1-2y+2y^2>=1/2,
    -2y+4y^2>=-1/4,
    -2y^3+2y^4>=-2/25.

For the last inequality, y^3(1-y) increases up to y=2/5 and its
endpoint is 24/625<1/25. Therefore, for x>=7/10,

    dF/dx >= 2x^3-(3/4)x^2-(4/25)x-16/125 >0.   (9)

The cubic in (9) increases for x>=7/10: its derivative is
6x^2-(3/2)x-4/25, at least 173/100 there. Its value at x=7/10
is 157/2000>0. Consequently F(x,y)>=F(x0(y),y).

For an explicit exact whole-interval positivity identity, put y=2t/5
and x0=7/10+9t/50, with t in [0,1]. Direct expansion of (8) gives

    G(t):=F(7/10+9t/50,2t/5)
      =2401/10000-(686/3125)t-(441/25000)t^2
        -(1141/62500)t^3+(77/50000)t^4
        +(131823/7812500)t^5+(38961/19531250)t^6.

Its complete Bernstein identity is

    G(t)=sum_{i=0}^6 b_i binom(6,i)t^i(1-t)^(6-i),

where, in order i=0,...,6, the exact coefficients are

    2401/10000,
    30527/150000,
    124313/750000,
    78687/625000,
    6496/78125,
    77352/1953125,
    49728/9765625.                                (10)

Every listed coefficient is strictly positive. The Bernstein basis
is nonnegative and sums to one on this single complete interval,
so G>0 there, including both endpoints. This is not a sampled sign
or a union of angle boxes. For direct reconstruction, if g_k are
the displayed monomial coefficients, every coefficient of both
identities is determined by

    b_i=sum_{k=0}^i g_k binom(i,k)/binom(6,k),
    g_k=sum_{i=0}^k b_i binom(6,i)binom(6-i,k-i)(-1)^(k-i).

Thus (8)--(10) provide the complete small rational certificate,
including the inverse identity; all fourteen conversions were also
reconstructed with exact Fraction arithmetic.

Since the actual domain has x<1, F>0 yields

    y(x+y)/[(1-y)(x-y)] < x/sqrt(1-x^2).

Combine this with (7). Using c,s>0 and c^2+s^2=1, squaring positive
quantities gives c^2<x^2, hence

    c<x.                                         (11)

## 3. The actual circle order makes C pressure strictly negative

Both actual B circle alternatives (1) now lie in the open first
quadrant. If epsilon=0 this follows from x,b,tau,s,c>0. If epsilon=1,

    (z_B)_x=x+tau*s-c>0,
    (z_B)_y=b+tau*c+s>0

by (11). Moreover direct expansion gives

    det(z_A,z_B)
      =b+tau*(a*c-b*s)+epsilon*(a*s+b*c)
      >b*(1-tau*s)>0.                           (12)

Therefore the ordinary circle directions satisfy

    0<theta_A<theta_B<pi/2.                      (13)

The whole physical boundary-path theorem in
BOUNDARY_THREE_PATH_RESULTANT_CONE.md, Section 1, puts the original
three directions in one consistent order with endpoint gap less
than pi. The orientation in (12) fixes which reflection of that
order is being used. Since every body is physically unique with a
positive circle load, resultant and corner directions coincide.
Thus the compatible lifts obey

    theta_A<theta_B<theta_C<theta_A+pi.

The physical B/C contact gives z_B dot z_C>0. This is the all-corner
acute-contact theorem ACUTE_LOADED_CONTACT_GRAPH.md, Section 2, whose
strict radius premise holds here because

    q>=6241/1600>15/4>2+sqrt(3).

For completeness, its elementary local input is that if a contained
unit square has circle corner z and q>2+sqrt(3), every point p of it
satisfies z dot p>|det(z,p)|. In inward orthonormal side coordinates
z has coordinates A,B>=1/2 and A^2+B^2=q. Checking the four vertices
reduces to q>A+B and q>2max(A,B), which follow from q>2 and
q>2sqrt(q-1/4). The latter is equivalent to q^2-4q+1>0. At a common
B/C point, both circle directions lie strictly within pi/4 of the
point direction, proving their dot product positive. This uses an
actual physical contact and does not require a special BC owner.

Because 0<theta_C-theta_B<pi, acuteness improves it to
theta_C-theta_B<pi/2. Combining with (13) gives

    theta_A<theta_C<pi.                           (14)

Now write c_H=(X,Y), where X>0>Y by (5)--(6). In the first quadrant,
the function X cos(theta)+Y sin(theta) is strictly decreasing.
Its value at theta_A is strictly negative, by original negative A.
Thus it is negative at every larger angle up to pi/2. Between
pi/2 and pi the two terms are nonpositive and the sine term is
strictly negative. Equation (14) consequently implies

    c_H dot z_C<0.

The actual C force is a strictly positive multiple of z_C. Hence
c_H dot F_C<0, contradicting the hypothesis of the theorem. This
contradiction proves (2).

## 4. Exact retained consequence for the remaining far family

ABC_FAR_UNIQUE_NONNEGATIVE_ROOT_PROJECTION_EXCLUSION.md separately
excludes cn=c_H dot n>=0 in the entire unique-C far return. Together
with its accepted C-pressure input and (2), every actual far residue
therefore satisfies

    0<P dot n<1/2,
    -1/2<c_H dot n<0.

Its previously proved whole-H support bound j dot Z<3/4 for every
Z in H is unchanged. No lower bound on every actual return point
is inferred here. In particular the entire unique-C far return,
the remaining minimum-f return, the whole ABC parent and all coarse
parents remain open unless a separate complete exit is supplied.

No extra H/B contact, altered circle mask, reassigned force, new
normal selection, numerical sign, Lean compilation or CI is used.
