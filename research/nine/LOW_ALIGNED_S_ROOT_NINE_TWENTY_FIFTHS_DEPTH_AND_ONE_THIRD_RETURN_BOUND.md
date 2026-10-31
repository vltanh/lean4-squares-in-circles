# Uniform southern depth and a one-third bound for a physical upper return

Date: October 28, 2026 UTC. Author: current root continuation.

**Status: complete new hand theorems, frozen for separate full independent
review.** The physical theorem strengthens the entire southern-page depth
region from 4/15 to 9/25. A separate scalar theorem bounds a possible upper
return by one third. A final comparison covers its whole parameter domain.
No selected force, actual mean, circle mask, degree or original family is
inferred from the scalar notation. No original-family flag closes here.

All physical units are the unchanged actual closed unit squares in the same
disk, with disjoint open interiors. Physical circle corners are retained
regardless of individual coefficients. No force is deleted, no neighbor is
replaced, and no application is moved.

## 1. Complete southern-page domain and exact input

Retain the full closed physical domain

    2<=R<=sqrt(17)/2,
    d=sqrt(R^2-1/4)-1, e=d-1,
    29/50<=a<=2/3, b=a-1,
    X=[e,d] times [b,a],
    L=[d,d+1] times [-1/2,1/2].                    (1)

Let D be any actual physical boundary unit with

    D subset {y<=b},
    Q=(x,b) in D intersect X, e<=x<=d.             (2)

Q may initially be any unchanged original shared-side mean. The degrees,
loads and other neighbors of X, L and D are unrestricted. The exact source

    LOW_ALIGNED_S_ROOT_SOUTH_BOUNDARY_DEPTH_AND_WALL_SPAN_BARRIER.md
    SHA256 4e4967d248c5d0d7375622297913fa9c166cbd8a8328c798bae7680a84bcb2ce

has precisely (1)--(2) as premises. Its Sections 1--4 prove

    14/15<d<=1, -1/15<e<=0,
    -21/50<=b<=-1/3,
    R^2=(d+1)^2+1/4,
    x>2/5,
    D=Q+[0,1](r,-s)+[0,1](-s,-r),
    r,s>0, r^2+s^2=1, r/s>2/3.                   (3)

In particular D is tilted and Q is its actual unique highest vertex.
That proof handles every aligned frame and every original shared-side mean
endpoint before deriving (3). Its separate radius-free Section 5 proves
for every actual unit K contained in x<=E and every M in K

    min_K y >= M_x+M_y-E-1.                       (4)

This needs no contact, force, degree or load hypothesis. It remains weak
at aligned frames. Only (3) and (4) from that exact source are used here.
All strict bounds in (3) hold at the closed R and a endpoints in (1).

**Strengthened physical theorem.** Throughout (1)--(2),

    r/s>9/10,                                    (5)

and every actual Y in D with Y_x<=e satisfies

    Y_y<b-9/25.                                  (6)

Consequently no actual K contained in x<=e and touching D can contain any
point M in the entire closed region

    M_x+M_y>=e+a-9/25.                            (7)

These are statements about whole physical contact sets, independently
of selected normals and circle multipliers.

## 2. The whole remaining ratio interval is excluded by physical corners

Suppose contrary to (5) that 2/3<q=r/s<=9/10. The following estimates
hold even on the enlarged closed interval 2/3<=q<=9/10:

    r<=9/sqrt(181)<67/100,
    s<=3/sqrt(13)<5/6,
    s>=10/sqrt(181)>2/3,
    0<s-r<=1/sqrt(13)<1/3,
    r+s<=sqrt(2)<99/70.                           (8)

Here r=q/sqrt(1+q^2) increases, s=1/sqrt(1+q^2) decreases, and
s-r=(1-q)/sqrt(1+q^2) decreases on the interval. The strict rational
comparisons follow respectively from 810000<812509, 324<325,
900>724, 9<13 and 9800<9801. All interval endpoints are retained.

Write g=1-a=-b and T=a-1/2. Then

    1/3<=g<=21/50, T>=2/25.

The actual top corner Q has norm squared at most 1+(21/50)^2<4.
The left adjacent corner Q+(-s,-r) has horizontal coordinate in
(-3/5,1) and vertical magnitude g+r<109/100, so

    |Q+(-s,-r)|^2<1+(109/100)^2<4.                (9)

It remains to check both other corners. Both actual frame alternatives
x+r<=d and x+r>d are covered below.

### 2.1. The whole noncrossing case x+r<=d

For Z_right=(x+r,-g-s), the first coordinate is positive and at most
d<=1. Its vertical magnitude is less than 21/50+5/6=94/75. Hence

    |Z_right|^2<1+(94/75)^2<4,                    (10)

with final reserve 8039/5625. For Z_opp=(x+r-s,-g-r-s), (3) and
(8) first give

    (Z_opp)_x>2/5-1/3=1/15>0.                    (11)

The noncrossing hypothesis also gives (Z_opp)_x<=d-s<1/3. The
vertical magnitude is less than

    21/50+99/70=321/175<37/20.

The signs justify squaring, and therefore

    |Z_opp|^2<(1/3)^2+(37/20)^2<4,                (12)

with final reserve 1679/3600. Equality x+r=d belongs to this case.

### 2.2. The whole crossing case x+r>d: right adjacent corner

The actual edge Q+u(r,-s) crosses x=d before its endpoint. At this
crossing its height is b-(d-x)/q. If that height exceeded -1/2,
a short subsequent part of the edge would enter the interior of the
occupied leaf L. The edge is below b<0, so the upper leaf boundary
is not an escape. Disjoint open square interiors prohibit an actual
edge portion inside the other square's open interior. Thus

    b-(d-x)/q<=-1/2,
    x<=d-Tq<=d-4/75.                             (13)

The equality at the genuine leaf corner is retained. By (8) and (13),

    0<x+r<d-4/75+67/100=d+37/60,
    g+s<94/75.

Subtracting the exact coupled radius in (3) yields

    |Z_right|^2-R^2
       <(d+37/60)^2+(94/75)^2-[(d+1)^2+1/4]
       =-(23/30)d+63101/90000
       <-433/30000<0.                            (14)

The final strict comparison is d>14/15. R is never varied independently
of d, and both closed radius endpoints remain covered.

### 2.3. The whole crossing case: opposite corner

Define on 2/3<=q<=9/10

    B(q)=(2/25)q+(1-q)/sqrt(1+q^2).

Because 1+q>=sqrt(1+q^2),

    B'(q)=2/25-(1+q)/(1+q^2)^(3/2)
          <=2/25-1/(1+q^2)
          <=2/25-100/181=-2138/4525<0.           (15)

Therefore

    B(q)>=B(9/10)=9/125+1/sqrt(181)
         >9/125+2/27=493/3375,                  (16)

where 1/sqrt(181)>2/27 follows from 724<729. The actual screen
(13), before its final relaxation, gives

    (Z_opp)_x=x+r-s
       <=d-(2/25)q-(s-r)
       =d-B(q)<d-493/3375.                      (17)

Its strict positivity is already proved in (11), and its vertical
magnitude is less than 321/175. Consequently

    |Z_opp|^2-R^2
       <(d-493/3375)^2+(321/175)^2
          -[(d+1)^2+1/4].                       (18)

The right side is strictly decreasing in d, with derivative
-2(1+493/3375). At d=14/15, the positive radius-minus-bound
reserve is exactly

    3589/900-(2657/3375)^2-(321/175)^2
       =7583021/2232562500>0.                   (19)

Here 2657/3375=14/15-493/3375 and
3589/900=(14/15+1)^2+1/4. The actual d>14/15 makes the reserve
larger still. This covers the entire crossing interval, including
q=9/10.

All four actual corners are strictly inside the original disk for
2/3<q<=9/10, hence so is their convex hull. That contradicts physical
boundary status. Together with the complete earlier q<=2/3 exclusion,
this proves (5). There is no uncovered frame or ratio endpoint.

## 3. The complete contact-set depth and forbidden region

For every unchanged Y in D write

    Y=Q+u(r,-s)+v(-s,-r), 0<=u,v<=1.

If Y_x<=e, then v>=(x-e+ur)/s. Thus

    Y_y=b-us-vr
        <=b-(r/s)(x-e)-u/s
        <=b-(r/s)(x-e)
        <b-(9/10)(2/5)=b-9/25.                 (20)

Both strict inputs r/s>9/10 and x>2/5, with e<=0, hold at
all closed endpoints in (1). This proves (6) for the complete closed
left portion of D, including every actual endpoint or aggregate mean.

Let K be contained in x<=e and physically touch D. If it contained
M in the closed region (7), (4) would give

    min_K y>=M_x+M_y-e-1>=a-1-9/25=b-9/25.

Every actual point of D in x<=e is strictly lower by (20), contradicting
the actual nonempty intersection K intersect D. No selected normal,
degree, load or force equation at K was used.

In particular such a K cannot contain an unchanged point of the form

    N=(e,a), M=N-v(s_0,c_0),
    c_0,s_0>=0, c_0^2+s_0^2=1, 0<=v<=1/4.       (21)

Indeed v(c_0+s_0)<=sqrt(2)/4<17/48<9/25, with final reserve
7/1200. This puts M strictly in the forbidden region. All axis
directions, both v endpoints and intermediate actual means are retained.
A caller must still prove the actual point form, the whole half-plane
condition on the real K, and its actual D contact.

## 4. A separate scalar theorem: a return parameter is less than one third

**Scalar theorem.** Suppose

    A>=0, K_0>0, 0<rho<=1,
    A^2+K_0^2<101/225,
    (A+1)^2+(K_0+rho)^2>=4.                     (22)

For

    ell=(K_0-rho A)/(K_0+rho)

one has

    ell<1/3.                                    (23)

No sign of ell is assumed. This scalar implication does not assert that
ell is an actual application or supply a missing force or torque equation.

Suppose ell>=1/3. The positive denominator gives

    rho<=2K_0/(3A+1).                            (24)

Put u=A+1 and S=sqrt(4-u^2). From (22),

    1<=u<1+sqrt(101)/15<17/10<sqrt(3), S>1.

The last rational comparisons follow from 404<441 and 289<300.
Since K_0+rho>0, (22) implies K_0+rho>=S. Combining this
with rho<=1 and then with (24) gives two positive lower bounds:

    K_0>=S-1,
    K_0>=S(3u-2)/(3u).                          (25)

They are equal at u_*=4/sqrt(13), S_*=6/sqrt(13). The first
dominates for u<=u_* because their difference is 2S/(3u)-1,
whose sign is that of 4-(13/4)u^2. The second dominates for u>=u_*.

### 4.1. The full interval 1<=u<=u_*

The first bound gives

    A^2+K_0^2>=(u-1)^2+(S-1)^2=6-2u-2S.        (26)

Its derivative is -2+2u/S. Since u/S<=2/3 throughout the interval,
it is strictly negative. The displayed lower bound is therefore at least
its endpoint value

    6-20/sqrt(13).                              (27)

### 4.2. The full interval u_*<=u<17/10

The second bound gives

    A^2+K_0^2>=H(u),
    H(u)=(u-1)^2+(4-u^2)(3u-2)^2/(9u^2)
        =41/9-(2/3)u-16/(3u)+16/(9u^2).        (28)

Its derivative is

    H'(u)=-2[3u^3-24u+16]/(9u^3).

The polynomial p(u)=3u^3-24u+16 is convex on [1,17/10],
as p''(u)=18u>0. Its endpoint values are

    p(1)=-5, p(17/10)=-10061/1000.

A convex function lies below the endpoint chord, so p is strictly
negative throughout that closed interval. Thus H is strictly increasing,
and its minimum on the range in (28) is H(u_*), the same value (27).

Both complete intervals force

    A^2+K_0^2>=6-20/sqrt(13)>101/225.            (29)

For the last comparison, both sides of 20/sqrt(13)<1249/225
are positive and the squared integer reserve is

    1249^2*13-400*225^2=30013>0.

This contradicts (22), proving (23). In particular rho=1 and the
physical lower radius threshold 2 are included. Every denominator
and every squaring has its required sign explicitly established.

## 5. Literal physical interpretation and caller obligations

Let n,j be a genuine orthonormal frame, with an unchanged physical
contact point N and an actual far corner Z satisfying

    N dot n=A>=0, N dot j=-K_0<0,
    Z=N+n-rho j, 0<rho<=1,
    |N|^2<101/225, |Z|^2>=4.                    (30)

Then (22) is an exact coordinate identity. In the chart (1),
N=(e,a) automatically has

    |N|^2=e^2+a^2<1/225+4/9=101/225.

If n=(-c,s), j=(-s,-c), c,s>=0 and c^2+s^2=1, then
A=as-ec and K_0=ac+es. Positivity of K_0 must be proved
by a caller; it is not a consequence of the chart alone. Z must
be an actual corner with the stated norm, for instance an actual
circle corner, rather than an unsupported candidate.

If the full original equations of a true two-contact boundary unit
establish an actual return parameter t=ell with t>=0, then t<1/3.
If an unchanged higher-degree star establishes only 0<=t<=ell,
the same bound follows. These are conditional substitutions only:
no equality, order, degree reduction or deleted extra force is
licensed here. Physical circle masks and zero individual coefficients
remain among the obligations of the literal caller establishing (30).

## 6. A uniform comparison for every remaining slanted-return parameter

Suppose

    c,s>=0, c^2+s^2=1,
    0<=t<1/3, 0<=v<1/8,
    k=c-s, w=c+s,
    if k>=0, then v<=(1-k)/4.                    (31)

Define

    D_*=sqrt(1-(tc+vs)^2)+t(c-s)+v(c+s).

The square root is defined since 0<=tc+vs<=t+v<11/24<1.
On the entire parameter domain (31),

    D_*<1+9/25=34/25.                           (32)

If k<=0, then tk<=0 and w<=sqrt(2), so

    D_*<=1+vw<1+sqrt(2)/8<1+17/96<34/25.

If 0<=k<=1/2, then

    D_*<=1+tk+vw<1+1/6+17/96<34/25,             (33)

with last reserve 9/25-1/6-17/96=13/800. This includes k=0
and k=1/2. When tk=0 the strict v and sqrt(2) bounds still
supply the required strictness.

If 1/2<=k<=1, then w=sqrt(2-k^2)<=sqrt(7)/2<4/3.
Since k>0, the strict t bound and the weak v bound give

    D_*<=1+tk+vw
        <1+k/3+(1-k)/3=4/3<34/25.               (34)

For k=1 the premise forces v=0; t<1/3 still gives strictness.
All axes, shared interval endpoints and actual zero t or v endpoints
are included. This proves (32) without an uncovered angular interval.

A later physical application deriving D_*>=1+9/25 from actual
unchanged contacts contradicts (32). Deriving that lower bound,
the actual meanings of t,v and the extra v inequality in (31)
remain caller obligations. No geometry is inferred by merely naming
the scalar expression.

## 7. Exact scope and preservation

The sole operative previous source is the exact 4e4967d file in
Section 1. Its complete physical entry and excluded q<=2/3 frames,
and its separate radius-free inequality, are invoked literally.
The new ratio interval, all four physical corners, theorem (22)
and the comparison (31) are proved in full above.

All arguments are exact continuous inequalities. Standard library
rational arithmetic additionally checked the displayed expansions
and reserves; this does not replace any geometric proof. No pose
search, angle grid, numerical optimization, Lean/Lake build, CI
or workflow was used. No frozen source, review, original graph,
load mask, flag, ledger or global theorem status is changed.
Complete original-family joins and their independent review and
root adoption remain separate work.

