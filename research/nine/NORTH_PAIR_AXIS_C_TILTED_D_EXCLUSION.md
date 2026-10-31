# The North/North pair cannot have an axis-owned C and a tilted D

Date: October 27, 2026.

**Status: complete original-domain hand exclusion, submitted for full
root and separate independent review.** This is the full shared
C-parallel / D-tilted North/North frame case for both surviving
genuine B-leaf types. All original C2/D2 equations, actual means
and the same nine squares remain.

Keep the high adjacent-S component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,
    d=1+epsilon, 0<epsilon<1/60,
    R^2=(d+1)^2+1/4<=1105/256.

A alone owns AB and has its strict outer-lower genuine S leaf:

    A=[-X,h] times [-v,H], X=1-h, H=1-v,
    X^2+v^2=d^2, |h|<=epsilon,
    P_AB=(h,-k), 0<k<v<13/50.

C,D each have one physical circle corner. The exact original
North reductions give

    AD North, P_D=(-t_D,H), t_D=X*k/v>0;

    j=(s,-c), f=(c,s), c,s>0, c^2+s^2=1,
    p=c/s<3/10;

    BC f, P_BC=(t,T) in B's actual (j,f) frame,
    T=1-w, 0<w<3/20, t>0.

Here the actual B near coordinate xi satisfies

    h=xi*s-w*c, k=xi*c+w*s,
    0<xi<=epsilon.

For an owned B leaf xi=epsilon, and the complete reduction is
ADJACENT_S_C4_OWNED_TILTED_LEAF_NORTH_CONTACT_REDUCTION.md.
For a strict B leaf 0<xi<epsilon; the complete reduction
ADJACENT_S_C4_STRICT_TILTED_ROOT_NORTH_CONTACT_REDUCTION.md
gives the stronger p<1/4 and k<3/20. Its exact
xi*(1+s)>wc implies w<k<3/20. Thus every common premise
above holds literally for both types. Their different actual
BC mean formulas are never identified in this proof.

A useful original-coordinate identity is

    h+k*p=xi*sqrt(1+p^2)<=epsilon*sqrt(1+p^2).         (1)

Both true root nonleaf force pairs are nonparallel. Together
with the unique physical C,D masks, the accepted compatible
all-cycle-owner theorem gives an actual side-axis owner to
every cycle edge. Every original mean remains.

Assume C owns its incoming f axis, whereas D is tilted at
its incoming world-North point. We prove this entire actual
frame case impossible.

## 1. The actual loaded-square frames and complete CD owner cover

The genuine loaded two-force high vertical-port theorem,
Section 1 of
ADJACENT_S_C4_PARALLEL_ROOTS_SHALLOW_DEPTH_EXCLUSION.md,
has exactly its required local scope here.

C is parallel to B and has the actual square and unique corner

    C=[z-1,z] times [T,T+1] in B's frame,
    Z_C=z*j+(T+1)*f,
    z=sqrt(R^2-(T+1)^2)>1/2.                          (2)

D is tilted at P_D. Its complete actual frame is

    D=P_D+[0,1]u+[0,1]v_D,
    u=(a,b), v_D=(-b,a),
    a,b>0, a^2+b^2=1,
    Z_D=P_D+v_D=(-t_D-b,H+a),                         (3)

    t_D*a-H*b>1/2,
    b/a<1/2, a>8/9.                                  (4)

The opposite circle corner has already been excluded by D's
true proper radial point and its physical boundary neighbor C.
In particular (4) concerns its unique physical mask.

Let g be the actual D-to-C unit normal. The full original D2
equation is

    F_D=nu_D*North-kappa*g, nu_D,kappa>0.

F_D is a positive multiple of the actual Z_D. Its negative
horizontal coordinate gives g_x>0. Its u coordinate is strictly
negative by (4), whereas North.u=b>0. Hence

    g_x>0, g.u>0.                                    (5)

If D owns CD, (5) leaves only g=u. If C owns it, its actual
axes with positive horizontal coordinate are j and f.
The alternative g=f would make both genuine C2 pair normals
parallel, which the boundary-neighbor two-force theorem excludes.
Thus the whole original owner cover is exactly

    D-owned g=u, or C-owned g=j.                     (6)

This keeps every owned-side mean and all coincident endpoints.
No selected normal is changed to obtain (6).

## 2. D-owned CD has incompatible actual heights

Suppose g=u. The actual D-side mean is

    Q=P_D+u+lambda*v_D, 0<=lambda<=1.                 (7)

Because u.j=a*s-b*c>0 and u.f=a*c+b*s>0, the minimum-u
point of the actual C is its bottom-left vertex

    Q=(z-1)*j+T*f.

Its world height is strictly less than

    T*s+c*(1-z)<1+c/2<23/20.                         (8)

Let the genuine D radial concurrence be q_D=P_D+rho*North.
Its radial line through Z_D in (3) gives the exact original
proper distance

    rho=(t_D*a-H*b)/(t_D+b)>1/[2*(t_D+b)].            (9)

The unchanged CD line through (7) is parallel to u. Taking
its v_D coordinate therefore gives lambda=a*rho. Hence

    Q_y=H+b+lambda*a
       >H+b+(1-b^2)/[2*(t_D+b)]
       >H+b+(1-b^2)/[2*(d+b)]
       >H+1/(2d).                                   (10)

Here t_D=X*k/v<X<d. The last comparison is exact: its
difference from 1/(2d) is

    b*(2d^2-1+d*b)/[2d*(d+b)]>0.

Since H>37/50 and d<61/60, (10) gives

    Q_y>37/50+30/61>23/20.

The final reserve is 499/6100. This contradicts (8), with
the entire original lambda interval retained.

## 3. C-owned CD gives an exact scalar obstruction

Suppose g=j=(s,-c). On D this normal is positive on u and
negative on v_D, so the actual application is its right vertex

    Q=P_D+u.

The genuine D proper radial point lies on the line Q-R*j and
on the vertical line through P_D. Their unchanged intersection
is

    q_D=P_D+(b+a*p)*North.

Comparing with the radial line through the actual Z_D gives

    t_D*[a*(1-p)-b]=b*(H+b+a*p).                      (11)

In particular a*(1-p)>b. Put r=b/a. Equation (11) is
equivalently

    t_D+b = r*(H+a)/(1-p-r).                         (12)

We now show that the original real-square conditions (1),
(3)--(4), (11) are already incompatible. This scalar argument
does not use an artificial C mean or any degree change.

### 3.1. A decreasing auxiliary angle bounds the original v and t_D

Keep the original d,p,R fixed. This paragraph defines scalar
comparison functions only; it does not construct a new packing
or reselect any contact normal.

Write

    D_r=1-p-r, S_r=sqrt(D_r^2+r^2),
    a_r=1/sqrt(1+r^2), b_r=r*a_r.

Equations (3),(12) give, at the original r,

    t_D+b_r=R*r/S_r,
    H+a_r=R*D_r/S_r.

The actual second coordinate is larger than the first:
H+a>37/50+8/9, and its square is greater than R^2/2.
Consequently D_r>r and

    0<r<(1-p)/2.

For every scalar 0<q<=r define

    v(q)=1+a_q-R*D_q/S_q,
    t(q)=R*q/S_q-b_q,
    U(q)=R*a_q*q*(p+q)/S_q.                          (13)

At the original q=r these are exactly v,t_D and
t_D*a-H*b. Both v(q) and t(q) are strictly increasing.
Indeed S_q<=1-p, D_q>=(1-p)/2, and

    v'(q)=q*[R*(1-p)/S_q^3-a_q^3]>0,

    t'(q)=R*(1-p)*D_q/S_q^3-a_q^3>0,

because R>2 and 0<1-p<1. The first bracket exceeds
R/(1-p)^2-1>0; the second derivative expression exceeds
R/[2*(1-p)]-1>0.

U(q) is also strictly increasing: a_q*q increases,
p+q increases, and S_q decreases on this interval.
It tends to zero at q=0. The actual unique-corner condition
(4) says U(r)>1/2. Thus there is a unique q0 in (0,r)
with U(q0)=1/2, and

    v>v(q0), t_D>t(q0).                              (14)

At this auxiliary equality, the vector of length R has
u-coordinate -1/2 and positive v_D-coordinate. Its latter
coordinate is sqrt(R^2-1/4)=d+1. This elementary orthogonal
decomposition gives, with a0=a_q0 and b0=b_q0,

    v(q0)=1-d*a0+b0/2,
    t(q0)=d*b0+a0/2.                                (15)

Equation (11), still an algebraic identity of the comparison
functions, then gives

    (b0+a0*p)*(a0+2*(d+1)*b0)=1.                     (16)

The equality in (16) is used only to bound scalar functions
of the original data. No two-corner mask is assigned to the
original unique-corner D.

### 3.2. Replace only the scalar radius bound by its rational endpoint

Set

    d_bar=61/60, E_bar=1/60.

For fixed p, the function

    F_d(b)=(b+p*sqrt(1-b^2))
                 *(sqrt(1-b^2)+2*(d+1)*b)

strictly increases with b on 0<b<1/sqrt(5), and with d.
For a direct derivative check, expand it as

    p+[1+2p(d+1)]*b*sqrt(1-b^2)
         +[2(d+1)-p]*b^2.

All indicated coefficients are positive, and
b*sqrt(1-b^2) increases on this interval.

Let b_* be its unique solution F_dbar(b_*)=1, and put
a_*=sqrt(1-b_*^2). The solution exists between zero and
1/sqrt(5): the endpoint values are p<1 and
p+(1+2p(d_bar+1))*(2/5)+(2(d_bar+1)-p)/5>1.
Equation (16) and d<d_bar give b0>b_*.

Both functions 1-d_bar*sqrt(1-b^2)+b/2 and
b+sqrt(1-b^2)/2 increase on this interval. Therefore
(14)--(15) imply the strict original bounds

    v>v_*=1-d_bar*a_*+b_*/2,
    t_D>t_*=b_*+a_*/2.                              (17)

The positivity of v_* will also be explicit in the interval
calculation below.

### 3.3. The original near-point identity gives the opposite inequality

The actual root radius yields

    X=sqrt(d^2-v^2)<d-v^2/(2d),
    k=v*t_D/X>v*t_D/d.

Combining these strict comparisons with the actual near-point
identity (1) gives

    v^2+2p*v*t_D
      <2d*epsilon*(1+sqrt(1+p^2))
      <=d_bar*E_bar*(4+p^2).                         (18)

Here sqrt(1+p^2)<=1+p^2/2 and d*epsilon<d_bar*E_bar.
No quantity from the original A or B is varied in (18).

We will prove the contrary exact lower bound

    v_*^2+2p*v_*t_*>d_bar*E_bar*(4+p^2).              (19)

Together with (17) and v_*,t_*>0, this contradicts (18).

## 4. A single exact positive polynomial proves (19)

Use the half-angle parameter

    x=b_*/(1+a_*),
    a_*=(1-x^2)/(1+x^2), b_*=2x/(1+x^2).

Equation F_dbar(b_*)=1 solves explicitly for p:

    p=N(x)/M(x),

    N(x)=15x^4+30x^3-212x^2-30x+15,
    M(x)=(1-x^2)*(15-15x^2+121x).                    (20)

The complete interval is

    7/60<x<5/24.                                    (21)

For an exact check, p in (20) decreases as b_* increases,
by the strict monotonicity of F_dbar in both b and p.
At the two proposed endpoints its values are

    p(7/60)=7486441/24640389>3/10,
    p(5/24)=-3359/836969<0.

The first comparison has integer cross-product reserve
943243>0. Both endpoint b values lie below 1/sqrt(5);
therefore the preceding monotonicity applies. The actual
0<p<3/10 proves (21).

Put

    L(x)=1+x^2,
    V(x)=121x^2+60x-1,
    W(x)=1+4x-x^2.

The exact bounds in (17) become

    v_*=V(x)/(60L(x)),
    t_*=W(x)/(2L(x)).

Both are positive on (21). In particular
v_*>-1/60+b_*/2 and b_*>840/3649, so v_*>0.

Multiplication of (19) by the positive denominator
3600*L(x)^2*M(x)^2 reduces it to P(x)>0, where

    P=V^2*M^2+60*N*V*W*M-61*L^2*(4*M^2+N^2).         (22)

For a fully explicit exact certificate, the ascending power
coefficients p_0,...,p_12 of this single polynomial are

    -81900, -180090, 7085697, 26506650,
    -111721388, -495701580, -267676434,
    559407180, 193777732, -56617050,
    168941937, -33415110, 1592100.

No interval of physical poses is sampled. The following
elementary change of polynomial basis proves positivity over
the entire closed interval containing (21).

Let l=7/60, Delta=11/120, and define the exact rationals

    A_i=Delta^i * sum_{j=i}^{12}
                        p_j*binom(j,i)*l^(j-i),

    B_k=sum_{i=0}^k A_i*binom(k,i)/binom(12,i).

Then direct binomial expansion gives the identity

    P(l+Delta*y)
      =sum_{k=0}^{12}
             B_k*binom(12,k)*y^k*(1-y)^(12-k).         (23)

The following are integer lower bounds on those exact rational
coefficients. Each entry follows by multiplying the displayed
positive binomial denominators; all inputs were given above.

| k | Lower bound for B_k |
|---|---:|
| 0 | 3709 |
| 1 | 14116 |
| 2 | 24382 |
| 3 | 34165 |
| 4 | 43061 |
| 5 | 50605 |
| 6 | 56262 |
| 7 | 59424 |
| 8 | 59408 |
| 9 | 55453 |
| 10 | 46718 |
| 11 | 32274 |
| 12 | 11110 |

As an additional endpoint check,

    B_0=8972092207549229898839/2418647040000000000,

    B_12=11270971939702743725/1014454095446016.

For 0<=y<=1 the weights in (23) are nonnegative and sum
to one. Every coefficient is at least 3709. Therefore
P(l+Delta*y)>=3709>0 on the entire closed interval.
This proves (19), and hence the contradiction in Section 3.

The coefficient table is a finite exact arithmetic verification
of one displayed polynomial identity. It is not a pose list,
a numerical sign test or a new geometric case division.

## 5. Exact whole-frame conclusion

The D-owned alternative in (6) contradicts the actual heights
in Section 2. The C-owned j alternative contradicts the unchanged
root near-point identity by Sections 3--4. Thus every actual
CD owner and every original mean is covered.

The proof uses only the common original North-domain facts
verified at the start, so it closes the entire C-parallel /
D-tilted unique/unique frame case for both surviving B-leaf
types. Their original BC mean formulas remain distinct and
unchanged throughout.

All nine squares, true A3/B3/C2/D2 equations, actual physical
circle masks and original normal choices are retained. The
auxiliary functions are scalar inequalities on fixed original
data; they do not change a pose or apply a selected-certificate
theorem to a modified configuration. No compilation, CI,
remote action or shared-metadata edit supplies a premise.

