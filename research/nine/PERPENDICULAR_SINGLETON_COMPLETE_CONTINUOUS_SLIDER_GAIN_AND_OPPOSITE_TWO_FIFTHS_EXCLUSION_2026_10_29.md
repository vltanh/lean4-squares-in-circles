# A complete continuous slider gain excludes every opposite return with b at least two fifths

Date: October 29, 2026 UTC. Author: roofs continuation.

**Status: complete proposed hand theorem, submitted for full independent
review.** The full original V2/A3/D3 equations force a uniform positive
slider gain over the entire opposite-return interval 2/5<=b<=1/2.
A general derivative compensation argument preserves that gain in the
actual upper-return height. Together with the already proved larger-b
exit, this excludes the whole opposite-D-vertex row for b>=2/5.

The proof treats the entire continuous scalar domain. Its two polynomial
comparison intervals prove one scalar inequality by convexity and
monotonicity; they are not sampled square orientations or certificates
for unexamined physical features. No entire original D02 row is claimed
closed.

## 1. Exact original setting, full stars and complete inputs

Retain all nine actual unit squares, the original containing-circle
origin, every original positive force, normal, full mean, physical
circle corner and individual zero coefficient. The original window is

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, 9/10<d<61/60.

In the physical-two West/strict perpendicular-singleton feature, keep

    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-t), 0<t<=1/2,
    H=t+1/2, 1/2<H<=1,
    h=(c,-s), e=(s,c), c,s>0, c^2+s^2=1,

    A=P+[-1,0]h+[-l,1-l]e, 0<l<1,
    W=P-xh-le, 0<x<1,

    v=W-Q=-a h+b e=(-u,y),
    a=H s+x>0, b=H c-l>0, a^2+b^2=1,
    u=a c-b s>0, y=a s+b c>0,
    w=-b h-a e=(-y,-u),
    D=Q+[0,1]v+[0,1]w.

Thus b<c, s<a and u^2+y^2=1. The full original positive stars are

    A:{V,D,B}, D:{V,A,C}, V:{A,D}.

A,D are unloaded true3; V is loaded true2 with two PHYSICAL circle
corners. The actual AD singleton is owned by A alone, with original
normal -e from A. Let mu,nu,gamma>0 be the AV,DV,AD magnitudes.
Write

    r=gamma/mu, q=gamma/nu, M=d s+c/2.

The full A3 equations give

    F_B=-mu h+gamma e,
    K=P-h+(1-l)e,
    r=(1-l)/(1-x)=(1-H c+b)/(1-a+H s).             (1)

The real B contains K+f, where

    f=(-h+r e)/sqrt(1+r^2).                        (2)

This follows in its own actual axes: adding a minimum-support unit
normal moves each nonzero coordinate inward by at most one, while a
zero coordinate preserves its entire actual side mean. The original
B square, not a reconstructed one, contains this point.

The full V2 moment retains

    nu t=mu M, nu/mu=M/t, t=Mq/r.                  (3)

Its remaining equations are unchanged:

    mu c+nu=k(d+1), mu s=-k eta,
    k>0, -1/2<=eta<=1/2.

Both individual-zero circle-weight endpoints remain physical-two
masks; neither is reclassified as a unique physical circle corner.

The full D3 force is

    F_C=-nu East-gamma e,
    F_C.v=nu u-gamma b,
    F_C.w=nu y+gamma a>0.

Its actual original C point or side mean is L=Q+w+zv with
0<=z<=1, and its full torque is

    q[b-(1-z)a]=u-z y.                             (4)

In the opposite-vertex row under consideration, the original z is one,
so the actual C point is Q+v+w and

    q=(u-y)/b>0.                                  (5)

No D-side mean is set to one to create this row; this is its original
strict support feature. The side-return row keeps its own original z
and is not assigned equation (5).

The four complete pinned inputs are:

| Source | SHA256 | Consumed role |
| --- | --- | --- |
| PHYSICAL_TWO_WEST_STRICT_PERPENDICULAR_SINGLETON_ADJACENT_RETURN_EXCLUSION_AND_COMPLETE_RESIDUAL_2026_10_29.md | f3718c86a99ef196eba1ee875b66375582a0fc588f10275ec171c442e46780dd | Whole actual chart, full stars and means; complete adjacent and c<=3/4 exits |
| PERPENDICULAR_SINGLETON_UPPER_RETURN_ANGLE_COMPENSATION_AND_LARGE_SIDE_COMPONENT_EXCLUSION_2026_10_29.md | 0afb19ae0fbde08c104b6e5bf554ab27885c31dc1c16275de625341f956ce167 | Exact actual upper point, concavity of G, and every return with b>=16/25 |
| PERPENDICULAR_SINGLETON_FULL_STAR_OPPOSITE_LARGE_COMPONENT_AND_RETURN_RATIO_EXCLUSION_2026_10_29.md | b5c43386afc7cba286514644eac4fe38dcf9996ab7ed7a34dc7fe02972704c1e | Entire opposite b>=1/2 and both residual rows q>=18/5; literal prior projection join |
| ACTUAL_UNIT_PROJECTION_BRIDGE_AND_PERPENDICULAR_SINGLETON_RETURN_INTERVALS_2026_10_29.md | 97815bf7d2558343a76316a8095096bb780a8e4fe1664274c1863bcbbb8d6132 | Whole physical B--N--C projection inequality and its exact remaining y intervals |

All four sources were read completely. The new compensation and entire
slider-gain proof are printed below. Every frozen input remains unchanged.

## 2. A derivative compensation valid already for b>=2/5

This scalar lemma uses (1), the full original H and the actual point
(2), without the opposite-row equation (5). Suppose only that b>=2/5
and c>3/4. Fix the actual a,b,H and compare the scalar angle
0<=phi<=the actual phi, where c=cos(phi),s=sin(phi).
All auxiliary denominators below remain positive throughout this
comparison; no square is moved to make an auxiliary angle physical.

Put

    D(phi)=1-a+H sin(phi),
    N(phi)=1-H cos(phi)+b,
    L(phi)=sqrt(D(phi)^2+N(phi)^2),
    A(phi)=atan(N(phi)/D(phi)),
    psi(phi)=phi+A(phi),
    U=cos(psi), V=sin(psi).

Here A(phi) is an auxiliary scalar angle, distinct from the square
named A. Since c>3/4 throughout the comparison, 0<=phi<pi/4;
0<A(phi)<pi/2 and 0<psi<3pi/4. Moreover

    L>=N>=b, H/L<=1/b<=5/2.

The actual f_y is sin(psi) at the actual phi. Direct differentiation
gives

    A'(phi)=-(H/L)sin(A(phi)-phi),

and therefore, for F(phi)=sin(psi(phi))+sin(phi),

    F'(phi)=c+U-(H/L)U sin(A(phi)-phi).             (6)

If U>=0, then psi<=pi/2 and
sin(A(phi)-phi)<=sin(A(phi)+phi)=V. The possible negative sign of
the first sine only strengthens the upper bound on the subtracted
term. Consequently

    F'>=c+U-(5/2)U sqrt(1-U^2).

For 0<=U<=1/2, sqrt(1-U^2)<=1 gives

    U-(5/2)U sqrt(1-U^2)>=-(3/2)U>=-3/4.

For 1/2<=U<=1, U sqrt(1-U^2)<=1/2 gives the same bound,

    U-(5/2)U sqrt(1-U^2)>=U-5/4>=-3/4.

Hence F'>=c-3/4>0 throughout the entire U>=0 alternative.

If U<0, psi>pi/2 implies
A(phi)>pi/2-phi>phi. Thus sin(A(phi)-phi)>0 and the last term
of (6) is positive. Also A(phi)<pi/2 gives U>-sin(phi)=-s.
It follows that

    F'>c+U>c-s>0.

These two complete alternatives cover every value of the scalar angle,
including the join U=0. Thus F increases strictly throughout the
whole comparison interval. At its initial endpoint,

    r0=(1-H+b)/(1-a),
    F(0)=sin(atan(r0))
         >=sqrt((1+a)/2).                         (7)

For the last inequality use H<=1 and
r0>=b/(1-a)=(1+a)/b. Since the actual phi is strictly positive,
(6)--(7) give

    f_y+s>sqrt((1+a)/2).                           (8)

The exact actual corner height is

    K_y=1/2+s+c(1-H c+b)
       =1/2+b+s+(1-c)(c-b)+(1-H)c^2.

All quantities here are original. Since c<1 and c>b, equation (8)
proves the strengthened entire-domain bound

    (K+f)_y>G(b)+(1-H)c^2,
    G(b)=1/2+b+sqrt((1+sqrt(1-b^2))/2),            (9)

for every b>=2/5 and c>3/4. This is a uniform derivative proof,
not an assumption that an auxiliary fixed-parameter angle describes
another packing.

## 3. Whole opposite-return geometry and the scalar reduction in b

The inherited complete exits already handle c<=3/4 and opposite
b>=1/2. To prove the new entire opposite b>=2/5 theorem it remains
to consider

    2/5<=b<1/2, c>3/4.                            (10)

Write the actual angles

    c=cos(phi), s=sin(phi),
    a=cos(delta), b=sin(delta),
    u=cos(theta), y=sin(theta),
    theta=phi+delta.

All are in their positive first-quadrant branches. The original
positive q in (5) gives u>y, and hence theta<pi/4.
In particular c>s and

    phi<pi/4-arcsin(2/5),
    s<(sqrt(21)-2)/(5sqrt(2))<3/8.                 (11)

For the last strict comparison, sqrt(21)<23/5 has square reserve
4/25, and

    9/64-[13/(25sqrt(2))]^2=217/40000>0.

Thus the whole actual scalar domain below lies in 0<s<3/8.

For fixed actual c,s,d, introduce only a scalar variable beta in
[2/5,b] and put

    a_beta=sqrt(1-beta^2),
    q_beta=(a_beta/beta)(c-s)-(c+s),
    D_beta=1-a_beta+s,
    N_beta=1-c+beta.

The original q is q_b; this follows from (5) and the actual formula
u-y=a(c-s)-b(c+s). Since q_beta decreases with beta and q_b>0,
q_beta>0 throughout this comparison. The comparison is not a new
force assignment to any physical unit.

The elementary inequality

    a_beta(1-beta)<beta(1+beta), beta>=2/5,         (12)

follows by squaring positive sides. The resulting polynomial is

    1-3beta+2beta^2-2beta^3<0.

It equals -1/125 at beta=2/5 and its derivative
-3+4beta-6beta^2 is strictly negative. Equivalently, (12) says

    a_beta-(1-a_beta)/beta^2<beta.

Differentiate the positive numerator q_beta D_beta exactly:

    d(q_beta D_beta)/d beta
      =(1/a_beta)*
        [(c-s)(a_beta-(1-a_beta+s)/beta^2)
            -beta(c+s)]
      <-(1/a_beta)*
          [2beta*s+(c-s)s/beta^2]
      <0.                                        (13)

N_beta is positive and increasing. Thus the whole positive ratio
q_beta D_beta/N_beta decreases with beta on [2/5,b].

The actual A ratio r in (1) decreases with H: its H derivative has
numerator -c(1-a)-s(1+b)<0. Since H<=1,

    r>=(1-c+b)/(1-a+s).

Combining this with the complete actual V2 equation (3) and (13)
gives the uniform necessary bound

    t=Mq/r
       <= M*q_b*D_b/N_b
       <= M*q_(2/5)*D_(2/5)/N_(2/5).             (14)

Every ratio and slider in the first line is original. Only the last
scalar comparison varies beta.

## 4. One exact polynomial supplies the whole slider gain

At beta=2/5, write a_0=sqrt(21)/5. The exact rational bounds are

    1833/2000<a_0<11/12,

with positive square reserves

    21/25-(1833/2000)^2=111/4000000,
    (11/12)^2-21/25=1/3600.

Also c=sqrt(1-s^2)<=1-s^2/2. Because c>s, the positive factors on
the right of (14) therefore have the following complete upper bounds:

    M=d s+c/2
       <1/2+(61/60)s-s^2/4 = V_0(s),

    q_(2/5)
       <(31/24)c-(79/24)s
       <=(31/24)(1-s^2/2)-(79/24)s = Q_0(s),

    D_(2/5)<167/2000+s,

    N_(2/5)>=2/5+s^2/2.

At the actual scalar s, Q_0(s)>q_(2/5)>0, so products and divisions
preserve every inequality. Define the comparison function

    T_0(s)
      =V_0(s)*Q_0(s)*(167/2000+s)/(2/5+s^2/2).

Equation (14) gives t<T_0(s) throughout the actual domain.
Consider the single polynomial

    P(s)=[(1-s^2)/2-1/5]*(2/5+s^2/2)
          -(1-s^2)*V_0(s)*Q_0(s)*(167/2000+s).

Its exact expansion is

    5760000 P(s)
       =380580-3560014s+3858786s^2+26476021s^3
          -6311821s^4-23846007s^5
          +1035655s^6+930000s^7.                 (15)

I prove P(s)>0 on the entire closed comparison interval [0,3/8].
This is stronger than the required actual domain (11).

### 4.1. The whole interval 0<=s<=1/4

Write the coefficients of P as p_0,...,p_7 in ascending order.
The fourth and fifth coefficients are negative and the sixth and
seventh are positive. Hence, on 0<=s<=1/4,

    P(s)>=Q(s)=A+B s+C s^2+D s^3,

where

    A=6343/96000,
    B=-1780007/2880000,
    C=214377/320000,
    D=p_3+p_4/4+p_5/16=24968203/6144000.           (16)

This is a whole-interval coefficient comparison:
p_4 s^4>=p_4 s^3/4 and p_5 s^5>=p_5 s^3/16.
No physical angle has been sampled.

C,D are positive, so Q is strictly convex for s>=0.
The two derivative signs are exactly

    Q'(1/8)=-306807197/1179648000<0,
    Q'(1/4)=706130159/1474560000>0.

Its unique minimum on [0,1/4] therefore lies in (1/8,1/4).
On that entire interval Q''>4, since

    C>2/3, D>4,
    C-2/3=3131/960000,
    D-4=392203/6144000.

At the single comparison point s_*=3/17, direct exact arithmetic gives

    Q(s_*)>1/6000,
    |Q'(s_*)|<1/500.

The respective rational reserves are

    Q(s_*)-1/6000=1005673/30185472000,
    1/500-|Q'(s_*)|=1424711/26634240000.

The whole curvature bound Q''>4, integrated between s_* and any
s in [1/8,1/4], yields

    Q(s)>=Q(s_*)+Q'(s_*)(s-s_*)+2(s-s_*)^2
          >=Q(s_*)-Q'(s_*)^2/8
          >1/6000-1/2000000
           =997/6000000>0.                       (17)

The location of the unique minimum then gives Q>0 over all of
[0,1/4], and (16) gives P>0 there. Equation (17) is a uniform
strong-convexity argument over the whole interval.

### 4.2. The whole interval 1/4<=s<=3/8

Differentiate (15), keeping its actual rational coefficients:

    P'(s)=p_1+2p_2s
            +s^2[3p_3+4p_4s+5p_5s^2]
            +6p_6s^5+7p_7s^6.

The bracket is bounded below throughout this interval by

    3p_3+(3/2)p_4+(45/64)p_5
       =1134796967/122880000>0.

The signs justify taking its negative-coefficient terms at the
upper endpoint and then its positive product s^2 at the lower
endpoint. The other positive terms may be discarded. Thus

    P'(s)>=p_1+p_2/2
          +(1/16)[3p_3+(3/2)p_4+(45/64)p_5]
          =1734634997/5898240000>0.               (18)

Since P(1/4)>0 by Section 4.1, P is positive on the entire second
interval too. Its exact value there is
P(1/4)=26707393/1572864000>0.

The two continuous arguments include the shared endpoint s=1/4 and
the closed comparison endpoints zero and 3/8. They prove the complete
polynomial assertion, not just its endpoint signs.

### 4.3. Translation back to the original unchanged slider

The defining denominator 2/5+s^2/2 is positive. Dividing the
established P(s)>0 by it gives

    (1-s^2)[1/2-T_0(s)]>1/5.

Since t<T_0(s), c^2=1-s^2 and H=t+1/2, this proves the strict,
whole-domain original slider gain

    (1-H)c^2=(1/2-t)c^2>1/5.                     (19)

No auxiliary value of beta or phi has replaced the actual H.
The original full-star equation was used first, and the scalar
bounds control only its necessary value.

## 5. The actual upper return is outside the original disk

The derivative compensation (9) applies on (10). The function G is
concave on (0,1), as follows either by direct differentiation or from
the complete pinned source. For completeness, if
J(b)=sqrt((1+sqrt(1-b^2))/2) and a=sqrt(1-b^2), then

    J''(b)=-1/(4aJ)-b^2/(4a^3J)-b^2/(16a^2J^3)<0.

Thus it suffices to bound its endpoints on [2/5,1/2].
At the lower endpoint the already checked a_0>1833/2000 gives

    J(2/5)^2>3833/4000>(489/500)^2,
    3833/4000-(489/500)^2=883/500000>0.

Hence

    G(2/5)>9/10+489/500=939/500.

At b=1/2, a=sqrt(3)/2>4/5. Therefore J(1/2)^2>9/10,
so J(1/2)>9/10 and G(1/2)>19/10>939/500.
Concavity proves

    G(b)>939/500 throughout 2/5<=b<=1/2.           (20)

Combine (9),(19),(20). The actual retained B point satisfies

    (K+f)_y>939/500+1/5=1039/500>R,

where the exact squared-radius excess is

    (1039/500)^2-1105/256=6711/4000000>0.          (21)

This contradicts containment of the unchanged actual B.

The proof includes b=2/5. The b=1/2 joining endpoint is covered
both by the continuous comparison and by the earlier complete
larger-b theorem. Together with that theorem and the earlier
c<=3/4 exit, this proves:

**Opposite-return theorem.** The entire original opposite-D-vertex
row is impossible for every b>=2/5, with all original force ratios,
physical masks and exterior contacts retained.

## 6. Literal original callers and exact remaining domains

In D02.L135 and D02.L1345 retain the exact original labels and edges

    A=0, V=1, D=2, C=3, N=4, B=5,
    A--V--D--C--N--B--A, AD.

A,D stay unloaded true3; V,B,C stay loaded true2. N stays unloaded
true2 in L135 and loaded true2 in L1345. Every original force,
torque, circle coefficient and full mean at B,C,N remains, as do
all three completing physical units. The new upper-return theorem
does not use or replace N's equation.

The already accepted complete bridge and large-return-ratio exits
retain their exact scopes. Combining them with only the complete
theorems above leaves the following necessary residual in this
particular physical-two perpendicular-singleton feature:

| Original support at D for C | Conditions still required of a survivor |
| --- | --- |
| Opposite vertex | c>3/4, 0<b<2/5, 11/50<y<1/sqrt(2), original z=1, 0<q=(u-y)/b<18/5 |
| D-owned exterior side | c>3/4, 0<b<16/25, y>3/11, original q=u/b<18/5 and z=u*a/c in (0,1) |

Every remaining row must still satisfy every actual containment,
nonoverlap, full-star and whole-mean constraint, and the complete
projection inequality of the pinned bridge source. No such residual
is asserted realizable. The side row is not assigned the opposite
identity (5) anywhere in the new proof.

Whole-data reflection transports the complete original chart, masks,
means, coefficients and labels. Other AD owner features, other
physical-two roof charts and unique-physical-circle types retain
their own domains. Neither entire D02 family, a coarse parent,
the global common-selection audit, the sharp nine-unit theorem,
equality classification nor Lean is declared closed.

## 7. Exact proof and independence boundary

The root-triangles continuation independently reconstructed the new
derivative compensation and scalar polynomial calculation after the
full derivations were supplied, and checked the same continuous
inequalities and rational values. A separate full-current-source
noncontributor review is still required before adoption of this
manuscript.

All scalar coefficients, derivatives and rational reserves above
were recomputed exactly from the displayed formulas. The comparison
points prove curvature and monotonicity statements over full
continuous intervals. No square pose, force choice or normal angle
was numerically sampled or used as a packing certificate.

No original force, normal, mean, physical corner, individual
coefficient, unit or true degree was changed. No frozen source,
original identifier, flag, ledger or metadata was edited. No
Lean/Lake build, CI/workflow, remote mutation or merge was used.

