# One free strict roof: the other-hub perpendicular interface has no diagonal bridge

Date: October 31, 2026 UTC. **Complete original-feature hand theorem.**
Input PR #11 head: `d896360d49bbdae72567ebe43fee939366ab2c20`.
Every original diagonal-N realization of the mixed free-roof, genuine
other-hub-owned perpendicular AD chart is excluded. The proof is an
angular lemma followed by two actual radial-position contradictions.
No computational certificate, numerical bound, Lean or CI is used.

## 1. Full original setting

Keep all nine actual units, the original disk, all full forces and
moments, contact sets, shared means, physical circle corners and
individual zero coefficients. Use the original radius window and chart

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1>9/10,
    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-1/2).

The literal original stars are

    A:{V,D,B}, D:{V,A,C}, V:{A,D},
    B:{A,N}, C:{D,N}, N:{B,C}.

A,D,N are unloaded and V,B,C are loaded; the displayed degrees are
their true positive degrees. The A-to-V roof is free, with unchanged
normal h=(c,-s), c,s>0. The D-to-V roof is D-owned, with unchanged
normal k=(C,S), C,S>0, C^2+S^2=1. Put v=(-S,C).
AD is a genuine singleton owned by D, and its normal is perpendicular
to k. Let mu,nu,gamma>0 be the AV,DV,AD magnitudes, and W the original
AD application. Retain the initially common three-singleton selector
and incident-diagonal avoidance already used by the original cover.

**Theorem.** The original unloaded N cannot be a diagonal transmitter
anywhere in this entire feature. The reflected case is included by a
whole-data reflection and simultaneous exchange of the two hubs and
their exterior neighbors.

## 2. The actual perpendicular chart and endpoint owners

The roof point Q is in the relative interior of D's maximum-k side.
Since AD is genuinely D-owned and perpendicular to k, W is in the
relative interior of an adjacent D side, and

    W-Q=-t_D*k+epsilon*v, 0<t_D<1.

If the A-to-D direction were +v, W would be on D's minimum-v side,
so epsilon<0. Then (W-P).v=epsilon-C<0, contradicting W's strict
maximum-v support at A relative to its distinct vertex P. Therefore
the actual direction is -v. Now W is on D's maximum-v side, giving
epsilon>0, and its strict maximum-(-v) support at A gives epsilon<C.

P and W are distinct strict A vertices. They cannot be opposite by
the pure physical opposite-port triangle obstruction, because V,D
physically touch. Thus they are adjacent. Define

    a=S+t_D>S,
    w=C-epsilon, 0<w<C.

Their actual edge and its length are

    u=W-P=-a*k-w*v,
    a^2+w^2=1.                                      (1)

In particular 0<a,w<1. Write

    C=cos(beta), S=sin(beta),
    a=sin(delta), w=cos(delta),
    0<beta<delta<pi/2,
    x=delta-beta>0.

The other inward A edge is forced by the strict -v support at W to be

    b=-w*k+a*v,
    u=(-sin(x),-cos(x)),
    b=(-cos(x),sin(x)),
    A=P+[0,1]*u+[0,1]*b.                            (2)

Its alternative -b has positive -v projection and is forbidden.
All statements concern the original actual frames.

Since AV is free and both AV and AD are physical singletons, the
unchanged three-distinct-singleton selector forces **AB physically
shared**. The complete A force is

    F_AB=-mu*h+gamma*v=p*b, p>0,
    K=P+b+t*u, 0<=t<=1.                             (3)

Both return forces have negative b component, so +b is the only
possible shared exterior direction. The original AB mean t retains
its entire closed interval. In particular b is an actual B own axis.

The complete D force is

    F_DC=-nu*k-gamma*v=-q*c_0,
    q=sqrt(nu^2+gamma^2)>0,
    c_0=(nu*k+gamma*v)/q.                           (4)

It strictly exposes the unique D corner

    L=Q-k+(epsilon-1)*v
     =P-(1+S)*k-(1+w)*v.                            (5)

Thus DC is also a physical singleton. All three D contacts are
singletons at pairwise distinct original applications. The same
initial selector excludes a free DC normal; D cannot own a normal
strictly between its own axes. Therefore **C owns c_0**, at its actual
maximum-c_0 support L. No new owner is selected.

## 3. A diagonal bridge forces perpendicular endpoint axes

Suppose N is diagonal. Its original full N2 gives

    T-U=sqrt(2)*n, |n|=1,

where T is B's actual minimum-n support and U C's actual maximum-n
support. The unchanged incident-diagonal avoidance makes B,C own n.
Thus their actual frames are parallel. Since they also respectively
own b,c_0 by Section 2, these latter axes must be parallel or
perpendicular.

In the (k,v) frame b has strictly negative/positive components
(-w,a), whereas c_0 has strictly positive/positive components. Thus
c_0 cannot be b or -b. The sole perpendicular direction with both
components positive is -u. Consequently

    c_0=-u=a*k+w*v,
    nu/gamma=a/w.                                  (6)

The entire D moment about Q, using (4),(5) and the actual W, is

    gamma*(1-t_D)=nu*(1-epsilon).

As t_D=a-S and epsilon=C-w, equation (6) yields

    E:=w*(1+S)-a*(1-C)-2*a*w=0.                    (7)

This identity retains the full original D star; it is not an imposed
orthogonal normal or an altered side mean.

## 4. A radius-free angular lemma: the actual A edge has x<pi/6

We prove directly from (7) that

    delta<pi/4 and 0<x=delta-beta<pi/6.             (8)

First, equation (7) is equivalently

    sin(delta+beta)=2*a*w+a-w.                      (9)

For delta>pi/4, a>1/sqrt(2), w>0 and a<1. The right side of (9)
is strictly greater than one. To see the strict sign without an
approximation, compare the two nonnegative quantities

    w*(2*a-1), 1-a.

Their squared difference is

    w^2*(2*a-1)^2-(1-a)^2
       =2*a*(1-a)*(2*a^2-1)>0.

Hence w*(2*a-1)>1-a, which is exactly 2*a*w+a-w>1.
This contradicts (9). If delta=pi/4, its right side equals one,
but beta<delta makes 0<delta+beta<pi/2, again impossible. Thus
delta<pi/4.

For the second assertion fix the actual x>0 and consider the
elementary comparison function

    F(y)=cos(x+y)*(1+sin(y))
           -sin(x+y)*(1-cos(y))
           -2*sin(x+y)*cos(x+y), 0<=y<=beta.

This is only a scalar comparison, not a modified physical packing
or a newly selected force system. On the whole comparison interval,
0<x+y<=delta<pi/4. Write a_y=sin(x+y), w_y=cos(x+y),
S_y=sin(y), C_y=cos(y). Direct differentiation gives

    F'(y)=(w_y-a_y)*(1-2*(w_y+a_y))
             -2*w_y*(1-C_y)-2*a_y*S_y<0.           (10)

Indeed w_y>a_y, w_y+a_y>1, and the last two terms are nonpositive.
The first term is already strictly negative. Equation (7) says
F(beta)=0. Since beta>0, (10) gives

    0<F(0)=cos(x)*(1-2*sin(x)).

Now 0<x<pi/4 and cos(x)>0. Therefore sin(x)<1/2, proving
x<pi/6 and completing (8). This is one continuous hand proof over
the whole angular domain, including no omitted endpoint or cell.

## 5. The actual endpoint support difference lies in the orthogonal cone

Let Delta=K-L. By (5),(7), its b projection satisfies

    (L-P).b=w*(1+S)-a*(1+w)=a*(w-C)<0,
    Delta.b=1+a*(C-w)>1.                            (11)

Its c_0=-u projection is

    Delta.c_0=a*(1+S)+w*(1+w)-t>0.                 (12)

For the strict sign, t<=1 and a+w>1 imply
a+w-1+a*S+w^2>0. Because b,c_0 are perpendicular unit vectors,
(11),(12) are exactly a strict positive-cone representation of Delta.

Apply the complete loaded-endpoint cone theorem to the original full
B2,C2,N2. Its hypotheses hold with B inward external axis b, C inward
external axis -c_0, original support means K,L, and this strict cone.
It retains coincident or parallel endpoint applications, both physical
circle masks, exterior two-corner concurrence and individual zero
coefficients. Consequently n lies in the closed positive cone of
b,c_0.

The original diagonal ownership already makes n an axis of their
common frame. The only directed axes in this quadrant are therefore

    n=b or n=c_0.                                  (13)

The parallel endpoint conclusion of the same complete theorem makes
the entire actual B radial along b in the first case, or the entire
actual C radial along -c_0=u in the second case. These are physical
positions, not assumptions on which circle coefficient is positive.

## 6. Both possible radial endpoints are impossible

### 6.1. B cannot be the radial endpoint

The actual minimum-b support of B is, by (2),(3),

    H_B=K.b=1-d*cos(x)+sin(x)/2.

If B is radial along b, H_B=d, so

    d=(1+sin(x)/2)/(1+cos(x)).

But (8) gives sin(x)<1/2 and cos(x)>sqrt(3)/2>1/2. Hence

    d<(5/4)/(3/2)=5/6<9/10,

contrary to the entire original radius window.

### 6.2. C cannot be the radial endpoint

If C is radial along u=-c_0, all its actual b coordinates lie in
[-1/2,1/2]. Yet its retained actual point L has, by (2),(11),

    L.b=-d*cos(x)+sin(x)/2+a*(w-C)
       <-d*cos(x)+sin(x)/2
       <-9*sqrt(3)/20+1/4
       <-1/2.                                      (14)

The last strict inequality is the exact comparison sqrt(3)>5/3,
equivalently 3>25/9. The preceding inequalities use w<C,
x<pi/6 and d>9/10. Thus the actual L would lie outside the actual
radial C, a contradiction. Every original DC mean is retained;
here it is the fixed D corner forced by (4).

Both alternatives in (13) are excluded. This proves the theorem.

## 7. Scope, reusable lemma and remaining branch

The angular lemma (7)--(10) is radius-free and uses only the original
D3 torque and the forced perpendicular actual endpoint axes. Its
two support consequences apply uniformly over the full free-roof
normal, every positive original weight, every original shared AB mean
and both physical endpoint masks. The two radial exclusions need only
d>9/10. They do not use numerical sampling or an external result
about a purported packing.

The complete original diagonal-N feature is closed. The side-N
alternative in this mixed genuine perpendicular chart remains a
separate obligation: it need not make B,C frames parallel and cannot
be assigned equation (6) without proof. Loaded N in D02.L1345 is
also outside the present unloaded-channel conclusion. No original
whole-row or coarse ledger flag is changed by this feature alone.

The whole same-axis genuine interface is excluded separately in
`TWO_STRICT_FREE_ROOF_OTHER_HUB_SAME_AXIS_COMPLETE_EXCLUSION_2026_10_31.md`.
The both-free-roof/nonfree-interface exclusion is
`BOTH_FREE_ROOFS_NONFREE_AD_HAND_EXCLUSION_2026_10_31.md`.
Shared AD remains its own physical feature and is not converted to
the singleton hypothesis used here.

## 8. Exact operative sources

The physical chart, five-application distinctions and unchanged
selector are supplied by
`PHYSICAL_TWO_CORNER_TRIANGLE_TIP_FIVE_DISTINCT_APPLICATIONS_AND_HUB_SINGLETON_OWNER_COVER_2026_10_29.md`.
The pure physical opposite-vertex obstruction used in Section 2 is
Section 2 of `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md`.
The cone and its complete parallel-endpoint radial conclusions are
Theorem 2.1 of
`LOADED_ENDPOINTS_FORCE_TRANSMITTER_CONE_AND_PHYSICAL_CORNER_CAP_2026_10_29.md`.
The unchanged incident-diagonal entry is the same one used in
`PHYSICAL_TWO_TWO_STRICT_FREE_INTERFACE_EQUILATERAL_COMPLETE_EXCLUSION_2026_10_30.md`.

All actual squares and full original equations remain. The source
adds no selector, normal perturbation, chosen side mean, independent
computer certificate, formal verification or full n=9 completion claim.
