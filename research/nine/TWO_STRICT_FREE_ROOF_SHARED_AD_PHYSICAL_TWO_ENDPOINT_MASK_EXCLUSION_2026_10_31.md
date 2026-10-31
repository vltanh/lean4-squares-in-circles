# A free strict roof and shared AD cannot have two physical-two exterior endpoints

**Date:** October 31, 2026 UTC. **Complete hand exclusion of the whole
stated physical-mask feature.** Input PR #11 head:
`d896360d49bbdae72567ebe43fee939366ab2c20`.

Keep the original nine actual units, all positive stars, physical
contacts, shared means and circle coefficients. In the mixed free/owned
strict-roof chart with physically shared AD, the two exterior endpoint
units B,C cannot both have two physical circle corners. Every original
exterior owner alternative is included. The proof does not require equal
circle weights at either endpoint, and an individual zero coefficient
does not change the physical mask.

No equation at N is used. Thus this whole-mask exclusion applies to both
D02.L135 and D02.L1345 whenever the same original shared-AD mixed-roof
chart is present. It also applies to either side or diagonal unloaded N.
It does not exclude the endpoint masks with a physically unique-circle
unit, or any other AD or roof feature.

## 1. Original physical chart and the same-nine radius entry

The complete chart derivation in Section 1 of
[TWO_STRICT_FREE_ROOF_SHARED_AD_COMPLETE_DIAGONAL_EXCLUSION_2026_10_31.md](TWO_STRICT_FREE_ROOF_SHARED_AD_COMPLETE_DIAGONAL_EXCLUSION_2026_10_31.md)
uses only the actual unloaded A3,D3, loaded V2, free AV, genuinely D-owned
DV, and positive-length shared AD. In particular its derivation precedes
every use of the equation or mask at N. We retain those complete original
premises here, with B,C still the actual exterior neighbors and physically
boundary units. Their additional forces and all circle coefficients stay.

The complete same-nine theorem
[NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md](NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md)
excludes R<=2 on the unchanged nine units. With

    d=sqrt(R^2-1/4)-1, R<=sqrt(1105)/16,

the full remaining radius range therefore gives

    14/15<d<61/60, R^2=(d+1)^2+1/4.                 (1)

The exact two comparison reserves are
15/4-(29/15)^2=11/900 and
(121/60)^2-1041/256=31/57600. No lower radius assertion
about the six-square component alone is made.

Use the actual physical-two V and its original inner corners

    V=[d,d+1] times [-1/2,1/2],
    P=(d,1/2), Q=(d,-1/2).

The complete shared chart fixes the actual common hub frame and units:

    k=(C,S), g=(S,-C), C=cos(beta), S=sin(beta),
    A=P-[0,1]k-[0,1]g,
    D=Q-[0,1]k+[-C,1-C]g,
    W=P-t*k, S<=t<=1.

The actual free A roof is h=(cos(alpha),-sin(alpha))=J k+H g,
where J=cos(alpha+beta), H=sin(alpha+beta), alpha>0. For the
original positive AV,DV,AD magnitudes mu,nu,gamma, the full
A,D,V equations give

    mu(J-H)=gamma(1-t),
    nu(1-C)=gamma(1+S-t),
    mu(d sin(alpha)+cos(alpha)/2)=nu(dS+C/2).

Consequently

    0<beta<alpha+beta<=pi/4,
    r=gamma/nu in [1-C,tan(beta/2)],
    m=gamma/mu=r*A0/B0,
    A0=d sin(alpha)+cos(alpha)/2, B0=dS+C/2.

The actual exterior hub forces and their unchanged exposed vertices are

    F_AB=-mu J k-(mu H+gamma)g, K=P-k-g,
    F_DC=-nu k+gamma g, L=Q-k+(1-C)g.

Normalize only these original forces:

    b=F_AB/|F_AB|=-a k-z g,
    a,z>0, a^2+z^2=1,
    cvec=-F_DC/|F_DC|=(k-rg)/sqrt(1+r^2).

Thus K is the actual minimum-b support of B, and L is the actual
maximum-cvec support of C. Put

    X=K.k=dC+S/2-1,
    Y=K.g=dS-C/2-1,
    L.k=dC-S/2-1, L.g=dS-C/2+1.                   (2)

The identities H+m-J=m t>0 and t>=S>0 give z>a. Also
X<1/4 and Y<-1/2: the first follows from
dC+S/2<=sqrt(d^2+1/4)<5/4, and the second from the
increasing function d sin(beta)-cos(beta)/2 on [0,pi/4].
In particular

    K.b=-aX-zY>z/2-a/4>0.                         (3)

The entire shared mean, including both endpoints and J=H, remains.

## 2. One uniform force-ratio estimate: a>3/5 and z<4/5

This estimate is useful throughout the full shared mixed-roof chart,
independently of the endpoint physical masks or the type of N.

At fixed d,beta the derivative of A0/J with respect to alpha is

    [d cos(beta)+sin(beta)/2]/cos(alpha+beta)^2>0.

We may therefore bound it at alpha+beta=pi/4, without requiring
that this equality be the actual original mean. Set u=tan(beta/2)>0.
The original inequality r<=u gives

    m/J
      <=u*[(d+1/2)C-(d-1/2)S]/[dS+C/2]
       =u*[(2d+1)(1-u^2)-(4d-2)u]/[4du+1-u^2].    (4)

The denominator is positive. Its comparison with three times the
numerator in (4) is exactly

    D(u)=1-(2d+3)u+(12d-7)u^2+(6d+3)u^3.

Using (1),

    D(u)>1-(151/30)u+(21/5)u^2+(43/5)u^3.

For 0<=u<=1/4, discard the nonnegative cubic term. The resulting
quadratic is decreasing on that interval and at 1/4 equals 1/240.
For u>=1/4 use u^3>=u^2/4. The resulting lower bound is

    1-(151/30)u+(127/20)u^2>0,

whose discriminant is -59/900. Thus D(u)>0 over the entire
original half-angle domain, and (4) proves

    m/J<1/3,
    z/a=(H+m)/J<=1+m/J<4/3,
    a>3/5, z<4/5.                                  (5)

These are bounds on the unchanged force magnitudes and directions.
No endpoint normal or shared mean is selected anew.

## 3. Complete physical-two support alternatives

A contained unit with two physical circle corners has them adjacent.
In its actual radial own frame it is [d,d+1] times [-1/2,1/2].
This follows directly by comparing the four squared corner radii in
its own coordinates: a two-corner maximum has one zero center coordinate,
and the positive other coordinate is d+1/2. The lower radius (1)
excludes the central four-corner equality.

Its minimum support in an owned unit direction belongs to

    {d,-1/2,-d-1},

and its maximum support belongs to {d+1,1/2,-d}. A non-owned
direction strictly exposes one actual vertex. No physical pair contact
can be at a containing-circle point: the two right-angle interior sectors
there would both lie strictly inside the same inward tangent half-plane,
and hence would overlap. Thus a physical contact exposed by a non-owned
direction must be an inner vertex, of squared norm d^2+1/4.

Suppose from now on that both B,C have these physical-two masks.
At B, (3) gives the exhaustive alternatives

    B owns b:      K.b=d;
    B does not:    |K|^2=d^2+1/4.                   (6)

At C, (2) gives L.g>1/2 and L.k<d-1<1/60. Hence
L.cvec<1/60<1/2, whether L.k is positive or nonpositive.
Its complete alternatives are therefore

    C owns cvec:   L.cvec=-d;
    C does not:    |L|^2=d^2+1/4.                   (7)

Neither table imposes a circle-force direction or equality between
the two individual corner coefficients.

## 4. Every physical-two B forces beta<pi/6

First suppose B owns b. If beta>=pi/6, then S>=1/2 and C>7/10.
Equations (1),(2) give

    X>-29/300, -Y<31/30.

Using 0<a<1 and (5),

    K.b=-aX+z(-Y)
       <29/300+(4/5)(31/30)
        =277/300<14/15<d,

contradicting the first alternative of (6). Thus this full owner
alternative requires beta<pi/6.

If B does not own b, the second alternative of (6) expands as

    d(C+S)+(S-C)/2=1.                               (8)

The left side is strictly increasing in beta on [0,pi/4]. At
beta=pi/6 it is strictly greater than

    (43+13 sqrt(3))/60>1,

using d>14/15; the last comparison follows from 13 sqrt(3)>17.
Equation (8) therefore also forces beta<pi/6. The full physical-two
B mask, with either exterior owner, has now given

    beta<pi/6.                                      (9)

## 5. The C-owned exterior alternative is impossible

Under (9), the following strict bounds hold throughout the original
chart:

    C>4/5, S<1/2, r<1/3,
    -L.k<151/300, L.g<133/120<10/9.

For example -L.k=1-dC+S/2, so (1) gives
1-(14/15)(4/5)+1/4=151/300 as an upper bound.
Likewise L.g=1+dS-C/2<1+61/120-2/5=133/120.

If C owned cvec, its first alternative in (7) would give

    d=-L.cvec=(-L.k+r L.g)/sqrt(1+r^2)>0.

The numerator is then positive, and division by sqrt(1+r^2)>=1
and the preceding exact bounds imply

    d<151/300+10/27
       =2359/2700<14/15,

contrary to (1). Thus C does not own its exterior direction. Its
actual inner-vertex equality is retained, not replaced by a side mean.

## 6. That actual C inner vertex excludes the B-owned alternative

Expand the second alternative of (7), using (2):

    0=|L|^2-(d^2+1/4)
      =2-C+S-2d(C-S+SC),

or equivalently

    d=(2-C+S)/[2(C-S+SC)].                          (10)

If S<=2/5, then C>9/10 and

    C-S+SC>43/50, 2-C+S<3/2.

Equation (10) would give d<75/86<14/15, again impossible.
Consequently S>2/5. With (9), C>sqrt(3)/2>6/7. Thus

    X>(14/15)(6/7)+1/5-1=0,
    -Y<3/2-(14/15)(2/5)=169/150.

If B owned b, its first alternative in (6), together with (5),
would now give

    d=K.b=-aX+z(-Y)
       <(4/5)(169/150)
        =338/375<14/15,

which is impossible. Therefore both original exterior directions are
unowned by their endpoint units. Both applications are genuine inner
vertices and both exact norm equalities in (6),(7) hold.

## 7. The remaining two actual inner-vertex equations contradict the radius

Equation (8) and (10) give simultaneously

    d=(2+C-S)/(2(C+S)),
    d=(2-C+S)/(2(C-S+SC)).                          (11)

Put q=C-S and p=C+S=sqrt(2-q^2), so 0<q<1.
Equating the two expressions in (11) is exactly F(q)=0, where

    F(q)=1+(5/2)q-q^3/2-(2-q)*sqrt(2-q^2).

Its derivative on [0,1] is

    F'(q)=5/2-(3/2)q^2+p+(2-q)q/p>0.

At q=12/25, p=sqrt(1106)/25<7/5. Therefore

    F(12/25)>33511/15625-266/125
              =261/15625>0.

The actual root consequently has q<12/25. The increasing function
(2+q)/(2 sqrt(2-q^2)) and the first equality in (11) now imply

    d<31/sqrt(1106)<14/15.

The final strict comparison follows by positive squaring, with reserve
196*1106-465^2=551. This last contradiction exhausts all four original
exterior ownership combinations at the two physical-two endpoints.

## 8. Complete original-mask consequence and remaining scope

In the original shared-AD mixed free/owned strict-roof chart, at least
one of B,C therefore has exactly one physical circle corner. This holds
for both unloaded-N L135 and loaded-N L1345. It is independent of N's
physical shape, contacts or force equation, because every step used only
the full original hub/V chart and the actual endpoint squares.

The universal force estimate (5) is an additional export for every
physical endpoint mask in this chart. The proof retains both shared-AD
mean endpoints, J=H, every original corner coefficient and every other
physical packing unit. Reflection gives the free-D-roof counterpart.

For unloaded N, the separate complete diagonal theorem and its
both-endpoints-owning-side exclusion still apply. Their surviving side
domain is now further restricted to an endpoint mask with at least one
physical unique-circle unit. This source does not by itself exclude
that remaining side domain or the other loaded-N endpoint masks, and
does not change an original row or coarse flag.

The proof consists of exact physical support alternatives, the full
unchanged hub identities, monotonicity and rational inequalities over
whole continuous domains. No numerical pose, computational certificate,
external proof script, Lean compilation or CI is used as a premise.
