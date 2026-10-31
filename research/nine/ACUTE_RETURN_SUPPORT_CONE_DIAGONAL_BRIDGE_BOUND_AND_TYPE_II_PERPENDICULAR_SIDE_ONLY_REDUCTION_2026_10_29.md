# An acute return-support cone bounds every diagonal bridge, and the Type II perpendicular row is side-only

Date: October 29, 2026 UTC. Author: roofs continuation.

**Status: complete proposed general hand theorem and whole original
Type II perpendicular-row diagonal exclusion, frozen for independent
review.** The general theorem has no circle-radius hypothesis. It
keeps the complete actual endpoint units and their original support
means, at arbitrary degrees and loads. It bounds the separation of
two actual support points by `sqrt(3)` whenever their inward directions
form the acute opposing cone specified below and an actual unloaded
diagonal square joins the endpoints.

In the entire remaining Type II D-owned perpendicular row, the full
original A3/D3 stars force precisely that acute cone, whereas the
unchanged support points have separation strictly greater than two.
Thus every diagonal transmission by the original unloaded N is
excluded simultaneously, at every angle, positive magnitude and full
original A-side mean in that row. Any remaining N in D02.L135 must
be its original side transmitter. That side alternative and the loaded
N of D02.L1345 are not declared excluded here.

## 1. General theorem, with every original support mean

Let B,C,N be distinct actual unit squares with disjoint open
interiors. Let Q_B be an actual minimum-support point or full
support-side mean of B in inward unit direction b. Let Q_C be
an actual minimum-support point or full support-side mean of C in
inward unit direction -c, where c is unit. Require

    b.c>0,
    Delta=Q_B-Q_C=lambda*b+eta*c,
    lambda,eta>=0, lambda+eta>0.                 (1)

Thus the support difference belongs to the closed positive cone
between b and c. Either cone coefficient can vanish. The parallel
case b=c is included. The strictly acute dot product in (1) is
an actual hypothesis; no perpendicular endpoint is silently added.

The actual N has zero total circle force and exactly two positive
body-pair forces, at its original B and C applications T and U.
Retain its full force and torque equations. Suppose this original
two-force transmission is diagonal. Retain the same original finite
diagonal avoidance from PHYSICAL_BODY_GRAPH_UNCROSSING.md:
at a physical point-only vertex/vertex contact, the unchanged selected
strict normal avoids both incident squares' diagonal directions.
This convention belongs to the initial common selection, before
multipliers, and is not imposed again on an extracted certificate.

**Acute support-cone theorem.** Under these exact hypotheses,

    |Q_B-Q_C|^2<=3.                              (2)

Consequently a support separation greater than sqrt(3) excludes
the complete original diagonal alternative.

The theorem uses no equation, boundary status or degree assumption
at B or C. Their supports can be strict vertices, genuine shared
means, side points, support-axis ties or either mean endpoint.

## 2. Full N force, torque and actual endpoint ownership

Write N's unchanged outward normals and positive magnitudes as
gamma_B*n_B and gamma_C*n_C. Its full unloaded force is

    gamma_B*n_B+gamma_C*n_C=0.

Unit length and positivity force gamma_B=gamma_C=gamma>0 and
n_B=d,n_C=-d for one unit direction d. Its full moment is

    gamma*det(T,d)-gamma*det(U,d)=0,
    det(T-U,d)=0.

Support makes T a maximum-d point of N and U a minimum-d
point. In the diagonal alternative retained here, they are opposite
N vertices, and the exact original relation is

    T-U=sqrt(2)*d.                               (3)

The two actual contacts cannot have positive shared length because
d is not an own side axis of N. If T or U were also a vertex
of its other incident unit, its selected normal would be an N
diagonal at a point-only vertex/vertex contact, contrary to the
retained initial convention. Therefore T is relative-side-interior
in B, U is relative-side-interior in C, and both B,C own d.

Choose the perpendicular unit w so (d,w) is oriented. The full
actual endpoint units consequently have descriptions

    B=T+[0,1]*d+[-beta,1-beta]*w,
    C=U+[-1,0]*d+[-chi,1-chi]*w,
    0<=beta,chi<=1.                              (4)

The actual endpoint interiors give strict beta,chi, but the closed
enlargement in (4) will prove every limiting side endpoint too.
No physical frame is assigned anew: (4) follows from both actual
owned interfaces. Every original support mean remains in (4).

For arbitrary support coordinates in those full squares, (3) gives

    Delta.d=sqrt(2)+xi_B+xi_C>=sqrt(2),
    0<=xi_B,xi_C<=1.                             (5)

Here xi_B=Q_B.d-T.d and xi_C=U.d-Q_C.d.

## 3. A complete signed support cover proves the general bound

Write b_d=b.d,b_w=b.w and c_d=c.d,c_w=c.w.

First, b_w and c_w cannot have the same strict sign. If both
are positive, Q_B minimizes the w coordinate of B, while Q_C
maximizes the w coordinate of C because its inward direction
is -c. Their exact original tangent coordinates in (4) give

    Delta.w=-beta-(1-chi)=chi-beta-1<=0.

But (1) gives Delta.w=lambda*b_w+eta*c_w>0.
If both are negative, the support coordinates instead give

    Delta.w=(1-beta)-(-chi)=1-beta+chi>=0,

whereas (1) gives Delta.w<0. Both contradictions include all
closed values of beta,chi. Hence

    b_w*c_w<=0.                                 (6)

The acute premise now gives

    b_d*c_d=b.c-b_w*c_w>0.

Thus b_d,c_d are both nonzero and have the same sign. They
cannot both be negative, since (1) would imply Delta.d<0,
contrary to (5). Therefore

    b_d>0, c_d>0.                               (7)

Consequently Q_B is on B's minimum-d side and Q_C is on C's
maximum-d side, including every original tangent-side tie. Thus
xi_B=xi_C=0 in (5), and

    Delta.d=sqrt(2).                             (8)

It remains to prove the whole closed tangent bound |Delta.w|<=1.
The following is the exhaustive sign-and-tie cover of (6).

* If b_w>0,c_w<0, both actual inward directions b and -c
  minimize w. Therefore Delta.w=chi-beta in [-1,1].
  If b_w<0,c_w>0, both maximize w and the same difference
  chi-beta results.

* If b_w=0,c_w>0, Q_B retains its entire original coordinate
  v_B in [-beta,1-beta], and Q_C has coordinate 1-chi.
  Thus Delta.w=v_B-1+chi<=chi-beta<=1. Equation (1) also
  gives Delta.w=eta*c_w>=0, so 0<=Delta.w<=1.
  If b_w=0,c_w<0, Q_C has coordinate -chi, whence
  Delta.w=v_B+chi>=chi-beta>=-1; (1) gives Delta.w<=0.

* If c_w=0,b_w>0, retain Q_C's entire original coordinate
  v_C in [-chi,1-chi]. Then Delta.w=-beta-v_C<=chi-beta<=1,
  and (1) gives Delta.w=lambda*b_w>=0. If c_w=0,b_w<0,
  Delta.w=1-beta-v_C>=chi-beta>=-1, and (1) gives Delta.w<=0.

* If b_w=c_w=0, (1) gives Delta.w=0.

This cover includes zero cone coefficients, parallel directions,
every original support mean and both enlarged endpoint values.
Together with (8), it gives

    |Delta|^2=(Delta.d)^2+(Delta.w)^2<=2+1=3.

This proves the general theorem without any radius estimate,
boundary hypothesis, discarded mean or force modification.

## 4. Exact original Type II perpendicular-row entry

Keep all nine actual squares, their containing disk and origin,
every original normal, application, positive force and circle term,
every full mean and every physical corner, including individual
zero circle coefficients. Use the exact conditional common-selection
entry of the original roof and port sources. Its prior simultaneous
nonempty open parameter domain remains an input.

The accepted complete singleton-West source at e63a1e1d leaves,
in its D-owned perpendicular feature, precisely this full chart:

    V=[a-1,a] x [b0-1,b0], Z=(a,b0),
    P=(a-1,b0-1), R=P+omega*North, 0<omega<1,
    nD=(C,S), tD=(-S,C), 0<C<S,
    h=(c0,-s), e=(s,c0), c0,s>0,
    H=c0*S+s*C, K=c0*C-s*S,
    nD=K*h+H*e, tD=-H*h+K*e,
    A=R-[0,1]*h-[0,1]*e,
    D=P-[0,1]*nD+[-t,1-t]*tD.                   (9)

The unchanged AD normal is g=-tD, genuinely D-only. The exact
original angular domain is

    0<alpha<pi/4<beta<pi/2,
    pi/4<theta=alpha+beta<pi/2,
    c0=cos(alpha),s=sin(alpha),
    C=cos(beta),S=sin(beta),
    H=sin(theta),K=cos(theta).                   (10)

In particular H>S>C>0, 0<K<C, s<C, c0>C, H+K>1,
and H^2+K^2=1. These strict comparisons follow from the whole
open angular interval (10), not from any sampled tilt.

All original magnitudes mu,nu,rho>0 remain. The full V2 is

    mu*East+nu*nD=kappa*Z,
    mu*det(R,East)+nu*det(P,nD)=0,
    (mu/nu)*(1-omega)=S-C>0.                    (11)

The actual AD application and the full geometry are

    W=R-e=P-u*nD+(1-t)*tD,
    u=H-omega*S in (0,1),
    t=1+K-omega*C in (0,1).                     (12)

The full unloaded A3 equations leave only the exact side return

    rho*K=mu*s,
    F_B=-(mu*C/K)*h,
    Q_B=R-h-z*e,
    z=s*H/C in (0,1).                           (13)

The entire original A moment determines this z. It is never set
to a convenient endpoint. The full unloaded D3 equations are

    F_C=-nu*nD-rho*tD,
    Q_C=P-nD-t*tD,
    nu*t=rho*(1-u)>0.                           (14)

Thus the original D application is its strict return vertex, and
every force in both hub stars remains. Equations (11)--(14)
are not replaced by a smaller exterior star.

The following proof retains all these equations. Its final geometric
implication needs no additional restriction on the original V ratio.

## 5. Rotate the whole data and retain the exact A mean

Use the actual oriented frame

    d0=-tD, n=nD.

Put p=1-u, so p,t are both strictly between zero and one. Define

    L=sqrt(p^2+t^2)>0,
    r=1-z=c0*K/C in (0,1).                      (15)

The identity for r follows from c0*K+s*H=C and the exact z
in (13). No independent side parameter is introduced.

In this rotated frame h=(H,K), e=(-K,H), and

    R-P=(-omega*C,omega*S),
    Q_C-P=(t,-1),
    Q_B-Q_C=(-E,V0),
    E=1+H+r*K,
    V0=p-K+r*H.                                (16)

For example, subtracting the original Q_C from Q_B gives the
first coordinate -omega*C-H+z*K-t. Substituting
t=1+K-omega*C gives -1-H-(1-z)K=-E. The second
coordinate is omega*S-K-z*H+1=p-K+(1-z)H=V0.

By (13),(14), the two actual normalized inward directions are

    b=-h=(-H,-K),
    -c=(t,-p)/L, or c=(-t,p)/L.                 (17)

Indeed (14) gives rho/nu=t/p. Therefore (17) is exactly
the original C force direction, not a new chosen normal.

The support separation is already too large for (2): since c0>C,

    E=1+H+(c0/C)K^2
      >1+H+K^2
       =2+H(1-H)>2.                            (18)

Thus |Delta|>2>sqrt(3). It remains to verify the full acute
positive-cone hypotheses, on the entire original continuous domain.

## 6. The actual exterior directions are acute at every original tilt

Their dot product is

    b.c=(t*H-p*K)/L.

Substitute (12) and p=1-H+omega*S:

    t*H-p*K
      =H-K+2*H*K-omega*(H*C+K*S).

The coefficient H*C+K*S is positive. Since omega<1,

    t*H-p*K
      >H*(1-C)+K*(2*H-1-S).                    (19)

If 2*H-1-S>=0, the right side is positive from H>0,C<1.
If 2*H-1-S<0, use K<C and H>S to obtain

    H*(1-C)+K*(2*H-1-S)
      >H*(1-C)+C*(2*H-1-S)
       =H*(1+C)-C*(1+S)
      >S-C>0.                                  (20)

The equality boundary 2*H-1-S=0 belongs to the first case
and is strict there. Thus b.c>0 over the entire original domain.

## 7. Both exact cone determinants are strictly positive

First,

    c0*H=S+s*K>S>C,
    r*H-K=K*(c0*H/C-1)>0,
    V0=p+(r*H-K)>p>0.                          (21)

Therefore

    det(Delta,b)=E*K+V0*H>0.                    (22)

For the other determinant, put

    A0=p*H+t*K,
    B0=t*H-p*K.

Then the exact expansion of (16) is

    L*det(c,Delta)=p*E-t*V0
                 =p*(1-t)+A0-r*B0.             (23)

We prove the last term is strictly positive with the entire original
omega interval retained. In the following one-variable comparison,
H,K,C,S,c0,s and r are fixed. The definitions p=1-H+omega*S
and t=1+K-omega*C give

    d/domega (A0-r*B0)
      =S*H-C*K+r*(S*K+C*H)>0.                  (24)

Here S*H-C*K=-cos(theta+beta)>0 because
pi/2<theta+beta<pi, and S*K+C*H>0.
The actual t<1 in (12) gives omega>K/C. We may evaluate
the increasing expression at this lower comparison endpoint,
without changing any original contact or mean. At omega=K/C,

    t=1,
    p0=1-H+K*S/C=1-s/C in (0,1),
    p0-r=-s*(1-H)/C.

Consequently

    (A0-r*B0)|_(omega=K/C)
      =H*(p0-r)+K*(1+r*p0)
       =-H*s*(1-H)/C+K*(1+r*p0)
      >K-(1-H)>0.                              (25)

The first strict comparison uses H*s/C<1, r*p0>=0 and
1-H>0. The second is H+K>1. All denominators and factors
are positive in the original domain. Equations (24),(25) prove
A0-r*B0>0 at every original omega. Since p>0,t<1,
(23) gives

    det(c,Delta)>0.                              (26)

Finally,

    det(c,b)=(t*K+p*H)/L>0.

Equations (22),(26) therefore give the exact strictly positive
cone representation

    Delta=lambda*b+eta*c,
    lambda=det(c,Delta)/det(c,b)>0,
    eta=det(Delta,b)/det(c,b)>0.                 (27)

Thus every hypothesis (1) has been proved for the actual two
unchanged support points and the actual original force directions.
No radial bound, extra circle equation, mean truncation or force
selection was used.

## 8. Exact original L135 consequence and load boundary

Retain the literal caller

    A=0,V=1,D=2,C=3,N=4,B=5,
    rim A--V--D--C--N--B--A, chord AD.

A,D are unloaded true3; V,B,C are loaded true2; N is unloaded
true2 in D02.L135. All six original units and all three additional
actual units remain. The full original conditional roof entry and
initial diagonal avoidance remain explicit inputs.

If the original N is diagonal, Sections 2--3 and (27) give
|Delta|^2<=3, while (18) gives |Delta|^2>4. This contradiction
excludes its entire diagonal alternative in the whole original
Type II D-owned perpendicular side-return row (9)--(14).

The full unloaded two-force theorem has only side and diagonal
transmission. Consequently every remaining N in this exact
owner/load row must have

    T-U=d_N,
    |d_N|=1,
    d_N an actual own side axis of N.             (28)

Its positive magnitudes, full moment, actual supports and any
original endpoint ownership remain unchanged. Equation (28) is a
necessary residual condition, not a declaration that a side bridge
exists. This source does not exclude that remaining side alternative.

For D02.L1345, N is loaded true2. It does not satisfy the
unloaded equation in Section 2, so this theorem makes no new
exclusion of that load alternative. Nor does it claim either whole
D02 parent, the whole Type II feature, the physical-two roof
domain, the global nine-square theorem or equality classification.

## 9. Complete direct inputs and verification boundary

| Complete operative source | SHA256 | Exact use |
| --- | --- | --- |
| UNIQUE_CIRCLE_TYPE_II_SINGLETON_WEST_COMPLETE_HUB_OWNER_AND_EXTERNAL_RETURN_DOMAIN_2026_10_29.md | e63a1e1d14c50363a244dae4d8927b2113a4222ca1064777660a366b092f351c | Full original Type II owner cover, genuine D-perpendicular chart, exact A mean and all V/A/D equations |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full unloaded true2 force/torque and complete side-or-diagonal transmission |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Same original finite diagonal avoidance and its endpoint-owner consequence |
| UNIQUE_CIRCLE_TRIANGLE_TIP_THREE_PORT_TYPES_AND_HUB_INTERFACE_OWNER_COVER_2026_10_29.md | 8266220efbb8ce769de90a90e27e86997400575d0b8bb80f5843af38ca447073 | Exact conditional Type II entry and original nonfree AD owner cover |
| D02_BOTH_UNLOADED_HUBS_UNIQUE_CIRCLE_ROOF_COMPLETE_NORMAL_OWNER_ASSEMBLY_2026_10_29.md | 97148714d460095f7e9c80332f01abdc45b5c9ad36950309973fe21b006972e7 | Prior compatible common-selection domain, preserved original roofs and no post-extraction choice |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original true degrees, both N loads and all three additional units |

The entire new generic proof, all tangent sign ties and closed means,
every full-star coordinate and both continuous determinant estimates
are printed above. The only new scalar comparisons are identities
and monotone trigonometric inequalities on explicitly stated full
intervals. No sampled force, angle or position is used.

The earlier common-selector compatibility obligation stays conditional.
No numerical pose search, angle mesh, packing certificate, shortened
star, replaced mean, altered mask, removed unit, metadata mutation,
remote write, Lean/Lake build, CI or merge was used. Full independent
current-source and literal-join review is required before adoption.
