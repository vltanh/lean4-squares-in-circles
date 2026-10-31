# The positive root-moment half and the final lower-house TDC.D exclusion

Date: October 28, 2026 UTC. Authors: root and thin_d continuation.

**Status: complete proposed hand exclusion of the entire positive
root-moment domain, with a literal join closing the original fine family
M6.B5L.HOUSE.LOWER.LTDC.D. Frozen for full root and separate independent
review. No original checklist or ledger is edited by this source.**

The new local ingredient is a radius-free geometric relay theorem for
two perpendicular owned ports of a unit square. It retains both actual
side means, every orientation of the relay square, and the equality
orientations. Applied after the actual full A3 equation, it excludes the
last East/South return pair. No degree-two equation is imposed on D3,
and no A--C contact is introduced.

## 1. A uniform perpendicular-port relay theorem

Use arbitrary orthonormal coordinates x,y. Let an actual unit U be

    U=[a,a+1] x [c-1,c],       b=c-1.

Let actual units V,W have the following original support contacts with U:

    P=(a+1,c-delta),   U-to-V normal East,
    Q=(a+tau,b),       U-to-W normal South,
    0<=delta<=1,       0<=tau<=1.

In particular the whole V lies in x>=a+1 and the whole W lies in y<=b.
Assume the actual physical contact V--W is nonempty. Fix numbers

    E>0, F>=0, H(x,y)=E*x-F*y, H0=E*a-F*c,
    0<=kappa<=F/E,     delta<=kappa*tau.                (1)

**Relay theorem.** Every actual point of W satisfies H>=H0. Hence W
cannot touch any actual set all of whose points have H<H0.

Only the displayed three unit squares and their actual supports enter
this theorem. Their circle masks, force magnitudes, other neighbors and
true degrees are arbitrary. The relation between delta and tau is a
caller hypothesis; no local force balance is assumed in this lemma.

### 1.1. Weak transverse span at the actual East application

For a unit square having a minimum-x support point P, every actual point
has y-coordinate at least P_y-1. At a vertex, its inward orthonormal axes
both have nonnegative x-coordinate. At most one axis has negative
y-coordinate, and that component has magnitude at most one. At a
side-interior application, the inward side axis is East and the full
tangent interval has length one. The mean's position on that interval
can only decrease the possible downward span. Side endpoints are also
included in the vertex argument.

Consequently the whole actual V satisfies

    y>=c-delta-1=b-delta.                              (2)

This weak bound deliberately retains the equality orientation.

### 1.2. The entire parallel W orientation

If W owns the South contact normal, its actual upper side is y=b and

    W=[ell,ell+1] x [b-1,b]

for its unchanged tangent interval. An actual point of V--W has
x>=a+1, so ell+1>=a+1, or ell>=a. Every actual point of W therefore
satisfies

    H>=E*a-F*b=H0+F>=H0.                              (3)

This includes every shared-side mean, either endpoint, and both limiting
vertex orientations. No location of Q within that upper side is fixed.

### 1.3. Every nonparallel W orientation

Otherwise the actual South application Q is the unique top vertex of W.
Its two inward unit axes, in the original x,y coordinates, are

    R=(C,-S), L=(-S,-C),
    C=cos(theta)>0, S=sin(theta)>0,
    0<theta<pi/2, C^2+S^2=1.

Thus the complete actual square is

    W=Q+[0,1]R+[0,1]L.                                (4)

Let Z=Q+tR+wL be an actual point of V--W, where 0<=t,w<=1.
Its x-coordinate is at least a+1, giving

    t*C-w*S>=1-tau.

Therefore

    Z_y=b-t*S-w*C
        <=b-(1-tau)*S/C-w/C
        <=b-(1-tau)*S/C.

Together with (2), this yields

    delta>=(1-tau)*S/C.

Using (1), and retaining the endpoints tau=0,1, gives

    tau>=S/(S+kappa*C).                               (5)

Suppose some actual point of W had H<H0. The two axis increments in
(4) are

    H(R)=E*C+F*S>0,
    H(L)=-E*S+F*C.

The application itself has H(Q)=H0+F+E*tau>=H0. Thus H(L)<0 is
necessary, and the exact minimum of H on (4) is H(Q)+H(L). The assumed
point therefore implies

    tau<S-(F/E)*(1+C)<=S-kappa*(1+C).                 (6)

But the difference between the lower bound in (5) and the last upper
bound in (6) has numerator

    S-(S-kappa*(1+C))*(S+kappa*C)
       =S*(1-S)+kappa*S+kappa^2*C*(1+C)>0.             (7)

Its denominator S+kappa*C is positive. Strict positivity already holds
in S*(1-S), including kappa=0. Equations (5)--(7) are contradictory.
This proves the relay theorem over every nonparallel orientation. The
two excluded theta endpoints were included in (3), so no limit remains.

## 2. The literal original house and its established exact reductions

Retain all nine actual closed unit squares and the original positive
physical certificate. The original lower-house graph is

    AT, DT, AD, AB, BC, CD, BL.

L is the genuine D leaf at B; the positive block circle loads are exactly
T,D,C. The true positive degrees are B3,A3,D3,T2,C2,L1. The three
remaining packing units are arbitrary and remain physically present.

Before invoking any radius-window theorem, apply the unconditional
same-nine result `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md`, with the
complete printed analytic entry point
`LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md`, to these unchanged nine
units. It gives R>2>79/40. Its hypotheses are only containment and
pairwise disjoint open interiors; it does not assume a positive graph,
lower radius window or a smaller packing theorem. Thus every original
R<=2 alternative is already impossible, and no low-radius domain is
silently discarded in the following reduction.

The complete small-support reduction gives the actual canonical chart

    B=[-s,r] x [-b_B,a0],
    r=R-sqrt(2), s=1-r,
    0<a0<=epsilon<1/60, b_B=1-a0>59/60,
    d=sqrt(R^2-1/4)-1=1+epsilon<61/60,
    sqrt(17)/2<R<=sqrt(1105)/16,
    r>16/25, s>1/3.

Here the stated stronger lower bound for r follows from strict high
radius: R>sqrt(17)/2>103/50 and sqrt(2)<99/70 give
r>113/175>16/25.

The original leaf is East, with positive force alpha_L*East and actual
application (r,0). The actual B-to-A normal n satisfies

    n_y>19/20, |n_x|<1/20,
    0<h_B(n)<=epsilon.                                (8)

The prior full moment and nonradial-return reduction establishes in
this actual domain, rather than only under an auxiliary assumption:

* A is physically clear and has exactly one own interval missing zero,
  by a distance a satisfying 0<a<=epsilon.
* Its original AB moment is strictly opposed to both original AT and AD
  moments; all three are nonzero. The original TD moment is nonzero.
* In a sign-normalized own frame, the exact actual square is

      A=[a,A0] x [b,c], A0=a+1, b=c-1,
      0<a<=epsilon, b<=0<=c.

  The AB feature is West with positive-height original mean, or strict
  Northwest with original normal (-u,v), u,v>0, u^2+v^2=1, at (a,c),
  satisfying c*v<a*u. The original AT and AD moments are both negative
  in this own chart. The complete original A3 force and torque hold.

Here and below a reflection is used only to express this actual A frame.
It does not identify opposite signs in the fixed B chart or move the
original leaf to another side. This source treats exactly

    m_BA=det(p_BA,n)>0                                 (9)

in that fixed shallow-top, leaf-East chart. The complete negative sign
was excluded in the separate negative-root-moment source. The zero sign
is already excluded by the full moment reduction.

## 3. The complete positive B3 star places all of C below a0

Write n=(k,eta). Equation (9) implies k>=0. Indeed, if k<0, the
actual B application is its upper-left vertex (-s,a0), whose moment is

    -s*eta-a0*k < -(1/3)*(19/20)+(1/60)*(1/20)<0,

contradicting (9). Thus

    0<=k<1/20, eta>19/20, k^2+eta^2=1.                (10)

The full unchanged B3 force equation is

    alpha_L*East+gamma*n+beta*m=0,
    alpha_L,gamma,beta>0,

where m is the actual B-to-C normal. Both its coordinates are strictly
negative: its x-coordinate balances a strictly positive sum, and its
y-coordinate balances gamma*eta>0. Consequently m strictly exposes
the actual lower-left B vertex

    P_C=(-s,-b_B).

The actual C has P_C as a minimum-m support point. The strict
support-span lemma, with m dot North<0, gives the whole-unit inequality

    max_C y < (P_C)_y+1 = a0.                         (11)

More generally, for every nonzero first-quadrant unit vector g,

    max_C g.z < g.P_C+1 < 1.                          (12)

The last strict inequality uses s,b_B>0. This is physical support
geometry; the original loaded C2 force and torque remain unchanged.

## 4. The complete A3 triangle star has one cap return

The following full feature cover uses only the sign-normalized A chart
and its full three-force equation from Section 2. It is independent of
the B-moment sign. Its complete proof is also Section 4 of the negative
root-moment source; the operative argument is restated here.

Call a negative-moment return a cap return if it is East at an original
mean (A0,Y), Y>0, or strict Northeast (f,t), f,t>0, at (A0,c), with

    A0*t<c*f.                                         (13)

Every cap return has actual support h>1. For East this is A0>1.
For Northeast, (13) gives h=A0*f+c*t>A0/f>1/f. The actual unit
beyond its support forces h<=d, so f>60/61 and t<11/61.

At most one distinct actual unit can occupy any of these caps. For
completeness the actual center bound is |C|<M=91/60. For a cap normal
g with g_x>60/61, |g_y|<11/61, the actual neighbor center obeys

    C.g>3/2, |C.Jg|<sqrt(181)/60<27/120,
    C_x>K=3501/2440, |C_y|<1/2.

The squared diameter of the common containing rectangle is

    (M-K)^2+4*(M^2-K^2)=52124381/53582400<1.

Distinct actual unit centers are at least one apart, so two cap returns
are impossible. This includes East normals and every original mean.

There is at least one cap return. Otherwise the strictly negative
return features are West, South, Southwest or Southeast. If AB is
West, full vertical balance makes both returns horizontal; their West
directions then contradict full horizontal balance. If AB is Northwest,
full torque about the actual lower-right A corner gives v>=u: the AB
term is lambda*(u-v), and all listed other terms are nonnegative.
The negative AB support c*v<a*u therefore implies c<a<=epsilon.
Full torque about (a,c), together with full horizontal balance, supplies
an actual Southeast return (f,-t), f>=t>0. Its negative origin moment
requires

    t/f>(1-c)/A0>59/61.

Its actual support is strictly greater than

    cos(theta)+(59/60)*sin(theta),
    atan(59/61)<=theta<=pi/4.

This positive concave function has endpoint values
7141/(60*sqrt(7202)) and 119/(60*sqrt(2)), both greater than61/60.
That contradicts the whole-neighbor support bound h<=d<61/60.

Write V for the unique cap unit and W for the other return unit. They
physically touch through the unchanged original TD edge. The complete
owned-axis triangle and opposite-vertex support-span arguments give:

* If V is East, W is South at its actual mean (x,b), a<=x<=A0,
  or strict Southeast at (A0,b).
* If V is strict Northeast, W is strict Southeast at (A0,b).

For East, any West or Southwest return has negative dot product with
that A-owned axis, contradicting the unit-triangle theorem. For
Northeast, the West and South axes have negative dot product with the
Northeast normal, so the same theorem applied at their owned side
excludes them. A Southwest return is at the opposite actual corner
and its outer unit is closed-disjoint from V by the strict support-span
lemma. North and Northwest have positive own origin moment; another
East or Northeast negative return would be a second occupied cap.
These facts exhaust all sides, endpoints and strict vertex cones.

If AB is West, V cannot be East: the remaining South or Southeast
return would have strictly negative y-component and no original force
would have a positive y-component. Hence in that case V is Northeast
and W is Southeast.

## 5. The actual positive-sign frame separates C from the cap

Use global axes from Section 2. Since the actual global AB moment is
negative in (9), express A in a reflected own frame (e,f), f=-Je, so
its AB own-coordinate moment is positive. For a West AB normal put
u=1,v=0; for Northwest retain u,v from Section 2. The unchanged actual
B-to-A normal is

    n=u*e-v*f, e=u*n-v*Jn, f=-Je.

Therefore

    e_x=u*k+v*eta>=0,
    e_y=u*eta-v*k.                                    (14)

In the West case e=n, so e_y=eta>0. In the Northwest case the actual
AB point p=a*e+c*f is on the actual upper B support, giving

    a0=a*e_y-c*e_x>0.                                 (15)

Since a>0, c>=0 and e_x>=0, this proves e_y>0 there as well. Thus
the actual e lies in the first quadrant, including its vertical edge.

The cap unit's actual support normal g also lies in that quadrant.
For an East cap it is e. For a Northeast cap g=f0*e+t*f, where
f0,t>0 and t/f0<c/A0. Its global x-component is positive. In the
Northwest AB case, (15) gives

    g_y>f0*(e_y-(c/A0)*e_x)
        =f0*(a0+e_y)/A0>0.                            (16)

In the West AB case, c<=1<A0 and (10) give instead

    g_y>=f0*(eta-k)>0.                                (17)

Thus (12) applies to the unchanged cap normal g. All of C has
g-projection strictly below1, whereas all of V has g-projection at
least its actual support h>1. C and V are closed-disjoint. Because
the original C--D contact is nonempty, necessarily

    V=T, W=D.                                         (18)

This proves the actual identities, rather than choosing which of the
two return bodies occupies the cap.

## 6. Every strict Southeast D return is excluded

Suppose the noncap D return is strict Southeast at Q=A0*e+b*f, with
normal p*e-q*f, p,q>0. Its global y-component p*e_y+q*e_x is strictly
positive. The strict support-span lemma in the global downward
direction therefore puts every actual D point strictly above Q_y-1.

If AB is Northwest, (15) gives

    Q_y-a0=e_y+e_x>=1,                                (19)

since e is a first-quadrant unit vector.

For the West AB case retain its actual mean (a,w), 0<w<=c. Thus
a0=a*eta-w*k. If k=0, the same height difference is exactly1.
If k>0, the actual BA application is B's upper-right vertex (r,a0),
so its unchanged own ordinate is

    w=r*eta-a0*k
       >(16/25)*(19/20)-1/1200>3/5.                  (20)

The actual Southeast port then has

    Q_y-a0=eta+(w+1-c)*k
       >=eta+w*k>1-k^2+(3/5)*k>1,                    (21)

using c<=1, 0<k<1/20 and eta=sqrt(1-k^2)>=1-k^2.
The nonnegative comparison at k=0 was treated separately, so no mean
or axis endpoint is lost.

In every case D lies strictly above a0. This contradicts its actual
contact with C, all of which lies strictly below a0 by (11). Thus
there is no Southeast D return. In particular all West AB features
are excluded, since Section 4 forced their noncap return to be
Southeast.

## 7. The last East/South pair contradicts the uniform relay theorem

The entire remaining actual feature set is now:

    AB: strict Northwest (-u,v), at (a,c), u,v>0;
    AT: East, at (A0,c-delta), 0<=delta<=1;
    AD: South, at (a+tau,b), 0<=tau<=1.

The unchanged AT mean has c-delta>0 because its own origin moment is
negative. Write the original positive force magnitudes as lambda,mu,nu
on AB,AT,AD. The entire force equation gives

    mu=lambda*u, nu=lambda*v.

Taking its full torque about the actual AB point (a,c) gives

    mu*delta-nu*tau=0.

Consequently, for kappa=v/u>0,

    delta=kappa*tau.                                  (22)

No force is deleted to obtain this relation. It covers both original
side means and all four mean endpoints.

Set E=e_y>0 and F=e_x>0. Equation (15) says the functional
H(x,y)=E*x-F*y is precisely global height and H0=E*a-F*c=a0.
Using (14),

    F/E-kappa
      =(u*k+v*eta)/(u*eta-v*k)-v/u
      =k/(u*e_y)>=0.                                  (23)

This inequality includes k=0 and the strict Northeast BA cone k>0.
No prior exclusion of the upper-right B vertex or bound on the AB
application norm is required.

Apply the relay theorem with U=A, V=T and W=D, retaining the original
physical T--D contact. Equations (22)--(23) supply all its hypotheses.
It places every point of D at global height at least a0. But (11)
places every point of C strictly below a0, contradicting the original
C--D contact. This excludes the last whole East/South interface.

## 8. Literal original-family join and exact scope

The unconditional same-nine analytic theorem first excludes every
original R<=2 and supplies R>2>79/40 for all radius-window callers.
The complete small-support theorem then excludes the original
larger-support domain and all remaining R<=sqrt(17)/2, before supplying
the canonical thin chart used here. The complete full moment theorem
then proves the actual near A strip and strict opposed moments in that
same chart, including the previous radial AD endpoint. Its exact torque
identities give m_BA nonzero.

The separate complete negative-root-moment theorem excludes m_BA<0.
Sections 2--7 above exclude the entire complementary sign m_BA>0 in
the same actual leaf-East chart. These alternatives exhaust the original
thin family. Hence their literal join excludes the entire original fine
identifier

    M6.B5L.HOUSE.LOWER.LTDC.D.

This conclusion retains the original all-nine packing, arbitrary three
completion squares, actual circle radius, original normals and shared
means, all physical circle masks and zero individual corner weights.
T remains loaded2, D remains loaded3, C remains loaded2, and A remains
the true unloaded3. The proof uses no fabricated A--C contact and no
normal reselection after extraction. Physical zero-force contacts do not
weaken any of the strict whole-unit separations used above.

The relay theorem in Section 1 is a separate uniform, radius-free
geometric conclusion. It can be used in other families whenever their
actual complete force equations establish its displayed mean relation.
Its proof is one continuous trigonometric inequality over the whole
orientation interval; no angle cells or pose samples occur.

## 9. Direct mathematical sources and pins

| Source | SHA256 | Exact scope used |
| --- | --- | --- |
| NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md | 4c9e708945938c3f9df575e76f7573903d6b5a0ce4eccb5bcea760353a47458a | Unconditional same-nine R>2 theorem with its current printed analytic fixed-value provenance |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Complete current analytic assembly and explicit unchanged-nine entry R>2>79/40, without a lower-window premise |
| UNLOADED_OPPOSED_MOMENT_STAR_AND_LOWER_HOUSE_TDC_D_SMALL_SUPPORT_REDUCTION.md | 008acc8485e591b34604bf3e0b0cdcb03b7220aa249fc8e49552a065770ca129 | Original large-support and low-radius exclusions; exact shallow B chart, original force cone and retained true degrees |
| LOWER_HOUSE_TDC_D_FULL_MOMENT_AND_NONRADIAL_RETURN_REDUCTION.md | 51ecccadb6cebf8cfd0b2d6c6707c9b4387150d47b9be200def1df858e993edd | Actual near-A own strip, full original opposed moments, radial AD exclusion and nonzero m_BA |
| LOWER_HOUSE_TDC_D_NEGATIVE_ROOT_MOMENT_EXCLUSION.md | 7274452fc0411a3643b4bfa32d0cacaf748c5a1612165e272b9387d3f3241084 | Complete negative-sign half for the final join; sign-independent center cap and A3 feature cover, fully restated in Section 4 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Full strict support-span and owned-axis triangle theorem with actual side means |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Literal original lower-house graph, exact load mask, actual degrees and all-nine contract |

All new inequalities are explicit full-domain hand identities. No
computational exclusion certificate, numerical search, Lean compilation,
CI, workflow, remote operation or metadata mutation is used.
