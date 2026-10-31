# Independent review: every acute return frame, the actual unique-V chart, and the terminal tilt bound

Date: October 28, 2026 UTC.

Reviewer: mixed_capacity_review continuation, separate from the
two_circle_v_review author. This reviewer did not derive or edit the source
under review. Root reports that it suggested using the genuine clockwise
T2 moment in the k>1 regime of Section 6; the author derived the scalar
comparisons and the resulting b<3/5 bound. That author-side route suggestion
is disclosed here and does not supply any of the checks below.

**Verdict: PASS at exactly the printed scope. No mathematical repair is
required.** The force-free theorem checks every actual corner throughout
the whole acute-frame domain, and the original-force corollaries have
literal hypotheses. The terminal bound uses the genuine U3 and T2, with
the correct sign in the left-handed U-axis coordinates. This proves
continuous necessary reductions, not the whole original D02 row.

## 1. Frozen source and complete review scope

Reviewed source:

    ALL_ACUTE_RETURN_FRAMES_LARGE_COORDINATE_INTERIOR_AND_TERMINAL_TILT_REDUCTION.md
    SHA256 533c90b4120cb08c9b73257eed5483d53569e2177be145807bb695d1d2923b1c

I read the entire proposed source, the entire ordered-frame scalar source,
the complete original two-interface cover, the complete physical-stress
source, and the complete six-body graph/load cover. I followed the
operative endpoint equations and physical order in the complete
single-hub path proof and reread the full degree-free boundary-pair moment
lemma. The same-nine lower-window result is used only to obtain R>2 on
the unchanged nine units. This checks the new arguments, the actual entry
into the older ordered theorem, and the exact original join. It does not
replace an older source's separately recorded review.

All seven direct source pins agree with the current files:

| Direct source | Verified SHA256 |
| --- | --- |
| PARALLEL_TIP_LARGE_X_RETURN_ALL_CORNERS_INSIDE_CIRCLE.md | 35ed0820293125307c28d2d6b0e14b841b5578517e67fa7aea90f42bb3544b35 |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| D02_SINGLETON_TERMINAL_AXIS_TWO_NONPARALLEL_RETURN_COVER.md | 7997a9a7eacc0aedf85801eda33b5e7a0ca2e4ce37b86b95f7cb1ba3b6c28ce9 |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 |

The new scalar theorem has no force or degree premise. Its full actual
domain is x>=9/8, y>=1/2, x^2+y^2>=4, e,f>0, e^2+f^2=1,
0<=r<=1, together with either y<=x or the entire conjunction
y>=x, x^2+y^2<=5, r*e*y<=x*(1-r*f). In the first alternative
x>=1 suffices. The old e<=f source also needs only x>=1 in its
second alternative. These stronger subdomain claims are checked below.

## 2. Four actual corners and the whole y<=x alternative

For Z=(-x,y), E=(1-x,y-1+r*f), u=(e,-f), v=(f,e), I obtain
the source's four increment pairs exactly:

    (1,B), (1+e,B+f), (1+f,B-e), (1+e+f,B+f-e),
    B=1-r*f in[1-f,1], B>0.

For a horizontal increment A and downward increment D, direct expansion
gives the exact deficit A*(2x-A)+D*(2y-D). The signs in this formula
are important when the third corner has D<0; the source keeps that case.

For E the deficit is at least one. For E+u and y>=1, its horizontal
part is at least f^2, and concavity on D in[1,1+f] gives a vertical
part at least e^2. For y<1, R>=2 implies x>sqrt(3)>3/2; the two
parts sum to more than 1+e-f>0. These arguments need no ordering of
e and f and include both closed r endpoints.

For E+v write k=r*f+e-1. If k<=0, the horizontal part is at least
e^2 and the vertical part (-k)*(2y+k) is nonnegative. If k>0 and
y<=x, then k<=j=e+f-1 and x>=sqrt(2). The exact lower bound is

    2sqrt(2)*(2-e)-(1+f)^2-j^2.

Its difference from

    6sqrt(2)-8+(e-(sqrt(2)-1))^2

is precisely 1-2ef>=0. The remaining constant is strictly positive
because sqrt(2)>4/3. This verifies the full third-corner argument,
including the absence of an e<=f assumption.

For E+u+v, squared norm is convex in the original scalar r. At r=0
its deficit is

    2[(x+y-2)*(1+f)+(x-y)*e].

Here x+y>2 follows from positive x,y and x^2+y^2>=4, so the
deficit is strictly positive when y<=x. At r=1, A=1+e+f is at
most 1+sqrt(2)<2sqrt(2)<=2x, while D=1-e is strictly between
zero and one and 2y>=1. Both terms of the exact deficit are then
strictly positive. Convexity of squared norm handles every intermediate
r, without moving the actual application or square.

This proves the entire first alternative already for x>=1, with no
upper radius bound and no torque inequality. It also covers y=x
without importing any hypothesis from the other alternative.

## 3. The new third-corner estimate for y>=x and e>f

The second alternative's scalar inequality rearranges to

    r<=r_*=x/(e*y+f*x)<1.

The strict upper bound follows from y>=x and e+f>1. The quantity
r_* is an algebraic comparison, not a substituted physical pose or
contact mean. If actual k<=0, Section 2 already applies. Otherwise
K=e-1+f*r_*>=k>0, and the deficit is strictly decreasing in k.
Thus the source's D_0 is a valid lower bound.

For fixed R,e,f, along 1<=x<=R/sqrt(2), y=sqrt(R^2-x^2), I
checked

    L=e*y+f*x,
    J=e*f*R^2/L^2,
    K'=J/y,
    D_0'/2=[y*(1+f-J)+K*(x-J)]/y.

The inequality L^2>=4efxy gives J<=(y/x+x/y)/4<=5/8:
indeed 1<=y/x<=2 throughout the whole interval because x>=1 and
R^2<=5. Consequently D_0'>0 wherever K>0. Where K<=0, the
direct lower bound

    D_0>=(1+f)*(1-f)+(-K)*(2y+K)>0

is valid since K>e-1>-1 and y>=1. As K increases strictly, its
positive set is one interval. If the interval starts after x=1, its
initial value at K=0 is already positive. The only additional endpoint
check is therefore at x=1 when that endpoint has K>0.

At x=1, the factorization

    D_0(1)=e*y*P(y)/(e*y+f)^2,
    P(y)=2e(1-e)y^2-(2e-1)(2f-e)y-2f(f-e)

is correct. In the new domain e>f one has e>1/sqrt(2)>1/2,
f-e<0, and y>=sqrt(3). The source's estimate is valid throughout
this whole domain:

    2f(2e-1)<2f*e^2<=e,
    (2e-1)(2f-e)<2e(1-e).

The first strict sign uses (1-e)^2>0; the non-strict step uses
2ef<=1. Subtracting e(2e-1) from the first bound gives the second.
Thus

    P(y)>2e(1-e)y(y-1)>0.

Every external factor in D_0(1) is positive. This checks the entire
new third-corner argument at x>=1, including equality in the original
scalar inequality. There is no search over x, r, or the acute frame.

## 4. The new fourth-corner bound at x>=9/8

At r=0, the exact fourth-corner deficit rewrites as

    4(x-1)*(1+f)+2(y-x)*(1+f-e)>0.

The two terms are nonnegative and cannot both vanish under R>=2.
At r=1 write A=1+e+f and D=1-e. For x>=sqrt(2), both terms of
the deficit are positive. For 9/8<=x<=sqrt(2), replacing y by its
lower bound sqrt(4-x^2) decreases the deficit. Along that lower circle
its derivative is

    2A-2D*x/sqrt(4-x^2)>0,

because x/sqrt(4-x^2)<=1 and A>D>0. The minimum is therefore at
x=9/8, y=5sqrt(7)/8. Since 7-(21/8)^2=7/64>0, the strict
lower comparison is the printed

    F=A*(9/4-A)+D*(105/32-D).

Set t=1-e. The new e>f domain gives 0<t<1-1/sqrt(2)<3/10 and
f=sqrt(t*(2-t)). Expansion gives exactly

    32F=16+97t-32t^2-(56-64t)*f.

Both quantities being compared here are strictly positive: the first
is more than 16 on this interval, and 56-64t is positive. Their
squared difference expands to

    256-3168t+25857t^2-21568t^3+5120t^4.

The coefficient bound is uniform:

    25857-21568t > 96933/5 > 19386 > 19000.

Retaining the strictly positive surplus in the linear and quartic terms
gives the source's whole-interval lower bound

    P_1(t)>256-3200t+19000t^2
           =19000*(t-8/95)^2+2304/19>0.

The expansion and completed-square identity are exact. The prior
positivity of the two unsquared sides makes the squaring step reversible
for the desired inequality. This proves F>0 and strict positivity at
r=1. Convexity then handles all original r in[0,1]. No torque or
upper-radius premise was used for this fourth-corner proof.

Together with Section 3, this handles every new e>f frame in the
second alternative. It preserves x=9/8, R^2=4, R^2=5, and the
allowed scalar equality cases; the strict inequalities come from
positive rational or radical reserves, not omitted endpoints.

## 5. Complete old ordered-frame input and actual scope

The source imports only the e<=f branch from
PARALLEL_TIP_LARGE_X_RETURN_ALL_CORNERS_INSIDE_CIRCLE.md. I read its
whole proof, not just its statement. With its a=e,b=f, it has exactly
the same actual square and the same two alternatives, with the stronger
x>=1 threshold. It retains e=f and all allowed r endpoints. It
expressly excludes e=0 and exhibits the aligned counterexample, so the
new theorem correctly does not extend to a closed frame endpoint.

The old source's first four-corner alternative has the same valid
arguments checked in Section 2. Its maximal-parameter derivative for
the third corner is exactly the one checked in Section 3. At x=1,
the old positive-K case forces 1/2<e<=1/sqrt(2). Its factor P(y)
is increasing for y>=sqrt(3), with P'(y)>17/24, and its comparison
quadratic gives

    P(sqrt(3))>(13/16)*(sqrt(2)-1)>0.

I checked the ingredients: e(1-e)>1/5, 2e-1<1/2,
2f-e<5/4, 2f(f-e)<=(4/3)*(1-2e^2), and the monotonicity of

    H(e)=(35/16)*(2e-1)+(4/3)*(1-2e^2).

For the fourth corner at e>=1/4, its complete concavity argument
proves e(x-1)+f(y-1)>1/2. This makes the actual W center's
u-coordinate negative for every r and proves the fourth corner is
strictly closer than the already interior third corner. At e<1/4,
the two endpoint arguments give a positive r=0 deficit and the explicit
r=1 reserve 39/40. These two intervals include e=1/4 and e=f
with no gap.

The older source's physical corollaries are not imported as a substitute
for the new chart. Its actual x>=1 force-free theorem is applied only
after Section 5 of the new source proves the complete W parametrization
and scalar inequality. No ordered-frame assumption is inferred from the
graph. The new e>f argument supplies precisely the previously uncovered
acute-frame side of the scalar theorem.

## 6. Genuine V2 force, torque, and the actual W chart

The new physical application assumes a true loaded V2 with unique
physical circle corner (-X,Y), X,Y>1/2, and actual supports

    V=[-X,1-X] times[Y-1,Y],
    P=(-X+p,Y-1), Q=(1-X,Y-1+q), 0<p,q<1.

The full circle resultant is a positive multiple of (-X,Y), since
there is only one physical circle corner and total V load is positive.
The unchanged pair forces are down toward U and right toward W.
Thus F_V=(-nu,mu), mu=Lambda*Y, nu=Lambda*X. The true torque
equation gives

    mu*(X-p)=nu*(Y-1+q),
    Y*p=X*(1-q).

Every sign and parameter in (16) follows from these original
applications. No physical two-corner mask is silently made unique and
no individual zero coefficient is assumed positive.

At P the actual inward U axes are

    u_0=(a,-b), v_0=(-b,-a), a,b>0, a^2+b^2=1.

The original UW application is the actual adjacent vertex P+u_0.
Strict exposure there gives

    -(b/a)*m_x<m_y<(a/b)*m_x,

and hence m_x>0. The actual W has its unique left vertex at Q and
its two inward directions are (s,c),(c,-s), with c,s>0. The only
possible original W-owned UW normals are these two positive-horizontal
axes. The minimum-(c,-s) side is the upward side from Q, whereas
P+u_0 is strictly below Q. Therefore the actual UW normal is (s,c)
and its original side-interior parameter sigma satisfies

    P+u_0=Q+sigma*(c,-s), 0<sigma<1,
    p=1-a+c*sigma, q=s*sigma-b>0.

It follows that b<s and c<a. The scalar r=q/s lies in(0,1) and
the actual W is precisely

    Q+[0,1](c,-s)+[0,1](s,c),
    Q=(1-X,Y-1+r*s).

Moreover p-r*c=1-a+(c/s)b>0. Combining this strict geometric
inequality with the original V2 torque gives

    r*c*Y<X*(1-r*s).

This is exactly the theorem's required scalar inequality at
x=X,y=Y,e=c,f=s. The new r is explicitly only a coordinate derived
from q; it replaces neither of the original contact parameters. The
argument uses no U3 premise and no equation at W, whose true degree may
be three or higher in this local application.

For physical-boundary W, the all-acute theorem therefore forces

    X<9/8,
    Y>5sqrt(7)/8>33/20.

The latter exact radical comparison has reserve
7-(66/25)^2=19/625>0. If c<=s, the fully checked older theorem
gives X<1 and Y>sqrt(3). The first alternative with X>=1
excludes Y<=X; if X<1 and Y<=X then R^2<2, also impossible.
Hence Y>X throughout the surviving physical chart. All of these
claims are necessary reductions on the actual unchanged W.

## 7. Full U3 terminal equations and the clockwise T2 sign

Section 6 separately assumes the complete singleton-terminal-axis
component, so the terminal consequences are not attached to the broader
Section 5 local theorem. The original forces from U toward V and W are
respectively mu*North and omega*(s,c), with both positive. Their sum
has both ordinary components positive. Of the four actual U axes, only
v_0=(-b,-a) can oppose that sum. Thus the terminal normal is v_0,
and the original terminal application is

    P_T=P+v_0+theta*u_0, 0<theta<1.

The horizontal U force is omega*s=tau*b. Torque about the actual P
is omega*(a*c+b*s)=tau*theta. Therefore

    theta=b^2+(c/s)*a*b.

These are the full three-force equations. No incident force has been
deleted, and the parameter theta is the original terminal application.

The actual occupied U arc runs from P through P+u_0 toward P_T.
Because det(u_0,v_0)=-1, this arc is clockwise in the displayed
ambient frame. The compatible boundary-path order has the same
orientation. The degree-free boundary-pair moment lemma has a strictly
negative moment on each clockwise directed path edge. The genuine
degree-two terminal torque therefore gives

    det(P_T,v_0)>0.

This is exactly the endpoint sign in the complete single-hub path
source. It includes the full original mean on T's other boundary edge
and needs no two-force equation at an internal boundary unit.

In these coordinates the determinant expands as

    det(P,v_0)=a*(X-p)+b*(Y-1)=z_1,
    det(u_0,v_0)=-1,
    det(P_T,v_0)=z_1-theta.

Thus theta<z_1, as printed. In particular the left-handed U-axis
pair does not reverse this crucial inequality; its minus sign is already
present in the determinant expansion.

## 8. Whole k>1 tilt interval and terminal-side monotonicity

For k=c/s>1, the actual geometry gives 0<b<s<1/sqrt(2),
and (17) can be written p=1-a+k(q+b). Substituting this and
theta=b^2+kab into z_1-theta gives exactly

    0<aX+bY-a-b+1-2b^2-a*k*(q+2b).

Cauchy's inequality gives aX+bY<=R. Since k>1, q>0 and a,b>0,
the displayed strict inequality implies

    R>(a+b)*(1+2b)-1.

On the whole 0<b<1/sqrt(2) interval, a=sqrt(1-b^2)>b and

    d/db[(a+b)*(1+2b)-1]
      =(1-b/a)*(1+2b)+2(a+b)>0.

At b=3/5, the right-hand side of the radius inequality is 52/25.
The exact upper-window reserve is

    (52/25)^2-1105/256=1599/160000>0.

Consequently b>=3/5 would contradict R<=sqrt(1105/256), and the
entire k>1 physical domain has b<3/5, a>4/5. This conclusion is
uniform in q, all other original magnitudes, every allowed terminal
parameter, and all physical masks on W and T.

Finally, along the actual terminal U side,

    d/dt |P+v_0+t*u_0|^2=2*(t-z_1).

Since 0<theta<z_1, this derivative is strictly negative on the whole
closed segment 0<=t<=theta. Hence |P_T|<|P+v_0|. This is a
correct strict comparison, but the source appropriately does not treat
it as an independent boundary-T contradiction.

## 9. Literal original D02 join, endpoints, and retained obligations

For M6.B6.HEXAGON.D02.L01345, the mapping is literally

    U=2,V=1,W=0,T=3,
    loaded boundary path1,0,5,4,3.

The true degrees are U3,V2,W3,5_2,4_2,T2, with all three extras
retained. The complete original owner cover supplies the V-owned
g=-Jn interface, L=n dot m>0, and its actual nonparallel singleton
geometry. In the right-handed ambient V frame with horizontal axis
-Jn and vertical axis n, the original U inward axes become exactly
(a,-b),(-b,-a), and the original W normal has positive coordinates
(K,L)=(s,c). The actual unique physical V corner is the upper-left
corner (-X,Y). This verifies the rigid-frame entry without a
translation of the circle origin or a reselected normal.

The new result therefore applies to every unique-circle V-owned member
of this exact original interface. Its geometry preserves every original
application and full mean. The full U3/T2 hypotheses apply only for
the terminal consequences. W remains true degree three; no W2 torque
or concurrence is asserted. Physical masks on W and T, all individual
zero circle coefficients, all other boundary-path means, and all three
completion squares remain present.

The source also correctly retains or separates every relevant endpoint:

| Endpoint or interface | Treatment |
| --- | --- |
| r=0 or r=1 | Both checked in the scalar square; the second alternative's own scalar inequality determines which can occur |
| e=f | Complete old ordered-frame theorem applies |
| e=0 or f=0 | Excluded by the explicit acute-frame premise, not claimed by a limit |
| y=x | Complete first alternative, without a torque premise |
| x=9/8 | Strict fourth-corner reserve proves interior |
| R^2=4 or R^2=5 | Included in the corresponding scalar alternative |
| Equality in r*e*y<=x*(1-r*f) | Third-corner maximal-parameter proof remains strict |
| c=s | Ordered case, not included in the k>1 terminal restriction |
| b=3/5 when c>s | Excluded by the exact positive radius reserve |
| Actual physical two-circle V masks | Outside the unique-V physical corollary; no silent mask conversion |
| W-owned remaining return | Not claimed excluded by this source |

The proven outcomes are the all-acute scalar theorem and the exact
necessary inequalities X<9/8, Y>5sqrt(7)/8, Y>X, together with
X<1,Y>sqrt(3) when c<=s and b<3/5,a>4/5 when c>s in the
full terminal component. The actual terminal-side norm comparison is
also valid. They do not themselves prove remaining closing-pocket
capacity or a whole original exclusion.

No original fine or coarse flag is changed by this review. In particular
the entire D02 row remains open until its remaining interfaces have
complete exits at their full original scope.

## 10. Verification boundary

All mathematical checks above are analytic whole-domain arguments.
A small local exact-integer/rational check independently expanded P_1,
verified the completed-square coefficients, verified the three printed
radical/radius reserves, and hashed the reviewed source and seven direct
inputs. It did not search a packing, sample a pose, test an angle mesh,
or generate a numerical exclusion certificate. These calculations are
arithmetic checks on the displayed identities, not substitutes for the
continuous proof.

No Lean/Lake compilation, CI or workflow, remote write, commit, normal
reselection, moved original application, degree truncation, physical
mean replacement, omitted completion unit, or original-ledger mutation
was performed. The source passes independent full review at its exact
stated scope.

