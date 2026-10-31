# Fresh recovery audit of the broad full-star and short-path tools and their perpendicular caller

Date: October 28, 2026. Reviewer: return_scalar_assembly continuation.

**Verdict: PASS for both complete broad theorems and their literal
perpendicular application in Sections 1--9 of the recovered caller.**
No repair to any frozen recovered source is needed. This is a fresh
complete mathematical read and reconstruction, not a transfer of the
earlier review verdicts or a hash-only audit.

I read the sources and their full earlier reviews from the preserved
checkout `/tmp/pr11-02b-resume`. That checkout was kept read-only.
Only this recovery-audit file is written in the current continuation
checkout. Root recovery and adoption remain separate.

## 1. Exact reviewed objects and independence

| Complete object read | SHA-256 |
| --- | --- |
| `BOUNDARY_SUPPORT_POINT_HALF_PLANE_MOMENT_MONOTONICITY.md` | `c1694bb4265871e2f2c499e16a2e7ac01173b436966558a90e245e79856fbe9b` |
| `REVIEW_BOUNDARY_SUPPORT_HALF_PLANE_MOMENT_RECOVERY_AUDIT_2026_10_28.md` | `4fd4c5a6f309c7ca450fef19aa81565a16845ff801d75c97d8f2a3aa4ac4c96f` |
| `SHORT_BOUNDARY_PATH_ARBITRARY_FRAMES_FULL_RADIUS_OPPOSITE_SUPPORT_EXCLUSION.md` | `34c9a02388146c9e085f66831eb3be49bd577cf1ec47ff7948f7306c0f4c24f1` |
| `REVIEW_SHORT_BOUNDARY_PATH_FULL_RADIUS_ARBITRARY_FRAMES_RECOVERY_AUDIT_2026_10_28.md` | `ed608360c4b15b269cf37921fecff34b025197a7089cb49d38345dbdcd63e277` |
| `INNER_PENTAGON_D_OWNED_END_PERPENDICULAR_RETURN_COMPLETE_EXCLUSION.md` | `d9a723f10d7d36fd4f818c85a9133094519bde38882b24defc4b40d0ced401cc` |
| `REVIEW_H4_D_OWNED_PERPENDICULAR_AND_WHOLE_OWNER_RECOVERY_AUDIT_2026_10_28.md` | `25be5dc587884f3e0e7e9831f0d143466ba467c04bc71d3240ce6c1502d9fda4` |

All six identities were verified from their actual bytes. I had no
construction contribution to these recovered sources before their
frozen reviews. Before this recovery I developed a separate, weaker
near-count/arc approach to the perpendicular geometry; that construction
does not enter any proof checked here and is not treated as independent
review of itself. The recovered argument is materially broader and
uses a different full-C3/support method.

I also read the complete current boundary-moment and angular-order
sources, and the complete statement and proof of the genuine E2
properness lemma used by the caller. The fresh mathematical approval
here covers the two broad sources and the new perpendicular proof.
The nonaxis and same-axis members of the caller's final D-owned union
were identity-checked but are not newly re-reviewed mathematically by
this file; their existing complete reviews remain necessary.

## 2. Full support-point moment theorem: exact domain

The geometric theorem assumes only R>sqrt(2), an actual contained
boundary unit K with minimum-x support P=(X,h), X>-1/2, h>=0, and
a nonzero nonnegative combination F of its physical circle-corner
vectors with F_y<=0. It concludes that an actual negative-moment
contact to any other contained unit has nonpositive normal y component.
The neighbor need not be loaded or physically boundary and can have
any true degree. The supporting direction need not be an own K axis.

The strict lower support coordinate X>-1/2 is operative. The proof
does not claim the endpoint X=-1/2. Conversely h=0, F_y=0, aligned
side endpoints and physical two-corner masks are all deliberately kept.
A zero F is not admitted, and the perpendicular caller has genuinely
positive C load, so its full F_C is nonzero.

The universal actual-neighbor support bound is valid independently of
the main sign hypothesis. The farthest-corner identity gives

    |center|^2+1/2+|center.u|+|center.v|
       >=|center|^2+|center|+1/2,
    |center|<=sqrt(R^2-1/4)-1/2.

Every unit halfwidth is at least1/2. Therefore a unit beyond a support
height a in a unit direction requires

    a<=d=sqrt(R^2-1/4)-1<R-1.

This applies to the whole actual neighbor at the original support,
without a force, normal-selection or mask premise on that neighbor.

I checked the auxiliary moment comparison with all divisions positive:
for U=(A,B), A>0, B>=0, g_y>0 and det(U,g)<0, one gets B>0,
g_x>0 and B>A*g_y/g_x. Thus U.g>A/g_x>=A. The case B=0 makes
the negative determinant impossible and is not omitted.

## 3. All tilted masks, normal cones and full side means

For a genuine minimum-x vertex, the full actual frame is
P+[0,1](c,s)+[0,1](s,-c), c,s>0. With adjacent vertices U,V and
opposite W, the exact norm comparisons are

    |U|^2-|P|^2=|W|^2-|V|^2=1+2Xc+2hs>0.

They remain strict for negative X in the permitted interval, since the
expression exceeds1-c. Thus P,V cannot be physical circle corners.
The positive height of U and the weak sign F_y<=0 force W to be a
physical circle corner of nonpositive height. Consequently

    c>=s, 0<=h<=c-s,
    R^2=(X+c+s)^2+(h+s-c)^2.

If X<=0 this radius is at mostsqrt(2), contrary to the hypothesis.
Hence X>0. The equal-height W_y=0 and diagonal c=s cases are still
included. A second physical corner with zero individual weight is not
discarded; it remains part of the geometric mask.

Writing A=U_x=X+c, I independently expanded

    (A+1)^2-[(A+s)^2+(c-s)^2]
       =2A(1-s)+s(2c-s)>0.

It gives U_x>R-1>d. A negative-moment positive-y normal at U would
therefore demand a real neighbor support beyond d, a contradiction.
This argument concerns the full closed normal cone, not one selected
normal sample.

The remaining support features are exhaustive:

- At P, a positive-y vector in the cone generated by -u,-v has
  nonpositive x component and strictly positive moment.
- At V, both cone generators have negative y component.
- At W, positive-y outward normals have positive x component while
  W_x>0 and W_y<=0, so their moments are strictly positive.
- At U, the preceding actual-neighbor support argument excludes every
  positive-y normal of negative moment.
- The two lower sides have negative-y normals; the upper-left side
  has positive moment everywhere.
- On the remaining side q=U+t v, 0<=t<=1, the exact identities are
  det(q,u)=det(U,u)+t and q.u=U.u. A negative original moment forces
  the already excluded negative U moment without moving q or t.

Every original shared-side mean and both closed endpoints are retained.
No vertex cone or parallel supporting endpoint is left for a genericity
assumption to handle.

## 4. Aligned masks and the arbitrary complete-star consequence

In the aligned case K=[X,X+1] times[B,B+1], the actual support point
only gives B<=h<=B+1 and h>=0. The strict normal-distance comparison
2X+1>0 puts every physical circle corner on the right side. The sign
F_y<=0 then forces the lower right corner to be physical and

    -1<=B<=-1/2,
    R^2=(X+1)^2+B^2.

The two physical corners at B=-1/2, either zero individual weight,
the B=-1 endpoint, and every original side mean remain. The radius
bound gives X>0 and U_x>R-1>d at the upper right corner. The top
side and upper-left cone have positive moment; the upper-right cone
uses the same support contradiction; lower cones and side normals
have nonpositive y. This completes the entire aligned case.

Reflection reverses the determinant and leaves y components unchanged,
giving the exact left-support version used at C. For the full star

    F-sum_i lambda_i N_i+sum_j mu_j g_j=0,

every original incoming and outgoing force is retained. Incoming
y components are nonnegative and all original outgoing moments are
strictly positive. If F_y<0, the reflected geometric theorem makes
all outgoing y components nonpositive, so the full y projection gives
F_y>=0, a contradiction. If an incoming y component is strictly
positive, the same proof starts with F_y<=0 and gives F_y>0.

This is a valid arbitrary-degree theorem. It has no two-force law,
concurrence, own-axis, boundary-neighbor or replacement-mean premise.
The only required outgoing information is the strict original moment
sign. The source's sole convention pin matches current
`PHYSICAL_CONTACT_STRESS.md` exactly.

## 5. Full-radius opposite-support theorem: actual traversal and masks

The second broad theorem assumes two through four distinct physical
boundary units forming a real touching path. Its actual center angles
must have a strictly increasing counterclockwise lift of total advance
less than2pi, with each step less thanpi. That lift is a hypothesis,
not an inference from an abstract graph order.

The endpoint supports have independent heights h_L,h_K>=0 and
coordinates X_L,X_K>-1/2. Their entire units lie in the respective
outer half-planes. Both nonzero full physical corner combinations have
nonnegative vertical component. No degree, force balance, common
height, endpoint ownership or upper-radius assumption appears.

I independently checked its physical center lemma. In a tilted right
endpoint, a negative center height implies c>s and
0<=h<(c-s)/2. The lower adjacent and opposite vertices then have
negative heights. The upper adjacent vertex is farther than P, and
the opposite vertex is farther still, since

    1+2Xs-2hc>s(2X+s+c)>0.

Thus every actual physical circle corner has negative height, contrary
to the nonnegative full resultant. The aligned version has the same
conclusion from its uniquely lower far tangent coordinate. The true
center therefore has nonnegative height and positive x coordinate.
Reflection gives the left center in the upper-left quadrant. All
zero-height, axis-aligned, two-corner and zero-coefficient endpoints
remain valid.

For R>=79/40, every physical boundary center has radius>5/4.
Actual touching center distance is at mostsqrt(2), so each minor gap
is less than theta=acos(9/25). The actual lift premise identifies each
step with that minor gap. The endpoint quadrants force the total to be

    pi+delta_L+delta_K,
    0<=delta_L,delta_K<pi/2.

Therefore delta_L+delta_K<alpha=3theta-pi. Paths with at most two
contacts are already impossible because their total is belowpi.
The three-contact case has the exact constants

    cos(alpha)=13959/15625>89/100,
    sin(alpha)=1204sqrt(34)/15625<9/20,
    0<alpha<pi/6.

The quadrant is fixed before comparing cosine: theta lies between
pi/3 andpi/2, so alpha lies between0 andpi/2.

## 6. Both full far-corner formulas and the continuous orientation bound

For an endpoint center r(C,S), every actual frame is covered by
u=(cos(psi),sin(psi)), v=(sin(psi),-cos(psi)), 0<=psi<=pi/2.
The actual horizontal support is exactly

                     X=rC-(cos(psi)+sin(psi))/2.

For psi>=delta, both own center coordinates are nonnegative, and
the actual far-corner offset is (u+v)/2. Put sigma=1/sqrt(2),
theta_0=delta-(psi-pi/4), t=sin(theta_0). Direct expansion gives

    X=C sqrt(R^2-t^2/2)-sigma[2C cos(theta_0)+S t].

The cosine is nonnegative on the complete stated interval. This
formula includes psi=delta and psi=pi/2,delta=0, where a far-corner
tie occurs. Choosing a tied actual corner for its radius identity
does not assign its original force coefficient a new sign.

The global radical loss is

    sqrt(R^2-t^2/2)>=R-(2/15)t^2,

because its rationalized coefficient is at most
1/[2(R+sqrt(R^2-1/2))]<2/15 throughout R>=79/40.
Combining this with sqrt(1-t^2)<=1-t^2/2 and completing the square
gives the full bound

    X>=g(delta)=(R-sqrt(2))cos(delta)
                    -(15/68)sin(delta)^2/cos(delta).

The coefficient15/68 follows from sigma-2/15>17/30. Denominators
are positive; S=0 is explicitly included without dividing by S.

For psi<delta the own v coordinate is negative, so the far offset
changes to (u-v)/2. I separately rederived the corresponding formula

    X=C sqrt(R^2-sin(theta_0)^2/2)
         -sigma[(C+S)cos(theta_0)+C sin(theta_0)],
    theta_0=psi+pi/4-delta.

It is not the first-case radius formula reused with a changed sign.
With T=S/C<45/89, Cauchy--Schwarz and the positive exact bounds

    sqrt(2+2T+T^2)<181/100,
    (99/140)(181/100)=17919/14000
       <1921/1500<sqrt(2)-2/15

give X>(R-sqrt(2))C>=g(delta). This covers psi=0,delta>0.
Together the two cases cover all frames, own-coordinate signs and
aligned/tied endpoints.

Finally g=(A+k)cos(delta)-k sec(delta), A=R-sqrt(2)>0,
k=15/68, is strictly decreasing away from0 and strictly concave
on[0,alpha]. Hence

    g(x)+g(y)>=g(0)+g(x+y)>g(0)+g(alpha)

when x,y>=0 and x+y<alpha, including x=y=0. The exact whole-domain
reserve is

    X_L+X_K
      >(157/280)(189/100)
           -(15/68)(81/400)(100/89)
       =1+57857/6052000>1.

This contradicts the original support span<=1. All substitutions
have the correct direction, and there is no hidden upper-radius or
finite coefficient/mesh premise.

## 7. Literal perpendicular D3, HC quadrant and moment signs

The recovered caller retains HA,HB,HC,HD,AB,BC,CD,DE,EA, all nine
actual units, H4,D3,C3,E2, and all physical masks. Its scope requires
A,B,C,E to be physically boundary. Thus it applies to all L0124 and
only the physical-boundary-A mask of L124; A's total coefficient may
remain zero in that mask.

The already excluded shared HD and the original strict singleton
convention justify the actual chart

    D=[0,1]^2, P_H=(0,t), 0<t<1,
    D->H=(-gamma,0),
    P_C=(s,1), 0<=s<=1, D->C=(0,mu).

Full D3 makes DE=(gamma,-mu) at P_E=(1,0), and its complete torque
is gamma*t+mu*s-mu=0. Consequently l=1-s>0,
mu*l=gamma*t, and n_E=(p,-q)=(l,-t)/sqrt(l^2+t^2).
The s=1 impossibility is proved from the original positive equations;
s=0 and every original shared-CD mean are retained.

The actual H has unique rightmost point P_H and axes(-a,-b),(-b,a),
a,b>0. Every original HC point S satisfies S_x<0,S_y>=1. The
actual H-to-C support normal N satisfies N_x>=0,N_y>0. I checked
the entire proof of that quadrant: supporting inequalities exclude
N_y<0 by the H upward-axis support, East and West separately exclude
N_y=0, and the complete tilted C vertex/side cone table excludes
N_x<0. The aligned C case retains its entire minimum-y side and
excludes its right and top faces by S_x<0 and max_y(H)<2.

The actual rim sector containing H fixes D-C-B-A-E-D as the positive
orientation. The occupied rim and simultaneous real circle accesses
give the physical boundary order C,B,A,E, including a zero-load A.
The corner-to-center deviation and strict center separation preserve
this order. Each real boundary contact is its minor center step, so
the total C-to-E lift is strictly between3pi/5 and6pi/5. The original
CB moment is positive and the original EA moment is negative.

These are actual origin moments and actual lifts, not contact labels
used as proxies for order. I reread the entire current geometric
moment-orientation and circle-angular-order sources for this join.

## 8. Full C3 gives the precise support and resultant hypotheses

With the original origin written O=(xi,zeta), let k=1-xi and
d_R=sqrt(R^2-1/4)-1<61/60. Full genuine E2 torque gives

    -q*k+p*zeta<0.

The actual E minimum support is p*k+q*zeta<=d_R. Their combination
gives zeta<q*d_R<d_R even if zeta is negative. The actual C North
support gives 1-zeta<=d_R.

If xi>=s, then k<=l and zeta<(t/l)k<=t<1. At every actual HC
point, S_x-xi<0, S_y-zeta>0, N_y>0 and N_x>=0. Its moment is
strictly negative. However the complete C3 torque is exactly

    mu_CH det(S-O,N)
       =mu_CB det(P_CB-O,g_CB)-mu*(s-xi)>0.

The contradiction proves xi<s, including the excluded equality case.
Both the original HC force and original CD term are present.

Use the oriented chart e=South,f=East, whose determinant is+1.
The original C support becomes

    (-X_C,h_C), X_C=1-zeta>1-d_R>-1/60>-1/2,
    h_C=s-xi>0.

The complete C3 force equation has its two incoming f components
equal to0 and N_x>=0. Its only outgoing CB moment is strictly
positive and retains its sign in this orientation-preserving chart.
The full-star moment theorem therefore gives(F_C)_x>=0 in the
original D coordinates. No force is deleted and no C-owned North
side is presumed. The broad path theorem's center lemma then gives
(c_C)_x>=0,(c_C)_y>0, namely0<arg(c_C)<=pi/2.

## 9. The actual auxiliary E top and the exact short-path call

The caller constructs an actual maximum-y point Q=(x_T,M) of the
unchanged E with x_T>=1 and0<=M<=p<1. I checked both support-owner
cases. At an E vertex, inward axes have nonnegative dot product
with(p,-q); at most one can have positive y component. Such an axis
has positive x component and y component at mostp. Adding exactly
that positive-y axis gives Q. If none increases y, P_E itself is a
valid top point. A zero-y axis needs no endpoint perturbation.
At an E side, its full parameter rho in[0,1] gives the exact top
point P_E+(1-rho)(q,p). This covers every original side mean and
every free-vertex possibility without inferring E ownership.

The properness theorem is applied only at the genuine E2, because
its actual other neighbor A physically touches the circle. Its
conclusion q_E=t_E F_E=P_E-O+ell*n_E, t_E>0,ell>=0, and xi<s
give(F_E)_x>0. The lemma's one-corner, two-corner, coincident-contact
and parallel-force exclusions retain the whole original radius
window. No claim that q_E lies inside E is made.

Suppose the actual top height Y=M-zeta were>=1/2. Then Y<d_R and
the actual E center height is strictly between-1/4 and31/60. Q has
positive original-origin x coordinate. If(c_E)_x<=0, its distance
from Q at most1/sqrt(2) makes |(c_E)_x|<1/sqrt(2), so its squared
radius is below2761/3600<25/16, contrary to physical boundary.
Hence(c_E)_x>0, and the center-angle range is

                         -pi/6<arg(c_E)<pi/2.

Together with C's range(0,pi/2], the positive C-to-E advance below2pi
is either belowpi/2 or above4pi/3. Neither lies in the actual path
interval(3pi/5,6pi/5). The supposed equality Y=1/2 is included in
the contradiction. Therefore Y<1/2.

In the same e=South,f=East chart, Q is a genuine right support with

    X_E=zeta-M=-Y>-1/2,
    h_E=x_T-xi>=1-xi>l>0,
    X_C+X_E=1-M<=1.

Both complete endpoint resultants have the required nonnegative f
components. The four distinct actual boundary units C,B,A,E provide
the real increasing center lift with each step<pi and total<2pi.
Every hypothesis of the broad full-radius opposite-support theorem
is therefore satisfied. Its conclusion that the span exceeds1 is
the contradiction. Q is never used in an original force or torque
equation; P_E remains the unchanged DE application throughout.

## 10. Identity reconciliation, remaining review limits and accounting

All fourteen direct pins displayed by the recovered perpendicular
source match the preserved checkout. In particular the two broad
sources and all operative caller conventions have their displayed
current identities. The two older angular-order and four-boundary-path
pins inside the boundary-moment source are exactly explained by one
extra terminal LF, with no mathematical change. The table also records
the separately checked triangle-chain historical identity, which has
the same one-LF relationship but is not a boundary-moment input pin:

| Current source | Current SHA-256 | SHA-256 after appending exactly one LF |
| --- | --- | --- |
| `CIRCLE_CONTACT_ANGULAR_ORDER.md` | `e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5` | `2625b3a2b730525a6397bc90232e78c5e1aac8091381c1f5e5fc8a71ef1da449` |
| `FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md` | `164d08bb2c4dfe8510247e44298d309920cb88a780221252d833f51aa654225f` | `6c38d162e1f2c435cf65a8b4a58a7001fe9489c65b3510159fee2687b9753708` |
| `TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md` | `29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82` | `0d61292a0aa57084b88b4a72754fc78e123e8b684dac09be966fb074ab58e877` |

These byte equalities were checked directly; no recovered source was
edited or silently repinned. The current boundary-moment source itself
is `851417d7fcd12ccb93a6f7f09ba7d7b2bf9bccc61c82fee3457b5ee4cee47e9a`.

This fresh audit approves the whole new perpendicular interface,
including shared CD, every original HC mean, arbitrary E support
owners, all aligned/tilted frames and all physical circle masks.
It does not infer the four-physical-boundary premises in the L124
mask where A is physically clear. It also does not independently
re-review the nonaxis/same-axis union merely because their pins match.
The recovered independent reviews and a current root adoption are
still needed for that full assembly and any original fine-gate credit.

All original H4,C3,D3,E2 equations, nine actual units, selected normals,
actual applications, full shared means, physical circle corners and
zero individual coefficients remain. No Lean/Lake invocation, CI or
workflow, computational certificate replay, source edit in the saved
checkout, commit, publication or gate/count change occurred during
this fresh audit.
