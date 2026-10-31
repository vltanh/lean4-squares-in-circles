# Independent review of the free-HD shared-DE pentagon exit

Date: October 28, 2026 UTC. Reviewer: recovery_audit continuation.

**Verdict: PASS for the entire free-HD, positive-length DE interface in
the stated four-physical-boundary domain.** The full shared DE mean is
retained; its strict D-side-interior range is derived from the real D3
torque. No C ownership is imposed. The original equations and applications
remain distinct from the auxiliary actual C support used for geometry.

## 1. Exact reviewed source and scope

Source: `INNER_PENTAGON_FREE_END_SHARED_E_RETURN_COMPLETE_EXCLUSION.md`.

- Bytes: 16,785.
- SHA-256: `a8a5174abe4dfec1f597fc7658b5843152f6bfa4b166ea6cd3960d3a1732fac2`.
- Git blob: `0acaa2ed81ca458cc2dc3e0b6d37f8e22c55e21c`.

I read the complete source and independently rederived the normal
table, whole HC contact-set bounds, actual rim order, original-origin
inequalities, full vertical-reach estimate, both exact p intervals,
auxiliary-support angular exit and final C3/path join. All eleven
displayed current direct pins match the checkout exactly.

The original graph is HA,HB,HC,HD,AB,BC,CD,DE,EA. H and D retain
their full unloaded degrees four and three. C and E retain their full
loaded degrees three and two. A,B,C,E are physically boundary, covering
the displayed feature in L0124 and L124's physical-boundary-A mask.
In the latter, A's original total circle coefficient stays zero. All
nine actual contained units and all original means, masks and forces
remain, throughout 79/40<=R<=sqrt(1105)/16.

The complete arbitrary-frame moment and full-radius path inputs at
c1694bb4 and 34c9a023 have separate full independent reviews by this
reviewer. The proper E2, angular, occupied-rim and physical-moment
inputs have also been independently reread in the preceding H4 caller
reviews. This review checks every new application on its actual domain;
it does not transfer approval from those earlier callers.

## 2. Complete original shared-E normal cover and full D3

Normalize the original free HD at P_H=(0,0) in D=[0,1]^2, with
actual vector (-a,-b), a,b>0. If the original shared DE axis were
West or South, full D balance would make DC strictly Northeast at
(1,1). The strict unit-support reach gives H wholly in x<1,y<1
and C wholly in x>0,y>0. Any physical HC point would lie in
int(D), impossible. Thus DE is East or North. A whole diagonal
reflection takes these two original possibilities to East, keeping
the actual load roles and all equations.

Write DE=(mu,0) at its unchanged shared mean P_E=(1,s), with the
complete actual E pose [1,2] times [r,r+1] and its real overlap
interval for s. Full D balance gives DC=(a-mu,b). If mu<a it is
the same forbidden Northeast feature; if mu=a it is the North
D axis, with negative dot product against DH, forbidden by the
actual D-H-C owned-axis triangle theorem. Therefore mu>a.

Put c=mu-a>0. The original DC vector is (-c,b), its original D
application is P_C=(0,1), and the exact full D torque is
c-mu*s=0. Thus

    mu=a+c, s=c/(a+c), 0<s<1,
    n_C=(-p,q)=(-c,b)/sqrt(c^2+b^2), p,q>0.

The strict s interval is proved from positive original magnitudes,
not imposed as a selection condition. The mean may still be either
endpoint of the actual DE overlap on E. All three D applications
are now pairwise distinct. Neither an external C side owner nor a
three-singleton selector has been inferred.

## 3. Whole HC contact-set location and strict original normal sign

Strict unit reach at H's actual minimum-Southwest support gives
max_x(H)<1 and max_y(H)<1. At C's actual minimum-Northwest
support (0,1), it gives max_x(C)<1 and min_y(C)>0. Therefore
every physical HC point S has 0<S_y<1 and S_x<1.

If S_x>0, it is an interior D point, contradicting physical
nonoverlap. If S_x=0, it belongs to the actual H-D intersection,
which is the singleton (0,0), but its height is positive. Hence
every point of the full HC contact set has S_x<0. This includes
every possible shared mean and its closed endpoints.

Let N be the unchanged original H-to-C normal. Testing its actual
supporting half-planes at H's (0,0) and C's (0,1) gives N_y>=0.
If N is East, its H application would have x=max_x(H)>=0. If N
is West, its C application would have x=max_x(C)>=0. Both are
incompatible with the whole HC contact-set bound. Thus N_y>0.
No force or degree assumption at H or C was replaced in this
physical argument.

## 4. Actual occupied-rim orientation and original moment signs

At D's center, the C and H rays have angles 3pi/4 and 5pi/4.
The E ray lies strictly between -pi/4 and pi/4 because 0<s<1.
Thus the H spoke is in the strict counterclockwise sector from
the C rim ray to the E rim ray. The real interior-H/outer-rim
contract fixes the positive orientation D-C-B-A-E-D. There is
no coincident D application in this caller.

The compatible simultaneous real circle accesses give the circular
order C,B,A,E. The physical corner-to-center deviation below pi/12
and center separation greater than pi/5 preserve that order in every
circle mask. The actual CB,BA,AE contacts are their displayed
counterclockwise minor arcs. Thus the real three-contact center lift
has 3pi/5<Delta<6pi/5 and total advance below 2pi.

The complete physical boundary-contact moment theorem consequently
gives CB strictly positive and E-to-A strictly negative. The latter
reverses the last A-to-E path edge. These are original-origin moments
at the unchanged actual applications, not at an auxiliary support.
A's physical boundary status suffices even with zero total load.

## 5. Original-origin support and genuine E2 sign

Let the unchanged circle origin be (xi,zeta) in the local D chart,
and let d_R=sqrt(R^2-1/4)-1<61/60. The universal contained-unit
center/halfwidth bound applied to E's minimum-East support gives

    1-xi<=d_R, xi>=1-d_R>-1/60.

The original E2 torque, with the strictly negative EA moment,
gives det(P_E-O,East)=-(s-zeta)<0. Therefore zeta<s<1.

The genuine E2 properness theorem applies because its actual neighbor
A is physically boundary. It supplies q_E=t_E F_E=P_E-O+ell East,
t_E>0 and ell>=0. Hence (F_E)_y=(s-zeta)/t_E>0. No assertion
that this concurrence lies inside a physical two-corner E is used.
No corresponding two-force equation is assigned to C or H.

## 6. Actual C right support, including every owner and side parameter

At the original minimum-n_C point P_C=(0,1), C has an actual
maximum-x point Q_C=(M,y_T) with 0<=M<=q<1 and y_T>=1.
I checked the complete physical construction.

At a vertex application, C's two inward orthonormal axes have
nonnegative dot product with n_C. At most one can have positive
x component, since otherwise expanding n_C in those axes would
contradict (n_C)_x<0. Such an axis v obeys -p*v_x+q*v_y>=0,
so v_y>0 and v_x<=q. Adding it, if present, and zero on the
other axis gives the claimed rightmost point. If neither increases
x, P_C is already a suitable point. A zero-component axis causes
no missing endpoint.

For a C-owned side, retain its whole actual tangential interval
[-rho,1-rho]J n_C, rho in [0,1], with J n_C=(-q,-p).
The actual right corner P_C-rho*J n_C=(rho*q,1+rho*p) gives
the same bounds, including rho=0 and rho=1. No side position is
selected or moved.

About the original circle origin, Q_C is a left support with
X_C=xi-M and h_C=y_T-zeta>1-s>0. P_E remains the actual
right support with X_E=1-xi and h_E=s-zeta>0. Their exact
span is X_C+X_E=1-M<=1. The lower bounds on both X values
are not assumed at this stage and are proved in the next steps.

## 7. Complete touching-reach and actual-point proof of xi<3/2

I rederived the two vertical reach estimates without a C-owned
premise. At H's minimum-Southwest vertex, at most one inward
axis can have positive y component. For such an axis the support
inequality a*v_x+b*v_y<=0 gives v_y<=a/sqrt(a^2+b^2).
Thus max_y(H) is at most that value. At C's minimum-Northwest
vertex, at most one inward axis can have negative y component,
and its downward amount is at most p. A C-owned side has the
same bound directly from its full tangent interval. Therefore

    min_y(C)>=1-p,
    a/sqrt(a^2+b^2)+p>=1

by the actual HC contact. The inequality is weak, so all equality
and side endpoints remain.

Every unit contains P+n when P is an actual minimum-n support
point and n is a unit vector. At a vertex the inward own-axis
coefficients of n lie in [0,1]; on a side, the complete inward
normal unit segment is present. Hence the fixed actual C contains
Z=P_C+n_C=(-p,1+q), without any new owner or application.

Suppose xi>=3/2. Since zeta<s, the actual contained Z satisfies

    |Z-O|^2>(3/2+p)^2+(1+q-s)^2.

Both compared coordinate differences have the required positive
sign: xi+p>=3/2+p, and 1+q-zeta>1+q-s>q>0.

For p>=3/8, this yields

    |Z-O|^2>(3/2+p)^2+q^2=13/4+3p
               >=35/8=1105/256+15/256,

contradicting containment. The p=3/8 endpoint is included.

For p<3/8, q>sqrt(55)/8. The actual touching-reach inequality
gives a/sqrt(a^2+b^2)>5/8 and hence b/a<sqrt(39)/5.
The original DC direction gives b/c=q/p>sqrt(55)/3, so

    c/a<3sqrt(39)/(5sqrt(55))<3/5,
    s=c/(a+c)<3/8.

Since q>7/8, one has 1+q-s>3/2. Also 3/2+p>3/2.
Thus the same actual point has squared norm greater than 9/2,
again impossible. Both continuous p intervals are now covered,
including all original C-side positions. Therefore xi<3/2 and
X_E=1-xi>-1/2 strictly.

## 8. Closed bad-support angular exit for C, without circular reasoning

At E the original support height, X_E>-1/2 and full positive
vertical resultant are already established. The complete arbitrary-
frame center lemma therefore puts its actual center in the upper
right quadrant, with positive x and nonnegative y:
0<=arg(c_E)<pi/2.

Now suppose X_C<=-1/2. The lower bound xi>=1-d_R and M<1
give X_C>-d_R>-61/60. Since C's actual center is one actual
horizontal halfwidth to the left of its maximum-x support -X_C,
and that halfwidth belongs to [1/2,1/sqrt(2)], it satisfies

    -1/4 < (c_C)_x < 31/60.

The actual Q_C has strictly positive original-origin height h_C.
If (c_C)_y<=0, its circumradius distance to Q_C would imply
|(c_C)_y|<1/sqrt(2). The resulting squared center norm is below
(31/60)^2+1/2=2761/3600<25/16, contradicting the physical
boundary-center radius greater than 5/4. Thus (c_C)_y>0.
When its x coordinate is negative, its cosine is greater than
-(1/4)/(5/4)=-1/5>-1/2; when x is nonnegative its angle is
already at most pi/2. Therefore 0<arg(c_C)<2pi/3.

The difference arg(c_E)-arg(c_C) now belongs to
(-2pi/3,pi/2). Its positive counterclockwise advance below 2pi
must be below pi/2 or above 4pi/3; equality of representatives
does not give a permitted distinct lift. Both alternatives conflict
with the real three-contact advance (3pi/5,6pi/5). Thus the
entire closed supposition X_C<=-1/2, including equality, is
excluded.

This argument uses C's actual support width and physical boundary
radius, without needing any sign of F_C. The proof only derives
the C3 resultant sign after establishing X_C>-1/2, so the use
of the general moment theorem in the next section is not circular.

## 9. Full C3 sign and uniform opposite-support contradiction

The unchanged complete C3 force equation is

    F_C-mu_CD*n_C-mu_CH*N+mu_CB*g_CB=0.

Both incoming vertical components are strictly positive, from q>0
and N_y>0. Its actual outgoing CB moment is positive. At the
actual maximum-x support Q_C, the required coordinate bounds
X_C>-1/2 and h_C>0 now hold. The complete reflected arbitrary-
frame moment theorem c1694bb4 consequently gives (F_C)_y>0.
For example, a nonpositive full F_C height would force the CB
vertical component nonpositive, contradicting the positive incoming
sum in the original equation. No C force was discarded.

The two actual opposite supports Q_C,P_E therefore satisfy every
premise of 34c9a023: support coordinates greater than -1/2,
positive heights about the unchanged origin, positive full endpoint
resultants, four distinct actual boundary units, the real touching
path C-B-A-E and its proven center lift, and exact span 1-M<=1.
That whole-radius theorem gives span greater than one, the required
contradiction throughout the complete original radius interval.

This excludes the entire free-HD shared-DE interface for L0124
and L124 with physically boundary A. Other free-HD contact features,
L124's physically clear A mask, and the whole original graph/load
rows retain their separate obligations. The proof introduces no
positive circle weight at A.

## 10. Exact direct-pin audit and preservation

All eleven current identities match:

| Source | SHA-256 |
| --- | --- |
| BOUNDARY_SUPPORT_POINT_HALF_PLANE_MOMENT_MONOTONICITY.md | c1694bb4265871e2f2c499e16a2e7ac01173b436966558a90e245e79856fbe9b |
| SHORT_BOUNDARY_PATH_ARBITRARY_FRAMES_FULL_RADIUS_OPPOSITE_SUPPORT_EXCLUSION.md | 34c9a02388146c9e085f66831eb3be49bd577cf1ec47ff7948f7306c0f4c24f1 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| INNER_PENTAGON_OCCUPIED_HUB_AND_EXTERIOR_POCKET_LOCALIZATION.md | 37fad266560ea5e2bca29723f4db00617c35a67be2e82b70fbf743b75006a502 |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 164d08bb2c4dfe8510247e44298d309920cb88a780221252d833f51aa654225f |
| BOUNDARY_CONTACT_ORIGIN_MOMENT_ORIENTATION.md | 851417d7fcd12ccb93a6f7f09ba7d7b2bf9bccc61c82fee3457b5ee4cee47e9a |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a |

No source was edited or repinned. The previously reconciled historical
terminal-LF identities remain unchanged. P_C=(0,1), the actual DE
shared mean (1,s), and every original HC/path application remain in
their original equations. Q_C and Z are points of the unchanged C
used only for geometric bounds. H4, D3 and C3 remain full, and only
the genuine E2 receives properness. All actual squares, masks, zero
individual weights and the original 2513/58 inventory remain.

I performed no pose sampling, numerical exclusion, Lean compilation,
CI, workflow, metadata edit, commit, push or publication. The tool
checks in this review establish exact source-byte identities; the
mathematical verification above is by complete hand derivation.
Root adoption remains separate.
