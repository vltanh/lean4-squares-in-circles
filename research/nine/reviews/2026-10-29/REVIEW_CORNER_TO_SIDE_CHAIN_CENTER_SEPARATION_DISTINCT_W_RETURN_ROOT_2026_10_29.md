# Full independent review: corner-to-side center separation and the complete distinct-W return

Date: October 29, 2026 UTC. Reviewer: root continuation.

**Verdict: PASS at the exact scopes stated below.** The radius-free
center-separation theorem and the entire distinct-W-axis return exclusion
are accepted. This review covers the complete frozen source and every
direct operative source/review in its input table. It does not close the
whole original D02.L0145 row or alter any fine/coarse checkbox.

## 1. Exact target and review independence

| Complete reviewed source | SHA256 | Scope |
| --- | --- | --- |
| CORNER_TO_SIDE_CHAIN_CENTER_SEPARATION_AND_DISTINCT_W_RETURN_D02_L0145_EXCLUSION_2026_10_29_CONTINUATION.md | e71af4dcc66cb419ecfb766ea2adbd576f6c1c5a3da6a123898bb45bea12e94e | Entire 555-line source: both theorems, support-center and path proofs, full mask entry, circle slope, low join, literal caller and limits |

Root suggested investigating whether the existing bridge-center theorem
could extend beyond the parallel feature. Root did not supply the new
center inequality, its comparison vector, or the different-W circle
slope argument. Those are the author's new proof. This review independently
checks their full derivations and complete applications.

Root authored an older force-free radial-corner input. Its existing
independent component review remains part of the preserved input chain;
the present review does not relabel that authorship or claim to be an
independent first review of root's older source. The new inequality and
new full feature theorem have separate authorship from this reviewer.

All nine direct entries listed in Section 9 below were read in full in
the continuing review session. The complete local source 71a5b91d was
read beyond the portion actually used, including its explicitly separate
later pocket and allocation conclusions. Those conclusions are not
premises of the new theorem. Existing transitive prerequisite audits are
preserved at their recorded scopes; no fresh recursive audit of every
historical source is asserted.

## 2. Actual support point and center: all frames and closed means

The standalone theorem retains a fixed actual point Q, the actual square

    W = Q + [0,1]m + [-kappa,1-kappa]r,
    m=(b,a), r=(a,-b), 0<a<=b, a^2+b^2=1,
    0<=kappa<=1,

and S=Q-(1,1). The actual C has minimum-n support point

    A=S+Lambda*n,
    n=-(alpha,beta), 0<=alpha<=beta,
    alpha^2+beta^2=1, Lambda>=1.

I checked that the center formula

    c-A=rho*n+t*j,
    j=(beta,-alpha), rho>=1/2, |t|<=1/2

is valid for every actual unit frame. At a vertex, the nonnegative
components x,y of n in the two inward unit axes have x^2+y^2=1;
rho=(x+y)/2 and the tangent displacement is plus or minus (x-y)/2.
For a side-interior point the normal distance is 1/2 and the full
tangent interval is [-1/2,1/2]. Both endpoints occur in the same
closed calculation. Thus no original shared mean is shifted and no
vertex or side endpoint is dropped.

The enlarged inequalities on rho and t are used only as bounds on
the real center. No replacement square, private force equation,
boundary mask or degree assumption has entered this step.

## 3. Complete comparison-vector calculation

Set e=(alpha,beta) and

    K=(1,1)+(m+r)/2,
    Delta_0=K+(3/2)e-(1/2)j.

The literal difference of the two actual centers is

    w-c=Delta_0+u*e+v*j-kappa*r,
    u=Lambda+rho-3/2>=0, v=1/2-t>=0.

The three required scalar products are checked separately:

1. Delta_0.e=K.e+3/2>0, since both K coordinates are positive.
2. Delta_0.j=K_x*beta-K_y*alpha-1/2
   >=b/sqrt(2)-1/2>=0. Here alpha<=1/sqrt(2)<=beta and
   b>=1/sqrt(2); the positive K coordinates justify both comparisons.
3. With C_0=b*beta-a*alpha and S_0=a*beta+b*alpha,
   both are nonnegative and C_0^2+S_0^2=1. Hence
   C_0+S_0>=1 and

       Delta_0.(-r)=b-a+[3*C_0+S_0-1]/2>=0.

For the actual total increment E=u*e+v*j-kappa*r, these facts give
Delta_0.E>=0. The norm identity

    |Delta_0+E|^2=|Delta_0|^2+2*Delta_0.E+|E|^2

then proves the comparison. In particular, no unproved pairwise
nonnegativity between increment directions is needed: all such cross
terms remain inside the nonnegative squared norm |E|^2.

I independently expanded the remaining exact expression:

    |Delta_0|^2
      =5+2a+(4+2a+b)*alpha+(2+a-2b)*beta.

Both coefficients are positive and the first exceeds the second.
Since alpha+beta>=1, this is at least 7+3a-2b. The complete
radius-free inequality follows:

    |w-c|^2 >= 7+3a-2b.

It includes a=b, alpha=beta, alpha=0, and kappa=0 or 1.
The closed threshold 3a>=2b gives |w-c|^2>=7. The strict range
a>3/5 and b<4/5 gives |w-c|^2>36/5. These are continuous
inequalities on the entire stated domains, not a sampled cover.

## 4. Genuine unloaded paths and unchanged applications

The path in the caller is the real positive path

    U-T_1-...-T_m-C, m>=1,

where each T_i is unloaded with exactly its two displayed positive
neighbors. Full two-force balance fixes the same normal and magnitude
on its incoming and outgoing forces. Full torque fixes the difference
of the actual application points as ell_i*n. The actual square gives
ell_i=1 in the side case or ell_i=sqrt(2) in the diagonal case.

For side transmission, the full original incoming and outgoing means
have the same tangent coordinate. Endpoints are retained. Successive
identities along the actual path therefore give

    A=S+(sum_i ell_i)*n,

with Lambda>=1. The incoming physical edge makes A the actual
minimum-n support point of C. No contracted U--C edge, fabricated
force, shortened larger-degree star, or new support point is used.

No load or degree condition at C is needed by the new center theorem.
The strict Southwest direction and S being U's actual corner are
proved from U's full three-force equation in the local feature entry.

## 5. Bridge-clearance theorem and physical boundary status

The source reproduces the entire force-free bridge consequence needed
in the original radius window. I checked each constant and the closed
separation threshold.

For any actual contained unit with center z,

    |z|<=sqrt(R^2-1/4)-1/2<91/60

throughout R<=sqrt(1105)/16. This follows from the farthest actual
corner bound |z|^2+|z|+1/2<=R^2; the strict numerical margin is
(121/60)^2-1041/256=31/57600.

If actual B touches W and C, then |b-w| and |b-c| are at most
sqrt(2). With M=(w+c)/2 and |w-c|^2>=7, the two exact
parallelogram identities give

    |b-M|<=1/2,
    |M|^2<(91/60)^2-7/4=1981/3600<9/16.

Thus |b|<5/4, and every point of B has norm less than

    5/4+1/sqrt(2)<5/4+29/40=79/40<=R.

The whole actual B is strictly circle-clear. If the proposed center
separation is larger than 2sqrt(2), the first identity already rules
out any such B; no inadmissible square root is taken. At separation
exactly sqrt(7), strictness is supplied by the original center bound.

This contradicts physical circle contact even when B's total circle
weight vanishes. No degree, private equilibrium or selected mask at
B is assumed. W and C likewise keep their complete original stars.

## 6. Whole distinct-W feature: complete local entry

The original premises are unloaded true U3 with neighbors V,W,T_1;
loaded true V2 with neighbors U,W; physical-boundary W of arbitrary
degree; and the genuine outgoing path. The original UV normal is a U
axis, UW is a non-U W axis, and VW is a different W axis that is not
a V axis. B is an actual physical-boundary unit touching W and C.

I checked the complete source 71a5b91d and its full review e27238b3
at the broad scope used here: its fourth body T need only be an
actual contained unit. It does not need to be loaded or physically
boundary. Consequently it applies to T_1 with its original true
two-neighbor path retained.

The local complete cover treats the parallel/shared UV possibility,
all alternative W axes, all V physical masks, and zero individual
circle coefficients before deriving the remaining chart. It gives

    0<theta_V<theta_W<pi/4,
    V=[-1/2,1/2] times [d,d+1] in V's actual frame,
    d=sqrt(R^2-1/4)-1,

and the real lower V corner M=(1/2,d) on the real W side. U's
full three-force and torque equation gives the unchanged outgoing
normal n=-(alpha,beta) with 0<alpha<beta, at S=Q-(1,1).

The source's later occupied-pocket and near-origin-allocation claims
are not used. No conclusion that depended on a loaded T has been
silently transferred to an unloaded T_1.

The complete force-free radial-corner input handles every possible
physical W mask before yielding the unique actual circle corner and
the actual chart

    W=M+[-zeta,1-zeta]*(g,h)+[0,1]*(h,-g),
    g,h>0, g^2+h^2=1,
    0<zeta<1, tau=1-zeta in (0,1),
    d=(tau^2+tau*g+h)/(2*(1+g-tau*h)).

The strict side positions come from the actual relative-interior
contacts. W keeps its arbitrary full degree and may have zero total
circle weight. The physical circle corner and equation are unchanged.

## 7. Entire high/critical slope and low/critical join

For R>=sqrt(17)/2 one has d>=1. I checked positivity of
1+g-tau*h on the whole closed tau interval and the strictly positive
derivative numerator

    (2*tau+g)*(1+g-tau*h)
       +h*(tau^2+tau*g+h).

Since the actual tau<1,

    1<=d=F(g,tau)<F(g,1)

implies 3h>1+g. If h<=3/5, then g>=4/5 and this is impossible;
thus h>3/5. The actual angle order gives

    a=sin(theta_W)>sin(theta_W-theta_V)=h>3/5,
    b=cos(theta_W)<4/5.

Reexpressing the same W at its actual U contact Q gives precisely
the standalone chart, with the same actual square and a renamed
tangent coordinate kappa. The genuine path supplies A. Hence

    |c_W-c_C|^2>36/5>7,

and the actual B is strictly circle-clear. This includes the exact
critical radius because tau<1 still gives a strict slope gap there.

For R<=sqrt(17)/2, the complete a967bb48 theorem and its separate
full review f0493ed4 apply to the true U3/V2 stars, both physical
boundary bodies V,W, original VW edge, and actual unloaded path.
C is allowed arbitrary full degree and load there. Its full
low/critical exclusion joins the present high/critical proof with
an overlap, leaving no radius endpoint unproved.

## 8. Literal original caller and exact progress boundary

In D02.L0145 the retained original edges are

    01,12,23,34,45,50,02,

with loads {0,1,4,5} and literal assignment

    U=2, V=1, W=0, T_1=3, C=4, B=5.

These give exactly U3, V2 and unloaded T_1 degree two. W remains
degree three. C and B remain their actual loaded degree-two units;
neither is assigned an unloaded transmission equation. In particular,
B's two contacts and physical circle contact are real original edges
and a real original mask. The three additional actual squares remain
present but are not needed for this contradiction.

The theorem closes the whole distinct-W-side branch of the sole-UV,
nonparallel-V, W-owned-only return interface, including all original
frames, physical masks, means and chain orientations. Its general
form also covers arbitrary full W,B,C degrees and any genuine
unloaded internal path length satisfying the literal premises.

The common-W-side case is separate. The no-U-axis, perpendicular-U-axis,
and sole-UT shared-contact interfaces are also separate. No theorem
here proves all of D02.L0145, its graph parent, another load row,
or a coarse cell. Fine and coarse counts remain unchanged by this
review. The global sharp n=9 theorem, equality and prerequisite
audit retain their existing OPEN status.

## 9. Complete direct inputs read and checked

| Complete source or review | SHA256 | Actual use checked |
| --- | --- | --- |
| MIXED_HUB_AXIS_DISTINCT_W_SIDE_NEAR_ORIGIN_INJECTION.md | 71a5b91d3a0bc95dd76ae9b663b801aeabc33cc34ffb261402c4f7af224a0242 | Entire source read; complete arbitrary-contained-T local owner/mask and W chart used |
| REVIEW_MIXED_HUB_DISTINCT_W_NEAR_ORIGIN_ROOT_2026_10_28.md | e27238b3fed5b53d5f590442a12bfbdcf48843bf43035802e5309f17fb7551b3 | Entire broad-scope local review and preserved component review boundaries |
| RADIAL_INNER_CORNER_BOUNDARY_NEIGHBOR_QUARTER_SIDE_BOUND.md | 37f0f207a86a9d2c4ead42edcfaac01c5dbdd4f08bc66e98e41f985adedc4011 | Entire actual physical-mask cover and exact circle equation; new derivative checked independently above |
| BOUNDARY_TRIANGLE_UNLOADED_TERMINAL_CHAIN_COMPLETE_RADIUS_REDUCTION.md | a967bb48602466727c2b28208f8884d50be96f03a553abaaa42d960661e9ee33 | Complete source read; whole low/critical original-star exclusion used |
| REVIEW_BOUNDARY_TRIANGLE_UNLOADED_TERMINAL_COMPLETE_RADIUS_REDUCTION_REVIEW_RESUME_2026_10_29.md | f0493ed4912561f48f61a806d7ad20cb832a094a2ff1b43f0258a566bac04623 | Complete independent review of the corrected full radius reduction |
| PARALLEL_BOUNDARY_TRIANGLE_TERMINAL_BRIDGE_CLEARANCE_AND_D02_L0145_FEATURE_EXCLUSION_2026_10_29_CONTINUATION.md | afb1c5aeb44ae8667a96ad6feac9b2fc67966a103d14a04359f30b57fa01aaba | Complete input read; bridge-center theorem independently rechecked without importing a parallel chart |
| REVIEW_PARALLEL_BOUNDARY_TRIANGLE_BRIDGE_CLEARANCE_L0145_PENTAGON_GLOBAL_2026_10_29_CONTINUATION.md | f3a743763aa8ea36099607a47b23a9c4d2aaad34c337e517689cabf7739965e5 | Full independent input review |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original forces, torque, actual support applications and genuine path equations |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original graph, load set, true degrees and full nine-square context |

This was a complete hand-proof and scope review, with exact-file identity
checks. No pose sampling, optimizer, packing certificate, changed normal,
chosen mean, suppressed physical corner, discarded original force,
Lean/Lake invocation, build, CI/workflow or merge was used.
