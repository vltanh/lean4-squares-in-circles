# Independent review of the shared-boundary-side, externally owned triangle-tip exclusion

Date: October 28, 2026 UTC. Reviewer: cycles.

**Verdict: PASS for the entire local theorem at R^2>=241/64, with no upper radius bound, and PASS for the whole original sole-UW-axis interface join. No repair is requested.** The original shared UW mean, its two endpoints, all three U forces, both V pair forces, every physical V circle mask and every individual weight endpoint are retained. The proof uses no boundary, owner, degree or force equation at T, and no reduced equation at W.

## 1. Exact source, complete inputs, and independence

The complete source read and independently checked is

    UNLOADED_HUB_SHARED_BOUNDARY_SIDE_TIP_OWNED_TRIANGLE_EXCLUSION.md
    4f7716231512e1c8c95318eaa80883037dce56c3759e0f0343584d151c49e8fd.

All five direct sources were read in full and their current exact hashes checked:

| Complete direct source | SHA-256 |
| --- | --- |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| D02_ALL_MASK_FREE_UV_EXCLUSION_AND_EXACT_SINGLE_HUB_AXIS_COVER.md | 214475cb4a6fe839b6589a346e12f2aea9be97b958a5229e1c1ff4344740e670 |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 |

The local proof uses only the first two inputs and its printed actual-square geometry and original equations. The structural cover, graph/load source and lower-radius source enter only the literal original-family application. In particular the local theorem does not depend on its own eventual sole-UW consequence or on a completion-capacity result.

I did not author or contribute the new placement argument, its all-mask V2 contradiction, its actual radial parameter bound, or its four-corner proof. My earlier full independent structural-cover review is

    REVIEW_D02_ALL_MASK_FREE_UV_SINGLE_HUB_AXIS_COVER_CYCLES_2026_10_28.md
    e239044ca0d128d0aa9b0fe015538bf02772dd78d3d190ebf3272c3dfb79e3c3.

That record retains the independent chains for older inputs I authored. It supplies the already checked current structural premise, not an author review of this new pentagon proof.

## 2. Exact local scope and original U3 inequality

The local theorem assumes four distinct actual interior-disjoint unit squares U,V,W,T in the same disk about O. U has its entire positive neighborhood V,W,T and zero circle load. V has its entire positive neighborhood U,W and positive total circle load. W is physically boundary but otherwise has arbitrary true degree, load and additional forces. T is unrestricted beyond its actual retained data and the UT contact. The actual UW intersection has positive length. The original UV normal is a V side axis, not a U axis, with its application in that V side's relative interior.

These are physical premises of the local theorem; no strict-normal selector is used in its proof. The original selected-certificate caller separately establishes the relative-interior premise.

After a rotation about the unchanged origin, the UW normal is North and U=[L-1,L]x[H-1,H]. The actual triangle side-normal theorem gives the original n_UV nonnegative North projection. Since it is not a U axis, that component is strictly positive and its horizontal component is nonzero. A horizontal reflection gives

    n_UV=v=(b,a), a,b>0,
    P=(L,H).

The entire original shared UW mean is S=(L-1+p,H), initially 0<=p<=1. Full U3 force makes the third normal strictly Southwest, so its actual application is Q=(L-1,H-1). The complete torque about Q is

    mu*(a-b)+omega*p=0.

Thus b>=a>0 and a<=1/sqrt(2). The equality a=b is retained exactly at the possible original mean p=0. The proof neither excludes that endpoint by a genericity claim nor replaces the mean by it.

No equation at W or T is used to obtain this inequality. Every original U force remains positive and present.

## 3. Exact actual V/W placement and complete side-interior geometry

The actual V frame is

    u=(a,-b), v=(b,a), det(u,v)=1,
    V=E+[0,1]u+[0,1]v,
    P=E+r*u, 0<r<1,
    E=(L-r*a,H+r*b).

Both inward axes have positive horizontal component, so E is the unique leftmost V vertex. Because r,b are in (0,1), its height is strictly between H and H+1.

Positive shared UW makes W parallel to U with the full slider

    W=[L-1+ell,L+ell]x[H,H+1], -1<ell<1.

The proof of ell<0 covers ell=0 explicitly. If ell>=0, P lies on W's bottom side. Choose 0<epsilon<a/b. The direction (-epsilon,1) has positive scalar product a-b*epsilon with V's inward side normal v, and P is a relative-interior side point of V. A sufficiently small displacement therefore lies in int V. It also lies in int W: it rises from the bottom and moves left, including when P is W's lower-right vertex at ell=0. The strict left-side bound follows from ell<1. This contradicts disjoint interiors.

With ell<0, W's left side lies strictly left of L-1, whereas E_x lies strictly between L-1 and L and E_y lies strictly inside W's vertical interval.

* If W's right side is left of E, its entire x projection is strictly left of V's unique minimum x, so VW cannot touch.
* If that side is right of E, E belongs to int W. An actual vertex of V in int W implies interior overlap near E.
* Therefore W's right side is exactly E_x.

Consequently ell=-r*a and the whole actual W is

    W=E+[-1,0]East+[-r*b,1-r*b]North.

VW is the singleton E in the relative interior of W's right side. Its unchanged original normal must therefore be West. This is forced by the real support geometry; it is not a chosen replacement normal.

The exact UW shared interval becomes

    [L-1,L-r*a]x{H},

so the original mean has the full constraint 0<=p<=1-r*a. The right endpoint and the left endpoint p=0 are both retained. Since r*a<1, the actual shared length remains positive. This completes the physical W-frame and VW-feature cover within the stated local hypotheses.

## 4. Full V2 equations and exhaustive physical-circle masks

All subsequent own coordinates are coordinates of the actual vector E-O in the orthonormal frame (u,v), so they do not translate the containing circle. Put A=E.u, B=E.v.

Writing the full outward circle resultant as F, the unchanged pair normals give

    F=mu*v+nu*East,
    East=a*u+b*v.

Hence

    F_u=nu*a>0,
    F_v=mu+nu*b>0,
    F_v-F_u=mu+nu*(b-a)>0.

The full original V torque is

    det(E,F)+mu*r=0,
    mu*r=B*F_u-A*F_v.

I independently checked the sign and the r term: the incoming application is E+r*u, det(u,v)=1, and the other application is E. Every radial circle atom has zero moment about O. The shared UW mean enters only through the already valid full U3 inequality b>=a.

Since the coordinate maxima of squared norm are independent, positive F_u and F_v imply A,B>=-1/2. If one were below -1/2, every physical farthest corner would have a negative corresponding coordinate and the full positive-load resultant would share that negative sign. This is a statement about every physical corner, not just a preferred atom.

A tie in both own coordinates would give R^2=1/2, impossible. The complete remaining masks are therefore:

1. Unique corner E+u+v, with A,B>-1/2.
2. Two physical corners on the outer u face, A=d, B=-1/2.
3. Two physical corners on the outer v face, A=-1/2, B=d.

Here

    d=sqrt(R^2-1/4)-1>=7/8,

because R^2-1/4>=225/64 at the closed threshold R^2=241/64. There is no omitted three-corner or opposite-two-corner mask, and zero individual coefficients do not alter this physical classification.

## 5. Complete unique and outer-u-mask contradictions

For the unique physical corner, write F=Lambda*(x,y), with x=A+1>1/2, y=B+1>1/2 and Lambda>0. Let k=b/a>=1. Full force and full torque give exactly

    mu=Lambda*(y-k*x),
    mu*r=Lambda*(y-x).

Subtracting yields

    mu*(1-r)=Lambda*x*(1-k)<=0.

The left side is strictly positive since mu>0 and the actual relative-interior parameter r<1. This contradicts the entire unique physical mask, including k=1 and the original UW mean endpoint that produces it.

For the outer-u two-corner mask, the entire original weight interval gives

    F=Lambda*(d+1,zeta), -1/2<=zeta<=1/2.

Therefore F_v<=Lambda/2<Lambda*(d+1)=F_u, contrary to the full force consequence F_v>F_u. The strict d lower bound is more than sufficient. Both individual zero-coefficient endpoints and every mixture are included.

These arguments impose no upper radius bound. They use only the genuine V2 and the original U3 inequality, not a leaf replacement or an equation of W.

## 6. Complete remaining mask and the actual r interval

For A=-1/2,B=d, the whole physical mask has resultant

    F=Lambda*(zeta,d+1), -1/2<=zeta<=1/2.

F_u>0 forces zeta>0; this is derived from the actual full equation. It does not select a circle coefficient. The surviving endpoint zeta=1/2 is retained, while the other initial weight values were excluded by the actual force sign.

The exact identities are

    mu=Lambda*(d+1-k*zeta)>0,
    mu*r=Lambda*(d*zeta+(d+1)/2).

Subtracting half the first gives

    mu*(r-1/2)=Lambda*zeta*(d+k/2)>0.

Thus the unchanged actual side parameter satisfies 1/2<r<1. In particular, for t=r*b and z=1-t,

    b/2<t<b, 0<z<1-b/2<1.

Every inequality is strict for a proved reason. No original application is moved, and no constraint from T or a W equilibrium is used.

## 7. Independent expansion of all four actual W deficits

In the actual V frame,

    E=(-1/2,d),
    East=(a,b), North=(-b,a),
    R^2=d^2+2d+5/4.

The exact W from Section 3 has the four vertices

    C0=E-t*North,
    C1=E-East-t*North,
    C2=E+z*North,
    C3=E-East+z*North.

I independently expanded all four, using

    E.North=b/2+a*d,
    E.East=-a/2+b*d,
    East.North=0.

The deficits are exactly

    D0=2d*(1+a*t)+1+b*t-t^2,
    D1=2d*(1+b+a*t)-a+b*t-t^2,
    D2=2d*(1-a*z)+1-b*z-z^2,
    D3=2d*(1+b-a+a*t)
          -[1+a+b-(2+b)*t+t^2].

The last form follows by substituting z=1-t into
2d*(1+b-a*z)-a-b*z-z^2. Thus no sign in the potentially delicate far corner has been hidden by the substitution.

All four are strictly positive on the entire stated domain:

* D0 is positive because t*(b-t)>0 and every other displayed term is positive.
* D1 is greater than 1+b-a>=1, since 2d>1, a*t>0 and t*(b-t)>0.
* D2 has 1-a*z>0. Its remaining quadratic decreases strictly in positive z, and z<1-b/2 gives
  1-b*z-z^2>b^2/4>0.
* Put N(t)=1+a+b-(2+b)*t+t^2. On 0<t<b, N'(t)<b-2<0. Since t>b/2,
  N(t)<N(b/2)=1+a-b^2/4<1+a<7/4.
  Meanwhile 1+b-a+a*t>=1 and 2d>=7/4. Therefore D3>0.

The last strict inequality remains valid at d=7/8 because the polynomial bound is strict. The equality a=b remains valid throughout. The physical weight endpoint zeta=1/2 remains valid because it still gives r>1/2 and r<1.

This compares every actual corner of W before making any choice of its physical mask. Convexity then places the whole actual W strictly inside the containing disk, contradicting its given physical boundary contact. No W circle load or W force equation is needed.

## 8. Exact radius scope and original entire-interface join

The local proof has no upper radius input. Its closed lower threshold is exactly a sufficient condition for d>=7/8 in the last deficit argument. The simple exact checks are

    241/64-1/4=225/64=(15/8)^2,
    4-241/64=15/64,
    (79/40)^2-241/64=27/200,
    (3/4)^2-1/2=1/16.

All are as printed. The theorem is not claimed sharp at its lower threshold.

The current structural source 214475cb proves that the entire original sole-UW-axis row has actual positive shared UW, externally V-owned UV at a strict U vertex and a relative-interior V-side point, and free UT. These are precisely the new local premises. The new local proof actually needs no free-UT or T-boundary premise, so it includes both physical T masks and the unique-T/shared-T4 exception without splitting them.

The literal original data remain

    U=2, V=1, W=0, T=3,
    rim 01,12,23,34,45,50,
    chord 02,
    loads {0,1,3,4,5},
    path 1,0,5,4,3.

The actual degrees are U3,V2,W3,5_2,4_2,T2. The local W degree is unrestricted and therefore includes its actual W3 without dropping a force. The local T data are unrestricted and therefore include its actual T2 without changing an application or circle weight. All three completing units remain; none must be positioned or routed to obtain the contradiction.

The same-nine lower-radius input is used only for the original caller and gives R>2, safely inside the local threshold. The source also correctly observes that the original declared lower radius 79/40 already exceeds this threshold. No stronger radius assumption has been placed on the original family.

Thus the complete original sole-UW-axis interface is excluded, over every original UW mean endpoint, every physical V/T mask and coefficient endpoint, every W3 force and every surviving free-UT alternative. This is a whole existing structural interface; it is not a new fine row or the entire D02 graph/load family.

## 9. Logical and accounting limits

The proof does not rely on a boundary-path length, any equation at T, any circle-load sign at W beyond its physical contact, or an upper radius bound. Other graph families may use the local theorem when they establish exactly the stated true U3, true loaded V2, physical-boundary W, positive shared UW and external V-side-interior UV premises.

A higher-degree V cannot be shortened to fit the theorem. A merely endpoint-valued mean is not enough to assert actual shared UW. A V-owned selected normal at an inadmissible point-only vertex endpoint is not silently put in the local relative-interior hypothesis.

The whole sole-UV and sole-UT interfaces remain outside this manuscript. The original D02 row and its coarse parent remain open. No ledger flag or count was changed by this review.

The audit used complete hand geometry, the full original equations and exact expansions. Fraction arithmetic checked only the displayed threshold reserves. No numerical pose, mesh, optimization, new computational exclusion certificate, normal reselection, changed mean, force deletion, fake degree-two W, Lean compilation, CI, workflow, commit or remote write was used.

**Entire local theorem and entire stated original sole-UW interface: PASS, no repair required.**

