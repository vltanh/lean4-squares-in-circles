# Recovered complete actual chart for adjacent shared triangle returns

Date: October 28, 2026 UTC. Reconstruction author: root.

**Status: complete reconstructed local chart, submitted for fresh independent review.** The original manuscript ADJACENT_SHARED_TRIANGLE_BOUNDARY_PATH_ACTUAL_CHART.md at historical SHA-256 64b092c58d7a3b2636cdce9b5965b59e376338c0f63038ea8b2f35b24b9ab2d2 is unavailable after executor recovery. This is a new proof with new bytes. The preserved review ea75746515238ff4c5edec1421ef76135ea90fec10eaf5f2f44a06204794f3e8 records the old theorem's intended scope only; it is not a review of this reconstruction.

## 1. Exact local hypotheses and conclusion

Let U,V,W,T be distinct actual closed unit squares in the same disk D_R, with pairwise disjoint open interiors. Work in

    2<R<=sqrt(Q), Q=1105/256.

The actual positive pair neighborhood of the unloaded U is exactly V,W,T. The actual positively circle-loaded V has exactly its two positive pair neighbors U,W. W and T physically touch the same containing circle. Their degrees, other forces and circle coefficients are arbitrary. The actual pair edge VW is positive.

Assume the actual physical intersections UV and UW have positive length and lie on adjacent sides of U. Every original force magnitude, selected unit normal, contact application or shared-side mean, physical circle corner and individual zero circle coefficient remains. No other square or force is removed.

**Chart theorem.** After one common rotation and, if needed, reflection about the unchanged circle origin, the actual entire squares have exactly the form

    U=[-a,1-a] times [b-2,b-1],
    V=[-a,1-a] times [b-1,b],
    W=[1-a,2-a] times [b-1-delta,b-delta],             (1)

where

    9/16<a<1, sqrt(3)<b<197/100, 0<delta<1,
    a^2+b^2=R^2,
    delta(2b-delta)=4(1-a).                           (2)

Both V and W have unique physical circle corners, respectively

    Z_V=(-a,b), Z_W=(2-a,b-delta).                    (3)

The original U-to-V, U-to-W and V-to-W normals are North, East and East. The original U-to-T normal is strictly Southwest, and its actual original application is forced to be

    P_T=(-a,b-2).                                    (4)

If mu,omega,nu>0 are the original pair magnitudes on UV,UW,VW, write the unchanged original shared-side means as

    M_UV=(s,b-1), -a<=s<=1-a,
    M_VW=(1-a,h), b-1<=h<=b-delta,
    M_UW=(1-a,z), b-1-delta<=z<=b-1.

Their complete equations imply

    nu/mu=a/b,
    s=-a*h/b,
    omega/mu=a*(b-h)/(b*(z-b+2))>0.                  (5)

All original side-mean endpoints are retained. This is an actual-coordinate reduction, not a pocket-capacity conclusion.

The proof uses the original strict point-contact convention only to cover the initially possible isolated VW endpoint. In that convention an isolated parallel-frame vertex/vertex contact has its selected normal strictly inside both vertex cones. Positive-length shared contacts retain their unique side normals and arbitrary original means.

## 2. Exhaustive placement of the three parallel squares

Two positive-length contacts on adjacent U sides force both V and W to be parallel to U. Rotate and reflect the whole physical configuration so V is above U and W is to its right. Initially write

    U=[x,x+1] times [y,y+1],
    V=[x+j,x+j+1] times [y+1,y+2],
    W=[x+1,x+2] times [y+k,y+k+1],
    -1<j<1, -1<k<1.                                (6)

The strict slider bounds are exactly the positive lengths of the U contacts. The physical VW contact requires j>=0 and k>=0. If both were positive, the two open squares would overlap in a rectangle of positive area. Hence

    j>=0, k>=0, j*k=0.                               (7)

No slider, contact endpoint or mean has been selected in (7).

Suppose k=0 and j>0. Then both V pair contacts have positive length on its lower side and both original V-outward normals are South. Its full positive circle resultant is therefore strictly North.

For a contained axis-parallel unit with nonzero center abscissa, every farthest corner has the same strictly signed abscissa; a positive weighted sum of those corners cannot have zero abscissa. Thus V's actual center abscissa is zero. Its positive North circle resultant and R>2 place its actual upper side on the circle, so the entire V is

    V=[-1/2,1/2] times [d,d+1],
    d=sqrt(R^2-1/4)-1>1/2.

The physical circle mask has both upper corners, and its full force has equal positive weights. This is a conclusion from the actual full force, not an assumed radial unit or an omitted zero-weight endpoint.

The unchanged W is

    W=[1/2-j,3/2-j] times [d-1,d].

Every one of its vertices has squared norm at most 9/4+d^2, whereas

    R^2-(9/4+d^2)=2d-1>0.

This contradicts W's actual physical boundary contact. Consequently j=0.

Set x=-a, y=b-2 and delta=1-k. Since 0<=k<1, the actual squares now have (1) with

    0<delta<=1.                                     (8)

If delta<1, the physical VW contact is a positive-length vertical segment, and its original V-outward normal is East. If delta=1, VW is the single actual point (1-a,b-1); its original normal in the strict convention is Southeast with both components nonzero. The isolated endpoint is still present at this stage.

## 3. Full V force fixes a physical circle corner before choosing any mask

The original V-to-U normal is South. In the delta<1 case the other original normal is East; in the delta=1 case it is strictly Southeast. With both pair magnitudes positive, the complete circle resultant is therefore strictly Northwest in both cases.

For an axis-parallel unit, all physical circle corners maximize the absolute values of the two coordinates independently. A strictly negative horizontal resultant rules out a positive center abscissa, and a strictly positive vertical resultant rules out a negative center ordinate. Thus

    a>=1/2, b>=1/2,
    Z_V=(-a,b) is an actual physical circle corner,
    R^2=a^2+b^2.                                   (9)

The equality alternatives a=1/2 or b=1/2, and every possible individual zero corner weight, have not been discarded. Containment of the actual U corner (-a,b-2) gives

    a^2+(b-2)^2<=a^2+b^2,
    b>=1.                                         (10)

This step does not assume that O lies in U.

## 4. All four physical W maximum-corner regimes

Since W physically touches the circle, its actual maximum corner norm equals R. Its farthest horizontal endpoint is 1-a when a>=3/2 and 2-a when a<=3/2. Its upper endpoint b-delta is farthest vertically when b>=delta+1/2, and its lower endpoint b-1-delta is farthest when b<=delta+1/2. We now exclude three regimes including all ties.

If a>=3/2 and the upper endpoint is farthest, equality with (9) gives

    1-2a=delta*(2b-delta)>0,

impossible by (8),(10).

If a>=3/2 and the lower endpoint is farthest, equality gives

    2a=1+(1+delta)^2-2b*(1+delta)
       <=delta^2<=1,

again impossible.

If a<3/2 and the lower endpoint is farthest, equality gives

    4a=4+(1+delta)^2-2b*(1+delta)
       <=3+delta^2<=4.

Here a<=1 and b<=delta+1/2<=3/2. Hence (9) implies

    R^2<=1+9/4=13/4<4,

contrary to R>2. The vertical tie is included in this exclusion. The horizontal tie was already included in the first two cases.

Only a<3/2 with the upper endpoint strictly farthest remains. Its exact equation is

    delta*(2b-delta)=4(1-a)>0.                       (11)

Thus a<1, and (9) gives b>sqrt(3). If delta=1, (11) and a>=1/2 would give 2b-1<=2, hence b<=3/2, impossible. Therefore

    1/2<=a<1, b>sqrt(3), 0<delta<1.                 (12)

In particular the entire isolated VW point endpoint has been excluded by actual containment. W's center has both coordinates strictly positive, since a<3/2 and its upper vertical endpoint is strictly farthest. Its physical circle mask is uniquely Z_W in (3). This conclusion covers every initial W mask without using any W force equation.

## 5. The full unloaded U equation fixes the original third application

Let mu and omega be the original positive magnitudes on UV and UW. The complete unloaded U force equation is

    mu*North+omega*East+mu_T*n_UT=0.

Thus the unchanged third vector is

    mu_T*n_UT=(-omega,-mu),

with both components strictly negative. This strictly exposes U's actual southwest vertex. Its original UT application is consequently P_T in (4); it is not a chosen endpoint replacing a variable mean.

The actual boundary unit T contains this same P_T and at least one physical circle corner. Its actual unit diameter is sqrt(2). The triangle inequality gives

    |P_T|>=R-sqrt(2)>0.

Using |P_T|^2=R^2+4-4b and squaring only positive sides yields

    b<=1/2+R/sqrt(2).                               (13)

In the upper window,

    (147/100)^2-Q/2=863/320000>0,

so b<197/100. Also

    a^2=R^2-b^2
        >=R^2/2-R/sqrt(2)-1/4
        >7/4-sqrt(2).                               (14)

The last strict inequality follows because R>2 and the difference from the value at R=2 is

    (R-2)*((R+2)/2-1/sqrt(2))>0.

Finally

    (367/256)^2-2=3617/65536>0,

so sqrt(2)<367/256=7/4-81/256. Equation (14) proves a>9/16.

Now a>1/2 and b>sqrt(3)>1/2 make V's actual center abscissa strictly negative and ordinate strictly positive. Thus its physical circle mask is uniquely Z_V. Both uniqueness conclusions have been proved from the full geometry, after retaining all initial masks and individual zero coefficients.

Only T's physical boundary status and unit diameter were used in (13)--(14); T has not been treated as a two-force unit in this local theorem.

## 6. Complete original mean and torque equations

Because j=0, UV is the whole common horizontal side. Because 0<delta<1, both remaining contacts have the positive shared lengths described in Section 1. Their original means therefore have exactly the full intervals printed there.

Write the positive V circle force as lambda*(-a,b), with lambda>0, absorbing only the common radial normalization into lambda. The complete V force equation gives

    nu=lambda*a, mu=lambda*b.

The circle force has zero origin torque. The complete V torque is

    -mu*s-nu*h=0,

which gives the first two equations of (5).

Take the complete unloaded U torque about its actual P_T. The UT force has zero moment there. The other two moments give

    mu*(s+a)-omega*(z-b+2)=0.

The entire original UW interval gives

    1-delta<=z-b+2<=1,

and the lower endpoint is strictly positive. The entire original VW interval gives h<=b-delta<b. Therefore

    omega/mu=(s+a)/(z-b+2)
             =a*(b-h)/(b*(z-b+2))>0.

This establishes (5) for every original mean, including every endpoint-valued mean. No midpoint, equal-magnitude assumption or new normal selection was made. In particular these local formulas do not assert an origin-moment sign for UT; a boundary-path caller must obtain that sign from its actual endpoint equations and order.

## 7. Literal original D02 join and complete scope boundary

For the original fine family M6.B6.HEXAGON.D02.L01345, retain the same nine physical squares and the original positive graph

    rim 01,12,23,34,45,50; positive chord02;
    positive circle-load set {0,1,3,4,5}.

Set

    U=2, V=1, W=0, T=3,
    boundary path V,W,5,4,T=1,0,5,4,3.

The true degrees are U3,V2,W3,5_2,4_2,T2, with U unloaded and all five path units positively loaded. Every original circle coefficient, chord force and all three arbitrary completion squares remain.

The same-nine analytic lower-radius theorem excludes the entire original R<=2 domain before this chart is applied. It is not a lower-radius claim for an isolated four- or six-body component.

If the original actual positive-length contacts UV and UW lie on adjacent U sides, every hypothesis of the local chart theorem holds. Equations (1)--(3) in particular meet the complete physical chart of ADJACENT_SHARED_TRIANGLE_BOUNDARY_PATH_POCKET_CAPACITY_ONE.md. The new source and its new independent review must be explicitly joined to that pocket theorem; the old unavailable 64b092 manuscript and its historical review are not silently substituted.

All graph-preserving relabelings act on the entire physical data together. The chart does not cover a singleton UV or UW contact merely because its original normal is a U side axis. It gives no whole original graph/load checkbox alone. The eventual pocket and all-three-extra allocation join must retain the complete original graph and true degrees.

## 8. Exact operative caller sources

| Source | SHA-256 | Exact use |
| --- | --- | --- |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Original graph, load set, degree and same-nine contract for Section 7 |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Complete original R<=2 exit with its existing analytic dependency chain |

The local proof is printed above in full. The proposed pocket target is ADJACENT_SHARED_TRIANGLE_BOUNDARY_PATH_POCKET_CAPACITY_ONE.md, SHA-256 c3f95f4c965513179f7e001113ffd2e3da67c267f0334ea3af394d422e7fad01; it is not a mathematical premise of the chart.

All scalar comparisons are exact hand inequalities. No pose search, angle grid, computational pose certificate, Lean compilation, CI, workflow, ledger change, commit or remote action is part of this chart proof.
