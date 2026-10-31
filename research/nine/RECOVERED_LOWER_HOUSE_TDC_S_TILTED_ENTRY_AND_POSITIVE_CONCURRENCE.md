# Complete tilted-root entry and positive concurrence for lower TDC.S

Date: October 28, 2026 UTC. Author: house continuation, with the strict Southwest/Southeast force calculation supplied by root.

**Recovery status: complete newly reconstructed hand reduction, requiring a fresh independent review at the new bytes.** This is not an exact-byte restoration of the historical source at SHA256 2ca671a16c528b376b1db09115f0fc72666937998f98bef7cf48cbab3c13762e. It restores the complete original tilted entry, actual signs, port order and small-port estimate. It also prints the required near-radial loaded-tip exclusion directly, so no lost near-radial manuscript is needed.

## 1. Original full graph and radius/root entry

Keep the original graph

    AT, DT, AD, AB, BC, CD, BL,

with true degrees B3,A3,D3,T2,C2,L1. A,B are unloaded; T,D,C have their unchanged positive total circle loads; L is the genuine S leaf at B. Retain all original positive magnitudes, separating normals, actual singleton applications and full side means, both physical circle masks and individual zero coefficients, every further physical contact, and all three other squares of the same nine-square packing.

The complete boundary-triangle third-support theorem, used literally at A3 with returns T2,D3 and third neighbor B, excludes d<=1 and gives

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60,
    -epsilon<=h_B(n_BA)<=epsilon.                       (1)

For a strictly tilted genuine S root use its actual own chart

    B=[U-1,U]x[V-1,V], U^2+V^2=d^2, U>=V>0.

The complete shallow-root inference gives

    1-epsilon<=U<=d,
    59/60<U<61/60, 0<V<31/120, U>V.                    (2)

Put a=U-1, b=V-1, so |a|<=epsilon and -1<b<-89/120. The real leaf port is P_L=(U,V), with radial direction e=(U,V)/d.

The complete force-free shallow-neighbor theorem applies to the actual boundary unit C. Its full BC normal cover is

    West, South, strict Southwest, strict Southeast.    (3)

Its proof also supplies the following radius-free local fact at P_L: no third unit can contain that point. B occupies its Southwest right-angle sector; the genuine tilted leaf occupies the half-plane in the strict Northeast direction e; each remaining connected angular gap is smaller than a right angle. A unit's connected tangent sector has angle at least a right angle. This fact applies to A as well, without assuming A is boundary.

## 2. Eliminate every BA feature except West and strict Northwest

Write the actual complete B force equation as

    lambda*(U,V)+F_A+F_C=0, lambda>0,                   (4)

where lambda absorbs the original positive leaf magnitude divided by d. F_A,F_C include their unchanged positive magnitudes.

If the BA normal is a B-owned East or North axis, its dot product with e is positive. Dotting the full B equation with that axis makes n_BA.n_BC<0. But the complete opposite-support theorem says that every surviving B-owned BA axis must have n_BA.n_BC>=0: the whole actual A return D is beyond that BA support, whereas C at the opposite face cannot reach across it. Thus both owned axes are excluded with every original mean.

The South axis has support 1-V>89/120>epsilon, contrary to (1). A strict Southeast normal (u,-v), u,v>0, has support

    U*u+(1-V)*v>=min(U,1-V)*(u+v)>epsilon,

also impossible. A strict Northeast normal uses P_L, where the actual leaf and B leave no room for another unit. The only additional feature to exclude is a strict Southwest BA normal at (a,b).

Suppose this last feature occurs, and write F_A=(-x,-y), x,y>0. Cover all four C features from (3).

### 2.1. BC West, with its whole original mean

Write F_C=(-z,0), z>0, and its original point as (a,zeta), b<=zeta<=V. Full force gives

    y=lambda*V, x+z=lambda*U.

Torque about P_L, using the actual two applications, gives

    y-x+z*(zeta-V)=0,
    z*(1+zeta-V)=lambda*(U-V)>0.                       (5)

Since x>0, z<lambda*U. Equation (5) therefore implies

    zeta>V*(U-1)/U>=-epsilon.

Together with zeta<=V and |a|<=epsilon, this puts the actual BC point inside radius

    sqrt((1/60)^2+(31/120)^2)<1/2.

But that same point belongs to the real boundary unit C, whose points have norm at least R-sqrt(2)>1/2. This contradiction includes both mean endpoints.

### 2.2. BC South, with its whole original mean

Write F_C=(0,-z), z>0, at (xi,b), a<=xi<=U. Full force gives

    x=lambda*U, y+z=lambda*V.

The actual torque about P_L gives

    x-y=z*(U-xi)<=z.

Hence lambda*U-y<=lambda*V-y, or U<=V, contradicting (2). The endpoint xi=a is included in the weak inequality.

### 2.3. BC strict Southwest

Both actual return applications are (a,b)=P_L-(1,1). Their full resultant is -lambda*(U,V). Its moment about P_L is lambda*(V-U), which cannot vanish because U>V. No individual force is removed or combined into a new physical neighbor.

### 2.4. BC strict Southeast

Write F_C=(z,-w), z,w>0, at (U,b). Torque about P_L gives

    y-x+z=0, so x=y+z.

The horizontal equation in (4) gives lambda*U=x-z=y. Its vertical equation gives lambda*V=y+w>y=lambda*U. Again V>U is impossible.

These four alternatives exhaust (3). Thus the complete actual BA cover is

    n_BA=West or strict Northwest.                     (6)

## 3. Eliminate BC West and strict Southeast

A West BC normal has zero vertical component. In (6) the BA vertical component is nonnegative, whereas the genuine tilted leaf's vertical component is strictly positive. This contradicts full vertical force balance. Hence BC is not West.

Suppose BC is strict Southeast at Q=(U,b). If BA is West, B owns the BA normal and its dot product with the Southeast BC normal is negative, already excluded by the complete owned-face implication.

If BA is strict Northwest, write n_BA=(-u,v), u,v>0. Its actual point is P_A=(a,V). Then

    n_BA.n_BC<0,
    n_BA.(P_A-Q)=u+v>1.

These are exactly the complete opposite-port hypotheses. The actual C lies on one side of the BA support while the entire actual D lies strictly on the other, contradicting CD.

Consequently the full remaining pair of actual normal features is

    n_BA=West or strict Northwest,
    n_BC=South or strict Southwest.                    (7)

All means in the two owned-axis features remain unchanged.

## 4. Actual B concurrence, including its possible nonpositive parameter

The two return lines in (7) are nonparallel. The full B3 force and torque equations put their intersection on the genuine radial leaf line. Write

    Q_B=sigma*(U,V).                                   (8)

First sigma<=1. In the West BA case its actual application has height sigma*V, which is at most V. In the strict Northwest case its actual point is (a,V); if sigma>=1, the displacement from Q_B to that point has both coordinates nonpositive and first coordinate strictly negative. It cannot be parallel to a strict Northwest normal. Thus sigma<1 in that case.

Suppose sigma<=0. We claim

    a<=0, a/U<=sigma<=0.                               (9)

For a strict Northwest BA normal, the vector (a-sigma*U,V*(1-sigma)) must have opposite coordinate signs, with its second coordinate positive. Therefore sigma>a/U.

For West BA and South BC, the actual South mean has x=sigma*U>=a. This gives sigma>=a/U.

For West BA and strict Southwest BC, the West mean gives sigma*V>=b. The vector from Q_B to the actual C point (a,b) consequently has nonpositive second coordinate. It is parallel to the strict Southwest normal and is nonzero: equality Q_B=(a,b) would force a/U=b/V, or U=V. Hence both its coordinates are strictly negative, giving sigma>a/U. This proves (9), including the possible a=0,sigma=0 endpoint of the two-owned-axis case.

Let P_C be the unchanged actual BC application. In the South case it is (sigma*U,b); in the strict Southwest case it is (a,b). Thus

    a<= (P_C)_x <=0, (P_C)_y=V-1<0.                    (10)

Since U<=1 in (9),

    V^2=d^2-U^2>=d^2-1=2epsilon+epsilon^2>epsilon^2.

In particular |a|<=epsilon<V<1, so the actual port norm p=|P_C| obeys

    11/15<89/120<1-V<=p,
    p^2<=a^2+(1-V)^2<1.                               (11)

Let m be the unchanged unit normal from B into C, and put

    u=P_C.m, v=P_C.Jm.

Both coordinates of P_C are nonpositive, and m is South or strict Southwest, so u>0. Since P_C lies on the original m line through Q_B,

    |v|=|Q_B.Jm|<=|Q_B|
        <=epsilon*d/U
        <61/3540<1/50.                                (12)

Using (11),

    u^2=p^2-v^2>(89/120)^2-(1/50)^2>(7/10)^2;

the last reserve is 21481/360000. Therefore

    |v|/u<1/35<1/20.                                  (13)

The next complete local lemma excludes precisely these actual C data.

## 5. A complete narrow near-radial loaded-tip exclusion

Let K be an actual positively circle-loaded unit square with exactly two positive pair neighbors, at least one of which is physically boundary. Keep every original mean and both physical circle masks. Assume an actual incoming unit normal n and its unchanged minimum-n point P satisfy

    sqrt(17)/2<R<=sqrt(1105)/16,
    p=|P| in (11/15,1),
    u=P.n>0, |P.Jn|/u<1/20.                            (14)

Then these complete physical data are impossible.

The full proper-concurrence Lemma 2.1 of TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md applies. For the unique physical circle-corner mask it gives

    P+rho*n=lambda*Z, rho>=0, 0<lambda<=1,

where Z is the actual circle corner. Its two-physical-corner conclusion keeps arbitrary individual weights.

If K has two physical circle corners, its actual radial S chart has minimum point norm d>1. This already contradicts p<1. Thus only the unique physical corner mask remains.

Suppose K owns n. Its actual n interval is [u,u+1], with u>0. The physical farthest corner Z is on the outer face n.Z=u+1. The concurrence normal equation gives lambda>=u/(u+1), and its tangent equation gives

    |Z.Jn|=|P.Jn|/lambda
           <=|P.Jn|*(u+1)/u.

Consequently

    R<=p+p/u
      <1+sqrt(401)/20
      <41/20<sqrt(17)/2,

a contradiction. The squared reserve for the last strict comparison is 19/400. Every actual tangent mean and its endpoints remain.

If K does not own n, P is its unique minimum-n vertex. Each inward own axis e_i has n.e_i>0. Since |P.Jn|<p/20<1/20,

    P.e_i=u*(n.e_i)+(P.Jn)*(Jn.e_i)>-1/2.

Thus the actual unique farthest corner is the opposite vertex Z=P+w, |w|=sqrt(2). The proper concurrence gives

    w=A*P+B*n,
    A=(1-lambda)/lambda>=0, B=rho/lambda>=0.

Writing p=|P| and using p>=u>0,

    P.w=A*p^2+B*u
        >=u*(A*p+B)
        >=u*|w|
        =sqrt(2)*u.                                   (15)

This includes lambda=1 and rho=0. It is a cone and triangle-inequality calculation, not an assumption about a selected circle mean.

By (14) and sqrt(401)<21,

    u=p/sqrt(1+(P.Jn/u)^2)>44/63.

Using sqrt(2)>7/5 in (15),

    R^2=|P+w|^2
        >=p^2+2+2sqrt(2)*u
        >=(u+sqrt(2))^2
        >(661/315)^2
        =1105/256+2208151/25401600.

This is the final contradiction. The lemma is complete for every owner, original side mean, unique mask and physical two-corner mask, without assuming both pair neighbors are boundary.

Apply it with K=C, incoming normal m=n_BC and port P_C. C's actual second neighbor D is physically boundary, and its full true degree is two. Equations (11)--(13) give every premise. Therefore sigma<=0 is impossible, proving

    0<sigma<=1.                                        (16)

## 6. The whole original concurrence and feature conclusion

The actual point Q_B belongs to B. Its y coordinate lies in (0,V], hence in [b,V]. If BC is South, its x coordinate is its actual mean and belongs to [a,U]. If BC is strict Southwest, the vector (a-sigma*U,b-sigma*V) has negative second coordinate and is parallel to that Southwest normal, so its first coordinate is negative too. Hence sigma*U>a, while sigma<=1 gives sigma*U<=U.

Every retained actual application is therefore exactly:

    BA West:             P_BA=(a,sigma*V);
    BA strict Northwest: P_BA=(a,V);
    BC South:            P_BC=(sigma*U,b);
    BC strict Southwest: P_BC=(a,b).

These are identities of the original selected points or means, not new choices. The entire complete tilted interface has

    Q_B=sigma*(U,V), 0<sigma<=1, Q_B in B.               (17)

Write n_BA=(-u,v), u>0,v>=0, and rotate properly so that the actual A-to-B normal e0=(u,-v) is East and Je0=(v,u) is North. For the unchanged P=P_BA, put k=P.e0 and y=P.Je0. By (1),

    |k|<=epsilon.

By (17),

    y=det(P,n_BA)
      =det(Q_B,n_BA)
      =sigma*(U*v+V*u)>0.                             (18)

The complete actual port bound is

    |P|^2<=a^2+V^2
          =d^2-2U+1
          <=d^2+2d-3
          =R^2-17/4
          <=17/256
          <(31/120)^2.                                (19)

The last exact reserve is 19/57600. Thus the whole tilted entry supplies

    |k|<1/60, y>0, |P|<31/120.

Finally the actual B port rays have counterclockwise order L,A,C. Relative to its center, the leaf port is (1/2,1/2). In the West BA case its unchanged relative height is 1/2-V+sigma*V>0; in the strict Northwest case it is the upper-left vertex. The C port is on the bottom side or at the lower-left vertex. These are distinct actual ports in precisely the stated order. No T2/D3 labels are interchanged.

## 7. Scope, inputs and recovery discipline

This proves the entire tilted entry needed by both the owned and unowned small-port hub theorems. It covers origin-interior, boundary-origin and origin-free roots, every remaining B owner and shared mean, sigma=1, and all physical C circle masks and individual zero weights. It does not by itself claim that the entire lower TDC.S family is excluded; the complete return-interface theorems are still the closing step.

| Source | SHA256 | Exact use |
|---|---|---|
| UNLOADED_BOUNDARY_TRIANGLE_HUB_THIRD_SUPPORT_AND_CRITICAL_EXCLUSION.md | d8661132bd2d97911116373d22968bbde2ff3c4c4a63c962c72d722ec3d5b089 | Whole low/critical exit and high two-sided BA support bound |
| LOWER_HOUSE_TDC_S_CLOSED_ORIGIN_SUPPORT_AND_SHALLOW_REDUCTION.md | 53a1f33837c353088f83b5226c2e37dfef6434037cd149755af4f24758cbfad6 | Complete tilted high-coordinate shallow inference only |
| SHALLOW_TILTED_S_ROOT_BOUNDARY_NEIGHBORS_ONE_SIDE.md | c8e399293ee684fa21a4d5028dc56ab9234007db2b7e1b3a35ad9e214efc45a3 | Complete actual C normal cover and the physical no-third-unit fact at the real tilted leaf port |
| RECOVERED_UNLOADED_TRIANGLE_OPPOSITE_PORT_SUPPORT_EXCLUSION.md | cfe8df3e3b877171802dda38a846a55e156d7677edcfb7b28870275f2a4b189d | Complete original owned-axis implication and strict opposite-port exclusion |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Full proper-concurrence Lemma 2.1 at true C2 with physical boundary neighbor D |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Actual genuine S-root/leaf geometry |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Exact original graph, load line, true degrees and all-nine contract |

The newly supplied Southwest force/torque cover and narrow near-radial lemma are printed in full. No lost source is cited as an available proof. No old review hash is attached to this reconstruction.

There is no pose search, angle mesh, changed normal, removed force, fake leaf or A--C contact, Lean compilation, CI, ledger edit or remote action.

