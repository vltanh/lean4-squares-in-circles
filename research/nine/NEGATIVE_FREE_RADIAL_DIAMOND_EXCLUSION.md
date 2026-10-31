# A free negative endpoint beside a radial diamond middle has positive whole-root pressure

**Status: complete whole-domain hand proof; root and separate independent full exact-source, geometric feature-cover, true H5/K3 and owner-assembly audits passed.**

Work in the common selected physical certificate, throughout

    79/40 <= R <= sqrt(1105)/16,  q=R^2.

The actual positive component is the triangle-attached diamond with edges HA,HK,HB,KA,KB,HX,XY,YH. H has true positive degree five and zero circle load; K has true degree three; A,B,X,Y have their true positive degrees two and positive total circle loads. The HXY petal remains intact, as do all three arbitrary physical completion squares and every additional zero-stress physical contact.

Assume K has two physical circle corners, A has one, and its actual corner z_A satisfies c_H dot z_A<0.

**Theorem.** HA cannot be a genuinely free point-only vertex/vertex contact. Every original HA normal, AK shared mean, K and B circle weight, and HB interface type is included. No force equation or two-force weight interval is imposed on K.

The proof works on the entire radius window, not just below R^2=17/4. Together with the already audited A-owned/shared and H-owned HA exits, it yields a complete radial-K diamond exclusion in Section 7.

## 1. The exact free/shared endpoint and radial frame

NEGATIVE_UNIQUE_NEIGHBOR_INNER_CONTACT.md puts every H/A point on the two inner A faces, excluding their far endpoints. Since HA is free, its actual point Q is the A vertex opposite z_A. Choose A's inward axes from Q so that

    A=Q+[0,1]e_x+[0,1]e_y,  z_A=Q+e_x+e_y,
    Q=(X,Y),  X,Y>−1/2,
    n_HA=(u,v),  u,v>0.

The original normal points from H into A. If AK were a singleton, the complete BOUNDARY_TIP_FIXED_APPLICATION_SELECTION.md would exclude free HA at true unique degree-two A with its physical boundary neighbor K. Its coincident-application cases are included in that theorem. This does not require degree two at K. Hence AK is genuinely shared.

The radius-free UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md applies to the actual physical triangle H,A,K. Its A-owned AK axis has nonnegative scalar product with the strict outward A-to-H normal −n_HA. Therefore the shared AK side is incident to Q. Exchange A's axes if needed so AK is its lower horizontal side and the actual A-to-K normal is −e_y.

The shared side makes K parallel to A. A physical radial unit has its radial direction along one of these two axes. Its outer radial face cannot admit a unit neighbor by width. Its inner radial face cannot admit a circle-touching neighbor, by the geometric radial-inner-face obstruction. For clarity, the latter follows from the complete right-support bound used in NEGATIVE_UNIQUE_TRIANGLE_TIP_OWNED_EXCLUSION.md, Section 3: at a right support point (d,y), |y|<=1/2, an arbitrary unit on its left has every corner's squared norm at most

    max(d^2,(d−1)^2)+(|y|+1)^2 <= d^2+9/4 < q,

because d=sqrt(q−1/4)−1>1/2 and q=d^2+2d+5/4. The bound includes all side means, vertices and aligned limits, including y=0 after reflection. Thus K's radial direction is horizontal.

The leftward radial orientation would put all K points in x<=−d<−1/2, while every A point has x>=X>−1/2, so they could not share a side. The actual radial direction is consequently rightward. Set

    d=sqrt(q−1/4)−1,  N=sqrt(q−9/4),  Delta=d+1−N.

The unchanged geometry is exactly

    K=[d,d+1]×[−1/2,1/2],
    A=[N−1,N]×[1/2,3/2],
    Q=(N−1,1/2),  z_A=(N,3/2).                         (1)

The whole radius window gives

    d>91/100,  321/250<N<=23/16<3/2.

The lower N squared reserve is1969/1000000. Moreover

    N^2−d^2=2d−1>0,  N<d+1,
    0<Delta<1,  N−1<d<N<d+1.

Thus the genuine AK overlap is exactly [d,N]×{1/2}. Keep its original mean as

    T_A=(N−1+tau,1/2),  Delta<=tau<=1.                 (2)

Let lambda,mu,gamma>0 be the actual A circle, HA and AK magnitudes, absorbing the common circle factor two. The true A force and torque give

    lambda(N,3/2)=mu(u,v)+gamma e_y,
    lambda(3/2−N)=gamma tau.

Therefore the ORIGINAL normal satisfies

    0<v/u=[3/2−(3/2−N)/tau]/N<=1.                     (3)

Every shared-mean endpoint, including tau=1 and u=v, remains. No K equation has been used.

## 2. Actual HK contact fixes the whole H frame

H has Q as a strict support vertex for n_HA. Every K point lies strictly to the right of Q, since its minimum x coordinate is d=Q_x+Delta. Physical HK therefore requires one H inward axis at Q to have positive first coordinate. Strict inward support by (u,v), with u>=v>0, and orthogonality give the complete frame

    H=Q+[0,1]w+[0,1]z,
    w=(c,−s),  z=(−s,−c),
    c,s>0,  c^2+s^2=1,  uc−vs<0,  c<s.               (4)

The other orthogonal choice would have both coordinates positive and violate the strict support condition. In particular Q is H's unique highest vertex, and V=Q+w is its unique rightmost vertex.

Actual HK contact requires c>=Delta. If c>Delta, then

    V_x=N−1+c=d+(c−Delta) in (d,d+1),
    V_y=1/2−s in (−1/2,1/2).

Thus V would belong to the open interior of K. An open neighborhood of a point in the closed unit H meets H's open interior, so this contradicts interior-disjointness. Consequently

    c=Delta=d+1−N,  s=sqrt(1−Delta^2).                (5)

The entire actual HK intersection is the singleton

    V=(d,1/2−s),                                     (6)

in the strict interior of K's left radial side. Its actual normal from H to K is exactly e_x. This is forced physical geometry, not a new normal choice or a replacement of a mean.

## 3. A single polynomial gives the needed H-center signs

Write c_H=(x_H,y_H). From (1), (4)–(5),

    x_H=N−1+(c−s)/2,
    y_H=1/2−(s+c)/2,
    x_H+y_H=N−1/2−s.                                 (7)

Since c,s>0 and c^2+s^2=1, c+s>1, hence y_H<0. We prove

    x_H+y_H>0,  and therefore x_H>0.                  (8)

Put

    P(N)=80N^4−96N^3+8N^2−40N+25.

For every N>=5/4,

    P'(N)=32N^2(10N−9)+16N−40 >=155>0.

The exact endpoint is

    P(321/250)=51496256/48828125>0.                   (9)

Thus P(N)>0 on the entire actual N interval. The single exact identity is

    P(N)=16{(3N^2−N+5/4)^2−4N^2(N^2+2)}.            (10)

Both terms being compared before squaring are positive. Since d+1=sqrt(N^2+2) and c=sqrt(N^2+2)−N, equations (9)–(10) imply

    0<3N^2−N+5/4−2N sqrt(N^2+2)
      =(N−1/2)^2+c^2−1
      =(N−1/2)^2−s^2.

As N−1/2>0 and s>0, this proves N−1/2>s, hence (8).

Equations (3), (7)–(8) now give the strict projections of two ORIGINAL H forces:

    c_H dot n_HA=(u−v)x_H+v(x_H+y_H)>0,
    c_H dot e_x=x_H>0.                               (11)

The first includes u=v; no actual AK mean was narrowed.

## 4. Every actual KB feature lies below K

A,K,B are physically circle-touching and AK,KB are actual contacts. CIRCLE_CONTACT_ANGULAR_ORDER.md excludes a physical triangle of three boundary units, so A and B are closed-disjoint. This is a derived physical noncontact, not an omitted graph edge.

Let g be the actual unit normal from K into B. At K, the actual KH normal is the side axis −e_x by (6). The radius-free triangle side-normal theorem applies to K,H,B and gives

    (−e_x) dot g>=0,  hence g_x<=0.                   (12)

If g_y=0, then g=−e_x, so B meets K's inner radial face with that owned normal. The full right-support bound in Section 1 makes B circle-clear, a contradiction. This includes genuine shared KB means and all endpoints.

If g_y>0 and g_x<0, the K support is its upper inner vertex (d,1/2). By (1), this point belongs to A, so B would physically touch A, contradicting their closed-disjointness.

If g_y>0 and g_x=0, then g=e_y and B lies wholly in y>=1/2. But H lies in y<=1/2, with its unique highest point Q. Its actual HB contact would force Q into B, again contradicting Q in A and physical A/B disjointness.

This exhausts every nonnegative vertical sign. Therefore

    g_y<0.                                           (13)

There are exactly two complete remaining feature classes:

* If g_x<0, KB is the singleton at K's lower inner vertex

      P=(d,−1/2).

* If g_x=0, then g=−e_y, and B lies wholly in y<=−1/2. The entire original bottom-side KB contact, point or shared mean, remains.

No K force balance or K weight interval has been invoked.

## 5. The true B equation and the complete H support fan

Every physical circle corner z_B of B has positive first coordinate. Indeed physical corner acuteness, ACUTE_LOADED_CONTACT_GRAPH.md, Theorem A.2, applies to z_B and each of K's two physical circle corners

    z_K^+=(d+1,1/2),  z_K^−=(d+1,−1/2).

Adding their two strict scalar products gives 2(d+1)(z_B)_x>0. This is geometric and applies even to a corner with zero multiplier. Thus the ORIGINAL B circle resultant F_B has positive first coordinate for either physical mask and every nonnegative individual weight split of positive total.

Let m be the actual unit normal from H into B, and let rho_B,rho_H>0 be B's two genuine pair magnitudes. Its true degree-two force equation is

    F_B=rho_B g+rho_H m.

By (12) and (F_B)_x>0, it follows that

    m_x>0.                                           (14)

We exhaust all actual H support features for this strict sign. Besides Q and V, denote its other vertices by

    U=Q+z,  W=Q+w+z.

The outward side normals, in boundary order Q,V,W,U, are

    QV: −z=(s,c),    VW: w=(c,−s),
    WU: z=(−s,−c),   UQ: −w=(−c,s).                  (15)

The latter two side normals and the entire cone at U have negative first coordinate, so (14) excludes them. Q cannot belong to B, because Q belongs to A and A/B are closed-disjoint.

V cannot belong to B either, in either retained KB feature. In the bottom-axis case, every B point has y<=−1/2, whereas V_y=1/2−s>−1/2. In the strict lower-inner-vertex case, K's support point is P and B lies in g dot x>=g dot P. But

    V−P=(0,1−s),  g dot(V−P)=g_y(1−s)<0,

so V is not in B.

The full remaining H fan is therefore its side VW, its bottom vertex W, or its side QV. On VW the normal is w and has strictly negative second coordinate. Every nonzero normal in W's outward cone, generated by w and z, also has strictly negative second coordinate. We next exclude all of QV, retaining every possible side mean.

If HB uses QV, its actual normal is m=−z=(s,c), and B lies in

    m dot x>=m dot Q.

In the bottom-axis KB case this is already impossible geometrically: B lies in y<=−1/2, while every point of QV has y>=1/2−s>−1/2.

In the strict lower-inner-vertex case B contains the original P=(d,−1/2). But, using c=Delta,

    P−Q=(c,−1),
    m dot(P−Q)=sc−c=c(s−1)<0.

This contradicts B's actual minimum-m support. The support value is the same for every original point or mean of QV; none has been moved.

Thus every actual HB feature satisfies

    m_x>0,  m_y<0.                                  (16)

By (7)–(8), its ORIGINAL force has strict positive center projection:

    c_H dot m=x_H m_x+y_H m_y>0.                     (17)

This covers H-owned, B-owned, free and shared HB interfaces. It made no assumption on B's circle mask or on the KB owner within its two complete features.

## 6. The intact petal contradicts the full H5 equation

Let M_XY=F_X+F_Y be the sum of the original circle resultants on the intact HXY end triangle. BOWTIE_CELL_CLOSED.md, Section 2, applies at its true degree-two loaded tips X,Y with arbitrary further forces at H. It gives

    c_H dot M_XY>0.

Cancellation of the internal XY pair force identifies M_XY exactly with the sum of the two original outward H-to-X and H-to-Y forces. The TRUE five-force equation at the unloaded H is therefore

    mu_HA n_HA + mu_HK e_x + mu_HB m + M_XY = 0,
    mu_HA,mu_HK,mu_HB>0.                              (18)

Its scalar product with c_H is strictly positive by (11), (17) and the complete end-petal pressure theorem. This contradicts (18), proving the free-HA theorem throughout the whole radius window.

All original forces were retained. In particular the three positive HK,KA,KB forces at K were never replaced by a degree-two equation. The proof uses B's true degree two only in Section 5, and H's true degree five only in the final full balance.

## 7. Whole radial-K diamond consequence

The same actual triangle-attached diamond cannot have a physical radial K in ANY endpoint mask.

To see the owner join explicitly, sum every original force equation in the six-body component. Internal pair forces cancel and give

    F_A+F_K+F_B=−M_XY.

The intact petal has c_H dot M_XY>0. Since K is physically radial and touches H, RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md gives c_H dot F_K>=0 for every original nonnegative K weight split; it is strictly positive whenever K's total is positive. In the KAB load orbit that total is positive. The strict petal term alone suffices for the negative-endpoint selection below. Thus at least one of F_A,F_B has negative c_H projection. Label that actual endpoint A, exchanging A and B only if necessary.

A cannot be physically radial, because the same radial-neighbor pressure theorem at its actual H contact would give a positive projection. Therefore A has a unique physical circle corner with c_H dot z_A<0. Its actual HA interface is one of the following exhaustive length/owner classes:

* An A-owned singleton or a genuinely shared HA. The entire class is excluded at all radii by NEGATIVE_UNIQUE_TRIANGLE_TIP_OWNED_EXCLUSION.md, using the actual physical triangle H,A,K and no K degree-two equation.
* An H-owned singleton. The entire class is excluded by NEGATIVE_H_OWNED_RADIAL_DIAMOND_CONTACT_EXCLUSION.md, including its high-radius join and all original H-side offsets.
* A genuinely free point-only vertex/vertex contact. Sections 1–6 above exclude its whole domain, with all original shared AK means retained.

These are the actual strict selected contact classes. No owner or zero-weight limit is omitted. The other endpoint may have one or two physical circle corners; the all-radial endpoint case is already impossible in the negative-endpoint selection itself.

Consequently the entire radial-K branch of the genuine H5/K3 triangle-attached diamond KAB load orbit is closed. The unique-K branch remains a separate obligation. Every petal force, every actual shared mean, every original physical mask and all three completion squares remain throughout. No numerical pose cover, angle partition, canonical motion, post-extraction normal change, deleted higher-degree force, Lean compilation or CI is used.
