# Transitive side ownership on one common side: complete physical chart, full torque elimination and exact disk-point model

November 1, 2026. PR #11 continuation. **Evidence at construction: H for the exact physical reduction below; the separate exhaustive rational certificate has its own X and review record.** Root and geometry independently reconstructed the force and moment formulas.

## 1. Exact original feature

Keep the same original physical certificate, all nine actual squares, their full force and moment equations, original applications, means, circle masks, zero coefficients and all other contacts. Three selected-circle-unloaded actual squares A,B,C have exactly the positive internal triangle and one original positive outside exit each. Outside terminals can repeat and have arbitrary frames, degrees and loads.

Assume the three pair intersections are singletons at distinct points, the core frames are pairwise nonparallel, and the side-owner tournament is transitive: C owns CA and CB, and A owns AB. Every nonowner application is the corresponding strictly exposed vertex and every owner application is in the relative interior of its actual support side. This manuscript treats the case where the two C-owned normals are the **same** own direction of C.

After one rigid motion and a horizontal reflection if necessary, the two C-owned contacts are

    p_CA=(0,0),       p_CB=(d,0),       0<d<1,

and C lies below y=0. Its exact horizontal placement is otherwise unrestricted; both actual contact points remain in its top-side interior.

## 2. Complete actual contact chart

A has its unique bottom vertex at p_CA. Write its own inward axes as

    u=(c,s),        v=(-s,c),
    c,s>0,          c^2+s^2=1,
    A=[0,1]u+[0,1]v.

Because the AB normal is A-owned, the geometric nonobtuse-normal theorem [UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md](UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md), applied to the actual triangle, gives that it has nonnegative dot product with the A-to-C direction South. Its possible own axes are therefore -u or -v.

The option -u is impossible: the A-owned support line through p_CA has level zero, whereas the actual B point p_CB=(d,0) has projection -cd<0, contradicting the A-to-B supporting halfplane. Hence the original A-to-B normal is exactly

    -v=(s,-c).

Its actual application P lies on the side issuing from p_CA in direction u, and is side-interior:

    P=ell u,        0<ell<1.                       (1)

At B the applications p_CB and P are strict vertices, because both corresponding normals are owned by the other cores. They are distinct. They must be adjacent: the complete radius-free strict-opposite-vertex support argument in [UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md](UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md), Section 2.3, applies to B's actual touching returns A,C. It requires no degree or load premise at those returns.

Thus |P-p_CB|=1. Solving this exact unit-distance equation gives

    H=ell s,
    K_0=sqrt(1-H^2)>0,
    d=ell c+K_0,
    P-p_CB=(-K_0,H).                               (2)

The negative square-root alternative for d is impossible, since K_0>ell c follows from ell<1. Thus the entire actual B chart is

    w=(-K_0,H),       z=(H,K_0),
    B=p_CB+[0,1]w+[0,1]z.

Here p_CB is the original bottom vertex and P is its original left vertex.

The exact condition d<=1 is equivalent to ell>=2c: since 1-ell c>0, square the positive comparison K_0<=1-ell c and cancel to get ell^2>=2ell c. Consequently the physical strict domain lies in

    0<c<1/2,       s=sqrt(1-c^2),
    2c<ell<1.                                      (3)

The closed relaxation 0<=c<=1/2, 2c<=ell<=1 is allowed for an interval proof, provided all removable boundary formulas are treated correctly.

Define the exact useful combinations

    K=s K_0+cH=s d>0,
    L=c K_0-sH=c d-ell<0.                          (4)

The strict sign of L follows directly from d<=1 and ell>=2c: L<=c-ell<=-ell/2<0. These are actual geometric consequences, not sampled angle restrictions.

## 3. Every original force and moment

Write a>0,t>0,b>0 for the original CA,CB,AB magnitudes. Normalize all forces by b>0. Thus the original oriented internal vectors are

    C-to-A=(0,a),
    C-to-B=(0,t),
    A-to-B=(s,-c).

The complete original translations give the outside vectors

    E_A=(-s,a+c),
    E_B=(s,t-c),
    E_C=(0,-a-t).                                  (5)

At A the own components are E_A dot u=as>0 and E_A dot v=1+ac>0. Its original outside application is therefore exactly q_A=u+v. Torque about p_CA, retaining the actual AB application ell u, gives

    -ell+det(u+v,E_A)=0,
    1-ell=a(s-c),
    a=(1-ell)/(s-c)>0.                            (6)

At B its two own components are

    F_w=tH-K,
    F_z=tK_0-L>0.                                 (7)

The complete original torque about p_CB uses the incoming AB vector (-s,c) at w, whose moment is -L. This gives exactly the following three support branches.

| Original B outside feature | Exact retained moment consequence | Actual original q_B |
| --- | --- | --- |
| F_w<0 | t=(K+L)/H>0, so K+L>0 | p_CB+z |
| F_w>0 | t=K/(H-K_0)>0, so H>K_0 | p_CB+w+z |
| F_w=0 | t=K/H; original side parameter tau=-ell L | p_CB+z+tau w |

For clarity, when q_B=p_CB+z+epsilon w, its full torque is

    -L+F_w-epsilon F_z=0.

For the zero branch F_w=0, the identity K K_0-LH=s implies F_z=s/H; hence epsilon=-LH/s=-ell L. This is the unchanged original mean forced by the full equation, not an endpoint choice. Since L in (-1,0) and ell<1, 0<tau<1.

C's original outside normal is South and its original application is some (m,-1) on its actual bottom side. Its complete moment about (0,0) is

    dt-(a+t)m=0,
    m=dt/(a+t),        0<m<d.                     (8)

Every full original core moment has now been used; no force or positive edge has been dropped. C's entire horizontal placement and all outside actual frames remain arbitrary subject to the original physical packing.

## 4. Three actual disk points and the stronger proof relaxation

If q minimizes a unit direction e on an actual unit square, then q+e lies in that same square. In own coordinates the nonzero components move inward from their minimizing endpoints by at most one; zero components keep the original coordinate. This applies to every original support mean and endpoint.

Apply this fact to the three unchanged outside neighbors. The original disk contains

    W_A=u+v+(-s,a+c)/sqrt(s^2+(a+c)^2),
    W_B=q_B+(s,t-c)/sqrt(s^2+(t-c)^2),
    W_C=(m,-2),       m=dt/(a+t).                  (9)

These are points of actual existing outside squares; they are not moved or fitted surrogate squares. Repeated outside terminals are harmless.

For proof, it is valid to enlarge (8) to the entire closed range 0<=m<=d. An exhaustive lower bound for every such m applies to the original mean. This enlargement removes all potentially singular ratios in C's mean near force-zero boundaries without asserting that a positive original force is zero.

Likewise, in each B branch write t=N/D with its displayed N,D>0. The same unit direction can be written without dividing by D:

    (sD,N-cD)/sqrt((sD)^2+(N-cD)^2),

where (N,D) equals (K+L,H), (K,H-K_0), or (K,H) in the three respective rows. The exact checker must prove its denominators positive on every certified closed enclosure or separately justify the boundary formula it uses.

## 5. Exact quantitative certificate interface

For any three actual disk points, their equally weighted variance satisfies

    V=(|W_A-W_B|^2+|W_B-W_C|^2+|W_C-W_A|^2)/9 <= R^2.

The separate exact arithmetic proof [computer_assisted/verify_transitive_same_side_triangle.py](computer_assisted/verify_transitive_same_side_triangle.py), with its emitted [transitive_same_side_triangle_certificate.json](computer_assisted/transitive_same_side_triangle_certificate.json), covers all three B support roots over the closed parameter relaxation (3), retaining the branch positivity conditions and the entire m range [0,d]. Its stated target is a uniform strict lower bound above 625/144, which gives R>25/12 and excludes the closed radius Q=1105/256.

The physical proof transfer consists precisely of Sections 1--4 and the variance inequality here. A reported arithmetic root count alone does not replace that transfer or a separate independent replay/review of the checker. The checker/manuscript's recorded proof status governs whether this quantitative conclusion is marked reviewed.

This is one entire transitive-owner feature. The perpendicular pair of C-owned axes is treated by a separate model; a whole direct-triangle or original-parent closure requires the explicit complete owner-family join.
