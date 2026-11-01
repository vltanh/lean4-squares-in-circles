# Transitive perpendicular-owner triangle: full exit arc reduced to two exact three-dimensional roots

November 1, 2026. **Evidence at construction: X; independent physical and arithmetic review requested.** This is a complete exact exclusion of the original chart specified below. It uses one analytic inequality for the full original A exit arc and exact rational interval certificates for two auxiliary scalar endpoint expressions.

**Theorem.** Every original physical configuration in this chart requires `R>25/12`, hence is impossible at `R²≤Q=1105/256`, with `625/144−Q=55/2304`.

The finite certificate has **5,696 nodes, 2,730 variance-certified leaves and 119 proved-empty angle leaves**, with no unresolved boxes. Every variance-certified leaf has exact reserve greater than `1/7000` above `625/144`. Certification of a variance bound does not assert that the leaf contains any feasible physical packing.

## 1. Original complete physical model

Keep the same nine actual interior-disjoint squares, disk center O and radius R, original support normals and applications, all positive forces and all circle masks. Three actual entirely circle-unloaded units A,B,C have the full positive internal triangle and one original positive outside exit at each. Outside terminals can repeat; no extra equation or frame assumption is placed on them.

C owns the AC and BC normals on two perpendicular sides. A owns AB, whose application lies in the relative interior of an A side and is a B vertex. A rigid motion and relabeling put the actual chart in the form

    C=[0,1]²,
    u=(c,s), v=(s,-c),       c=cos(alpha), s=sin(alpha),
    w=(C_0,S), V=(-S,C_0),   C_0=cos(beta), S=sin(beta),
    0<beta<alpha<pi/4,
    p_A=(1,s_0), p_B=(t_0,1),
    A=p_A+[0,1]u+[0,1]v,
    B=p_B+[0,1]w+[0,1]V,
    P=p_A+ell u=p_B+w,
    t_0=1-C_0+ell c,
    s_0=1+S-ell s,
    S/s<ell<1.

Here C_0 is a scalar, distinct from the physical square C. Both original C-owned applications are in side interiors, so `0<t_0,s_0<1`.

Normalize the original AB magnitude to one by a common positive scaling. The original internal oriented vectors are

    C-to-A=(a,0),   a>0, at p_A;
    C-to-B=(0,t),   t>0, at p_B;
    A-to-B=(-s,c)=-v, at P.

The three complete outside vectors are therefore

    F_A=(a+s,-c), F_B=(-s,t+c), F_C=(-a,-t).

No original positive force is removed in this model.

## 2. Full moments determine the B side mean and the C exit direction

The own components of F_A are `ac>0` and `1+as>0`, so its unchanged outside application is

    q_A=p_A+u+v.

Its complete torque about p_A gives

    ell-1+a(c-s)=0,
    a=(1-ell)/(c-s)>0.

This explains the necessary angle condition c>s in the physical chart.

Put

    K=sC_0-cS=sin(alpha-beta)>0,
    L=cC_0+sS=cos(alpha-beta)>0.

The B outside own components are `tS-K` and `tC_0+L>0`. Torque about P=p_B+w gives three possible support signs. If the first component were positive, the opposite-corner exit would require

    t(C_0-S)+K=0,

impossible because beta<pi/4. If it were negative, the other-corner exit would require

    -tS+K-L=0,

impossible because `0<alpha-beta<pi/4` implies K<L. Therefore its first component is exactly zero:

    t=K/S,  F_B/|F_B|=V.

Keep B's original outside mean `q_B=p_B+V+eps w`, `0≤eps≤1`. The unchanged full torque forces

    eps=L/(tC_0+L)=LS/s.

The identity `KC_0+LS=s` justifies the second equality. No original mean is reset.

At C, the full outside vector has both components negative, so its original application is `(0,0)`. Its complete torque gives

    a s_0=t t_0.

Consequently its unchanged unit exit direction is exactly

    F_C/|F_C|=(-t_0,-s_0)/sqrt(t_0²+s_0²).

The proof below uses this necessary exact direction and then enlarges the parameter set by dropping the additional algebraic constraint `a s_0=t t_0`. Enlarging the domain cannot remove any original physical configuration.

## 3. Actual outside points and the bounded A exit arc

At any original contact q with outward unit normal n, the same physical outside square contains q+n. In own coordinates, adding a unit normal moves inward from each minimizing support endpoint by at most one. This includes all original side means and endpoints.

The actual disk therefore contains

    w_A=q_A+e_A,  e_A=(a+s,-c)/sqrt((a+s)²+c²),
    w_B=p_B+2V+eps w,
    w_C=(-t_0,-s_0)/sqrt(t_0²+s_0²).

Since a≥0, the first coordinate of e_A is at least s. Thus the original unit direction lies on the entire closed Southeast arc between

    e_0=(1,0),  e_1=(s,-c).

The auxiliary endpoint expressions used below are not asserted to be actual outside contacts or disk points. Their only role is to bound the squared variance of the **actual** three points through an exact scalar concavity inequality.

## 4. Analytic reduction of the full A exit arc

For three actual disk points, write

    V(e)=(|q_A+e-w_B|²+|w_B-w_C|²+|w_C-q_A-e|²)/9.

The mean-square identity gives `R²≥V(e_A)`. On a unit arc, the dependence on e is affine:

    V(e)=constant+(4/9) v_0 dot e,
    v_0=q_A-(w_B+w_C)/2.

We prove the signs `v_0,x≥1` and `v_0,y≤0` on the whole enlarged closed chart used below.

First, `q_A,x=1+c+s≥2`, `w_C,x≤0`, and

    w_B,x=t_0-2S+eps C_0≤2,

because `t_0≤1`, `0≤eps≤1` and `0≤C_0≤1`. Thus `v_0,x≥1`.

Next, `q_A,y=s_0+s-c≤1+s-c≤1`, and `w_C,y≥-1`. We claim `w_B,y≥3`. For S>0, with c≥s,

    eps S = (c/s)C_0 S²+S³≥C_0 S²+S³,
    w_B,y≥1+C_0(2+S²)+S³.

For `0<S≤1/sqrt(2)<3/4`, both terms being compared are positive and

    C_0²(2+S²)²-(2-S³)²
      = S³(4-3S-2S³)>0.

The sign follows from `3S+2S³<99/32<4`. At S=0 the same conclusion holds with equality `w_B,y=3`. Hence `v_0,y≤1-(3-1)/2=0`.

Parameterize the full original unit exit arc by `e=(cos(delta),-sin(delta))`, `0≤delta≤arccos(s)`. Then

    v_0 dot e=v_0,x cos(delta)-v_0,y sin(delta)

is nonnegative and concave, since its second derivative is its negative. Its minimum on the closed arc is at an endpoint. Therefore

    V(e_A) ≥ min(V(e_0), V(e_1)).

It suffices to prove both auxiliary scalar endpoint expressions strictly greater than 625/144. No physical square or original support direction is changed by this reduction.

## 5. Three compact rational parameters, including every limit face

Set

    p=tan(alpha/2),  r=S/s,
    ell=r+(1-r)z,  0≤r,z≤1.

The closed angle domain is `0≤p≤sqrt(2)-1`, equivalently

    1-p²-2p≥0.

For convenient rational root boxes, each endpoint mode starts with

    p in [0,1/2], r in [0,1], z in [0,1],

and retains that exact polynomial angle predicate. Boxes lying completely beyond its allowed interval are proved empty; crossing boxes are enclosed and subdivided without losing the irrational boundary.

All required point formulas are bounded without the singular a or t expressions:

    c=(1-p²)/(1+p²), s=2p/(1+p²),
    S=r s, C_0=sqrt(1-S²),
    ell=r+(1-r)z,
    s_0=1-(1-r)z s,
    t_0=1-C_0+ell c,
    eps=r(cC_0+sS),
    q_A=(1+c+s,s_0+s-c),
    w_B=(t_0-2S+eps C_0,1+2C_0+eps S),
    w_C=(-t_0,-s_0)/sqrt(t_0²+s_0²).

The two endpoint expressions use `q_A+(1,0)` and `q_A+(s,-c)`, respectively.

The unit normal denominator is uniformly positive: on the rational root box p≤1/2 one has s≤4/5, and thus `s_0≥1-s≥1/5`. The square root defining C_0 likewise has a positive radicand. The original force limits beta→0 or alpha→pi/4 cause no unresolved division because a and t were eliminated before interval evaluation.

The interval intersections `0≤t_0≤1` and `0≤eps≤r` use the exact chart facts `C_0≥c`, `ell≤1`, and `cC_0+sS≤1`. They preserve every original mean and every angle-boundary enclosure.

## 6. Exact certificate and complete run

The checker [verify_transitive_perpendicular_triangle.py](verify_transitive_perpendicular_triangle.py) imports only the audited exact rational interval and integer-square-root primitives from [verify_perpendicular_single_free_triangle.py](verify_perpendicular_single_free_triangle.py). It uses no floating-point operation, numerical tolerance, angle sample, third-party dependency, Lean or CI.

Both complete three-dimensional roots are bisected at exact rational midpoints. Every split retains both closed children. At each leaf, exact outward component intervals give lower bounds on all six squared coordinate differences and hence on the auxiliary endpoint V. A leaf is accepted only after proving `V>625/144` or an exact angle-domain impossibility. Resource exhaustion raises `UNRESOLVED`.

The [complete split-tree certificate](transitive_perpendicular_triangle_certificate.json) records all root boxes, splits, full binary addresses, leaf boxes, exact variance bounds and empty-domain reasons. A separate checker can therefore verify full root coverage and every arithmetic leaf without trusting the adaptive split heuristic.

Reproduce from the repository root:

    python research/nine/computer_assisted/verify_transitive_perpendicular_triangle.py --certificate research/nine/computer_assisted/transitive_perpendicular_triangle_certificate.json

| Auxiliary A arc endpoint | Nodes | Variance-certified leaves | Proved-empty angle leaves | Maximum depth |
| --- | ---: | ---: | ---: | ---: |
| e_0=(1,0) | 985 | 438 | 55 | 9 |
| e_1=(s,-c) | 4,711 | 2,292 | 64 | 17 |
| **Total** | **5,696** | **2,730** | **119** | **17** |

Every variance-certified leaf has exact reserve **greater than 1/7000** above 625/144; the raw least fractions are retained in the certificate. No support-mean or coordinate-domain emptiness leaf was needed in the recorded run. There are no remaining boxes or uncovered boundary charts.

## 7. Whole-chart implication and original-case boundary

The exact computation proves both endpoint expressions larger than 625/144 on every original parameter value. Section 4 then gives `V(e_A)>625/144` for the full original A exit direction, so the actual original disk must satisfy `R²>625/144`.

This closes the entire displayed transitive perpendicular-C-owner feature, with arbitrary original side means, every strictly positive force ratio and every outside terminal identity. It does not require a particular outside orientation, a numerical minimum, or independent auxiliary contacts that need not exist.

The exhaustive original owner/chart reduction and subsequent original-case join remain distinct proof obligations. At construction, this complete exact certificate has executed successfully and is awaiting independent physical-transfer review and arithmetic replay. It is not a Lean proof and does not by itself alter a canonical original coarse or fine flag.
