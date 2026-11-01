# Transitive-owner same-side triangle: three exact support roots exclude the complete chart

November 1, 2026. **Evidence at construction: X, independent physical and arithmetic review requested.** This theorem concerns the full chart stated below. It is a uniform exact exclusion, with all original side means and outside terminals retained, and does not change a canonical original gate without its caller join.

**Theorem.** Every such original triangle requires `R>25/12`; in particular it is impossible at `R²≤1105/256`, since `625/144−1105/256=55/2304`.

The complete exact certificate has **three support roots, 745 nodes, 320 variance-certified leaves and 54 proved-empty leaves**, with no unresolved boxes. Every variance-certified leaf has exact reserve greater than `1/3000` above `625/144`; the arithmetic certificate does not claim that such a leaf contains a feasible physical configuration.

## 1. Actual physical chart and original complete stresses

Keep the actual nine interior-disjoint unit squares in one disk about O, their selected physical force-and-torque certificate, and all original means and positive edges. Three entirely circle-unloaded bodies A,B,C have their positive internal triangle and exactly one original positive outside exit each. Outside actual neighbors can coincide and have arbitrary frames, loads, degrees, circle masks and remaining contacts.

C owns both AC and BC on the **same** North side. A owns AB, at a point in the relative interior of the indicated A side; B meets that side at a genuine vertex. Normalize the original AB magnitude to one by a common positive scaling of all six local forces.

After a rigid motion, the actual contacts and square frames are

    p_A=(0,0),  p_B=(d,0),
    u=(c,s),  v=(-s,c),       s=sqrt(1-c²),
    A=[0,1]u+[0,1]v,
    w=(-C_0,S), V=(S,C_0),   C_0=sqrt(1-S²),
    B=p_B+[0,1]w+[0,1]V,
    P=ell u=p_B+w,
    S=ell s,   d=ell c+C_0,
    0<c<1/2,  2c<=ell<1.

C_0 is a scalar; C denotes the third physical square. The actual North side of C contains both p_A and p_B, so d≤1. Conversely in this chart `d≤1` is equivalent to `ell≥2c`, by squaring the positive inequality `C_0≤1-ell c`. The endpoints are retained in the closed enclosure; a caller whose contacts lie strictly inside C's side supplies the corresponding strict subdomain.

The original internal force vectors are

    C-to-A: (0,a),   a>0, at p_A;
    C-to-B: (0,t),   t>0, at p_B;
    A-to-B: (s,-c)=-v, at P=ell u.

The full outside vectors are therefore

    F_A=(-s,a+c),  F_B=(s,t-c),  F_C=(0,-a-t).

All six original forces remain present. None is replaced by a zero-force limit. The closed root boundaries used below are overapproximations of these strict original equations.

## 2. The full A torque fixes its magnitude and application

The two own-frame components of F_A are

    F_A dot u = as>0,
    F_A dot v = 1+ac>0.

Thus its unchanged original outside application is q_A=u+v. Torque about p_A=(0,0), with the original AB application ell u, gives

    -ell + det(u+v,F_A)=0,
    1-ell+a(c-s)=0.

Consequently

    a=(1-ell)/(s-c)>0.

The denominator is uniformly positive on the closed root rectangle `0≤c≤1/2`, because `s≥sqrt(3)/2>1/2`.

## 3. Exactly three complete B support alternatives

Set

    K=sC_0+cS>0,
    L=cC_0-sS<0.

For the original strict chart, `S=ell s≥2cs>c`, so L<0 follows by squaring `cC_0<sS`. The closed root enclosure may use L≤0. The B outside components are

    F_B dot w = tS-K,
    F_B dot V = tC_0-L>0.

Its original AC-independent moments are best taken about P=p_B+w. The C force applied at p_B contributes `-tC_0`; its internal BA force applies at P and contributes zero. The sign of the first component gives precisely three cases:

| Root | Original B outside support | Full torque consequence | Required positive-force predicate |
| --- | --- | --- | --- |
| 0 | q_B=p_B+V | `t=(K+L)/S` | K+L>0 |
| 1 | q_B=p_B+w+V | `t=K/(S-C_0)` | S>C_0 |
| 2 | q_B=p_B+V+eps w, original side mean | `t=K/S`, `eps=-ell L` | Original t>0; 0≤eps≤1 |

For the first row, full torque is `tS-K-L=0`; the resulting first own component is L<0, as required. For the second row, it is `t(S-C_0)-K=0`; the first own component is positive. For the third row, set the first own component to zero and retain the original side application. The remaining torque gives

    (1-eps)(tC_0-L)=tC_0.

Since `KC_0-LS=s`, substitution gives `eps=-ell L` exactly. This mean is nonnegative, and

    eps=ell²s²-ell cC_0 <=ell²s²<=1.

Thus all original B support-side means and endpoints are included, rather than replaced after extraction.

The three rows exhaust the sign of one scalar of the complete original F_B; no additional support features are omitted.

## 4. Actual outside points and a safe entire-mean relaxation

At every original contact q with outside unit normal n, the actual outside square contains q+n. This elementary own-coordinate fact includes all outside frames, support means and endpoints. Therefore the original disk contains

    w_A=u+v+F_A/|F_A|,
    w_B=q_B+F_B/|F_B|.

The full C translation points its outside force South. Its unchanged outside application has the form `(m,-1)`. Full C torque gives

    m=d t/(a+t),  0<m<d.

Its actual outside neighbor consequently contains `w_C=(m,-2)`. For the exclusion we allow **every** m in the entire closed interval [0,d], a larger set than this exact original formula. This enlargement preserves every physical original mean and removes a harmless zero-over-zero expression on some nonphysical closed boundary points; it does not shorten any original equation.

For exact evaluation, write t=N/D according to the three root rows:

    root 0: (N,D)=(K+L,S),
    root 1: (N,D)=(K,S-C_0),
    root 2: (N,D)=(K,S).

Every original row has D>0. Cancel it homogeneously before normalization:

    F_B/|F_B|
       = (sD,N-cD)/sqrt((sD)²+(N-cD)²).

This exact expression remains bounded when t becomes arbitrarily large, and the enlarged boundary D=0 is handled without dividing by zero. No actual positive original force has been set to zero.

## 5. Exact squared-variance obstruction

For three actual disk points,

    R² >= V = (|w_A-w_B|²+|w_B-w_C|²+|w_C-w_A|²)/9.

We preserve the dependence on the one original mean m in the horizontal coordinates by using the exact identity

    (x_A-x_B)²+(x_B-m)²+(m-x_A)²
      = (3/2)(x_A-x_B)²+2(m-(x_A+x_B)/2)².

The checker encloses m over [0,d], computes a rigorous lower bound on this expression, and adds the three vertical squared differences, where w_C,y=-2 is fixed. This is a uniform lower bound for every original m, not the value at a selected convenient mean.

On every variance-certified leaf, that lower bound gives `V>625/144`, hence `R>25/12` for every original configuration in its domain.

## 6. Exhaustive closed roots and exact arithmetic

Each of the three support roots starts with the whole rectangle

    c in [0,1/2], ell in [0,1],

retaining the physical predicate ell≥2c and its corresponding support/positive-force predicate from Section 3. These three roots cover all original strict configurations. Their closed faces are included as algebraic overapproximations of the indicated strict feature, not asserted to realize all possible different physical features at a degenerate angle.

The checker [verify_transitive_same_side_triangle.py](verify_transitive_same_side_triangle.py) imports only the exact interval and integer-square-root primitives of the separately audited [perpendicular checker](verify_perpendicular_single_free_triangle.py). It uses rational intervals, exact endpoint arithmetic and rational outward square-root bounds on denominator `2^18`. It uses no floating-point number, angle sample, optimizer, external library or numerical tolerance.

All conditional interval intersections use stated necessary original facts: `0≤S≤1`, `0≤d≤1`, L≤0, nonnegative N or D on its selected positive-force branch, and the original side-mean range `0≤eps≤1`. If the resulting interval is empty, that entire physical root box is impossible. If a positive denominator or square-root norm cannot yet be certified, the checker subdivides; it does not discard the box.

Every split takes an exact rational midpoint and retains both closed children. Every successful terminal record is either an exact original-domain impossibility or the strict variance inequality. Exhausting a resource limit produces `UNRESOLVED`, never a success claim. In the recorded run all roots terminate completely.

The [complete split-tree certificate](transitive_same_side_triangle_certificate.json) records every split, every binary address, every leaf box and reason, and each exact rational variance lower bound. The split heuristic need not be trusted: a separate verifier can reconstruct all closed root coverage and recompute the terminal bounds.

## 7. Reproduce and compare the complete finite output

From the repository root:

    python research/nine/computer_assisted/verify_transitive_same_side_triangle.py --certificate research/nine/computer_assisted/transitive_same_side_triangle_certificate.json

| Original B support root | Nodes | Strict variance leaves | Proved-empty leaves | Max depth |
| --- | ---: | ---: | ---: | ---: |
| 0: original corner p_B+V | 175 | 67 | 21 | 8 |
| 1: original corner p_B+w+V | 321 | 144 | 17 | 15 |
| 2: complete original side mean | 249 | 109 | 16 | 13 |
| **Total** | **745** | **320** | **54** | **15** |

The empty leaves comprise 37 geometric-domain contradictions, 5 nonpositive-force contradictions in root 0, and 12 impossible-support-branch contradictions in root 1. No original-mean emptiness leaf was needed. Every strict variance leaf has certified exact reserve **greater than 1/3000** above 625/144; the complete raw least fractions are stored in the certificate.

This compact three-row table summarizes exact finite arithmetic coverage. The displayed rows are not three independent handwritten variance inequalities; the 320 variance-certified leaves and full tree are the exact computational component.

## 8. Whole-feature conclusion and honest adoption boundary

The three roots exhaust every actual support alternative of the B exit. The complete A and C equations and all original means were retained before making only a safe enlargement of m's domain. The exact tree therefore excludes the **entire transitive-owner same-C-side chart** at `R²≤1105/256`, including every positive force ratio, original mean and outside-terminal identity.

The caller must supply the exhaustive physical owner/chart reduction stated in Section 1. This theorem does not automatically cover a different transitive arrangement with perpendicular C-owned axes, a cyclic ownership graph, or a remaining free-normal mask. Those features need their own theorems and then a common original-case join.

At construction this computational theorem has run to completion, and independent physical-transfer review plus a separate exact certificate verifier are requested. No Lean, Lake or CI has been used; no global original parent/fine flag follows solely from this feature source.
