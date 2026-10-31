# A three-boundary rooted C4 has a negative terminal concurrence

Date: October 26, 2026.

**Status: accepted complete uniform concurrence theorem and exact forbidden-ray reduction after full root and independent reviews in `REVIEW_C4_THREE_BOUNDARY_NEGATIVE_CONCURRENCE_ROOT_2026_10_26.md` and `REVIEW_C4_THREE_BOUNDARY_NEGATIVE_CONCURRENCE_GLOBAL_2026_10_26.md`.** Both reviews pin the unchanged mathematical source before this acceptance-only status edit. This does not exclude every rooted C4 or close C3.334. No shared ledger is changed.

Keep the common physical certificate and all original units in

    79/40<=R<=sqrt(1105)/16.

Let H-T_1-T_2-T_3-H be an actual positive four-cycle. Each T_i has true positive degree two and positive total circle load. H may have arbitrary additional original forces. Keep the actual circle resultants F_i, every physical circle mask and every individual zero corner weight. Put

    M=F_1+F_2+F_3.

The two actual outward root-force vectors are u from H toward T_1 and v from H toward T_3. Summing only the three true private-body equations and origin moments gives

    u+v=M,
    det(P_1,u)+det(P_3,v)=0,                              (1)

at their unchanged root applications. No root equation is truncated.

## 1. The exact boundary-path inputs

The full boundary-path cone theorem `THREE_BOUNDARY_PATH_RESULTANT_CONE.md` gives

    F_2=alpha F_1+beta F_3,          alpha,beta>0,           (2)

where F_1,F_3 are linearly independent. Their directions have a strict angular difference between zero and pi.

Every T_i has a physical boundary neighbor. The complete degree-two boundary concurrence theorem in `TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Lemma 2.1, therefore gives genuine nonparallel force lines and

    q_i=t_i F_i,                     t_i>0,

with proper ports at T_i. No claim that a two-circle-corner q_i lies inside its square is made.

Let f and g be the actual positive directed forces on T_1-T_2 and T_2-T_3. Properness at both endpoints gives

    q_2-q_1=l f,
    q_3-q_2=m g,                    l,m>0.                (3)

The coefficients are strictly positive: otherwise the two concurrence points would coincide, which is impossible for distinct nonzero positive rays F_i in the strict boundary order. The true private force equations are

    u=F_1+f,
    F_2=f-g,
    v=F_3-g.                                              (4)

At the actual root contacts, endpoint properness gives

    q_1=P_1+a_1 u,
    q_3=P_3+a_3 v,                  a_1,a_3>=0,           (5)

where the positive force magnitudes have simply been absorbed into the nonnegative proper-length coefficients.

## 2. The entire nonparallel root concurrence has negative sign

**Theorem 1.** If u,v are nonparallel, their actual force lines concur at

    q=-t M,                         t>0.                 (6)

This conclusion needs no physical leaf or other outside-circle direction.

Since the lines meet at q, (1) gives det(q,M)=0. The cone identity makes M=(1+alpha)F_1+(1+beta)F_3 nonzero. Thus q=k M for a real k.

From (2)--(4), the actual root forces in the independent basis F_1,F_3 are

    u=[1+(alpha t_2-t_1)/l] F_1+(beta t_2/l) F_3,
    v=(alpha t_2/m) F_1+[1+(beta t_2-t_3)/m] F_3.          (7)

The displayed off-diagonal coefficients beta t_2/l and alpha t_2/m are strictly positive. The concurrence points q_1 and q lie on the same u line, and q_3 and q lie on the same v line. Hence, for real c,e,

    q_1-q=c u,
    q_3-q=e v.

Compare the F_3 coefficient in the first identity and the F_1 coefficient in the second, using (7):

    -k(1+beta)=c beta t_2/l,
    -k(1+alpha)=e alpha t_2/m.                            (8)

The value k=0 would force c=0 and then q_1=0, impossible. If k>0, both c and e are strictly negative. Equations (5) would give

    q=P_1+(a_1-c)u=P_3+(a_3-e)v,

with both displayed coefficients strictly positive. Thus q would lie on two distinct actual outward normal rays of the closed convex H. Each corresponding P_i is the unique nearest point of H to q: for x in H and lambda>0,

    |P_i+lambda n_i-x|^2
      =lambda^2+|P_i-x|^2+2lambda n_i.(P_i-x)
      >=lambda^2,

with equality only at x=P_i. Uniqueness therefore forces P_1=P_3. But two nonparallel outward rays from the same point meet only at that point, whereas both coefficients are positive. This is a contradiction.

Consequently k<0, proving (6). The argument retains all original root means and applies equally to singleton and shared contacts.

## 3. Opposite parallel root normals are impossible independently of root pressure

Suppose the actual root unit normals are n and -n, with positive magnitudes mu,nu. In (n,Jn) coordinates let y_1,y_3 be the transverse coordinates of P_1,P_3. Equation (1) gives

    mu y_1=nu y_3.

If these coordinates are nonzero, they have the same strict sign. Endpoint properness (5) preserves their transverse coordinates in q_1,q_3. Thus F_1 and F_3 have the same strict transverse sign, and so does F_2 by (2). This contradicts M=u+v parallel to n. If one coordinate is zero both are zero, making F_1,F_3 collinear, also impossible. This excludes every opposite-normal case, without an origin or pressure premise at H.

## 4. The complete parallel case is impossible under the forbidden-ray hypothesis

Assume now

    H intersect {-s M:s>=0} is empty.                     (9)

By Section 3 the only possible parallel root normals have the same sign n. Thus M=(mu+nu)n. The actual moment gives

    mu y_1+nu y_3=0.

Neither transverse coordinate can vanish: if one vanishes both do, and (5) makes the endpoint resultants collinear. Hence their signs are strictly opposite.

The two actual ports are distinct. Their common support face is therefore an H side, so n is an actual own side axis. In coordinates with n=e_x, write

    H=[s-1,s] times [b,b+1].

The opposite port-height signs give b<0<b+1. Consequently the entire side-coordinate interval [s-1,s] on the n axis belongs to H. Hypothesis (9) excludes every nonpositive point of that interval, so s-1>0 and s>1.

Both actual neighbors T_1,T_3 lie beyond this support. Their center n-projections exceed 3/2, while their center norms are below M_*=91/60. Thus their centers lie in a rectangle with longitudinal width less than 1/60 and transverse width less than 2 sqrt(181)/60. Its squared diameter is

    1/3600+4(181/3600)=29/144<1.

This contradicts their disjoint unit incircles. All parallel root cases are therefore excluded under (9).

## 5. Exactly one improper root port is the remaining nonparallel alternative

Keep (9) and a nonparallel root pair. Theorem 1 gives q=-tM, t>0, so q does not belong to H. Write its two actual root ports as

    P_i=q+b_i n_i,

where the real b_i need not initially be nonnegative. Neither b_i can be zero, because that would put q in H. Both cannot be negative: as in Section 2, q would lie on two distinct outward normal rays and violate uniqueness of nearest-point projection.

If both were positive, all hypotheses of `ROOTED_NONPOSITIVE_RAY_PROPER_PORT_CAP_EXCLUSION.md` would hold, and its complete two-neighbor cap contradiction would exclude the configuration. Thus any remaining nonparallel candidate must have exactly one negative and one positive proper-length coefficient.

Its two unit normals must also be strictly obtuse. To see this, a pair of actual square normals with nonnegative scalar product always has proper intersections: if one normal is an own side axis, the elementary common-side line calculation gives the two coefficients nonnegative; if neither is an axis, equal vertices give concurrence at that vertex, adjacent vertices give the positive common-face formula, and opposite vertices have strictly negative scalar product. This exhausts the square's support features, including axis endpoints. Nonnegative scalar product is therefore incompatible with the required one-improper-port alternative.

This is an exact remaining alternative, not its exclusion. At the improper port, b_i<0 and q=P_i+(-b_i)n_i: the concurrence lies on the actual outward normal ray from that port. Its neighbor still has its true loaded degree-two equation. No root degree or circle force is discarded.

## 6. Scope in the mixed triangle/four-body chain

For the original middle triangle A-H-C with O in int A and this terminal C4 as all other positive pair attachments at H, the full external resultant is exactly M. Indeed H is physically circle-clear: otherwise H,T_1,T_2,T_3 would form an actual boundary four-cycle, forbidden by `CIRCLE_CONTACT_ANGULAR_ORDER.md`, Section 5. Thus no root circle force is omitted. The accepted `ROOTED_ORIGIN_TRIANGLE_EXTERNAL_RAY_RESTRICTION.md` supplies exactly (9) for the entire terminal-block resultant M. The source above therefore eliminates every parallel terminal-root pair and every nonparallel pair proper at both root ports. The residual whole three-load C4 case has precisely the one-improper, strictly-obtuse root pair of Section 5.

Other load masks require their own true equations; the present source does not declare an unloaded private body loaded or apply the boundary-neighbor concurrence theorem without its real premise. It does not close an entire coarse row. No Lean compilation, CI, numerical sampling, remote action, or shared-ledger edit is used.
