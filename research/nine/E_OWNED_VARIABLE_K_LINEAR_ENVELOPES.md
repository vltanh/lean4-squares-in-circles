# Complete endpoint-owned linear outer support envelopes

This note proves the two endpoint-owned scalar inequalities needed by
`UNRESTRICTED_JOINT_FIVE_SQUARE_HIGH_FLOOR_CAP.md`. A hand calculation
covers the interval next to the sharp point. Two complete finite tables,
with 25 and 28 leaves, cover the rest. Both tables have passed complete
independent replays using two exact arithmetic implementations.

The endpoint slope is eliminated by the hand comparison in Section 5 of
`MAIN_OWNED_ENDPOINT_SLOPE_REDUCTION_HAND_PROOF.md`. Its multiplier range
and its unboxed endpoint constant are essential to this proof.

## 1. The original physical expression and its reduction

Set

    Q=1105/256, r=sqrt(Q), rho=sqrt(Q-1/4)-1/2,
    a=46, b=27/2, K=207/16, T=211/4.

Let E and S be original physical unit squares in the centered disk of
radius at most r. Work in the right frame; horizontal reflection gives
the left statement. The shoulder center lies in the original rectangle

    B_S=[23/30,13/12] x [25/32,21/16].

Write H_V(q) for the centered support halfwidth of the physical square V
in direction q, and h_V=H_V(e_x)=H_V(e_y). Suppose E owns the separating
normal n=(-w,1), where |w|<=1/14. Let m=(1,z) be the central-to-shoulder
normal and define

    Phi(E,S;w,z,k)
      =(a e_x-kn) dot c_E+(bm+kn) dot c_S
         -a h_E-kH_E(n)-bH_S(m)-kH_S(n).

For every fixed k in [K,20], the cited hand comparison gives

    Phi(E,S;w,z,k)
      <= E_0(k)+(bm+k e_y) dot c_S-bH_S(m)-k h_S,       (1)

where

    E_0(k)=r sqrt(a^2+k^2)-a-k.                        (2)

The original center and orientation of S remain fixed during this
comparison; every central term is unchanged. The inequality is strict
for w!=0. If the original containing radius is strictly less than r,
the nonzero endpoint support coefficient also makes it strict at w=0.

The endpoint contribution (2) is unboxed. For k>K, its maximizing
center need not lie in the original endpoint rectangle, so replacing
(2) by a smaller boxed endpoint support would not follow from (1).
Every table row and the independent checker retain exactly (2).

We will prove that for every t in [0,6] there are admissible multipliers
k_- and k_+, possibly different for the two signs, such that

    Phi(E,S;w,-t,k_-) <= T-16t,
    Phi(E,S;w, t,k_+) <= T+(29/2)t.                    (3)

Both inequalities are strict whenever t>0 or w!=0. No shoulder
orientation is prescribed in this endpoint-owned case.

## 2. Hand proof on the complete interval 0<=t<=1/16

Choose k=K. The orientation-free scalar inequality in Section 1 of
`LOCAL_QUADRATIC_JOINT_CAP.md`, evaluated at the reduced slope w=0,
gives

    E_0(K)+(bm+K e_y) dot c_S-bH_S(m)-K h_S
      <=T+(3K/2)z-K z_++19z^2.                       (4)

This estimate is valid for every original orientation of S. Its
endpoint term at w=0 is precisely (2), because the endpoint penalty
minimum is a+K. It therefore applies after the comparison (1), even
though that comparison does not create a new physical packing.

For z=-t, subtract the first target in (3). The residual is at most

    -(109/32-19t)t <= -(71/32)t.

For z=t, subtract the second target. The residual is at most

    -(257/32-19t)t <= -(219/32)t.

Both rational coefficients are positive. Thus (3) holds on the entire
closed interval, strictly for t>0. At t=0 the original w!=0 or strict
radius clause follows from (1), as stated above.

## 3. A complete orientation-free scalar formula

For a square frame with orthonormal side vectors u,v, put

    H_theta(q)=(|q dot u|+|q dot v|)/2.

For a finite list of vectors define

    M(q_1,...,q_j)=min_theta sum_i H_theta(q_i).

The minimum is given by a finite candidate list: align one nonzero q_i
with a square side, and also include the coordinate frame. Between
consecutive alignment angles, the support sum is positive and has the
form A cos(theta)+B sin(theta); its second derivative is the negative
of that sum, so it cannot have an interior minimum. Zero vectors may
be omitted; limiting cases follow by continuity.

For fixed k,z let

    v=(b,k+bz), q_1=(b,bz), q_2=(0,k),
    P=M(q_1,q_2).

For the original physical shoulder, each of the following is a valid
upper bound for the last three terms on the right of (1):

    C_1=r|v|-M(v,q_1,q_2),
    C_2=rho|v|-P,
    C_3=H_B_S(v)-P.                                  (5)

The first follows from the disk support inequality
`v dot c_S+H_S(v)<=r|v|`. The second uses the universal unit-square
center-radius bound |c_S|<=rho. The third retains the original center
rectangle. Its support is the exact elementary expression

    H_B_S(v)=((x_l+x_h)v_x+(y_l+y_h)v_y
                +(x_h-x_l)|v_x|+(y_h-y_l)|v_y|)/2.

Consequently the scalar expression

    B(k,z)=E_0(k)+min(C_1,C_2,C_3)                     (6)

bounds the entire original endpoint-owned physical domain after (1).
Every bound is uniform over the original independent shoulder frame.
The finite tables verify

    B(k,-t)-T+16t<0,
    B(k, t)-T-(29/2)t<0                               (7)

on the complementary closed interval [1/16,6].

## 4. Complete finite tables and independent replay

Every table row specifies a closed rational interval for t and a
rational multiplier k=N/4096 with 52992<=N<=81920. Thus K<=k<=20
throughout every row. The rows are leaves of exact midpoint partitions
of [1/16,6]. Their closed boundaries overlap, so there are no omitted
boundary points.

`certify_E_variable_k_linear.py` chooses the rational multipliers using
numerical exploration, then verifies its proposed rows with outward
96-bit intervals. Numerical minimization contributes no hypothesis to
the proof. The separate checker `verify_E_variable_k_linear.py` imports
no producer: it reconstructs (2), (5), (6), (7), the permitted multiplier
range, the initial root, and every exact midpoint split.

The primary replay uses the standalone 64-bit directed integer interval
implementation `verify_joint_five_dyadic.py`. A second complete replay
uses `verify_joint_five_fraction.py` and `interval_fraction.py`, with
exact Fraction arithmetic and independently bounded radicals. Both
implementations evaluate direct interval bounds and centered mean-value
bounds. At absolute-value, minimum, maximum and orientation-candidate
changes, derivative intervals include all branches that can be active.
The checker recomputes the residual upper bound; the bound recorded by
the producer is not trusted.

| Target | Nodes | Leaves | Maximum depth | Largest independently replayed residual upper |
|---|---:|---:|---:|---|
| Negative, coefficient 16 | 49 | 25 | 6 | `-390316577538710779/18446744073709551616` |
| Positive, coefficient 29/2 | 55 | 28 | 6 | `-1356885473253615769/9223372036854775808` |

Both largest bounds are strictly negative. All nodes and all leaves
were visited by each complete replay. Certificate SHA-256 values are:

    E_variable_k_linear_negative_cover.json
    94ddb170a16bf4b222e1ede3e85c6a24537b6fa9c23cceb68f73c210f93c91fc

    E_variable_k_linear_positive_cover.json
    ec1bf64bc56f7fb84485be5c6f40477c3d7e3e65797f1c8f603f3473717c7751

The data, producers and independent checkers are in `computer_assisted`.
Complete replay records have suffixes `_dyadic_replay.json` and
`_fraction_replay.json`. The following tables print every interval and
multiplier, so their coverage is also directly inspectable without
following the binary tree.

## 5. Conclusion and joint use

Section 2 covers [0,1/16], while the complete tables cover [1/16,6].
Together with (1), they prove (3) for every endpoint-owned physical
normal and every central slope in [-6,6]. The choice of k may depend
on the slope cell, but is fixed throughout that cell and is always
nonnegative. It is therefore a valid multiplier on the original
physical separating slack.

Combining this theorem with the shoulder-owned theorem
`LINEAR_OUTER_SCALAR_ENVELOPES.md` gives an owner-independent outer
bound with coefficients 29/2 on positive central slopes and 16 on
negative central slopes. The central transfer theorem retains the
original common central square and pays these two slopes jointly.
The full assembly is in
`UNRESTRICTED_JOINT_FIVE_SQUARE_HIGH_FLOOR_CAP.md`.

## Appendix. Every complementary interval and multiplier

### Negative central slope

| Closed t interval | Numerator N in k=N/4096 |
|---|---:|
| [1/16, 159/1024] | 56365 |
| [159/1024, 127/512] | 57705 |
| [127/512, 349/1024] | 62684 |
| [349/1024, 111/256] | 62684 |
| [111/256, 539/1024] | 67476 |
| [539/1024, 317/512] | 67476 |
| [317/512, 729/1024] | 74157 |
| [729/1024, 103/128] | 74157 |
| [103/128, 919/1024] | 80263 |
| [919/1024, 507/512] | 80263 |
| [507/512, 301/256] | 54756 |
| [301/256, 697/512] | 70146 |
| [697/512, 99/64] | 75276 |
| [99/64, 887/512] | 81920 |
| [887/512, 491/256] | 81920 |
| [491/256, 1077/512] | 81920 |
| [1077/512, 293/128] | 81920 |
| [293/128, 681/256] | 81920 |
| [681/256, 97/32] | 81920 |
| [97/32, 871/256] | 81920 |
| [871/256, 483/128] | 81920 |
| [483/128, 1061/256] | 81179 |
| [1061/256, 289/64] | 81179 |
| [289/64, 673/128] | 79002 |
| [673/128, 6] | 79002 |

### Positive central slope

| Closed t interval | Numerator N in k=N/4096 |
|---|---:|
| [1/16, 159/1024] | 54594 |
| [159/1024, 127/512] | 54594 |
| [127/512, 111/256] | 52992 |
| [111/256, 317/512] | 52992 |
| [317/512, 729/1024] | 52992 |
| [729/1024, 103/128] | 52992 |
| [103/128, 919/1024] | 52992 |
| [919/1024, 507/512] | 52992 |
| [507/512, 1109/1024] | 52992 |
| [1109/1024, 301/256] | 52992 |
| [301/256, 1299/1024] | 52992 |
| [1299/1024, 697/512] | 52992 |
| [697/512, 1489/1024] | 52992 |
| [1489/1024, 99/64] | 52992 |
| [99/64, 887/512] | 52992 |
| [887/512, 491/256] | 52992 |
| [491/256, 1077/512] | 52992 |
| [1077/512, 293/128] | 52992 |
| [293/128, 1267/512] | 52992 |
| [1267/512, 681/256] | 52992 |
| [681/256, 1457/512] | 52992 |
| [1457/512, 97/32] | 52992 |
| [97/32, 871/256] | 52992 |
| [871/256, 483/128] | 52992 |
| [483/128, 1061/256] | 52992 |
| [1061/256, 289/64] | 52992 |
| [289/64, 673/128] | 52992 |
| [673/128, 6] | 52992 |
