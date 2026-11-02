# Low central floor: the complete left-side extra exclusion

This note gives the exact mathematical caller and finite certificate for the following statement over the unchanged physical `000/01` domain:

> If y_P-h_P<=1/10, every extra square S with x_S<=-29/60 is below M1.

The result retains arbitrary independent orientations and all original physical constraints. It combines a short direct inequality for x_P<=7/100 with a complete four-dimensional exact interval table for the complementary interval. It is not a closure of the entire nine-square mask. The remaining central extras are not omitted or presumed impossible.

The complete table is `computer_assisted/left_above_extra_certificate.json`; its independent exact arithmetic replay is `computer_assisted/verify_left_table_exact.py`. The latter imports neither the floating discovery program nor an external solver. Its report is `computer_assisted/left_exact_verification_report.json`. Deliberately invalid split, incomplete-tree, and false-leaf controls were all rejected; see `computer_assisted/left_damaged_certificate_controls.json`.

## 1. Whole-mask inputs and notation

Use the established common upward routing of L,P,R. Write

    p=h_P,   r=h_R,   x=x_P,   y=y_P,   X=x_R,   Y=y_R,
    rho=91/60,   Q=1105/256,
    C=451/810,   B=263/480,   K=2093/1800,
    d0=1409/1800,   J=29927/30000.

The proof in `WHOLE_MASK_SHOULDER_AND_NORMAL_REDUCTIONS.md`, including Section 2.1, gives

    y_L,y_R>3/4,
    every side extra has y_S<7/20,
    if a side extra is above its main, then
        y_S>-113/600,
        29/60<=|x_S|<B,
        |x_S-x_Main|<1/15.

The original main-center cone bound gives y_Mi>-139/120. Existing physical main clearance gives |y_S-y_Main|>97/100. The original central bounds are

    -1/12<x<23/60,
    23/30<X<13/12,
    y_P-y_M2>29/30,        hence y>-23/120,
    1/2<=p,r<=1/sqrt(2),   y<=p+1/10.

Every pair of physical units satisfies center distance at least 1+|h_A-h_B|, proved in Section 4 of `LOW_CENTRAL_FLOOR_RIGHT_SIDE_EXTRA_BARRIER.md`.

## 2. The two weighted caps and their shared main span

Put

    A0=-x_0-h_0,         A3=x_3-h_3,
    a=46, b=27/2, T=211/4.

The actual four-chain gives A0+A3>=2. The universal center bound gives A0,A3<61/60, so A0,A3>59/60. The established physical two-square caps give

    a A0+b(-x_L-h_L)<=T,
    a A3+b(X-r)<=T.                                    (1)

Since the L--P comparison is actual, -x_L-h_L>=p-x. Thus (1) implies the following necessary inequalities:

    x>p-C,          X<r+C,
    D:=X-x <=1+r-p,                                   (2)

and

    A3 >= A:=max(59/60,157/184+(27/92)(p-x)).            (3)

For example, (3) follows from

    A0 <=T/a-(b/a)(p-x),        A3>=2-A0.

The D bound follows by adding the two caps and using A0+A3>=2, since 2T=2a+b. These are consequences of the original physical caps; they do not replace the two main endpoints by independent free centers.

## 3. R is above P throughout the low-floor domain

Suppose instead y>=Y. Since Y>3/4 and y<=p+1/10, we would have p>13/20. Equation (2) then gives

    x>13/20-451/810=151/1620>9/100,
    D<13/12-9/100=149/150.

Also 0<=y-Y<1/sqrt(2)+1/10-3/4<3/50. The squared center distance would be less than

    (149/150)^2+(3/50)^2=22282/22500<1,

contradicting the two center disks. Consequently

    E:=Y-y>0,           D>=E,                           (4)

where the second inequality is the original P--R cone condition. The physical center-distance bound therefore also implies

    2D^2 >=(1+|p-r|)^2.                               (5)

## 4. A hypothetical left-side extra forces P above it

Assume that a left-side extra S is above M1, and write s=h_S. Its x-coordinate belongs to (-B,-29/60], and its height is below 7/20. From (4), the shoulder lower bound, and X<13/12,

    y=Y-E>=Y-D>3/4-X+x>x-1/3.                         (6)

If y<=y_S, its vertical gap from P is less than 41/60-x, and its horizontal gap is less than x+B. By (2), x>1/2-C=-23/405, while x<23/60. The convex quadratic

    (x+B)^2+(41/60-x)^2

is below one at both endpoints of [-23/405,23/60], and hence throughout. At the right endpoint it is (149/160)^2+(3/10)^2<1; at the left endpoint it is less than (1/2)^2+(3/4)^2=13/16<1, since B-23/405<1/2 and 41/60+23/405<3/4. This contradicts center distance at least one. Therefore P is above S.

## 5. Eliminate the left extra without losing its orientation cost

Set V=y-y_S>0. The near-vertical S--M1 center geometry and the orientation-aware main bound give, exactly as in the right-side proof,

    y_S>-139/120+max(1,s+12/25)-1/225,
    V<y+K-max(1,s+12/25).                              (7)

The P--S horizontal gap is less than x+B. Their center distance is at least 1+|p-s|. Consequently any such S must satisfy

    (x+B)^2+[y+K-max(1,s+12/25)]^2>(1+|p-s|)^2,        (8)

with the square bracket positive. The strictness comes from the strict bounds on both positive gaps.

The most favorable value of s in (8) is s=p. Here is the complete reduction. Put H=13/25 and k=y+293/1800. The positive upper vertical gap is

    k-max(s-H,0).

For fixed p, minimize

    (1+|p-s|)^2-max(k-max(s-H,0),0)^2                  (9)

over s in [1/2,1/sqrt(2)]. If p<=H, it decreases up to s=p and increases afterwards. If p>=H, it decreases on s<=H; on H<=s<=p its derivative, while the second term is positive, equals

    -2(1+p-k-H)<0,

because y<=p+1/10 gives k<=p+473/1800 and hence 1+p-k-H>=391/1800>0. On s>=p its derivative is 2(1-p+k+H)>0 whenever that second term is positive. Where it vanishes, the first term alone has the same required monotonicity. The existing positive vertical gap ensures k>0. This proves that (9) is minimized at s=p in every case.

Since x+B<149/160<1, a nonpositive resulting vertical upper bound would itself be impossible. Thus (8) implies

    v:=y+K-max(1,p+12/25)>0,
    (x+B)^2+v^2>1.

Equivalently,

    y>y_low:=max(1,p+12/25)-K+sqrt(1-(x+B)^2).         (10)

This eliminates S only after retaining its original physical pair constraints through (7)--(9). It is not a projection-only proxy assumption.

## 6. Direct hand closure for x<=7/100

From (7), for every s one has

    V<d0+max(p-s,0).

The positive horizontal gap is less than x+B<=1483/2400. Put t=max(p-s,0). Then

    (1+t)^2-(1483/2400)^2-(d0+t)^2
       =281903/51840000+2t(1-d0)>0.

This contradicts the center-distance bound 1+|p-s|>=1+t. It covers the entire x<=7/100 branch, including its equality face.

It remains to treat x>=7/100; overlap at the boundary is harmless.

## 7. Four exact variables for the remaining branch

For each unsigned orientation use its slope parameter t in [0,1]:

    a(t)=1/sqrt(1+t^2),      b(t)=t/sqrt(1+t^2),
    h(t)=(a(t)+b(t))/2,     k(t)=(a(t)-b(t))/2.

Thus p=h(tP), r=h(tR), with associated aP,bP,kP and aR,bR,kR. Both independent physical chiralities remain allowed. The exact closed parameter box is

    tP,tR in [0,1],
    x in [7/100,23/60],
    X in [23/30,13/12].                               (11)

The next formulas bound Y and eliminate y,Y without sampling them.

### 7.1. The R-corner upper bound

For one physical chirality the two relevant corners are (X+kR,Y+r) and (X+r,Y-kR). For the other they are (X+r,Y+kR) and (X-kR,Y+r). Since Y>3/4>kR, their exact disk constraints imply

    U_plus =min(sqrt(Q-(X+kR)^2)-r,
                kR+sqrt(Q-(X+r)^2)),
    U_minus=min(sqrt(Q-(X+r)^2)-kR,
                sqrt(Q-(X-kR)^2)-r),
    Y <= U:=max(U_plus,U_minus).                      (12)

Allowing the larger chirality bound is a valid relaxation.

### 7.2. The adaptive original-endpoint inset top

The original endpoint E=M3 has h_3<8/15 and k_3=sqrt(1/2-h_3^2). The established chord estimate h_3+k_3>=1-(73/1000)(h_3-1/2) gives h_3+k_3>=J. Its retained outward-quadrant corner bound yields

    Q >= (x_3+k_3)^2+(|y_3|+h_3)^2
       >= (A+J)^2+(|y_3|+h_3)^2.

For completeness, h+sqrt(1/2-h^2) is concave on [1/2,8/15] and equals 1 at the left endpoint. At the right endpoint,

    (1/2-(8/15)^2)-(13927/30000)^2
       =38671/900000000>0.

Thus its right endpoint is greater than J=29927/30000, and the chord from (1/2,1) to (8/15,J) is the stated affine lower bound. The outward-quadrant corner estimate is valid for either physical chirality: x_3>|y_3|, so the alternative offset order (x_3+h_3)^2+(|y_3|+k_3)^2 is at least (x_3+k_3)^2+(|y_3|+h_3)^2.

Because h_3+g_3>=1, the top of the original endpoint's inset obeys

    y_3+g_3 >=g_3-|y_3|
              >=1-sqrt(Q-(A+J)^2).

Retain also its previous strict lower bound 221/600, and put

    c_A=max(221/600,1-sqrt(Q-(A+J)^2)).                (13)

This is the coupling of the left weighted cap, actual main span, and original right endpoint. Replacing it by the constant 221/600 would be insufficient for the present certificate.

The endpoint x-coordinate is below rho, and g_3>15/32. Hence

    g_3-(x_3-X)>X-503/480=:delta.

The separating-axis theorem between R and the endpoint's inset has only the two coordinate directions and R's physical axes. Horizontal separation is impossible because x_3-X<3/4<g_3+r. Vertical separation requires Y-y_3>=g_3+r. An R-owned separator gives either of the two other alternatives. Consequently

    Y >=c_A+min(r,(1/2+delta*bR)/aR,
                   (1/2+delta*aR)/bR).               (14)

The last alternative is omitted when bR=0; its numerator remains positive throughout (11), so its limit is positive infinity. This handles the aligned boundary without division by zero.

### 7.3. The genuine P--R physical side-normal condition

The reduced relative orientation has

    cos gamma+sin gamma
       >=aP*aR+bP*bR+|aP*bR-bP*aR|.

Every original physical separating axis has unsigned components (aP,bP), (bP,aP), (aR,bR), or (bR,aR). Since D>=E>0, the largest possible absolute projection in the first two cases is at most aP*D+bP*E, and similarly for R. Thus physical nonoverlap necessarily gives

    max(aP*D+bP*E,aR*D+bR*E)
       >=s0:=(1+aP*aR+bP*bR+|aP*bR-bP*aR|)/2.         (15)

By (10) and (12), E=Y-y<U-y_low. Replacing E by that upper bound in (15) can only increase its left side. This provides a necessary inequality entirely in (11). In particular, the table has not replaced physical nonoverlap by center disks alone.

## 8. The exact exclusion table

For each box in (11), compute rational intervals for the displayed functions. Every terminal box is excluded by one of the following strict tests. Each expression in the middle column must be nonnegative at a physical witness; the table proves its interval upper bound negative. Rule 4 uses its separately stated lower-bound test.

| Rule | Necessary expression or test | Terminal boxes |
|---|---|---:|
| 0 | x-p+C | 157 |
| 1 | r+C-X | 12 |
| 2 | 1+r-p-D | 19 |
| 3 | 2D^2-(1+abs(p-r))^2 | 277 |
| 4 | A<=61/60 | 0 |
| 5 | p+1/10-y_low | 104 |
| 6 | U-c_A-minimum reach from (14) | 3060 |
| 7 | U-y_low | 0 |
| 8 | max(aP*D+bP*(U-y_low),aR*D+bR*(U-y_low))-s0 | 8115 |
| **Total** | **Complete closed parameter box (11)** | **11744** |

All 11,744 leaves passed a separate exact arithmetic replay. The complete binary tree has 23,487 nodes and maximum depth 33. Its positive exclusion reserves all exceed 1/10000000.

The certificate format is a preorder list. Values 0,1,2,3 split that coordinate at its exact rational midpoint, and a negative value -j-1 assigns leaf rule j. Starting from the four rational intervals (11) determines every box uniquely. Each split covers its parent's closed box, with harmless overlap on the split face. The verifier rejects incomplete trees, trailing nodes, invalid coordinate indices, or nonpositive leaf reserves. There are exactly one more leaves than internal nodes.

Every interval endpoint and arithmetic operation in replay is a `fractions.Fraction`. Square roots are enclosed by integer square roots at scale 2^44, and the verifier explicitly checks the squared lower and upper enclosures. It uses monotonicity of a,k and b,h on [0,1], whose derivative signs follow directly from the formulas in Section 7. This is a finite rational table proof. The floating discovery program only selected subdivisions and rule tags; none of its arithmetic is trusted by replay.

Thus (11) has no witness satisfying the necessary consequences of a left-side extra above M1. Together with Section 6, every x_P in the original mask has been covered. The theorem follows.

## 9. Consequences and exact remaining scope

Combine this theorem with `LOW_CENTRAL_FLOOR_RIGHT_SIDE_EXTRA_BARRIER.md`. Under y_P-h_P<=1/10, every side extra lies below its corresponding inner main. Consequently every occupied extra side forces that main above -7/20.

The earlier central adjacent-proxy barrier gives

    y_P-h_P>min(y_M1,y_M2)+869/1860.

The low-floor hypothesis therefore forces

    min(y_M1,y_M2)<1/10-869/1860=-683/1860<-7/20.

At least one side has no extra. Since a side already contains its selected shoulder and has capacity at most two outsiders in the strict-radius domain, the two extras cannot both occupy the other side. Therefore at least one extra is central, |x|<29/60. If both inner mains are below -7/20, both extras are central.

These are whole-mask reductions. They do not exclude the central-extra configurations, do not change the fixed mask count, and do not prove unrestricted equality. The all-nine-square mask remains open until those configurations and the complementary central-floor branch are assembled.
