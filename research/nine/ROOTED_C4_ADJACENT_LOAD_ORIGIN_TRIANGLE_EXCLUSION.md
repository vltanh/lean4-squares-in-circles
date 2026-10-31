# A terminal adjacent-load C4 cannot attach to an origin-interior triangle

Date: October 26, 2026.

**Status: accepted complete whole load-mask exclusion after full root and independent reviews in `REVIEW_C4_ADJACENT_LOAD_ORIGIN_TRIANGLE_ROOT_2026_10_26.md` and `REVIEW_C4_ADJACENT_LOAD_ORIGIN_TRIANGLE_GLOBAL_2026_10_26.md`.** Both reviews pin the unchanged mathematical source before this acceptance-only status edit. This retains the possible original circle load at the terminal root until it is proved zero. It does not close the entire C3.334 cell, whose other rooted four-body branches retain their own obligations.

Keep all nine original physical unit squares and the common compatible selected certificate. Work initially in 79/40<=R<=sqrt(1105)/16. The accepted same-nine theorem `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md` supplies

    2<R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60.                              (1)

Suppose A,H,C form an actual positive triangle and O belongs to the open interior of A. Each of that triangle's complete external systems has zero origin moment. At H the only external positive pair forces are those of the actual terminal C4

    H-U-V-W-H.

The private bodies U,V have true positive degree two and positive circle loads F_U,F_V. The private W has true positive degree two and zero circle load. H keeps its full actual circle resultant G_H and its two middle-triangle forces. All other physical bodies stay in place.

**Theorem.** This entire original configuration is impossible.

In the intended C3.334 chain, A is the intact end-petal root, H is the four-cycle articulation, and C is the untouched true loaded tip of the middle triangle. The theorem below uses the origin-interior and full-moment hypotheses exactly as stated. It does not replace G_H+F_U+F_V by the private-branch sum before proving G_H=0.

## 1. Exact channel geometry and the complete root-normal signs

The true unloaded W transmits a positive force of magnitude lambda. The physical bypass U touches both channel endpoints H,V. `UNIT_BYPASS_NORMAL_CHANNEL.md` gives reserve exactly one and transverse separation of U,W. Rotate and reflect the entire configuration so that

    e=e_x,
    W=[alpha,alpha+1] times [z,z+1],
    P=(alpha,y_0) in H intersect W,
    P_V=(alpha+1,y_0) in V intersect W,
    y_0 in [z,z+1],
    H subset {x<=alpha},
    V subset {x>=alpha+1},
    U subset {y>=z+1}.                                    (2)

Let Q be the unchanged H-U application, n the actual unit normal from H toward U, and mu>0 its magnitude. Let g be the actual U-V normal, of magnitude gamma>0. Then

    Q_x<=alpha,          Q_y>=z+1>=y_0,
    alpha+1<=d,          alpha<=d-1<1/60.                 (3)

The last bound is the sharp support bound on the contained V. Summing the true private-body equations gives, without using any truncated H equation,

    F_U=mu n-gamma g,
    F_V=lambda e+gamma g,
    M:=F_U+F_V=mu n+lambda e,
    mu det(Q,n)+lambda det(P,e)=0.                       (4)

The exact local root-feature calculation in Sections 1--3 of `TRIANGLE_C4_ADJACENT_LOAD_EXCLUSION.md` needs only (2)--(4), before that source invokes its old intact-petal force. Here is its whole required geometric cover.

First n_x>=0. If n_x<0, the full unit support-span lemma at the minimum-n point Q of U gives max_U(x-Q_x)<1. But U has an actual point in V with x>=alpha+1, whereas Q_x<=alpha, a contradiction. This retains every actual support feature and mean.

If n_y<0, the H support inequality gives

    0>=n.(P-Q)=n_x(alpha-Q_x)+n_y(y_0-Q_y)>=0.

Thus Q_y=y_0=z+1. If n_x>0 it also gives Q=P; the support excludes any H point on its right support face below P. If n_x=0, n=-e_y and all of H lies above y=y_0, with the same consequence. The actual H-W contact is the singleton P, a vertex of both H and W, with e a W side-axis normal. This contradicts the existing strict point-only vertex/vertex convention. Therefore

    n=e, or n_x>=0 and n_y>0.                             (5)

In the parallel case n=e, H must own this side axis. Otherwise its right support is a single vertex P=Q. The strict singleton convention forces P to lie in the relative interior of W's left side, since a W endpoint would again be a vertex/vertex contact with a side-axis normal. W then occupies the entire right local half-plane near P, and overlaps the distinct U which also contains P on that side. Thus the whole parallel alternative has an actual H side normal e.

## 2. Every positive channel height is already geometrically impossible

Suppose alpha>0. Equations (3) imply d>1 and R>sqrt(17)/2. The complete orientation-uniform cap lemma in `FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md`, Section 1, applies to V, all of whose points have x>=alpha+1>1>59/60. Every V point has direction within

    beta=arctan(13/20)

of e. The actual point Q belongs to the boundary square U, so

    |Q|>=R-sqrt(2)>3/5,
    Q_x<=alpha<1/60,
    angle(e,Q)>arccos(1/36).                              (6)

Choose the actual U-V application T. It belongs to V and to the same boundary U as Q. The local all-orientation angular-shadow theorem in `BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md`, Section 2, needs only R>=sqrt(17)/2 and gives U shadow length strictly less than omega=arctan(23/16). No seven-cycle premise enters that local statement. Hence

    angle(e,Q)<beta+omega.

But beta+omega<pi/2 and

    cos(beta+omega)=21/sqrt(446665)>1/36,

the final comparison being 756^2=571536>446665. This contradicts (6). This argument retains every root load, tip mask, actual mean and orientation. We may therefore assume

    alpha<=0.                                             (7)

## 3. The actual private force signs, including the parallel root case

Each U,V is truly loaded degree two and has the other as a physical boundary neighbor. The complete proper-concurrence theorem `TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Lemma 2.1, gives positive radial concurrence points q_U,q_V and the actual proper ports. Their two circle-resultant directions are distinct and nonparallel, by the full boundary order and acute-contact bounds.

If n=e, (4) gives mu Q_y+lambda y_0=0. Together with Q_y>=y_0, this implies

    Q_y>0>y_0.

Indeed equality would make both heights zero, hence both positive endpoint concurrences horizontal, contradicting their nonparallel resultant directions. Their proper H/channel ports preserve these heights. Thus F_Uy>0>F_Vy in the parallel case, and M_x=mu+lambda>0.

Now suppose n_y>0. The genuine root-line intersection is

    b_0=(Q_y-y_0)/n_y>=0,
    q=Q-b_0 n,
    a_0=alpha-q_x>=0,
    P=q+a_0 e,             Q=q+b_0 n.                     (8)

The nonnegative a_0 follows from n_x>=0 and Q_x<=alpha. Endpoint properness and the real width-one channel give

    q_U=q+u n,             u>=0,
    q_V=q+v e,             v>=a_0+1>0,
    q_V-q_U=l g,           l>0.                          (9)

The last strictness uses the distinct positive endpoint rays. Equation (4) gives det(q,M)=0, so q=tau M for a real tau. In the independent basis n,e, equations (4),(9) give

    q_U=(tau mu+u)n+tau lambda e,
    F_U=(mu+gamma u/l)n-(gamma v/l)e.

Since q_U is a strictly positive multiple of F_U and v>0, comparison of their e coefficients gives tau<0. Therefore

    q=-t M, t>0,
    q_x<0,       q_y=y_0<0,
    M_x>0,       M_y>0.                                   (10)

The proper V port preserves q_Vy=y_0, so F_Vy<0. Since F_U+F_V=M and M_y>0, F_Uy>0.

Thus both root alternatives have the common unchanged signs

    y_0<0,
    M_x>0,
    (F_U)_y>0>(F_V)_y.                                   (11)

In the nonparallel case (8),(10) additionally give a strictly negative terminal concurrence with both actual root ports proper. All possible individual zero circle weights remain in these statements.

## 4. The possible circle force at H is zero: no load is deleted

Assume for contradiction that G_H is nonzero. Then H,U,V are three physically boundary squares in their actual path order. The full boundary-path cone theorem applies to their original positive total circle loads and gives

    F_U=a G_H+b F_V,                 a,b>0.                (12)

Every H point has x<=alpha<=0, so (G_H)_x<=0. From M=F_U+F_V and M_x>0, equation (12) gives (F_V)_x>0. Since (F_V)_y<0<(F_U)_y and the true U,V boundary resultants have positive dot product, (F_U)_x>0. Equation (12) then also gives (G_H)_y>0.

Every physical circle corner of H has strictly negative x coordinate. For an H-owned channel axis, the right-face corners are strictly nearer the origin than the corresponding left-face corners, because alpha<=0. Otherwise P is H's unique rightmost vertex; it is an actual contact with W and cannot be a circle point, while all other H vertices have x<alpha<=0. This is the usual impossibility of sharing a containing-circle point, including all masks.

Consequently write G_H=(-g,h) with g,h>0. Among its original positive-weight circle corners choose

    z_H=(-X,Y),
    X>0, Y>0,               Y/X>=h/g.                     (13)

Such a corner exists because h/g is the weighted mean of the corner ratios Y_j/X_j with positive weights proportional to their actual circle weights times X_j. A positive mean has a positive term at least that mean. No original weight is changed and no artificial force is introduced.

Acuteness of the physical H,U contact gives G_H.F_U>0. Thus

    (F_U)_x/(F_U)_y < h/g <=Y/X.                           (14)

Because (F_V)_y<0, one of V's original positive-weight circle corners z_V=(x_V,y_V) has y_V<0. The physical U,V acute-contact theorem gives F_U.z_V>0. Equations (11),(14) imply

    x_V>0,
    (-y_V)/x_V < (F_U)_x/(F_U)_y <Y/X.

Both selected actual corners have norm R. Comparing their ratios therefore gives

    x_V>X.                                                (15)

We now contradict (15) using the complete physical H frame, with no degree-two equation at H.

### 4.1. The selected H corner in an owned side frame

If H owns e, write H=[alpha-1,alpha] times [l,l+1]. Since y_0<0 belongs to its vertical interval and the selected corner has positive height, it is the upper-left corner, with

    X=1-alpha,             0<Y=l+1<1.

Set w=1. Then X=w-alpha and Y^2<2-w^2.

### 4.2. The complete tilted minimum-side frame

If H does not own e, P=(alpha,y_0) is its unique rightmost vertex. Label its actual inward axes

    u=(-a,b),              v=(-b,-a),
    a,b>0,                 a^2+b^2=1,
    H=P+[0,1]u+[0,1]v.

The points P and P+v have negative height. A positive-height circle corner is therefore P+u or P+u+v. If it were P+u=(-X,Y), then 0<Y<b<1 and R>2 would give X>sqrt(3)>a. The actual further corner z_H+v would satisfy

    z_H.v=Xb-Ya>b(X-a)>0,

so its squared norm would exceed R^2+1, impossible. Thus the selected original circle corner is the opposite vertex P+u+v. Set w=a+b. Then

    1<w<sqrt(2),
    X=w-alpha,
    0<Y=y_0+b-a<b-a,
    Y^2<2-w^2.

Both the aligned and tilted cases consequently give

    1<=w<=sqrt(2),
    X=w-alpha,
    X^2=R^2-Y^2>2+w^2.                                  (16)

For every w>=1,

    4(2+w^2)-(1+w+sqrt(2))^2
      =3(w-1)^2+(4-2sqrt(2))(w-1)+6-4sqrt(2)>0.

Thus (16) yields

    2X>1+w+sqrt(2).                                      (17)

The true channel makes the minimum V x coordinate alpha+1. A unit square's horizontal width is at most sqrt(2), so the actual selected V corner obeys

    x_V<=alpha+1+sqrt(2)
        =1+w+sqrt(2)-X<X,

contrary to (15). This excludes every possible positive circle load at H. Hence

    G_H=0.                                                (18)

The proof allows H to remain physically boundary with zero circle weight; physical clearance is not needed. It retains every physical one-/two-corner mask and every original individual zero weight. The conclusion is the vanishing of the entire actual circle force, obtained before using any private-branch ray restriction.

## 5. The actual middle triangle now supplies the final contradiction

By (18), the full external system at H in the middle triangle has resultant exactly M=F_U+F_V. Its origin moment is zero by the summed original private moments (4). The other full external systems retain their stated zero origin moments. Since O belongs to int A, the accepted `ROOTED_ORIGIN_TRIANGLE_EXTERNAL_RAY_RESTRICTION.md` gives

    H intersect {-s M:s>=0} is empty.                    (19)

In the parallel case, H owns e, M is a positive multiple of e, and the actual port heights Q_y,y_0 strictly straddle zero. The actual H side contains (alpha,0). By (7), this is a point of the forbidden nonpositive M ray, contradicting (19).

In the nonparallel case, (8),(10) give q=-tM, t>0, and proper root ports Q=q+b_0 n, P=q+a_0 e. The point q is excluded from H by (19), so both a_0,b_0 are strictly positive. With

    Z=mu/b_0+lambda/a_0>0,

the positive convex combination of Q,P with weights (mu/b_0)/Z and (lambda/a_0)/Z belongs to H and equals

    q+M/Z=(1/Z-t)M.

Hypothesis (19) forces its scalar coefficient to be strictly positive. But M_x>0, so this actual H point has positive x coordinate, whereas H lies in x<=alpha<=0. This is the final contradiction.

Every channel orientation, parallel/nonparallel root pair, root circle load, actual mask, side owner, original mean and individual zero weight has been covered. No degree-two equation was imposed on H and no root circle force was dropped before (18).

## 6. Exact original-family scope

For the full no-bridge C3.334 chain with intact petal at A, middle triangle A-H-C and terminal four-cycle H-U-V-W-H, the adjacent private-load mask {U,V} and its reflected mask {V,W} satisfy the theorem. The origin-interior premise follows from the actual intact petal, and the branch moment sums keep every other original force. The root H has its true degree four throughout. The one remaining arbitrary physical completion square is retained and is needed in the same-nine R>2 input just as in its original theorem.

The single-private-load masks, opposite-private-two-load mask, full-three-private-load mask, and terminal hub-diamond branch have not been silently included in this statement. This is a complete adjacent-load exit within the original full-family cover, not a new coarse cell or a claimed complete C3.334 proof.

No numerical pose, Lean compilation, CI, remote action, or shared-ledger edit is used.
