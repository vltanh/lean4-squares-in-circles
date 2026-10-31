# Uniform orientation and actual terminal-port bounds for the unique-minus tip-owned return

Date: October 28, 2026 UTC. Author: cycles continuation. The three-fifths ratio theorem is a separately pinned root/cycles scalar input. Root and cycles independently obtained the lower vertical-port estimate below.

**Status: complete proposed uniform entry theorem, submitted for independent review.** In the entire original unique-V/minus-W return, the actual angle ratio satisfies L/K>2/3. The whole physical radius window then gives

    a>b,
    -1/2<B_T<1/60,
    E>5/24.

With the genuine original terminal moment and the actual physical boundary T, it also gives A_T>1/4. Thus the unchanged occupied endpoint cap may use min(A_T,E,4/5)>5/24. No small-port contradiction or closing-pocket capacity is claimed here. The remaining diagonal inequality and actual routing still require a final proof.

## 1. Complete original entry and notation

Use TERMINAL_HUB_AXIS_TIP_OWNED_POSITIVE_DOT_FULL_MASK_ENTRY.md at the frozen pin below. All its original contacts, positive magnitudes, true degrees, physical corners and full means remain. In particular,

    a,b,c,d>0, a^2+b^2=c^2+d^2=1,
    K=ad+bc>0, L=ac-bd>0, K^2+L^2=1,

    n=(a,b), k=Jn=(-b,a),
    m=(c,-d), l=Jm=(d,c),
    original VW normal=-k.

Keep the actual relative-interior singleton parameters, not chosen endpoints:

    0<tau<K-b<K,
    s=1-tau in(0,1),
    rho=a-(L/K)*(b+tau) in(0,1).

Restrict to the unique physical V corner. The full original V2 equations and the full-mask entry give

    X>Y>1/2, X^2+Y^2=R^2, R>=2,
    rho=1-(Y/X)*s,
    V=[X-1,X] x [Y-1,Y],
    M=(X-s,Y-1).

The actual physical W minus corner, including a physical plus/minus tie, is

    Z_W^-=(X-s+L-K,Y-1-K-L),
    |Z_W^-|=R.

Write

    C=1+L*(X-s)-K*(Y-1)>1/2,
    t=K*(X-s)+L*(Y-1)<=1/2.                       (1)

The complete preceding min-face proof is what makes this the exhaustive actual remaining W mask; no circle point is selected by coefficient size. A tie keeps both physical corners, even if one has zero individual coefficient.

Set

    z=L/K, r=Y/X, kappa=d/K=a-z*b,
    h=bc/K=b^2+a*b*z=1-a*kappa,
    D=X-1, E=Y-1+rho=Y-r*s.                       (2)

The positively oriented V-top frame is (-k,n). The unchanged original terminal application is

    S=(-A_T,B_T),

    A_T=E+b-a*h,
    B_T=D-a-b*h.                                  (3)

The original global horizontal/vertical frame has

    P=(a*D-b*E,b*D+a*E),
    S=P-(1,h),
    H_T=S_y=a*E+b*D-h=a*A_T+b*B_T.                (4)

The formulas in (3)--(4) use the original U3 torque and the same actual UT application; they remain valid for its full original mean if UT has positive shared length.

Sections 2--3 require only R>=2. Sections 4--6 explicitly add R^2<=1105/256. The terminal-height and diameter arguments add their complete original physical premises in Section 6.

## 2. One affine-circle comparison excludes every z<=2/3

First X-s>X-1>0 and Y>1/2 give

    -1/2<t<=1/2.                                  (5)

Put

    A0=1+K-s*L>0,
    B0=1+L+s*K>0.

Expressing the actual V circle equality in the orthonormal (m,l) coordinates of W and subtracting the actual minus-circle equality gives the exact identity

    C=1-(1-s^2)/(2*A0)+(B0/A0)*t,
    C^2+(1-t)^2=R^2.                              (6)

For clarity, if u=C-1, the V circle coordinates are
X=K*t+L*u+s and Y=L*t-K*u+1. Substitution and subtraction of (u+1)^2+(t-1)^2 give
2*A0*u=2*B0*t+s^2-1, which is exactly (6). All original quantities are unchanged.

Suppose z<=2/3. Then L<=2/sqrt(13), K>=3/sqrt(13), and K-L>0. Therefore A0>1. Also

    2*A0-B0
       =1+2K-L-s*(2L+K)
       >=1+K-3L
       >=1-3/sqrt(13)>0.                         (7)

The second lower bound follows because (1-3z)/sqrt(1+z^2) decreases on 0<=z<=2/3: its derivative is -(3+z)/(1+z^2)^(3/2).

At the scalar endpoint t=-1/2, formula (6) gives

    -1/2<C(-1/2)<1.

Indeed its intercept lies strictly between 1/2 and 1, and B0/(2*A0) lies strictly between zero and one by (7). Consequently

    C(-1/2)^2+(3/2)^2<13/4<4.                     (8)

At t=1/2 the same formula is

    C(1/2)=1+(L+s*K+s^2)/(2*(1+K-s*L)).

This is strictly increasing in s on [0,1]: its numerator is positive and has derivative K+2s>0, while its positive denominator decreases. Thus

    C(1/2)
       <=1+(1+K+L)/(2*(1+K-L))
        =1+(1+L)/(2K)
       <=(8+sqrt(13))/6.                          (9)

The last step uses
(1+L)/K=sqrt(1+z^2)+z<=(sqrt(13)+2)/3.
Every quantity in (9) is positive. Hence

    C(1/2)^2+1/4
       <=(86+16sqrt(13))/36<4,                    (10)

where sqrt(13)<29/8 follows from the exact squared reserve 9/64.

For the fixed actual s,K,L, C(t) is affine. Its squared norm C(t)^2+(1-t)^2 is convex on the entire closed interval [-1/2,1/2], so (8),(10) put every point of that interval strictly below 4. Equation (6) and R>=2 contradict this. Therefore the entire actual minus mask satisfies

    z=L/K>2/3, L>2/sqrt(13)>1/2.                  (11)

No physical pose, force ratio, normal or mean has been changed in this scalar comparison. The physical tie t=1/2 was explicitly retained.

## 3. The whole radius ratio and original orientation

The unique original V identity and the actual geometry give

    rho=a-z*(b+tau)<1-z*tau.

Together with rho=1-r*s and tau=1-s, this yields

    s>L/(L+K*r).                                  (12)

Apply THREE_FIFTHS_RATIO_BOUND_FOR_POSITIVE_DOT_MINUS_BOUNDARY_CORNER.md to the actual minus point, using (11),(12). Its complete scalar scope is R>=2, L>=1/2; it uses no upper radius or terminal premise. The result is

    r=Y/X<3/5,
    X>10/sqrt(34)>12/7.                           (13)

The strict rational comparison has squared reserve
50/17-144/49=2/833.

From the exact side and force identities,

    tau=(r-1+kappa)/(r+z)>0,
    kappa>1-r>2/5.                                (14)

This also forces the whole original n angle below 45 degrees. If b>=a, then a<=1/sqrt(2), and (11) gives

    kappa=a-z*b<=a*(1-z)<1/(3sqrt(2))<2/5,

contrary to (14). Thus

    a>b>0.                                       (15)

No two-circle V mask is assigned (12) or (14): that full physical-mask interface is a different completed input. This theorem concerns the unique physical V mask only.

## 4. The actual upper vertical port, uniformly over the full angle interval

Now assume the original upper radius R^2<=1105/256. Since Y>1/2,

    X<121/60,
    D<61/60,                                     (16)

with squared reserve
(121/60)^2-(1105/256-1/4)=31/57600.

Put epsilon=b+a*z=c/K. Because kappa=a-z*b>0, one has z*b<a, so

    epsilon-z=b-z*(1-a)
       =b*[1-z*b/(1+a)]>0.                       (17)

Write a=cos(alpha), b=sin(alpha), with 0<alpha<pi/2. The inequality kappa>0 gives alpha<atan(1/z), hence

    a>z/sqrt(1+z^2)=L.

Using (11),

    z*(1+a)> (2/3)*(1+2/sqrt(13))>1.              (18)

For the final strict sign it is enough that sqrt(13)<4. Equations (17)--(18) give epsilon>1/(1+a). Therefore, keeping h=b*epsilon,

    a+b*h
       =a+b^2*epsilon
       >a+b^2/(1+a)=1.

The actual port in (3) consequently obeys

    B_T<X-2<1/60.                                 (19)

This whole orientation argument keeps the actual strict parameters; no extremal orientation is substituted into a physical force equation.

## 5. The actual lower vertical port, uniformly over the full circle interval

From h=1-a*kappa and (14),

    a+b*h=a+b-a*b*kappa
            <a+b-(2/5)*a*b.

Let u=a+b in (1,sqrt(2)]. Then ab=(u^2-1)/2, and the last upper bound is

    u-(u^2-1)/5.

It increases throughout [1,sqrt(2)], since its derivative is 1-2u/5>0. Hence

    a+b*h<sqrt(2)-1/5,
    B_T>X-sqrt(2)-4/5.

Use X>12/7 from (13) and sqrt(2)<99/70. Their exact comparison gives

    B_T>12/7-99/70-4/5=-1/2.                      (20)

Thus (19)--(20) establish the complete actual vertical box

    -1/2<B_T<1/60.                                 (21)

Root independently obtained the same whole lower bound from (13)--(14). The proof printed here supplies the exact calculation rather than treating that agreement as an independent review.

## 6. Genuine terminal torque and actual physical boundary force a usable cap

For this section, retain a complete original loaded boundary path V,W,...,T with 3 through 6 vertices, genuine endpoint T2, and the original U3 spokes to V,W,T. These are the literal current original D02 premises. Keep every W force and the whole path; no W2 surrogate is used.

At the actual V-owned VW singleton,

    det(M,-k)=-(X-s)<0.

The degree-free boundary-pair moment lemma identifies the clockwise boundary order for this original edge. The boundary angular-order theorem puts the rest of the same actual path in that same direction. At the genuine T2 endpoint, the moment of the incoming path force is therefore strictly negative. Its original torque equation makes the moment of the positive U-to-T force strictly positive. That unchanged normal is West, so

    H_T=det(S,West)=S_y=a*A_T+b*B_T>0.              (22)

This proves the height condition from the actual path and true T2. It is not a hypothesis inserted into a scalar surrogate.

Every actual physical boundary unit containing S satisfies its exact diameter inequality

    |S|>=R-sqrt(2).

For R>=2,

    (R-sqrt(2))^2>12/35,                           (23)

because sqrt(2)<99/70. This uses the actual T and unchanged original UT application, including a full shared mean if the local caller has one.

First A_T must be positive. Otherwise (22) requires B_T>0. By (15), b/a<1; hence -A_T<(b/a)*B_T<1/60, while (19) gives B_T<1/60. Then |S|^2<1/1800, contradicting (23). Thus A_T>0.

If A_T<=1/4, the entire box (21) gives

    |S|^2=A_T^2+B_T^2<1/16+1/4=5/16<12/35,

whose final reserve is 17/560. Therefore

    A_T>1/4.                                     (24)

The incoming V application has the further exact coordinate bound

    E=Y*(1-s/X)
       >(1/2)*(1-1/X)
       >(1/2)*(1-7/12)=5/24,                     (25)

using 0<s<1 and (13). Thus the actual possible weaker endpoint cap level

    q=min(A_T,E,4/5)

satisfies

    5/24<q<=4/5<9/10,
    A_T>=q, E>=q.                                (26)

Equation (26) is a bound on unchanged actual coordinates. It does not by itself prove that every extra unit lies in the corresponding cap.

## 7. Exact scope of the remaining work

This complete entry leaves only the following additional scalar and geometric requirements for the weak-cap matcher:

    A_T-B_T<199/250,

and a proof that the actual occupied crosscut routes every entire extra into x<=-q and its stated angular cone.

Indeed, if the displayed diagonal bound were established, (21),(23) would already force B_T>-7/20. If -1/2<B_T<=-7/20, then A_T>0 and A_T<199/250+B_T give

    |S|^2<(199/250+B_T)^2+B_T^2.

The right side is convex on [-1/2,-7/20], and its two endpoint values are

    21101/62500<12/35,
    40177/125000<12/35,

contradicting (23). This is an implication only; the diagonal inequality is not claimed by the present source.

For the literal original D02.L01345 substitution U=2,V=1,W=0,T=3, every original equation and all nine units remain. The present theorem is a uniform completed entry for the unique-minus feature, not a completed original row. No new fine identifier or checkbox credit is requested.

## 8. Exact direct inputs

| Complete source | SHA-256 | Exact use |
| --- | --- | --- |
| TERMINAL_HUB_AXIS_TIP_OWNED_POSITIVE_DOT_FULL_MASK_ENTRY.md | 1e9e597ad4b13995909cdac5d204b111d20ef305768fe6d44def11264e4a4c49 | Entire actual V-owned chart, original means, true U3/V2, every W physical corner and tie, X>Y, actual terminal formulas |
| THREE_FIFTHS_RATIO_BOUND_FOR_POSITIVE_DOT_MINUS_BOUNDARY_CORNER.md | 692044ebc896f0464fb2b9bf5d6ae07db38f8cfd7ab29054dd47bbcd5b554fdc | Whole continuous r<3/5 theorem, only after the actual L and s premises are proved |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original force, torque, strict singleton supports and complete physical circle coefficient conventions |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 | Degree-free physical boundary-pair moment/order lemma only |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Same actual loaded path order and its genuine endpoint edge |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal unchanged graph, load mask, true-degree mapping and three retained extra units |

The entry source has the separate full independent cycles review at SHA-256 77623fdce8cb6d780ce745a788d52d21719bf796d4ba717954784a4ae14252c8. The ratio input is root/cycles work and has the separate complete house review REVIEW_THREE_FIFTHS_MINUS_RATIO_SCALAR_HOUSE_2026_10_28.md at SHA-256 4c5f4772fce8ee0d243f82c603358b33b853d42285f49fb320d33c7e4b993cb5. This manuscript does not transfer authorship agreement into review credit.

No actual normal, side parameter, mean or physical corner has been changed. No W equilibrium has been imposed. No Lean compilation, CI, pose enumeration, numerical optimization, remote write or shared-ledger edit was used.

