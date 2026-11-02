# Low central floor forces both extra squares into the central strip

This is a computer-assisted hand/table proof over the complete routed `000/01` predicate. All centers and independent physical frames remain moving, and all original physical squares remain present. No Lean, Lake, or CI is used.

**Theorem.** If `y_P-h_P<=1/10`, then

    y_M1,y_M2<-7/20.

Consequently both additional squares F,G have `|x|<29/60`. Each is either above P or below both inner main centers, and at most one is below both.

The final section combines these complete reductions with the central-upper whole-floor theorem and the completed unrestricted joint cap. The optional separate bound y_P<16/25 is not needed and is not a dependency of this proof.

## 1. Reuse of the already derived four-variable physical reduction

Use the notation and exact physical inequalities of Sections 1--3 and 7 of `LOW_CENTRAL_FLOOR_LEFT_SIDE_EXTRA_EXACT_PROOF.md`:

    p=h_P, r=h_R, x=x_P, X=x_R, y=y_P, Y=y_R,
    D=X-x, Q=1105/256, C=451/810, J=29927/30000.

The following facts did not use its hypothetical left-side extra and therefore hold on the entire low-floor mask:

    x>p-C,          X<r+C,
    W:=1+r-p-D>=0,
    Y>y,           D>=Y-y,
    2D^2>=(1+|p-r|)^2,
    A=max(59/60,157/184+(27/92)(p-x))<=A3<61/60.

The orientation parametrization, including both physical chiralities, is

    a(t)=1/sqrt(1+t^2), b(t)=t/sqrt(1+t^2),
    h(t)=(a(t)+b(t))/2, k(t)=(a(t)-b(t))/2.

The complete closed box is

    tP,tR in [0,1],
    x in [-23/405,23/60], X in [23/30,13/12].          (1)

The left proof derives from original R corners the upper bound

    Uplus=min(sqrt(Q-(X+kR)^2)-r,
              kR+sqrt(Q-(X+r)^2)),
    Uminus=min(sqrt(Q-(X+r)^2)-kR,
               sqrt(Q-(X-kR)^2)-r),
    Y<=U=max(Uplus,Uminus).                          (2)

From the original endpoint M3, the shared cap span, and its retained physical inset, it also derives

    c_A=max(221/600,1-sqrt(Q-(A+J)^2)),
    delta_R=X-503/480,
    Y>=c_A+min(r,(1/2+delta_R*bR)/aR,
                  (1/2+delta_R*aR)/bR).             (3)

The last branch is omitted at bR=0. Its numerator is positive throughout (1). Finally the original P--R physical nonoverlap gives

    max(aP*D+bP*(Y-y),aR*D+bR*(Y-y))>=s_PR,
    s_PR=(1+aP*aR+bP*bR+|aP*bR-bP*aR|)/2.           (4)

No side-extra hypothesis enters (1)--(4). Their proofs, including the two chirality corner orders, the adaptive endpoint inset, and the relative-orientation support bound, are the ones already supplied in the left-side proof.

## 2. Keep the two inner widths in the shared main span

Let

    S=x_M3-x_M0-h_M0-h_M3.

Actual separation on all three main edges gives

    S>=2(h_M1+h_M2).

The two physical weighted caps, together with actual L--P separation, give the stronger inequality

    46*S+(27/2)*(D+p-r)<=211/2.

Consequently

    h_M1+h_M2 <= 1+(27/184)*W.

Since each inner halfwidth is at least 1/2, each satisfies

    h_Mi <= 1/2+(27/184)*W,
    g_Mi=1/(4h_Mi) >= 1/[2+(27/46)*W].

Retain also the previously proved `g_Mi>15/31`, and define

    g=max(15/31,1/[2+(27/46)*W]).                    (5)

Thus both original inner main insets have halfwidth at least g. This is a consequence of the shared original main span, not an independent replacement of either main square.

## 3. Physical P--main inset clearance

For each inner main, let d_i be its positive horizontal center distance from P. P lies strictly between the two inner main centers. The actual main-chain inequalities and the universal center bound imply

    x_M1 > h_M1-61/60,
    x_M2 < 61/60-h_M2.

Hence, using `h_Mi+g_Mi>=1`,

    g_M1-d_1 > -x-1/60,
    g_M2-d_2 >  x-1/60.

Both are bounded below by

    delta=-|x|-1/60.                                (6)

The original P center is above both main centers. Their horizontal distances obey

    d_1 <23/60+31/60=9/10,
    d_2 <31/60+23/405<9/10,

while `g_Mi+1/2>15/31+1/2>9/10`. Thus an inset-to-P separating axis cannot have a nonpositive vertical component: its horizontal contribution would be less than the required inset support plus the radius-1/2 support of P. Horizontal projection separation is impossible for the same reason.

The inset's vertical axis or a genuine side axis of P therefore gives, with `V_i=y-y_Mi>0`,

    V_i >= g_Mi+min(p,
                    (1/2+(g_Mi-d_i)*bP)/aP,
                    (1/2+(g_Mi-d_i)*aP)/bP).

Both rational alternatives are increasing in `g_Mi-d_i`; using (5)--(6) gives the necessary lower bound

    V_i >= g+R_P,
    R_P=min(p,(1/2+delta*bP)/aP,
                (1/2+delta*aP)/bP).                 (7)

Again omit the last branch at bP=0. Its numerator is positive even on the full root, since `delta>=-2/5` and `aP<=1`. All signs and boundary orientations are therefore covered.

If either inner main had `y_Mi>=-7/20`, equation (7) would force

    y>=y_low:=g+R_P-7/20.                            (8)

This is the new physical input for the main-height table.

## 4. The complete main-height table: both inner main centers are below -7/20

Use the same complete root box (1), the same necessary inequalities (1)--(4), and now the lower bound (8). The certificate uses the expression in (8) for `y_low` throughout.

| Rule | Contradictory necessary condition | Leaves |
|---|---|---:|
| 0 | x-p+C>=0 | 2998 |
| 1 | r+C-X>=0 | 3 |
| 2 | W>=0 | 74 |
| 3 | 2D^2-(1+abs(p-r))^2>=0 | 351 |
| 4 | A<=61/60 | 0 |
| 5 | p+1/10-y_low>=0 | 2672 |
| 6 | upper bound (2) at least lower bound (3) | 18324 |
| 7 | U-y_low>=0 | 0 |
| 8 | (4), with Y-y replaced by U-y_low | 34803 |
| **Total** | **All of (1)** | **59225** |

The canonical file is `badfloor_mainheight_certificate.json`; its independent rational verifier is `verify_badfloor_mainheight_exact.py`. The complete tree has 118,449 nodes, 59,225 leaves, and maximum depth 38. Every leaf passed exact replay with positive reserve exceeding 1/10000000000. Therefore (8) is impossible, proving both strict bounds `y_M1,y_M2<-7/20`.

The verifier uses only exact fractions and integer square-root enclosures at scale 2^44; it imports no discovery producer or numerical solver. The prescribed rational root and every midpoint split are reconstructed during replay, and full binary coverage is checked. Its report records the exact tree hash, the leaf counts, and the actual minimum rational reserve.

## 5. Both remaining physical squares are central

The complete left and right low-floor side-extra exclusions show that any extra in either side strip must be below its own inner main. But the established one-sided main-height theorem says that any such lower side outsider forces that inner main above -7/20. Section 4 gives the opposite strict inequality for both mains.

Thus neither extra can occupy either closed side strip, and

    |x_F|<29/60,       |x_G|<29/60.                  (9)

This conclusion does not need the separate strict-radius side-capacity theorem: it follows from the original physical side exclusions and the main-height contradiction. It is therefore valid at closed Q as well.

The actual outer cone edges give `y_Mi>-139/120`. Together with Section 4,

    |y_M1-y_M2|<139/120-7/20=97/120<59/60.

Each central extra has vertical distance greater than 59/60 from the main in its own half-plane. Therefore its height cannot be between the two inner main heights: it is either above both or below both. This covers the x=0 line as well, where both clearance statements apply.

## 6. At most one central extra is below the main pair

For a central unit below both inner mains, reflect the established central adjacent-proxy barrier vertically. Its whole upper edge then satisfies

    y_S+h_S < max(y_M1,y_M2)-869/1860
             < -7/20-869/1860
             = -1520/1860
             < -9/20.

If both F and G were below both mains, both would be central units lying wholly below -9/20. The reflected two-square central-strip cap (`TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md`) excludes this, including equality at Q. Thus at most one of F,G is below both mains, and at least one is above both.

The remaining possibilities still retain all original pair and corner constraints: one central upper and one central lower extra, or two central upper extras. The next section sharpens the meaning of upper.

## 7. Every central upper extra is above P

Let F be a central extra above the inner main in its own half-plane, and suppose for contradiction `y_F<=y`. The equal-height case is already impossible because their horizontal gap is less than `29/60+23/60=13/15<1`; hence `y_F<y`.

Add the unsigned orientation variable `tF in [0,1]`, with components `aF,bF`, halfwidth f, and offset kF defined by the same formulas as before. The physical main/F inset clearance is particularly simple here. The actual main-chain position bounds give, for its assigned main,

    g_M-|x_F-x_M| > |x_F|-1/60 >= -1/60.

The main center is above -139/120. The same physical inset argument as Section 3 therefore gives

    y_F > -139/120+g+R_F,
    R_F=(1/2-bF/60)/aF.                             (10)

To justify the simplified last expression, the general reach is the minimum of

    f, (1/2-bF/60)/aF, (1/2-aF/60)/bF.

The middle term is at most f, because their difference is

    -(bF/aF)*(kF+1/60)<=0.

For bF>0, the last term minus the middle term is

    (aF-bF)*(1/2-(aF+bF)/60)/(aF*bF)>=0.

At bF=0 the last term is omitted and the other two equal 1/2. Thus (10) covers every orientation without a limiting division.

Let the actual P/F gaps be `d=|x-x_F|` and `v=y-y_F>0`. Put

    d_max=|x|+29/60,
    s_PF=(1+aP*aF+bP*bF+|aP*bF-bP*aF|)/2.

The original physical separating axis belongs to P or F. Irrespective of both physical chiralities and of the sign of their horizontal gap, its absolute projection is no larger than one of

    aP*d_max+bP*v, bP*d_max+aP*v,
    aF*d_max+bF*v, bF*d_max+aF*v.

Its support sum is at least s_PF. Consequently

    v >= e_min := min((s_PF-aP*d_max)/bP,
                     (s_PF-bP*d_max)/aP,
                     (s_PF-aF*d_max)/bF,
                     (s_PF-bF*d_max)/aF).           (11)

The branches with zero denominator are omitted. Every numerator is positive: `s_PF>=1`, each component is at most one, and `d_max<=13/15<1`. Thus no zero-denominator branch can provide a separator, and the displayed convention covers all boundary orientations.

Combining (10)--(11), any such F would force

    y>y_low:=-139/120+g+R_F+e_min.                  (12)

Use (12) in the same nine exact table rules, now on the five-dimensional root consisting of (1) and `tF in [0,1]`. The complete table is `central_upper_below_p_certificate.json`; the independent rational replay is `verify_central_upper_below_p_exact.py`.

| Rule | Leaves |
|---|---:|
| 0 | 4225 |
| 1 | 0 |
| 2 | 44 |
| 3 | 2116 |
| 4 | 0 |
| 5 | 3416 |
| 6 | 4270 |
| 7 | 0 |
| 8 | 47929 |
| **Total** | **62000** |

Every leaf passed the independent Fraction/integer-square-root replay, with positive reserve exceeding 1/10000000000. There are 123,999 nodes and maximum depth 27. The fifth nonnegative split tag is coordinate 4; the leaf tags and complete-tree convention are unchanged.

Thus no central upper extra can have center at or below P. Together with Sections 5--6, the entire low-floor mask has only these two possibilities: both extras above P, or one above P and one below both mains. This is an exhaustive reduction. In either possibility there is an original physical central extra U above P, which supplies the next theorem’s caller.

## 8. Completed strict-radius consequence

The original central extra U supplied above satisfies |x_U|<29/60 and
y_U>y_P. The complete hand/table theorem
`CENTRAL_UPPER_EXTRA_WHOLE_FLOOR_HAND_TABLE.md` gives y_U-h_U>1/10.
Its final section verifies every center band and separator range for the
original five physical units M0,L,U,R,M3. The completed theorem
`UNRESTRICTED_JOINT_FIVE_SQUARE_HIGH_FLOOR_CAP.md` therefore gives

    46*(x_M3-x_M0-h_M0-h_M3)+27/2 < 211/2

whenever the containing squared radius is strictly below Q. The actual
main four-chain gives the adjusted span at least two, making the left
side at least 211/2. This contradiction excludes the entire low-floor
branch of the routed 000/01 mask at every strictly subcritical radius.
All finite geometric reductions in this manuscript hold already at
closed Q; the displayed final strict inequality uses the radius premise.
