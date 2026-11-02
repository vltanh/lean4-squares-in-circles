# A low central floor forbids a right-side extra above the right inner main

This is a complete hand proof of the stated consequence of the full `000/01` domain. It is an internal branch exclusion, not a proof of the entire mask. Every bound below retains its original physical squares. No Lean, Lake, or CI is used.

Use the upward routing and notation of `A2_000_01_ATTEMPT.md`, at closed squared radius Q=1105/256. The main chain is M0,M1,M2,M3 and the selected short chain is L,P,R. Write h_S for coordinate halfwidth, g_S=1/(4h_S) for inset halfwidth, and H_S for physical directional support. Let S be one of the two additional physical squares.

## Theorem

If

    y_P-h_P <= 1/10,        x_S >= 29/60,

then

    y_S < y_M2.

Consequently the existing one-sided main-height theorem gives y_M2>-7/20 whenever such a right-side extra exists. There can be no right-side extra if, additionally, y_M2<=-7/20.

The proof does not presume a coordinate separator for any new pair. The reflected simultaneous chain reversal gives the corresponding actual/weak-reversed mask statement; it does not assert the same conclusion for the left side of the unmodified `000/01` predicate.

## 1. Inputs already derived on the whole mask

Put M=M2, E=M3, p=h_P, g=h_S, and c=221/600. The source bounds are

    29/60 < x_M < 31/60,       h_M<31/60,
    89/60 < x_E < 91/60,       g_E>15/32,
    |y_E|<=1/8,               g_E-|y_E|>c,
    |x_S|<13/12,              |center_S|<91/60,
    -1/12 < x_P < 23/60,      y_P-y_M>29/30,
    y_P>y_M,                  y_M<7/20,
    1/2 <= p,g <= 1/sqrt(2) < 71/100.

The actual L--P comparison gives an additional exact bound:

    x_P >= x_L+h_L+p > -13/12+1/2+p = p-7/12.       (1)

The outer M--E cone comparison and x_E-x_M<31/30 give

    y_M >= y_E-(x_E-x_M) > -1/8-31/30=-139/120.     (2)

Thus y_P>-23/120.

The hand argument in `WHOLE_MASK_SHOULDER_AND_NORMAL_REDUCTIONS.md` gives y_R>3/4. Together with the existing two-high-center side cap, this implies y_S<9/16 for every right-side extra S. Also x_R>23/30 and |center_R|<91/60 give

    y_R^2 < (91/60)^2-(23/30)^2 = 137/80
          < (131/100)^2.

Both S and R belong to the right side strip, whose x-width is 3/5. Since y_S<9/16<y_R and their center distance is at least one,

    y_R-y_S>4/5,        hence y_S<51/100.            (3)

Assume for contradiction that S is above M. The existing physical inner-main clearance gives y_S-y_M>97/100, so (2) implies

    y_S > -139/120+97/100 = -113/600 > -c.           (4)

## 2. The right endpoint confines S horizontally

The endpoint E contains its centered aligned square of halfwidth g_E, and the vertical projection of this inset contains [-c,c] in its interior. The radius-1/2 disk centered at S is disjoint from the inset's interior. Moreover x_S<x_E.

If y_S<=c, (4) puts the S center inside the inset's vertical projection. Its horizontal distance to that inset must therefore be at least 1/2. Hence

    x_E-x_S >= g_E+1/2 > 31/32,
    x_S < 91/60-31/32 = 263/480.                    (5)

If y_S>c, its vertical distance to the inset is less than

    51/100-c = 17/120.

The disk-to-inset distance inequality then gives

    x_E-x_S > g_E+sqrt(1/4-(17/120)^2)
             >15/32+23/48 =91/96.

The square-root comparison is 3311/14400>(23/48)^2; after multiplication by 57600 it is 13244>13225. Thus in this case

    x_S <91/60-91/96=91/160.                        (6)

## 3. The branch y_S>c is impossible by the two center disks

The x-order is x_S>x_P. By (1) and (6),

    0<x_S-x_P<91/160+7/12-p<=313/480<2/3.

The assumed floor bound gives y_P<=p+1/10<81/100. Together with y_P>-23/120 and c<y_S<51/100, it yields

    |y_P-y_S| < max(81/100-c,51/100+23/120)
              =421/600<71/100.

Their squared center distance is therefore less than

    (2/3)^2+(71/100)^2=85369/90000<1,

contrary to disjointness of their contained radius-1/2 disks. Hence y_S<=c and (5) holds from now on.

## 4. Two physical center-distance estimates retaining orientation

For any two physical unit squares A,B, with coordinate halfwidths h_A,h_B,

    |center_B-center_A| >= 1+|h_A-h_B|.              (7)

Here is a proof. Reduce the absolute orientation angles to alpha,beta in [0,pi/4], so h=(cos angle+sin angle)/2. Their reduced relative angle gamma is at least |alpha-beta|: it equals this difference for equal chiralities; for opposite chiralities it is min(alpha+beta,pi/2-alpha-beta), and both arguments are at least the difference. For alpha=beta+delta,

    (cos alpha+sin alpha)-(cos beta+sin beta)
      =(cos delta-1)(cos beta+sin beta)
         +sin delta(cos beta-sin beta)
      <=cos delta+sin delta-1.

The function cos t+sin t increases on [0,pi/4]. Therefore

    cos gamma+sin gamma >=1+2|h_A-h_B|.

The separating-axis theorem supplies a side normal of one physical square, on which the sum of support halfwidths is exactly (1+cos gamma+sin gamma)/2. The center distance is at least its projection on that unit normal, proving (7).

For S and the nearly aligned inner main M, the stronger orientation-aware estimate already proved in `UNRESTRICTED_ACTUAL_FOUR_CHAIN_FULL_SIDE_MAIN_HEIGHT_HAND_PROOF.md`, Section 2, is

    |center_S-center_M| > g+12/25.                  (8)

For clarity, its ingredients are a_M>999/1000 and b_M<7/200, obtained from h_M<31/60. If k_S=sqrt(1/2-g^2), then the physical support sum gives a center distance greater than 1/2+(999/1000)g-(7/200)k_S>g+12/25, since g<1 and k_S<=1/2. The two center disks also give distance at least one.

By x_S>=29/60, (5), and the main x-band,

    |x_S-x_M| < max(31/480,1/30)<1/15.

Put m=max(1,g+12/25). Since S is above M, (8) and the disk bound imply

    y_S-y_M>sqrt(m^2-1/225)>m-1/225.               (9)

The last inequality follows by squaring its nonnegative right side and using m>=1.

## 5. The two remaining physical units must have P above S

From (1) and (5),

    0<D:=x_S-x_P<181/160-p<=101/160<2/3.           (10)

If y_P<=y_S, then y_S-y_P<c+23/120=14/25<3/5, so the squared center distance would be less than (2/3)^2+(3/5)^2=181/225<1. This is impossible. Thus V:=y_P-y_S>0.

Combine (2), (9), and y_P<=p+1/10:

    V < p+2273/1800-max(1,g+12/25).                (11)

We now contradict the exact lower bound (7) for P,S.

## 6. A two-row rational table closes every orientation

First suppose 1/2<=p<=13/25. Since m>=1, (10)--(11) give

    D^2+V^2 < (181/160-p)^2+(p+473/1800)^2.

This is a convex quadratic in p, so its maximum on the interval is at an endpoint. The exact endpoint reserves are

| p | 1 minus the displayed quadratic |
|---|---|
| 1/2 | 1020911/51840000 |
| 13/25 | 706703/51840000 |

Both are positive. Thus D^2+V^2<1, already contradicting the center disks.

Now suppose p>=13/25. Put t=max(p-g,0) and d0=1409/1800<1. Equation (11) gives V<d0+t: if g>=13/25, its right side is d0+p-g; if g<=13/25, it is d0+p-13/25<=d0+p-g. Equation (10) also gives D<489/800. Therefore

    D^2+V^2 < (489/800)^2+(d0+t)^2
             <(1+t)^2
             <=(1+|p-g|)^2.

The strict middle comparison follows from the exact identity

    (1+t)^2-(489/800)^2-(d0+t)^2
      =706703/51840000+2t(1-d0)>0.

This contradicts (7). All possible p,g have been covered, and the assumption that S is above M is impossible. The theorem follows.

## Scope

This proof excludes one entire geometrically defined branch of the full moving mask, including arbitrary independent orientations and every separator owner. It does not exclude central extras, does not give the same left-side assertion in `000/01`, and does not by itself prove the central floor exceeds 1/10. It adds no mandatory gate. The whole `000/01` predicate and the unrestricted theorem remain open.

Small nonlinear and numerical searches were used to test this direction. The proof above uses neither their answers nor an unverified UNSAT certificate: every final step is a physical separation argument, a previously established whole-domain input, or an explicit rational comparison.
