# Exact consequences of the complete 000/01 predicate

These are necessary consequences of the unchanged physical mask, for use inside its computational or hand proof. They do not exclude the mask and do not close a roadmap gate.

Keep the notation of `A2_000_01_ATTEMPT.md`: actual center-cone four-chain M0,M1,M2,M3; selected short chain L,P,R with L--P actual and P--R weak; two additional physical units F,G; Q=1105/256. Apply its established common vertical reflection so that L,P,R lie above both inner main centers. All original physical pair and corner constraints remain in force.

## 1. The two shoulder centers are above 3/4

The established whole-mask short-chain position bounds are

    x_L < -23/30,       x_R > 23/30,
    |x_L|, |x_R| < 13/12.

For the right shoulder and its original outer main E=M3, the actual-four bounds give

    89/60 < x_E < 91/60,
    h_E < 8/15,        g_E=1/(4h_E)>15/32,
    |y_E| <= 1/8.

In particular, x_R<x_E and the horizontal center gap obeys

    D=x_E-x_R < 91/60-23/30 = 3/4.

The open radius-1/2 disk at the center of R lies in its interior. The centered aligned square of halfwidth g_E lies in E. Thus the distance between that disk's center and the aligned square is at least 1/2. With V=|y_R-y_E| this says

    max(D-g_E,0)^2 + max(V-g_E,0)^2 >= 1/4.

Since D-g_E<9/32<1/2, it follows that

    V > g_E + sqrt(1/4-(9/32)^2)
      > (15+sqrt(175))/32
      > 7/8.

The final strict comparison is sqrt(175)>13, equivalently 175>169. The established routing has y_R>y_E, so

    y_R > y_E+7/8 >= -1/8+7/8 = 3/4.

Reflection in the vertical axis gives the identical proof for L and M0. Therefore

    y_L>3/4,             y_R>3/4.

This uses original physical nonoverlap and the endpoint's retained inscribed square, rather than only the two center disks. It is valid at closed Q as well as below Q.

One can retain the stronger existing budget g_E-|y_E|>221/600 and obtain

    y_L,y_R > 221/600+sqrt(175)/32 > 25/32.

For the last comparison, 25/32-221/600=991/2400, and

    175*75^2-991^2 = 2294 > 0.

The simpler 3/4 bound already suffices for the consequences below.

## 2. A side extra has height below 9/16

The existing theorem `TWO_SQUARE_SIDE_STRIP_CENTER_CAP_HAND_PROOF.md` excludes two physical units whose centers both lie in

    29/60 <= x <= 13/12,       y >= 9/16,

and its horizontal reflection excludes the analogous left-side pair. Since R already belongs to the right strip and has y_R>3/4>9/16, any additional square S in that strip must obey y_S<9/16. Similarly L supplies the left-strip conclusion. Thus for S=F or G,

    |x_S| >= 29/60  implies  y_S < 9/16.

This implication also holds at closed Q. It does not assert that S is below its corresponding inner main.

If S is above that main, the existing whole-half-plane clearance |y_S-y_M|>97/100 does give

    y_M < 9/16-97/100 = -163/400.

If S is below the main, the existing one-sided main-height theorem gives y_M>-7/20. These alternatives are exhaustive and disjoint because their center heights differ by more than 97/100. Neither alternative alone is a contradiction.

### 2.1. Both side-extra bounds strengthen to y_S<7/20

If S is below its inner main, this follows from y_M<7/20. Suppose instead that S is above it. Reflect horizontally so that this is the right side, write X=x_R, and keep x_S positive.

The main's outer cone edge gives y_M>-139/120, so y_S>-113/600 by its clearance above the main. Also R has

    y_R^2 < (91/60)^2-(23/30)^2=137/80<(131/100)^2.

The already proved y_S<9/16<y_R and side x-width 3/5 imply y_R-y_S>4/5 by the two center disks. Hence y_S<51/100.

Put c=221/600. The matched outer main's inset has vertical projection containing [-c,c] in its interior. If y_S<=c, disk-to-inset clearance gives x_S<263/480. If y_S>c, its vertical distance to the inset is less than 51/100-c=17/120, and the same distance inequality gives

    x_E-x_S>15/32+sqrt(1/4-(17/120)^2)
              >15/32+23/48=91/96,
    x_S<91/160.

The positive square-root reserve is 19/57600. In either case

    29/60 <= x_S <91/160<23/30<X,
    -113/600<y_S<51/100<y_R.

Assume y_S>=7/20. Put l=29/60 and eta=7/20. Since |center_R|<rho=91/60, the squared S--R center distance is strictly below

    f(X)=(X-l)^2+(sqrt(rho^2-X^2)-eta)^2,
    23/30 <= X <=13/12.

Indeed reducing x_S to l increases the positive horizontal gap, reducing y_S to eta increases the positive vertical gap, and increasing y_R to the upper semicircle increases it again. The function

    f(X)=rho^2+l^2+eta^2-2lX-2eta sqrt(rho^2-X^2)

is convex, since the upper semicircle is concave. Its maximum on the interval is therefore at an endpoint.

At X=23/30, sqrt(rho^2-X^2)=sqrt(137/80)<1309/1000, with squared reserve 981/1000000. Thus

    f(23/30)<(17/60)^2+(959/1000)^2
             =1-371/9000000<1.

At X=13/12 the upper semicircle has height sqrt(1014)/30<11/10, so

    f(13/12)<(3/5)^2+(3/4)^2=369/400<1.

Both endpoints contradict center distance at least one. Therefore y_S<7/20 on both sides. This uses the selected shoulder's stricter x-band, and does not assert the corresponding statement for an arbitrary pair of side squares.

It follows in particular that a side extra above its own inner main forces

    y_M<7/20-97/100=-31/50.

For such an above-main extra, y_S belongs to (-113/600,7/20), which is wholly inside (-c,c). Therefore the stronger horizontal bound always holds:

    29/60 <= |x_S| <263/480,
    |x_S-x_M|<1/15.

These consequences hold without a low-floor hypothesis on P.

## 3. Safe ordering of the two additional labels

For the strict-radius domain, the existing side-capacity theorem gives at most two outsiders in each closed outer side strip. L already occupies the left strip and R the right strip. Swap only the unrestricted labels F,G if necessary so that x_F<=x_G. Then

    -13/12 < x_F < 29/60,
    -29/60 < x_G < 13/12,
    x_F <= x_G.

Indeed x_F>=29/60 would put F,G,R together on the right, and x_G<=-29/60 would put F,G,L together on the left. Both violate side capacity. Relabeling F,G changes no selected chain and preserves all 36 pairs and corners.

Unlike Sections 1--2, this step cites a strict-radius capacity result and must not be silently advertised as a closed-Q exclusion premise.

## 4. Every separator of a weak cone edge faces forward

This last statement is independent of the disk, main chain, and shoulder height. Let two physical squares A,B have equal horizontal and vertical halfwidths h_A,h_B in the chosen coordinate frame. Suppose their center difference (D,V) satisfies

    D >= |V|,       0 < D < h_A+h_B.

Let n be any genuine separating normal oriented from A to B:

    n dot (c_B-c_A) >= H_A(n)+H_B(n),

where H denotes the centered physical support halfwidth. Then n_x>0.

To prove this, assume n_x=-a<=0 and write b=|n_y|. If b<=a, then

    n dot (D,V) <= -aD+b|V| <= (b-a)D <= 0,

whereas the support sum is positive for a nonzero normal. If b>a, the same estimate and the weak comparison give

    n dot (D,V) <= (b-a)D < (b-a)(h_A+h_B).

Subadditivity and positive homogeneity of support give the reverse-triangle lower bound

    H_S(n) >= H_S((0,n_y))-H_S((a,0))
           = b h_S-a h_S = (b-a)h_S

for each physical square S. Adding this bound contradicts the separator inequality. These two cases prove n_x>0.

In particular, every genuine P-to-R separator in 000/01 has positive horizontal component. No central-floor assumption, bound |y_R-y_P|<1, prescribed separator owner, or restricted square orientation is needed. This permits removal of every left-facing separating-axis branch for that edge, provided its direction is consistently oriented P-to-R.

## Status and method

All displayed deductions are hand proofs with exact rational or squared-integer comparisons. No numerical failure is used as proof evidence. No Lean, Lake, or CI was run. The complete moving nine-square mask and A.2 remain open; these deductions are proof-search inputs, not new mandatory gates or whole-domain closures.
