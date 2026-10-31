# Adaptive V-arc endpoints give a whole terminal-center matching theorem

Date: October 28, 2026 UTC. Author: pentagon continuation.

The house continuation supplied the exact physical plus-mask port identities and the reviewed uniform port box used in the concrete corollary below. The adaptive projection, two-limiter comparison, enlarged low-Y domain and capacity join are proved here. Root identified the potential reuse of the low-Y projection on the distinct unique-minus domain; no unproved minus inequality is used in this source.

**Status: complete proposed hand theorem, submitted for independent review.** The theorem compares the actual terminal center with whichever side of the actual V square first meets the radius-9/8 circle. It does not impose a fixed215-degree terminal cutoff or a fixed bound on A-B.

The full unique-V/plus-W physical domain satisfies the theorem. A broader low-Y projection version is stated separately so that a second physical caller can use it without importing the stronger plus-port box.

## 1. Entire force-free domain and two versions of the angle theorem

Put

    Q_*=1105/256, rho_*=9/8, sigma_*=1/sqrt(2).

Keep the unchanged containing disk and actual unit squares. Assume

    2<=R<=sqrt(Q_*),
    1/2<=Y<1,
    X^2+Y^2=R^2,
    X>0,

    V=[-Y,1-Y] x [X-1,X].                          (1)

Let T be an actual physically boundary unit square contained in this disk. Let its actual point S have coordinates

    S=(-A,B) in T.

The point need not be a vertex or a selected force application. Every T frame and physical circle mask is included. Set

    D=X-1,
    e=A-Y,
    f=B-X+2.                                       (2)

The actual T center is c_T. Once its first coordinate is shown negative, theta_T denotes its unique angular lift in (90,270) degrees.

Define the two actual V arc limiters

    phi_L=acos(-Y/rho_*),
    phi_B=180 degrees-asin(D/rho_*),
    phi_*=min(phi_L,phi_B).                         (3)

Both inverse functions have their ordinary principal values. The bounds below ensure 0<Y,D<rho_*, so both limiters lie strictly between90 and180 degrees.

**Theorem L: the larger low-Y projection domain.** Suppose

    1/2<=Y<=3/4,
    A>1/4,
    -1/2<B<1/2,
    -e+3f> -824/2625.                              (4)

Then the actual terminal center lies strictly left of the origin and

    theta_T<250 degrees,
    theta_T<phi_*+100 degrees.                     (5)

**Theorem H: the high-Y vertical domain.** Suppose

    3/4<=Y<1,
    A>7/15,
    -7/20<B<1/6,
    f>4/3-sqrt(2).                                 (6)

Then the actual terminal center lies strictly left of the origin and

    theta_T<235 degrees,
    theta_T<phi_*+100 degrees.                     (7)

The overlapping endpoint Y=3/4 is included in both comparison domains.

**Whole-domain corollary.** Throughout the entire range(1), the conditions

    A>7/15, -7/20<B<1/6,
    e-f<19/125,
    f>4/3-sqrt(2)                                  (8)

imply the angle bound in(7). Indeed the stronger point box gives theta_T<235 for either Y range, and

    -e+3f=2f-(e-f)
       >8/3-2sqrt(2)-19/125
       >8/3-99/35-19/125
        =-824/2625.                                (9)

No force, degree, owner, resultant or side-mean premise occurs in Theorems L and H.

## 2. Elementary geometric and trigonometric reserves

Every actual boundary unit center satisfies

    |c_T|>=R-sigma_*>=2-sigma_*,
    |c_T-S|<=sigma_*.                              (10)

These use a genuine physical circle corner and the actual unit circumradius. No resultant is substituted for that physical corner.

The elementary comparison sqrt(2)<99/70 gives

    sigma_*<99/140,
    (2-sigma_*)/rho_*>362/315=:lambda_0.            (11)

Its squared reserve is1/4900. Also sqrt(5)<9/4, with squared reserve1/16.

Put

    s_10=sin(10 degrees), c_10=cos(10 degrees).

The triple-angle identity 3s-4s^3=1/2, which is strictly increasing for 0<=s<=1/2, gives

    173/1000<s_10<87/500.

The lower and upper polynomial reserves are respectively427717/250000000 and28997/31250000. Squaring the upper sine bound gives

    c_10>63/64,

with reserve46711/64000000. In particular

    c_10>49/50, s_10>1/6,

    H_10:=3c_10-s_10>25/9,
    C_10:=c_10+3s_10>3/2.                          (12)

The last two rational reserves are97/72000 and27/8000.

Two further consequences will be useful:

    sin(20 degrees)=2s_10*c_10>1/3,
    sin(70 degrees)=1-2s_10^2>15/16.               (13)

The reserves from the same rational bounds are697/96000 and487/250000.

Finally,

    sin(55 degrees)=cos(35 degrees)
       =(c_10+s_10)/sqrt(2)>9/11.                  (14)

Using sqrt(2)<99/70, the final comparison has reserve13/79200.

All angles and comparisons in this source are exact; decimal angle samples are not used.

## 3. Center-left and the two preliminary terminal-angle bounds

First assume the weaker point box in(4). If (c_T)_x>=0, (10) and A>1/4 give

    0<=(c_T)_x<sigma_*-1/4,
    |(c_T)_y|<sigma_*+1/2.

Their squared sum is strictly below (2-sigma_*)^2. Indeed its deficit is

    (2-sigma_*)^2
       -(sigma_*-1/4)^2-(sigma_*+1/2)^2
        =51/16-(9/2)*sigma_*>0,

because sigma_*<17/24, with squared reserve1/576. This contradicts(10). Hence c_T lies strictly left.

If its angle is at least180 degrees, then

    -(c_T)_y/|c_T|
       <(sigma_*+1/2)/(2-sigma_*)<15/16.

For the last inequality it suffices that sigma_*<22/31, which follows from sigma_*<17/24<22/31; the latter difference is1/744. By(13), this excludes every angle at least250 degrees on the left-half-plane lift. Thus the weaker box gives theta_T<250.

Now assume the stronger point box in(6) or(8). Center-left already follows. For its negative vertical component,

    -(c_T)_y/|c_T|
       <(sigma_*+7/20)/(2-sigma_*)<9/11.            (15)

The last comparison is equivalent to sigma_*<283/400, whose squared reserve is89/160000. Equation(14) therefore excludes angles at least235 degrees. This proves the preliminary bounds in(5) and(7) without any diagonal-port assumption.

## 4. The two actual V limiters are well-defined

From(1),

    X>sqrt(3), D>sqrt(3)-1>73/100.

Also Y>=1/2 and the radius upper bound give

    X<121/60, D<61/60<rho_*.

The relevant squared reserve is

    (121/60)^2-(Q_*-1/4)=31/57600>0.

The strict lower comparison sqrt(3)>173/100 has squared reserve71/10000. Since Y<1<rho_*, both quantities in(3) are valid and phi_*>90.

Every radius-rho_* point at an angle

    90 degrees<phi<phi_*                            (16)

lies in the open actual V square. Its first coordinate is negative, hence strictly below the positive right boundary1-Y, and phi<phi_L puts it strictly above the left boundary -Y. Its vertical coordinate is below rho_*<X and phi<phi_B puts it strictly above D.

Thus(3) uses the actual V sides. It is not a hypothetical angle whose radius point lies outside V.

## 5. The common projection comparison for the low-Y theorem

Assume(4). Write a candidate angle in the third quadrant as

    theta=180 degrees+delta.

On 0<delta<70 degrees the function

    cos(delta)+3sin(delta)

is strictly increasing. Its derivative is positive because

    3cos(delta)-sin(delta)
       >3cos(70 degrees)-1
        =3sin(20 degrees)-1>0

by(13).

Suppose theta_T is at least one of phi_L+100 or phi_B+100. If that cutoff already exceeds250, the supposition is impossible by Section3. Otherwise the relevant angular interval lies within the preceding increasing range. From(10), its negative center projection is at least the projection at the cutoff with radius2-sigma_*.

The original point projection is exactly

    S_x+3S_y=3X-Y-6-e+3f
             >3X-Y-6-824/2625.                    (17)

On the other hand the actual unit center displacement always satisfies

    (1,3).(S-c_T)<=sqrt(10)*sigma_*=sqrt(5).        (18)

We will contradict(18) for each actual cutoff. The proof uses a projection of the actual center displacement; it does not replace the terminal square by an independently movable center.

## 6. Low Y: the entire left-side limiter

At theta=phi_L+100 degrees, elementary addition formulas give

    -(cos(theta)+3sin(theta))
       =[H_10*Y+C_10*sqrt(rho_*^2-Y^2)]/rho_*.

Equations(10)--(12),(17) and X>=sqrt(4-Y^2) show that the alleged theta_T>=phi_L+100 would force

    (1,3).(S-c_T)-sqrt(5) > G_L(Y),

where

    G_L(Y)
      =lambda_0*[(25/9)*Y
                  +(3/2)*sqrt(rho_*^2-Y^2)]
          +3sqrt(4-Y^2)-Y-6-824/2625-9/4.           (19)

This is concave on the whole closed interval[1/2,3/4]. It is therefore enough to check its two endpoints.

At Y=1/2 use

    sqrt(rho_*^2-Y^2)>1,
    sqrt(4-Y^2)>387/200.

The squared reserves are1/64 and231/40000. Direct rational substitution gives

    G_L(1/2)>4943/81000>0.                          (20)

At Y=3/4 use

    sqrt(rho_*^2-Y^2)>5/6,
    sqrt(4-Y^2)>37/20.

Their squared reserves are5/576 and3/200. The resulting bound is

    G_L(3/4)>6311/94500>0.                          (21)

Concavity now makes(19) strictly positive throughout the entire low-Y interval, contradicting(18). Therefore

    theta_T<phi_L+100 degrees.                     (22)

No W mask or force equation was used.

## 7. Low Y: the entire bottom-side limiter

At theta=phi_B+100 degrees the corresponding projection formula is

    -(cos(theta)+3sin(theta))
       =[C_10*D+H_10*sqrt(rho_*^2-D^2)]/rho_*.

Since Y<=3/4 and R>=2,

    D>=sqrt(55)/4-1>17/20.

Together with Section4 this gives the whole enlarged comparison interval

    17/20<=D<=61/60.

Using Y<=3/4 in(17), the alleged theta_T>=phi_B+100 would force

    (1,3).(S-c_T)-sqrt(5)>G_B(D),

where

    G_B(D)
      =lambda_0*[(3/2)*D
                    +(25/9)*sqrt(rho_*^2-D^2)]
          +3D-15/4-824/2625-9/4.                  (23)

This function is concave on that entire interval.

At D=17/20, use sqrt(rho_*^2-D^2)>73/100, whose squared reserve is409/40000. At D=61/60, use sqrt(rho_*^2-D^2)>12/25, whose squared reserve is581/360000. The exact endpoint bounds are

    G_B(17/20)>4489/141750>0,
    G_B(61/60)>494/23625>0.                         (24)

Thus(23) is strictly positive throughout the enlarged interval, again contradicting(18). This gives theta_T<phi_B+100. Together with(22) and Section3, Theorem L is complete.

The proof covers the closed Y endpoints and every intermediate continuous orientation. It only needs the projection premise in(4), not separate bounds on e or f.

## 8. The vertical comparison for the high-Y theorem

Assume(6). Its lower bound on f gives the actual point inequality

    B=X-2+f>X-sqrt(2)-2/3.

Consequently(10) implies

    -(c_T)_y<sqrt(2)+2/3+sigma_*-X.                 (25)

Equivalently, with D=X-1,

    -(c_T)_y<sqrt(2)-1/3+sigma_*-D.                 (26)

The constants have the exact upper bounds

    sqrt(2)+2/3+sigma_*<1171/420,
    sqrt(2)-1/3+sigma_*<751/420.                    (27)

These use sqrt(2)<99/70 and sigma_*<99/140.

On the third-quadrant lift up to theta_T<235, the function -sin(theta) is strictly increasing. Thus an alleged terminal angle at least one of the two cutoffs again gives a lower bound at that cutoff, with radius at least2-sigma_*. If a cutoff is already beyond theta_T, there is nothing to prove.

## 9. High Y: the entire left-side limiter

At theta=phi_L+100,

    -sin(theta)
       =[c_10*Y+s_10*sqrt(rho_*^2-Y^2)]/rho_*.

By(11)--(12), X>=sqrt(4-Y^2), and(25)--(27), the alleged theta_T>=phi_L+100 would require

    H_L(Y)<0,

where in fact

    H_L(Y)
      =lambda_0*[(49/50)*Y
                    +(1/6)*sqrt(rho_*^2-Y^2)]
          +sqrt(4-Y^2)-1171/420.                   (28)

This function is concave on the closed enlarged interval[3/4,1].

At Y=3/4 use the same lower radicals5/6 and37/20 as above. At Y=1 use sqrt(rho_*^2-1)>1/2 and sqrt(3)>173/100. The squared reserves at this second endpoint are1/64 and71/10000. Exact substitution yields

    H_L(3/4)>18763/283500>0,
    H_L(1)>3872/23625>0.                           (29)

Thus(28) is strictly positive throughout the whole comparison interval, a contradiction.

## 10. High Y: the entire bottom-side limiter

For Y>=3/4, the exact radius upper endpoint gives

    X^2<=Q_*-9/16=(31/16)^2.

Together with Section4,

    73/100<D<=15/16.

At theta=phi_B+100,

    -sin(theta)
       =[c_10*sqrt(rho_*^2-D^2)+s_10*D]/rho_*.

Equations(11)--(12),(26)--(27) therefore contradict the alleged theta_T>=phi_B+100 as soon as the following function is positive:

    H_B(D)
      =lambda_0*[(49/50)*sqrt(rho_*^2-D^2)
                      +(1/6)*D]
          +D-751/420.                              (30)

It is concave on the entire enlarged interval[73/100,15/16].

At D=73/100 use sqrt(rho_*^2-D^2)>17/20, with squared reserve409/40000. At D=15/16 use sqrt(rho_*^2-D^2)>99/160, with squared reserve99/25600. Exact substitution gives

    H_B(73/100)>9217/236250>0,
    H_B(15/16)>32531/1260000>0.                     (31)

This proves the bottom cutoff uniformly. Together with Sections3 and9, Theorem H is complete. Equation(9) then proves the whole-domain corollary(8).

All eight endpoint bounds in(20),(21),(24),(29),(31) have strict positive rational reserves. They are endpoints of four globally concave comparison functions, not a list of sampled physical cases.

## 11. The complete unique-V/plus-W physical domain supplies the criterion

Use the complete actual entry and uniform plus-port theorem pinned below. Keep every original U3 and V2 equation, every actual relative-side-interior point, the full actual W mask and all true W/T degrees. In particular an actual W two-circle tie is included whenever its plus corner is physical.

Their unchanged identities give

    2<=R<=sqrt(Q_*),
    X>sqrt(3), 1/2<Y<1,
    X^2+Y^2=R^2,

    a,b>0, a^2+b^2=1,
    z=L/K>0, tau>0,
    kappa=a-z*b>2/3,
    h=b^2+ab*z=1-a*kappa,

    rho=a-z*(b+tau),

    A=Y-1+rho+b-ha,
    B=X-1-a-hb.                                    (32)

The complete actual boundary-terminal proof at88f89381 supplies

    A>7/15, -7/20<B<1/6.                           (33)

Define e and f as in(2). Their exact expressions are

    e=a^3+b-1-z*[b(1+a^2)+tau],
    f=1-a-b^3-z*ab^2.                              (34)

The house continuation supplied these identities in this physical chart. They are expanded from the original points in(32), without moving an application or changing a force.

First,

    e-f=a+a^3+b+b^3-2
             -z*[b+tau+ab(a-b)].                   (35)

The subtracted bracket is strictly positive: it equals
b*(1+a^2-ab)+tau, and ab<=1/2. For u=a+b in(1,sqrt(2)],

    a+a^3+b+b^3=(5u-u^3)/2<=5sqrt(15)/9<269/125.

The maximum follows by differentiating this one cubic. The last squared reserve is

    (269/125)^2-125/27=622/421875>0.

Therefore e-f<19/125 on the entire physical domain.

Second, the equivalent exact formula

    f=1-a-b+ab*kappa

and kappa>2/3 give

    f>1-u+(u^2-1)/3>=4/3-sqrt(2).                  (36)

The last quadratic is decreasing on[1,sqrt(2)], since2u<3. Equations(33),(35),(36) are exactly the whole-domain hypotheses(8).

Thus every original unique-V/plus-W case, including the physical W tie, has

    theta_T<235 degrees,
    theta_T<min(phi_L,phi_B)+100 degrees.           (37)

No unique-force identity has been imposed on a physical-two V mask. This concrete corollary applies to the unique V domain exactly as stated. The force-free Theorems L and H themselves are broader and may have other literal callers.

## 12. Conditional whole-pocket capacity with a closed forty-degree route

Assume either Theorem L, Theorem H or the whole-domain corollary, and retain actual contained units V,T and a collection of other actual units E, all pairwise interior-disjoint.

Suppose a caller has proved, for each whole E,

    E is contained in {x<=-q}, q>=1/6,              (38)

and, on the canonical common left-half-plane lift,

    theta_E<=theta_T+40 degrees.                   (39)

The caller must prove the actual whole cap and upper route for its occupied pocket. They are not conclusions of a scalar point estimate.

The cap puts each extra center strictly left, hence theta_E is in(90,270), and gives dist(0,E)>=q>=1/6. The complete one-sixth-clearance theorem gives its closed centered radius-rho_* arc of halfwidth20 degrees in its open interior. The actual boundary T has clearance at leastR-sqrt(2)>1/6 and has the same closed centered arc.

By the strict angle conclusion already proved, choose an actual angle phi such that

    90<phi<phi_*,
    theta_T<phi+100 degrees.                       (40)

Section4 puts its radius-rho_* point in open V.

Every extra center must satisfy theta_E>phi. Otherwise its center-direction radius-rho_* point, which lies in its open interior by the centered-arc theorem, would be at an angle in(90,phi] and hence in open V by Section4. This contradicts actual interior disjointness. This proves the required lower ordering directly from the actual V arc; no separate lower-route hypothesis or hypothetical V point is needed.

If theta_E>=theta_T, (39) would give a minor gap at most40 degrees between two centers whose closed halfwidth20-degree arcs lie in disjoint open interiors. Their gap is strictly greater than40, including exclusion of equality. Thus theta_E<theta_T.

For two ordered extras, the first gap from the actual open V point exceeds20, the mutual gap exceeds40, and the last gap to T exceeds40. All are minor gaps in the interval(phi,theta_T), whose length is strictly less than100 by(40). Their sum would exceed100, a contradiction.

Therefore the whole collection has capacity at most one. This argument does not require connectedness of a whole square's intersection with the radius-rho_* circle. A caller's upper bound theta_T+37.5 degrees fits the closed hypothesis(39) literally.

## 13. Exact scope and verification boundary

The adaptive center-angle theorems are force-free physical geometry. The concrete plus corollary retains every original force, actual side parameter, true degree and physical mask from its two complete inputs. The conditional capacity theorem still requires a proved actual whole-square cap and the actual upper route. It supplies no original occupied crosscut or graph allocation by itself.

The larger low-Y criterion(4) is intentionally separate. Any second physical caller must supply that criterion at its own unchanged original points; no missing minus-mask premise is inferred by analogy.

| Complete operative source | SHA-256 | Exact use |
| --- | --- | --- |
| TERMINAL_HUB_AXIS_TIP_OWNED_POSITIVE_DOT_FULL_MASK_ENTRY.md | 1e9e597ad4b13995909cdac5d204b111d20ef305768fe6d44def11264e4a4c49 | Only Section11: complete actual plus chart, genuine unique V identity, all W masks and ties |
| TERMINAL_HUB_AXIS_UNIQUE_PLUS_UNIFORM_PORT_BOX.md | 88f89381e0a978c301880dcf49f7cbf735fa7c04b16927d391e23c85db2e3c1a | Only Section11: whole kappa>2/3 and actual terminal point box, with all original equations and physical endpoints |
| ONE_SIXTH_CLEAR_UNIT_CENTERED_NINE_EIGHTHS_ARC.md | ae58afaf0564b403ab802bdc4ccb5f5a318013fd9aba778c6e4220e720aceb0a | Only Section12: complete closed centered twenty-degree half-arcs at actual clearance at least1/6 |

The actual angle estimates in Sections1--10 are self-contained. Exact rational checks confirm all eight displayed endpoint reserves, their radical comparison reserves and the elementary trigonometric bounds. The continuous proof is given by concavity, actual center displacement, and monotonicity on entire angular intervals.

No fine or coarse original flag is changed by this manuscript alone. No normal, application, force, circle coefficient, physical corner, actual side mean, completing square or plane embedding is changed. No Lean compilation, CI, pose enumeration, numerical optimization, numerical geometric certificate, remote write or shared-ledger mutation is used.

