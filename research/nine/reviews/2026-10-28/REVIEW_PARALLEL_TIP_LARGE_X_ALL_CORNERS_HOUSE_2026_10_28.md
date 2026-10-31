# Independent full review: the parallel-tip large-x all-corner theorem

Date: October 28, 2026 UTC. Reviewer: house continuation.

**Verdict: PASS, without source repair.** This is an independent review of the entire scalar/geometric theorem and both complete original-force corollaries. It is not an adoption of a caller whose actual chart has not yet been supplied.

## 1. Exact target and complete direct source

I read the complete target at its frozen bytes:

    PARALLEL_TIP_LARGE_X_RETURN_ALL_CORNERS_INSIDE_CIRCLE.md
    SHA-256 35ed0820293125307c28d2d6b0e14b841b5578517e67fa7aea90f42bb3544b35.

I also read the entire sole direct input:

    PHYSICAL_CONTACT_STRESS.md
    SHA-256 d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5.

The target is self-contained mathematically in Sections 1--8; the direct input supplies the unchanged physical force, torque and shared-mean conventions in Sections 9--10. I did not contribute to the target's discovery or derivation.

## 2. Full hypotheses and all four actual corners

I checked the exact coordinate increments from Z=(-x,y) to all four corners of

    W=(1-x,y-1+r*b)+[0,1](a,-b)+[0,1](b,a).

Every displayed deficit is exactly A*(2x-A)+D*(2y-D). All four corners are retained; no guessed physical far-corner mask is used.

The first two corner proofs work on the entire common domain. In the y<1 subcase of C_10, x>sqrt(3) follows strictly from R^2>=4, and its final lower bound is 1+a-b>0. In the y>=1 subcase the separate endpoint concavity bound on D_1 is valid on its full closed interval.

For C_01 with y<=x, the reduction k<=a+b-1 and x>=sqrt(2) preserves the correct inequality directions. I independently expanded the final expression and recovered exactly

    4sqrt(2)-4+a^2-2ab+2a*(1-sqrt(2))
      >=6sqrt(2)-8+(a-(sqrt(2)-1))^2>0.

This branch uses no torque inequality and no upper radius bound.

For C_11 with y<=x, I independently expanded the r=0 deficit

    2[(x+y-2)(1+b)+(x-y)a].

Here x+y>2 is strict because x,y>0 and x^2+y^2>=4. At r=1 both of the stated projection terms are strictly positive. Convexity of the squared norm in r, equivalently concavity of the deficit, gives the entire closed parameter interval rather than only its endpoints.

## 3. The complete y>=x maximal-parameter and derivative argument

The original inequality r*a*y<=x*(1-r*b) is exactly equivalent to

    r<=x/(a*y+b*x).

On y>=x its upper comparison parameter lies strictly below one, since a+b>1. Replacing the actual k by the comparison K is legitimate only in the positive-k branch, where the deficit decreases with k; the source makes precisely that split.

I independently differentiated the fixed-radius expressions. With L=a*y+b*x, y'=-x/y and J=abR^2/L^2, the exact identities are

    K'=abR^2/(yL^2)>0,
    D'/2=[y*(1+b-J)+K*(x-J)]/y.

The square comparison L^2>=4abxy is valid, and 4<=R^2<=5 with x>=1 gives 1<=y/x<=2. Thus J<=5/8 throughout the entire interval. Both terms making D' positive are strictly positive when K>0.

I checked the transition logic at K=0. The negative-K expression is already strictly positive; K is increasing. If the positive-K interval starts after x=1, its initial value is covered continuously by that strict comparison. If it starts at x=1, the complete endpoint proof supplies the base value. There is no missing sign-changing interval or reliance on sampled values.

## 4. Exact endpoint factorization and the full a interval

At x=1, write

    L=a*y+b,
    K_num=a*((a-1)*y+b).

After using a^2+b^2=1, the numerator of the comparison deficit is

    a^2 L^2-2y*K_num*L-K_num^2.

I expanded it directly. Its coefficients are

    y^3: 2a^2(1-a);
    y^2: -a(2a-1)(2b-a);
    y:   -2ab(b-a);
    constant: 0.

These give exactly the target's factorization D(1)=a*y*P(y)/L^2.

The implication K>0=>a>1/2 is strict and legitimate, since 1-a>0. I checked every uniform comparison in P':

    a(1-a)>1/5,
    y>5/3,
    2a-1<1/2,
    2b-a<5/4,

which yield P'>17/24. The second negative-term bound uses b<2a and a<=b to preserve the nonnegative factor 1-2a^2. The comparison H(a) is increasing up to the retained endpoint a=1/sqrt(2), and the resulting reserve is precisely

    P(sqrt(3))>(13/16)*(sqrt(2)-1)>0.

Thus the endpoint proof covers the whole continuous a interval, including a=b.

For C_11 at y>=x and a>=1/4, I checked the complete concavity reduction in x, both strict radical endpoint comparisons, the actual center-coordinate identity, and the exact relation

    |C_11|^2-|C_01|^2=2(E.u+1/2)<0.

For 0<a<1/4, the r=0 rewritten deficit is strictly positive on the stated radius domain. At r=1, A_3*(2-A_3)>-9/16 and the vertical contribution is >123/80, leaving the printed strict reserve 39/40. These two a ranges exhaust every positive permitted angle.

## 5. Both physical corollaries and their limits

I rederived the complete unique-mask force and torque equations:

    F_V=(-nu,mu)=Lambda*(-x,y),
    mu*p+nu*(y-1+r*b)=0.

Using the unchanged lower mean bound p>=r*a-x gives exactly

    r*a*y<=x*(1-r*b).

Only the positive total unique-corner coefficient is divided out. The entire original mean interval remains, and no higher-degree W equation is invoked.

For the horizontal physical-two mask y=1/2, the first scalar alternative applies directly because x=sqrt(R^2-1/4)>1. No circle-weight ratio, upper radius bound or torque inequality is needed. Both physical corners and either individual zero weight remain. The vertical two-circle mask x=1/2 is explicitly outside the conclusion.

The target correctly leaves the actual W placement, the actual original mean interval, a<=b, and the original family allocation to its caller. It does not silently prove those hypotheses.

## 6. Endpoints, independence and adoption boundary

I checked r=0, r=1, a=b, x=1, y=1/2, y=x, R^2=4, R^2=5, and equality in the original torque/mean inequality wherever they satisfy the actual theorem alternative. Every final corner estimate remains strict. The deliberately excluded a=0 aligned counterexample is real and the target does not hide it.

The four-corner conclusion implies the whole closed square is strictly inside the disk by convexity. No original physical mask, individual coefficient, degree, actual mean or normal is altered.

This full independent PASS can be cited by a later physical caller only after that caller's complete actual chart and original-force joins have themselves been reviewed. I have not treated the scalar result as a whole original-family exclusion. No pose search, numerical sampling, Lean compilation, CI, remote write or ledger change was used.

