# Independent hand review: negative separating-normal half and cap equality

October 31, 2026. Reviewer: parallel endblock agent. Reviewed source:

    PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md.

**Scope:** independent reconstruction of the physical support reduction and triangle-frame formulas; every branch of Section 5; the equality derivation in Section 6; and the direct chain summation in Section 7. The detailed positive-normal scalar estimates of Sections 3--4 are assigned to a separate reviewer and are not certified by this review.

No mathematical program, symbolic script, numerical interval cover, Lean or CI was used. All calculations below are hand identities and rational comparisons.

## 1. One transcription correction

The displayed Section 5 comparison

    B(19/20)^2 = 872313/1280

must read

    B(19/20)^2 = 872289/1280.

Indeed

    B(t)^2 = 89505/256 + (5589/16)t,

so at t=19/20 its numerator over 1280 is

    447525 + 424764 = 872289.

The stated upper bound B(19/20)<209/8 remains true. The smaller corrected value strengthens it, and no later estimate changes.

No other defect was found in the assigned sections. This review accepts those sections after the displayed numerator is corrected.

## 2. Physical reduction and the three triangle-frame formulas

Starting from the actual separating inequality

    n dot (c_B-c_M) >= h_M(n)+h_B(n),

the vectors -a e-k n and -b e+k n give the exact sign in the support bound. Containment bounds each center projection by its circle support minus the corresponding square support. The penalty is exactly the sum of three square support functions in (6); it is not a center-distance relaxation.

The separating normal is an own axis of at least one actual square by the rectangle Minkowski polygon facet argument. The other square's orientation can be bounded by the minimum bounding-box semiperimeter of the three-edge triangle.

For the triangle with vertices 0,w e,-k n, direct projection gives:

- e-frame: w+k[s+max(c,0)];
- n-frame: k+w(c+s) for c>=0, k+w s for -k/w<=c<=0, and w(s-c) for c<=-k/w;
- diagonal frame: L+wk s/L for c>=-k/w and w(w+kc+ks)/L for c<=-k/w.

These agree with (7). At the transition c=-k/w both formulas join. The denominators are nonzero because w>k.

The finite edge-parallel minimization is justified by the strictly negative second derivative of the positive expression A cos(theta)+B sin(theta) between successive projection-extremum changes. The degenerate c=+/-1 triangles are covered directly. Thus the five ownership combinations in (8) are exhaustive.

## 3. Section 5 constants

The following exact squared values were independently recomputed:

    A(9/32)^2 = 498847/256,
    B(9/32)^2 = 229311/512,
    A(19/20)^2 = 1475381/1280,
    B(19/20)^2 = 872289/1280.

They imply the printed rational upper bounds. The subsequent constants are correct:

    (133/64)(177/4+85/4) = 17423/128,
    (133/64)(34+209/8) = 63973/512,
    63973/512 - (a+b+k) = 26885/512 < 211/4.

The derivative sign K'<0 follows from a/A>b/B at zero and the opposite monotonicities of those two ratios. Its strict concavity and tangent (26) have the stated signs.

## 4. All five negative-normal branches

### 4.1 The N_a,E_b entry

The support sum on [0,t0] is b+k+kt+(a+k)s. The second-derivative comparison uses the exact identities

    A^2-a^2s^2=(at-k)^2,
    B>=b,

so the stated convexity is valid.

On [t0,t1], concavity of t+s and the two printed endpoint radical comparisons give t+s>49/40. The support sum is

    b+(a+k)(t+s)>54847/640.

Subtracting from K<137 gives 32833/640<T. On [t1,1] the support sum is at least a+b+k. All shared endpoints are retained.

### 4.2 The E_a,N_b entry

The tangent reduction is exactly

    T-(b+k/2)t+(b+k)(1-s).

The ratio is (b+k/2)/(b+k)=71/94, and

    t/(1+s)<=19/26<71/94

on the printed interval. The final interval uses the same lower support sum a+b+k. Strictness away from t=0 is justified.

### 4.3 The N_a,N_b entry

The low-interval tangent reduction and the 9/62 bound are correct. Beyond t0, its support sum exceeds that of 4.1 by exactly

    (b-k)(t+s-1)>=0.

This gives the whole stated interval without dropping a boundary.

### 4.4 The D_a,N_b entry

For t<=t0, the factorization

    D_a(-t)-N_a(-t)=(A-k)(A-as)/A

is correct and nonnegative.

For t0<=t<=2/3, writing Delta=A-a+kt gives

    E_a(-t)-D_a(-t)
      = a Delta/A + ks(1-a/A)
      <= a Delta/A
      <= a k^2s^2/[2(a-k)^2]
      <=1863/529<4.

The original inequality A<a holds throughout this interval. The corresponding strict improvements are correctly bounded by 22833/5120 and 501/80 at the two endpoints; concavity supplies the whole interval.

For t>=2/3, the squared difference in the positive comparison is precisely

    u^2 s [2(t-u)-s q^2].

The bracket is positive from q<=1, 2(t-u)>=37/48 and s<3/4. At t=1 the factor s vanishes and equality in the comparison is harmless; the surrounding cap bound remains strict. This confirms the endpoint as well as the open interval.

### 4.5 The N_a,D_b entry

The identity

    D_b(t)-b-ks=(B-b)(B-ks)/B

and B>=b+kt imply (30), because ks/B<1/sqrt(2)<3/4. The low-interval tangent bound has the correct coefficient 3k/4.

The concave lower function J has the printed values

    J(t0)>857151/10240>167/2,
    J(4/5)=353/4.

Consequently the resulting bound is 6735/128<T.

On [4/5,t1], the bounds A(4/5)<37 and B(4/5)<51/2 give K<130. At t1 the lower estimate s>3/10 yields

    J(t1)>99781/1280>311/4,

so its concavity gives the entire stated interval. The final interval uses D_b>=B and the concavity of b+(a+k)t+a s, with its minimum lower bound a+b+k. All five entries are therefore covered.

## 5. Equality and the chain terminal

The Section 5 estimates are strict whenever c<0. At c=0 the diagonal-frame penalty exceeds w+k by

    (L-w)(L-k)/L>0.

Together with strictness in the separately reviewed positive half, only c=0 and e/n-aligned square frames can attain equality. The triangle-frame argument has no hidden interval of equal minima, because its positive trigonometric expression has strictly negative second derivative within each fixed-extrema interval.

For n=sigma(0,1), the actual maximizing circle corners are

    z_M=(-2,-9sigma/16),
    z_B=(-3/2,23sigma/16).

Subtracting the aligned corner offsets gives centers

    (-3/2,-sigma/16), (-1,15sigma/16),

which are exactly the displayed equality centers after renaming sigma. They have vertical separation one, satisfy the actual separating equality and attain radius squared 1105/256. The radius is necessarily r because the second support bound in (5) is strict below r.

Finally the projection-chain summation is valid without any common coordinate-separation assumption for cross-chain pairs. The four-chain endpoint difference is at least the total widths of its two interior squares, hence at least two. The three-chain analogue is at least one. The actual physical endpoint pairs are disjoint and can therefore use the cap theorem directly. The weights satisfy

    2a+b=2T=211/2.

At equality every intervening projection width is one and every intervening projection gap is zero, so the frames are aligned and the stated projected coordinates follow. The perpendicular coordinates remain free subject to the original physical packing; no unproved equality rigidity is inserted.

This proves the stated direct seven-square terminal once the complementary positive-half scalar review is complete. It does not prove the global extraction of such chains or close an original n=9 parent by itself.

