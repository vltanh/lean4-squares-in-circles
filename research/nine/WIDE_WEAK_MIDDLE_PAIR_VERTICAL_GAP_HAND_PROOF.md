# A wide inner frame forces more than 81/100 vertical separation

November 2, 2026. Complete physical hand proof, with exact rational
reserves. No new finite search, Lean, Lake, or CI is needed.

## 1. Statement and original width resource

Retain four original physical unit squares A,B,C,D in the closed disk
Q=1105/256. Their two outer comparisons are actual and the middle
comparison is its original horizontal cone comparison. The accepted
outer-link theorem supplies

    1/2≤hB,hC<13/20,
    etaB+etaC<1/30,       eta(h)=h+1/(4h)−1,
    xC−xB≤61/30−hB−hC.

The last inequality follows directly from the two actual outer links,
the endpoint center bound |xE|<91/60 and hA+hD≥1. Put

    H=max(hB,hC),       K=min(hB,hC).

**Theorem.** If H≥59/100, then

    |yC−yB|>81/100.                                (1)

This retains both original main frames and their original physical
pair. It does not turn their cone comparison into an actual projection
separation.

The function eta increases on [1/2,13/20] and eta(3/5)=1/60. Therefore
the original resource implies

    K≤min(H,3/5).                                  (2)

Write k=√(1/2−H²), a=H+k and b=H−k. Every folded owner angle of
the original B/C pair is no larger than that of H. Its tangent is less
than 1/2: throughout the interval a>9/10 and b<2/5.

## 2. Every physical owner is covered by the wider frame

Assume contrary to (1) that |yC−yB|≤c=81/100. Set

    d=61/30−H−K,         s=1+H−K.

The true horizontal gap is nonnegative and at most d. The true support
of every original owner axis is at least s, by the accepted physical
two-frame support bound 1+|hB−hC|. For an owner with folded components
(ai,bi), every possible signed projection is at most one of

    ai*d+bi*c,          bi*d+ai*c.                 (3)

Both expressions increase with its folded angle up to the H-frame.
Indeed d∈[11/15,283/300] and tan(theta)<1/2. Their derivatives have
the respective signs of c−d*tan(theta)>0 and
d−c*tan(theta)>0. Thus it suffices to prove

    s−a*d−b*c>0,       s−b*d−a*c>0.               (4)

For fixed H the derivatives of these residuals with respect to K are
a−1≤0 and b−1<0. In view of (2), the worst allowed value is
K=min(H,3/5). This is a monotone bound on the same original pair,
not a replacement orientation.

## 3. Exact residuals for 59/100≤H≤3/5

Here use K=H, so s=1 and d=61/30−2H. Put

    A(H)=2H²−(853/300)H+1,
    q(H)=367/300−2H>0.

The two residuals in (4) are A−qk and A+qk.
The function A decreases on this interval, so

    A(H)≥A(3/5)=7/500.

This proves the vertical residual positive. For the horizontal one,

    (A−qk)'=4H−853/300+2k+qH/k>0.

For example H≥59/100, k>37/100 and q>0 give a lower derivative
bound 77/300>0 before even using the last positive term. Its minimum
is consequently at H=59/100. At that endpoint k<39/100, and

    A(59/100)=559/30000,   q(59/100)=13/300,
    A−qk >559/30000−(13/300)(39/100)=13/7500>0.

Every radical comparison here follows by squaring positive quantities:
k²≥7/50>(37/100)² and k(59/100)²=1519/10000<(39/100)².

## 4. Exact residuals for 3/5≤H≤13/20

Now use K=3/5, so s=H+2/5 and d=43/30−H. Put

    A(H)=H²−(373/300)H+2/5,
    q(H)=187/300−H.

The residuals are again A−qk and A+qk. Completing the square gives

    A(H)≥2/5−(373/600)²=4871/360000.

Also k<3/8, the positive part of q is at most 7/300, and the negative
part has absolute value at most 2/75. Hence

    A−qk >4871/360000−(7/300)(3/8)
          =1721/360000>0,
    A+qk >4871/360000−(2/75)(3/8)
          =1271/360000>0.

These bounds include the sign change of q and the shared H=3/5 face.
Equations (3)–(4) now show that none of the original physical owner
axes can separate B and C under the supposed vertical gap. This
contradicts their physical nonoverlap and proves (1).

## 5. Consequence for an original lower-side extra

In the routed low-floor 010/11 domain, the completed main-height theorem
gives yB,yC<−1/4. The independent outer-cone bound gives yB,yC>−6/5.
Suppose an original extra S is in a closed side strip and below its
assigned original main M. The accepted 3,387-leaf physical pair envelope
gives

    yM>f(hM),
    f(h)=−(2/3)h+max(0,min((h−1/2)/6,(27/50−h)/3))+1/400.

The full transfer audit is `LOWER_SIDE_HEIGHT_ENVELOPE_01011_TRANSFER_AUDIT.md`.
In particular f(h)≥−13/30+1/400>−9/20 on the complete inner range.

If hM≥59/100, (1) applies. M cannot be the lower of the two main
centers: that would put the other main above

    −9/20+81/100=9/25>−1/4,

contrary to its completed upper height bound. Therefore M is the higher
main, and the other original main's lower height bound yields

    yM>−6/5+81/100=−39/100.                       (5)

Thus a lower-side extra supplies the improved necessary envelope
max(f(h),−39/100) when its assigned main has h≥59/100; the original
f(h) remains valid below that threshold. Both closed width pieces may
include their common boundary. This implication uses the otherwise
missing original main pair, including its physical separation.

For completeness, (1) also implies max(yB,yC)>−39/100 whenever either
inner width is at least59/100, independently of side extras. A future
stronger uniform main-height theorem could consume this implication;
no such stronger theorem is assumed here.

The vertical-gap theorem and envelope improvement are complete local
hand consequences. They do not themselves exclude every lower-side
extra or change the fixed mask ledger.
