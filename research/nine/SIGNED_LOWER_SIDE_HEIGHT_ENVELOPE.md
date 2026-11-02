# Two signed lower-side main-height bounds

November 2, 2026. Complete physical hand/table proof with a separate exact
replay. This is a two-original-square lemma, not a full-mask closure.
No Lean, Lake or CI.

## 1. Statement and unchanged physical scope

Reflect horizontally if necessary so an original main M and an original
lower side square S are on the right. They are physical unit squares with
disjoint open interiors; every original corner of S lies in the closed
disk of squared radius Q=1105/256. Keep their independent original frames.
Let

    h=hM in [1/2,13/20], g=1/(4h),
    g-1/60 <= xM <= 61/60-h,
    29/60 <= z=xS <= 13/12, yS<yM.

Assume the main coordinate interval is nonempty, as it is for every
physical outer-actual caller. Write the main's folded signed first axis
as `(a,epsilon*b)`, where a>=b>=0, a^2+b^2=1 and h=(a+b)/2.

The two conclusions are

    epsilon=-1  =>  yM > -1/3,                         (N)
    epsilon=+1  =>  yM > F(h),                         (P)

where

    F(h)=-331/1000 -(9/20)(h-1/2) -(7/4)(h-1/2)^2.

At an aligned main either sign represents the same physical frame; both
bounds are valid. In the left-side caller, epsilon is the negative of
the original global chirality. Equivalently it is the product of that
chirality with the side sign, right=+1 and left=-1.

The hypothesis on the original main center is exactly the accepted
outer-actual band with the nonnegative other-main eta contribution
omitted. No actual middle or short comparison, shoulder height, old
31/60 main-width bound, or condition on an unselected ninth original
is used in this lemma.

## 2. The original physical separator and the main position

Put k=sqrt(1/2-h^2), a=h+k, b=h-k. For S retain its original slope
`t in [0,1]` and chirality s in {-1,+1}, so

    A=1/sqrt(1+t^2), B=t*A, H=(A+B)/2, K=(A-B)/2.

Every genuine owned separator of this original pair has the same exact
support sum

    sigma=(1+|a*A+epsilon*s*b*B|
              +|s*a*B-epsilon*b*A|)/2 >= 1.

The horizontal displacement from S to M is d=xM-z. The stated bands
imply |d|<3/4. Since M is higher, a normal with nonpositive vertical
component has projection less than one and cannot separate the pair.
The four exhaustive upward owned normals are

    (epsilon*a,b), (-epsilon*b,a), (s*A,B), (-s*B,A).

Every numerator sigma-nx*d is greater than1/4. It is therefore sound
to weaken its required clearance by increasing ny to max(ny,1/40).
At ny=0 its horizontal axis was already impossible; including the
finite clipped candidate in the following minimum only weakens it.
For fixed original frames define

    C(xM)=min_n (sigma-nx*(xM-z))/max(ny,1/40).

Then the actual original pair obeys yM-yS>=C(xM).
The function C is the minimum of four affine functions of xM and is
concave. Hence throughout the same original main band,

    C(xM) >= min(C(g-1/60), C(61/60-h)).              (1)

The same original position was minimized only after deriving its
physical inequalities. No independent main positions are chosen for
different physical constraints.

## 3. Retain every original side-square corner

Reflect S vertically. Its chirality becomes -s and its center is
(z,-yS). For that reflected original frame the four signed offsets
are `(H,s*K),(-s*K,H),(-H,-s*K),(s*K,-H)`.
Thus its original circle constraints imply

    -yS <= U(z,t,-s)
         := min_v [sqrt(Q-(z+v_x)^2)-v_y].            (2)

All four radicals are real on the complete parameter root: the largest
absolute horizontal corner is at most 13/12+1/sqrt(2)<sqrt(Q).
Combining (1)--(2) gives the necessary lower bound

    yM >= min(C(g-1/60),C(61/60-h))-U(z,t,-s).        (3)

This bound requires neither yS<0 nor any newly imposed cone comparison.

## 4. The complete three-variable table

For each of the four independent sign choices (epsilon,s), the table
covers the entire closed rational root

    (h,t,z) in [1/2,13/20] x [0,1] x [29/60,13/12].

It proves that the right side of (3) strictly exceeds the relevant
bound (N) or (P):

| Main epsilon | Side s | Target lower height | Strict leaves |
|---|---|---|---:|
| -1 | -1 | -1/3 | 43 |
| -1 | +1 | -1/3 | 82 |
| +1 | -1 | F(h) | 39 |
| +1 | +1 | F(h) | 8,908 |
| Total | | | 9,072 |

The forest has18,140 nodes, maximum depth30, and no frontier. Every
internal event bisects exactly one of the three rational coordinates;
both closed children are retained. The finite certificate is
`signed_lower_side_envelope.json`.

The independent standard-library checker
`verify_signed_lower_side_envelope.py` imports no producer. It uses
exact Fraction intervals and checked outward90-bit square-root bounds,
reconstructs all four roots, every midpoint, both main-position endpoints,
all four physical owners, and all four original circle corners. Every
strict leaf passed, as recorded in
`signed_lower_side_envelope_independent_replay.json`.

For tighter but exact support bounds, the checker uses this elementary
endpoint fact. When the two chiralities agree, the unsigned relative
angle lies between the two extreme endpoint angle differences and the
support `(1+cos(delta)+|sin(delta)|)/2` increases with |delta| on
[0,pi/4]. The minimum is1 if the angle intervals overlap. When the
chiralities differ, their angle sum lies in[0,pi/2]; its support minimum
occurs at an endpoint and its maximum at an endpoint or pi/4. The
pi/4 crossing is tested without trigonometric approximation by
`t+u+t*u=1`. All endpoint supports are reconstructed from rational
slopes and outward radicals. This bounds the original relative angle;
it does not replace either original frame.

The polynomial F decreases throughout this h interval, so its endpoint
values give its full exact interval range. Frame a,k decrease, b,h
increase with folded slope; the corresponding main components use their
exact h endpoint monotonicity. Artificial table points with an inverted
main band are harmless extensions: implication(1) is used only for a
true original main in its nonempty band.

The certificate SHA-256 is

    6276930ef4ca999e2c581ef4da84625353b4442b502458272378f907194a2ed5.

## 5. Use in the weak-middle low-floor continuation

The previous lower-side bound f(h), this signed bound, and the independent
main-pair height bridge may be combined by taking their maximum.
For a hypothetical lower-side original in the low-P-floor domain, the
latter bridge also supplies h<31/50. On h>=57/100 it supplies the
additional lower height3h-211/100. Each bound concerns the same assigned
original main. None imposes a new comparison on the lower side original.

The complete no-lower-side exclusion still requires combining this main
height information with both original selected short pairs and their
shared original P. The present result supplies that information; it
does not declare any fixed mask closed.
