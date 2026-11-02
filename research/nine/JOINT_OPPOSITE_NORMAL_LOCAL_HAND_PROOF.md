# A joint sharp neighborhood for all central-separator signs

This hand proof treats five physical squares and retains the central
square only once. Sections 1--6 prove a quantitative local theorem for
opposite central normals without a central floor. Section 7 extends the
argument to arbitrary signs of both central normals, using the whole
floor one tenth. It supplies the complete four-dimensional sharp cube
for a possible larger joint terminal. It does not close the complementary
parameter domain or a full nine-square mask.

Write

    Q=1105/256, r=sqrt(Q), a=46, b=27/2,
    K=207/16, T=211/4, eps=1/64.

For a centered physical unit square S write H_S(v) for its support
halfwidth and h_S=H_S((1,0))=H_S((0,1)). Put `x_+=max(x,0)`.

## 1. Local joint theorem

Let E_L,E_R,L,R,P be physical unit squares in the centered disk of
radius R0<=r. Suppose there are genuine separating vectors

    n_L=(w_L,1), E_L to L;   n_R=(-w_R,1), E_R to R;
    m_L=(-1,-t), P to L;     m_R=(1,t), P to R,

where

    |w_L|, |w_R|, |t| <= eps.

No separator ownership, floor, center-cone comparison, or common
orientation is required. Then, with

    D=x_E_R-x_E_L-h_E_L-h_E_R,

one has the quantitative bound

    aD+b <= 2T-(157/64)(|w_L|+|w_R|+|t|).           (1)

It is strict if R0<r. Thus, for endpoints of an actual four-chain,
whose adjusted span satisfies D>=2, every nonzero local slope is
excluded even at radius r. At zero slopes the ordinary actual
four-plus-three equality route remains.

## 2. One endpoint-and-shoulder support expression

In the right frame put `n=(-w,1)`, `m=(1,z)` and

    A=sqrt((a+Kw)^2+K^2),
    B=sqrt((b-Kw)^2+(K+bz)^2),
    d=sqrt(1+w^2), e=sqrt(1+z^2), p=1+wz,
    q=z-w.

The endpoint and shoulder penalties are

    P_E=a h_E+H_E(a e_x-Kn)+K H_E(n),
    P_S=H_S(bm+Kn)+b H_S(m)+K H_S(n).

For every physical orientation and `|w|,|z|<=eps`, we claim

    r(A+B)-P_E-P_S
       <= T-(K/2)|w|+(3K/2)z-K(z-w)_+
                      +48w^2+25z^2.               (2)

The next two sections prove this scalar statement using only rational
comparisons and elementary differentiation.

## 3. Lower bounds for the two support penalties

Each penalty is the sum of the two side lengths of the bounding
rectangle of a triangle in the square's frame. Its minimum over all
frames occurs at an edge alignment: between changes of an extreme
projected vertex the quantity is a positive function
`U cos(theta)+V sin(theta)` with strictly negative second derivative.

### Endpoint triangle

The coordinate-edge candidate is exactly

    E0=a+K+K w_+.

The n-edge candidate, for w>=0, is at least E0, since its difference
from E0 is `(1+w-d)(a/d-K)>=0`. For w<=0 that candidate is
`a/d+Kd>=a+K-23w^2`, using `1/d>=1-w^2/2` and d>=1.

The diagonal candidate is `A+aK/A`. Its projection formula is valid
throughout this cube because `K^2 d^2+aKw>0` and `a^2+aKw>0`.
Here `47<A<49`, so

    A+aK/A >47+aK/49 > a+K+K/64 >= E0.

For the last strict comparison the exact difference is `289/50176`.
It follows in every frame that

    P_E >= a+K+K w_+-23w^2.                         (3)

### Shoulder triangle

The three edge alignments give

    N=Kd+b p/d+b q_+/d,
    M=be+K p/e+K q_+/e,
    V=B+bKp/B.

The projection formulas hold because p>0, `b|q|<Kd^2`, and
`K|q|<be^2`. For the diagonal, both inner projection numerators
`b^2 e^2+bKq` and `K^2 d^2+bKq` are positive.

Use `1/d>=1-w^2/2`, `1/e>=1-z^2/2`, `|wz|<=(w^2+z^2)/2`,
and `q_+<=2eps`. Since b>=K,

    N >= b+K+Kq_+-b(1+eps)w^2-(b/2)z^2,
    M >= b+K+Kq_+-(K/2)w^2-K(1+eps)z^2.

All four displayed quadratic coefficients are below 14. Moreover
`73/4<B<77/4`, and p>=1-eps^2, so

    V >73/4+(4bK/77)(1-eps^2)
       >b+K+2Keps >=b+K+Kq_+.

The second strict difference is `172669/360448`. Consequently

    P_S >= b+K+K(z-w)_+-14(w^2+z^2).                (4)

Every denominator is positive. The numerical-looking norm bands used
above follow directly by squaring their rational endpoints; Section 6
prints the corresponding reserves.

## 4. Upper bounds for the two norms

The sharp identities are

    A(0)=23r,       B(0,0)=9r,
    32Q-a-b-2K=T.

For A, its derivative at zero gives `r A'(0)=2K`. Its second derivative
is `K^4/A^3`. Since A>47 and r<21/10, the second-order Taylor remainder
is less than w^2. Thus

    r A <=23Q+2Kw+w^2.                              (5)

For B, regard it as the Euclidean norm of `(b,K)+(-Kw,bz)`.
Along every segment from the origin to a point in the parameter cube,
that vector has norm greater than 18. The Hessian of Euclidean norm
has operator norm at most 1/18. Taylor's theorem therefore gives

    r B <=9Q-(3K/2)w+(3K/2)z
                  +(r/36)(K^2 w^2+b^2 z^2)
         <=9Q-(3K/2)w+(3K/2)z+10w^2+11z^2.          (6)

Indeed `(21/10)K^2/36<10` and `(21/10)b^2/36<11`.
Adding (5)--(6) and subtracting (3)--(4), then using
`w/2-w_+=-|w|/2`, proves (2).

## 5. The two opposite central supports cancel their center coefficient

Add K times each endpoint separating slack and b times each central
separating slack to `aD+b`. Because `m_L+m_R=0`, P's center coefficient
vanishes exactly. The disk-support inequalities for the other four
squares give

    aD+b <= b+H(w_L,-t)+H(w_R,t)
                       -b H_P(m_L)-b H_P(m_R),

where H denotes the left side of (2) for the corresponding original
endpoint and shoulder. The left expression is understood after
horizontal reflection; no individual square is moved.

Every unit square contains its centered disk of radius one half.
Consequently

    H_P(m_L)+H_P(m_R)=2H_P((1,t))
                   >=sqrt(1+t^2)>=1.

The constant b is therefore paid. Apply (2) twice; the terms linear in
t cancel. Put

    W=|w_L|+|w_R|,
    C=(-t-w_L)_+ +(t-w_R)_+.

The remaining upper bound is

    aD+b-2T <=-(K/2)W-KC
                  +48(w_L^2+w_R^2)+50t^2.          (7)

For t>=0, `t<=|w_R|+(t-w_R)_+`; for t<=0 the reflected inequality
gives `|t|<=|w_L|+(-t-w_L)_+`. Thus `|t|<=W+C`, and hence

    (K/2)W+KC >= (K/4)(W+|t|).

The quadratic part of (7) is at most `50eps(W+|t|)`. Since

    K/4-50eps=207/64-50/64=157/64,

(1) follows. If R0<r, the original radius replacement is strict:
each endpoint support coefficient has vertical component -K and is
nonzero. This finishes the proof.

## 6. Rational arithmetic reserves

These comparisons verify the finite norm bands and triangle margins:

| Comparison | Positive rational reserve |
|---|---:|
| `(a-K eps)^2+K^2-47^2` | `58533729/1048576` |
| `49^2-(a+K eps)^2-K^2` | `103790751/1048576` |
| `47+aK/49-(a+K+K eps)` | `289/50176` |
| `(b-K eps)^2+(K-b eps)^2-(73/4)^2` | `6014369/1048576` |
| `(77/4)^2-(b+K eps)^2-(K+b eps)^2` | `10414687/1048576` |
| `73/4+(4bK/77)(1-eps^2)-(b+K+2K eps)` | `172669/360448` |

The remainder coefficients may be bounded using

    (21/10)K^2/36=99981/10240<10,
    (21/10)b^2/36=1701/160<11.

This is a finite hand calculation. No numerical search or exclusion
program is a premise of the theorem.

## 7. The full sharp cube, with every central-separator sign

Keep the five physical squares and endpoint separators of Section 1,
but now let the two central separators be arbitrary

    m_L=(-1,z_L),       m_R=(1,z_R),
    |w_L|, |w_R|, |z_L|, |z_R|<=1/64.

Assume also the original central whole-floor condition

    y_P-h_P>=1/10.

Then the stronger four-variable local conclusion is

    aD+b <=2T-(33/160)(|w_L|+|w_R|+|z_L|+|z_R|).     (8)

It is strict whenever R0<r. In particular every nonzero point of this
closed cube is excluded at radius r when D>=2. Again no separator owner
or square orientation is prescribed.

### The central triangle for signed slopes

Put `S=z_L+z_R`. We first need

    |S| h_P+H_P(m_L)+H_P(m_R)>=1+|S|                 (9)

whenever `|S|<=1`. To prove it, reflect vertically if necessary so
S>=0, and consider the triangle with vertices `(0,0),(1,z_R),(0,S)`.
Its bounding-rectangle side sum is the left side of (9). The
vertical-edge alignment has horizontal extent one and vertical extent
at least S.

For a sloping-edge alignment put `d_i=sqrt(1+z_i^2)`. If z_i>=0,
the third vertex projection lies between the edge endpoints: this is
equivalent to `z_L*z_R<=1`, which holds because either the product is
nonpositive or it is at most `S^2/4<=1/4`. The candidate is then
`d_i+S/d_i`. If z_i<0, the third projection lies beyond one endpoint,
so the candidate is `d_i+S(1-z_i)/d_i`, which is larger. In either
case it is at least `d_i+S/d_i>=1+S`, since `1<=d_i` and `S<=1`.
The edge-alignment minimum principle proves (9). At S=0 the triangle
is a segment; its minimum rectangle side sum is at least one directly.

### Keep the original common height of P

Add the same four separation slacks as in Section 5. P's center
coefficient is now `(0,-bS)`. Write Y=y_P and h=h_P. If S>=0, use
`Y>=h+1/10`. If S<0, use the valid containment bound `Y<=r-h`.
Together with (9), these give respectively

    b-bS Y-bH_P(m_L)-bH_P(m_R) <=-(11/10)bS,

    b-bS Y-bH_P(m_L)-bH_P(m_R) <=b(1-r)S.           (10)

Here the b on the left is the original constant in the objective
`aD+b`. The first inequality uses the given floor, and the second uses
the top of the same physical square. Their directions follow from
the sign of -S; no height inequality is reversed incorrectly.

Put

    W=|w_L|+|w_R|, Z=|z_L|+|z_R|,
    C=(z_L-w_L)_+ +(z_R-w_R)_+,
    alpha=153/160, B0=K/2-alpha=441/80.

The sum of the two scalar estimates (2), followed by (10), has a
quadratic error at most

    48(w_L^2+w_R^2)+25(z_L^2+z_R^2)
       <=(48/64)(W+Z).                             (11)

Its linear deficit, when S>=0, is

    (K/2)W+KC-(729/160)S.                          (12)

For any real w,z, since `0<B0<K`, one has

    B0|w|+K(z-w)_+>=B0 z_+.

Thus (12) is at least

    alpha W+(B0/2)(Z+S)-(729/160)S
      =alpha W+(441/160)Z-(288/160)S
      >=alpha(W+Z),                               (13)

because `0<=S<=Z`.

When S<0, the linear deficit is instead

    (K/2)W+KC+b(39/16-r)|S|.

Since `r<21/10`, its last coefficient is greater than `729/160`.
The same elementary inequality gives the lower bound

    alpha W+B0(z_L_++z_R_+)+(729/160)|S|
       >=alpha(W+Z),                              (14)

because `Z=2(z_L_++z_R_+)+|S|`, `B0>=2alpha`, and `729/160>=alpha`.

Finally `alpha-48/64=153/160-120/160=33/160`.
Combining (11)--(14) proves (8). The strict subcritical radius step
is exactly the one already explained in Section 5.

This closes the entire sharp cube for a joint five-square certificate;
the argument includes both signs, every zero face, and all physical
normal-owner choices. A finite complement proof must still retain its
original geometric bands and cover every remaining parameter point.

## 8. A variable floor, including the aligned bad-floor neighborhood

The preceding argument has the following explicit parameter form. Let

    -1/24<c<=1/10,
    alpha=(b(1+c)-K)/2>0,
    0<eps0<=1/64,       48eps0<alpha.

Replace the central floor by `y_P-h_P>=c` and the four slope bounds
by `|w_L|,|w_R|,|z_L|,|z_R|<=eps0`. Then

    aD+b <=2T-(alpha-48eps0)
                        (|w_L|+|w_R|+|z_L|+|z_R|). (15)

The same strict subcritical-radius conclusion holds. The scalar estimate
(2) is unchanged, since its domain contains the smaller cube.

For completeness, put `B0=K/2-alpha`. In the S>=0 branch the linear
deficit is

    (K/2)W+KC-(K/2-2alpha)S.

Exactly as in (13), it is at least

    alpha W+(B0/2)Z+(-K/4+3alpha/2)S.

Our floor range gives `0<alpha<=153/160<K/6`. Therefore the last
coefficient is nonpositive, and S<=Z gives the lower bound
`alpha(W+Z)`. In the S<0 branch the proof of (14) still applies,
because `B0>=2alpha` and `b(39/16-r)>729/160>alpha`.
The quadratic part is at most `48eps0(W+Z)`, proving (15).

Three exact instances are:

| Floor c | Slope cube eps0 | alpha | Final strict coefficient |
|---|---:|---:|---:|
| `-1/30` | `1/2048` | `9/160` | `21/640` |
| `-1/60` | `1/512` | `27/160` | `3/40` |
| `-27/1280` | `1/384` | `711/5120` | `71/5120` |

These are local theorems with their original floor and slope hypotheses.
They become exclusions of a physical nine-square neighborhood only after
a caller derives those hypotheses from that neighborhood, without adding
an unproved floor or replacing a weak edge by an actual coordinate edge.
