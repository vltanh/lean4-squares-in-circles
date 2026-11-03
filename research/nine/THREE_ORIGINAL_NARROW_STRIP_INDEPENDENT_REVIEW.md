# A universal three-square strip inequality with a quadratic endpoint correction

Independent derivation and arithmetic review, November 3, 2026.
No Lean, Lake, or CI. The argument is a finite hand proof; the seven Bernstein
coefficients below were additionally recomputed using an independent Python
`Fraction` conversion. No numerical optimization is a premise.

The middle-square Steiner construction and the rational point `(2/5,1)` were
proposed by the B-family agent. This note independently derives the scalar
calculation, checks every Bernstein coefficient, and gives the original-coordinate
quadratic consequence needed by the all-nine model.

## 1. Statement in the original coordinates

Let three independently oriented, interior-disjoint unit squares have centers
`I=(x_I,y_I)`, `F=(x_F,y_F)`, `H=(x_H,y_H)`. Suppose

    y_I <= y_F <= y_H,
    max(x_I,x_F,x_H)-min(x_I,x_F,x_H) <= w <= 7/10.

Put `V=y_H-y_I` and `Delta=x_H-x_I`. Then

    V + (5/14) Delta^2 >= min { 2, 208/75 - (29/15) w }.      (T)

In particular the following two exhaustive guarded rows are valid:

    w <= 2/5:
        V + (5/14) Delta^2 >= 2;

    2/5 <= w <= 7/10:
        V + (5/14) Delta^2 + (29/15) w >= 208/75.            (R)

The two rows agree at `w=2/5`. The parameter `w` may be an actual horizontal
spread or any proved upper bound on it. When the horizontal extrema are named,
`w` may be their coordinate difference, making (R) a degree-two polynomial
inequality in the original coordinates. It is valid for every physical chirality
and contact, without any circle hypothesis. No ninth square is discarded when
this necessary inequality is used inside a nine-square proof.

The correction is essential: an unguarded claim `V>=2` for a narrow center
strip is false for three parallel squares placed along a slightly tilted unit
column. No such claim is used here.

## 2. The equal-endpoint geometric lemma

First suppose the endpoint centers are on a common vertical line and the middle
center lies vertically between them. Let `L` be their vertical separation and
`d` the horizontal distance from their line to the middle center. If `d<=7/10`,
then

    L >= B(d),   B(d):=min { 2, 208/75 - (29/15)d }.          (E)

Translate the middle square to center zero and call it `S`. Every other original
center has distance at least `1/2` from `S`: its open incircle of radius `1/2`
is contained in its own open square. Consequently both endpoint centers lie
outside the interior of the rounded square

    K = S + closed_disk(0,1/2).

The set K contains the closed unit disk because S contains the half-unit disk.
Thus, on the vertical line at distance d<=7/10, the K-section contains height
zero in its interior. The endpoint centers lie on opposite sides of zero and
outside the interior of K. Their separation is therefore at least the complete
length of that vertical section. Boundary contact is allowed throughout.

Let P be the vertical Steiner symmetrization of S: each vertical section is
replaced by a centered section of the same length. The vertical Steiner
symmetrization of K contains

    P + closed_disk(0,1/2).                                 (S)

Here is a direct section proof. A vertical section of S at x_1, added to a
vertical disk section at x_2, is contained in the section of K at x_1+x_2.
Its length is the sum of the two section lengths. The centered K-section
therefore has at least their sum as its length. Taking all decompositions
x=x_1+x_2 proves (S). No unproved equality of Steiner symmetrization with a
Minkowski sum is asserted.

## 3. One rational point belongs to every rounded symmetrized square

Choose a canonical square angle with side components a>=b>=0,
`a^2+b^2=1`. Set

    t=b/a in [0,1], r=sqrt(1+t^2),
    k=(1-t)/(2r), h=(1+t)/(2r), A=r/2.

The upper boundary of P is

    A                         for |x|<=k,
    (h-|x|)/(2ab)             for k<=|x|<=h, when b>0.

Thus `(k,A)` is an actual point of P. The case b=0 is the aligned rectangle
and belongs to the first formula.

We prove that the fixed point Z=(2/5,1) belongs to P+disk(0,1/2).
For 0<=t<=1/6, k>=5/(2sqrt(37))>2/5 and A>=1/2. Hence `(2/5,A)`
is in P and its distance from Z is at most 1/2.

For 1/6<=t<=1, define

    f(t) = (k-2/5)^2 + (1-A)^2.

We show f is convex and both endpoint values are strictly below 1/4.
A direct simplification gives

    f(t)=4/25+5/4-r+r^2/4-t/(2r^2)-(2/5)(1-t)/r,

and differentiation gives

    f''(t) = (2/5)(1-3t-2t^2)/r^5
             + t(3-t^2)/r^6 + 1/2 - 1/r^3.

Equivalently,

    10 r^6 f''(t)
      = 5(1+t^2)^3+30t-10t^3-r(6+12t+18t^2)
      >= P_6(t),

where `r<=1+t^2/2` and

    P_6(t)=-1+18t-6t^2-16t^3+6t^4+5t^6.

On [1/6,1], the degree-six Bernstein coefficients of P_6 are exactly

| k | coefficient b_k |
|---|---:|
| 0 | 82301/46656 |
| 1 | 29681/7776 |
| 2 | 253/48 |
| 3 | 139/24 |
| 4 | 191/36 |
| 5 | 13/3 |
| 6 | 6 |

Explicitly, with `s=(6t-1)/5`,

    P_6(t)=sum_(k=0)^6 b_k binom(6,k) s^k(1-s)^(6-k).

All coefficients are positive, and the Bernstein basis is nonnegative with
sum one on [0,1]. Hence P_6>0, so f''>0 on the complete interval.

At t=1/6, `k=5/(2sqrt(37))` lies in [2/5,21/50), while
`A=sqrt(37)/12>101/200`. Consequently

    f(1/6) < (1/50)^2+(99/200)^2
             =9817/40000 <1/4,

with reserve 183/40000. The bounds follow by squaring positive quantities:
625>592, 62500<65268, and 92500>91809. At t=1,

    f(1)=83/50-sqrt(2)<1/4,

since sqrt(2)>141/100, whose squared reserve is 119/10000.
A convex function on a closed interval is at most the larger of its endpoint
values. Thus f<1/4 on [1/6,1]. The point `(k,A)` is therefore within distance
1/2 of Z. This completes the fixed-point assertion at every angle, including
zero slope, diagonal slope, and the common endpoint t=1/6.

## 4. Convert the fixed point into the full strip envelope

The convex unconditional body P+disk(0,1/2) contains the unit disk and the point
`(2/5,1)`. In particular it contains `(0,1)` and `(7/10,71/100)`; for the latter,

    1-(7/10)^2-(71/100)^2=59/10000>0.

Convexity therefore gives upper half-height at least 1 for 0<=d<=2/5, and at
least

    1-(29/30)(d-2/5)=104/75-(29/30)d

for 2/5<=d<=7/10. Both lower bounds are bounds on the centered section of K
by (S). Doubling them proves (E). The function B is nonincreasing on [0,7/10].

## 5. Rotation is valid for the original unequal endpoints

Return to the original centers and write

    F-I=(u,v), H-F=(u',v'), H-I=(Delta,V).

All pair center distances are at least one. Since the common horizontal span
is at most w<=7/10,

    v,v' >= sqrt(1-w^2) >= sqrt(51)/10 >7/10,
    V>7/5.

In particular the original weak vertical ordering is automatically strict.
The scalar product of F-I with H-I satisfies

    (F-I) dot (H-I)=u Delta+vV
       >= -w^2+2(1-w^2)=2-3w^2 >=53/100>0.

The identical estimate for `(H-F) dot (H-I)` shows that after rotating all
three originals so H-I is vertical, F projects strictly between the endpoints.
Thus the middle-order guard of (E) is proved, rather than assumed after rotation.

Let L=|H-I| and let d be F's perpendicular distance to the endpoint line.
The point of that line at original height y_F has x coordinate
`x_I+Delta*v/V`, a convex combination of the endpoint x coordinates. Its
horizontal distance from F is at most w. Therefore

    d = (V/L) |x_F-x_I-Delta*v/V| <=w.

Applying (E) after the common rigid rotation gives `L>=B(d)>=B(w)`.
All three physical frames and physical separation constraints are preserved.

Finally

    L=sqrt(V^2+Delta^2)
      <= V+Delta^2/(2V)
      <= V+(5/14)Delta^2,

where the first inequality follows by squaring nonnegative quantities and
the second uses V>7/5. Combining these inequalities proves (T) and (R).

## 6. Safe linear consequence from an already proved endpoint interval

If a caller additionally proves `ell<=Delta<=u`, then

    Delta^2 <= (ell+u)Delta-ell*u

by `(Delta-ell)(Delta-u)<=0`. Consequently a valid necessary linear row is
obtained from (R) by replacing its positive square term with
`(5/14)((ell+u)Delta-ell*u)`. The interval must hold for the complete caller;
a numerical pose or a bound from a child cannot be promoted to its parent.

No whole cell or mask is declared closed by this theorem alone. A complete
caller must establish the three distinct original labels, vertical order,
horizontal width bound, and any bound used for the optional linear row.
