# A sharp five-corner obstruction with arbitrary orientations of both tilted squares

**Status: complete conditional hand theorem.**
Let eight interior-disjoint unit squares fit in a disk
`D_R` centered at zero. Suppose four distinguished
squares A,B,D,E are axis-parallel in one common frame,
normalized to horizontal x and vertical y. Let their
centers be p_A,p_B,p_D,p_E and assume

    (p_B-p_A).y >= 1,       (p_D-p_E).y >= 1,
    (p_B-p_D).x >= 2.                                   (1)

Let G,H be two **other** unit squares with completely
arbitrary orientations. Suppose there is an orthonormal
frame

    e=(cos t,sin t),     f=(-sin t,cos t),
    0<=t<=pi/4,

for which these three full-square projection
separators hold, with the stated directed order:

    e dot(p_A-p_G) >= h_A(e)+h_G(e),
    e dot(p_G-p_H) >= h_G(e)+h_H(e),
    f dot(p_E-p_H) >= h_E(f)+h_H(f).                    (2)

Here `h_S(n)` is the support of the *centered*
unit square S in direction n. Every expression
in (2) is a directly checkable geometric separating
inequality; it need not be an actual contact equality.

**Theorem.** Under (1)--(2), the disk contains
five points P1,...,P5 satisfying the **entire**
projected five-corner obstruction:

    (P2-P1).y >= 2,
    (P2-P3).x >= 3,
    (P3-P4).y >= 2,
    f dot(P4-P5) >= 1+sin t,
    e dot(P1-P5) >= 2+cos t.                            (3)

Consequently `R>=R_hat`, where `R_hat` is the
exact global minimum of this five-corner family
proved in HUMAN_FAMILY_CLOSURE.md. Equality is
attained within this conditional geometric
class by the previously constructed candidate.

**No common-orientation assumption on G or H is
used.** In fact neither is required to have
a side normal in direction e or f: only the
projection gaps (2) matter. The remaining
global obstruction is to force (1)--(2), or
an equally strong alternative, in *arbitrary*
eight-square minimizers.

## 1. A simultaneous two-axis point inside any rotated unit square

**Lemma.** For every unit square H centered
at p_H and every orthonormal pair e,f, set

    L=2*h_H(e)=2*h_H(f),      1<=L<=sqrt(2).

Then the point

    P_H=p_H+(L/2-1)*(e+f)                              (4)

belongs to H.

**Proof.** Let a,b be the orthonormal side axes
of H. If a makes some angle delta to e, the
four absolute direction cosines are the
absolute sine and cosine of delta, so

    |e dot a|+|e dot b|
     =|f dot a|+|f dot b|
     =|cos delta|+|sin delta|=L.

The same identities give

    |a dot(e+f)|<=L,   |b dot(e+f)|<=L.

Since L<=sqrt(2)<2, the scalar 1-L/2 is positive.
Thus by (4),

    |a dot(P_H-p_H)| <= (1-L/2)*L,
    |b dot(P_H-p_H)| <= (1-L/2)*L.

But

    (1-L/2)*L
      =1/2-(L-1)^2/2 <=1/2.                             (5)

Therefore both local coordinates of P_H in
H's own orthonormal frame lie in
[-1/2,1/2], exactly the definition of
membership in H. This proves the lemma.
When L>1 the inequalities are strict,
so P_H even lies in the open interior.

The point (4) has the two simultaneous
projection identities

    e dot(P_H-p_H)=f dot(P_H-p_H)=L/2-1.                (6)

The equality of H's projected half-widths
in perpendicular directions is special to
a *square*, and (5) is the needed exact
compensation for its arbitrary rotation.

## 2. Choose the five genuine disk points

Put c=cos t, s=sin t. Use the following
actual square vertices and the point (4):

    P1=p_A+(1/2,-1/2),    bottom-right A,
    P2=p_B+(1/2, 1/2),    top-right B,
    P3=p_D+(-1/2,1/2),    top-left D,
    P4=p_E+(-1/2,-1/2),  bottom-left E,
    P5=P_H.                                             (7)

Every P_i belongs to one of the packed
unit squares and therefore to D_R.
There is no requirement that P5 be a
vertex or touch the containing circle.

The three axis-parallel differences are

    (P2-P1).y=(p_B-p_A).y+1 >=2,
    (P2-P3).x=(p_B-p_D).x+1 >=3,
    (P3-P4).y=(p_D-p_E).y+1 >=2.                        (8)

These are exactly the first three
inequalities in (3), with no discarded
square nonoverlap constraints.

## 3. Derive both oblique inequalities with the SAME P5

For a unit square in the standard x/y
frame, its support half-width along
either e or f is (c+s)/2. Also every
unit square G, of **any** orientation,
satisfies

    h_G(e)>=1/2.

The first two full-square separators
in (2) therefore add to

    e dot(p_A-p_H)
       >= h_A(e)+2*h_G(e)+h_H(e)
       >= (c+s)/2+1+L/2.                              (9)

By (7),

    e dot(P1-p_A)=(c-s)/2.

By (6), `e dot(p_H-P5)=1-L/2`.
Adding these to (9) gives

    e dot(P1-P5)
       >= (c+s)/2+1+L/2
          +(c-s)/2+1-L/2
       =2+c.                                           (10)

This is the **fifth** inequality in (3).

Likewise the third separator in (2) gives

    f dot(p_E-p_H)>=(c+s)/2+L/2.

The chosen P4 satisfies

    f dot(P4-p_E)=(s-c)/2,

while (6) gives `f dot(p_H-P5)=1-L/2`.
Adding them yields

    f dot(P4-P5)
       >= (c+s)/2+L/2
          +(s-c)/2+1-L/2
       =1+s.                                           (11)

This is the **fourth** inequality in (3).

Crucially (10) and (11) use the **same**
P5, constructed inside the single
arbitrarily rotated square H. Taking
separate e-minimizing and f-minimizing
vertices of H would not have justified
that compatibility. The exact point
lemma closes precisely that issue.

All five projections (3) now hold.
The least-five-corner-family theorem
therefore gives R>=R_hat. QED.

## 4. Comparison with the exact candidate and missing global step

In the candidate's rotated construction,
A,B,D,E are the four standard outer
contact squares; their normal-order
coordinates give the three separations
(1), with horizontal span exactly two.
The tilted G lies between A and H in
e projection, and E lies beyond H in
f projection, so all three inequalities
(2) also hold, with equalities in the
appropriate directions. The existing
construction therefore realizes the
conditional sharp radius R_hat and
shows that this conditional theorem
cannot be improved at the endpoint.

The new contribution is that the last
two oblique inequalities require **no**
parallelism of G with H (or either
tilted square with the e/f frame).
They need only three directed
projection separators and the four
standard square frames.

This is not an unrestricted n=8 proof.
Neither (1) nor (2) has been derived
for every arbitrary radius-minimizing
eight-square configuration. In
particular an exterior contact ring
can use square-owned oblique separators
instead of the displayed directions,
and the four putatively standard
outer squares need not be parallel.
Forcing an admissible decomposition
or proving a sharp alternative remains
the genuinely open mathematical step.
