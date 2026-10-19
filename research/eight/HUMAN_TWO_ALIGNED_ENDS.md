# The exact five-corner lower bound needs only two aligned end squares

**Status: completed conditional hand theorem.**
This strengthens HUMAN_OBLIQUE_TWO_AXIS_POINT.md:
the two upper middle squares B,D need **not**
share the end squares' orientation. The
tilted squares G,H may also have **arbitrary**
independent orientations. Only the two end
squares A,E are assumed axis-parallel to a
single chosen orthonormal frame.

It is not yet the unrestricted eight-square theorem:
forcing the coherent separators and the two
aligned end squares in every minimizer remains
a global structural obligation.

## Theorem

Let A,B,D,E,G,H be six unit squares with
pairwise disjoint open interiors, all contained
in the closed disk D_R centered at zero.
Let a,b be an orthonormal frame with b=Ja.
Assume **only A and E** have sides parallel to
a and b. All four frames B,D,G,H are arbitrary.

For any square S write

    h_S(n)=max_(x in S) n dot(x-p_S),

the support function of S translated to its
center p_S.

Suppose the following three directed
outer-chain projections hold:

    b dot(p_B-p_A) >= h_B(b)+1/2,
    a dot(p_B-p_D) >= h_B(a)+h_D(a)+1,
    b dot(p_D-p_E) >= h_D(b)+1/2.                    (1)

The middle inequality is automatic, for example,
if **a seventh unit square C** lies between B and
D and the B-C and C-D pairs have oppositely
oriented separating axes both parallel to a:
then their two separation inequalities add to

    a dot(p_B-p_D)
      >=h_B(a)+2*h_C(a)+h_D(a)
      >=h_B(a)+1+h_D(a).

Choose an angle `0<=t<=pi/4` and put

    e=cos(t)*a+sin(t)*b,
    f=-sin(t)*a+cos(t)*b.

Assume additionally these three oblique
directed projections:

    e dot(p_A-p_G)>=h_A(e)+h_G(e),
    e dot(p_G-p_H)>=h_G(e)+h_H(e),
    f dot(p_E-p_H)>=h_E(f)+h_H(f).                    (2)

**Conclusion:** there exist five actual disk points
P1,...,P5 satisfying

    b dot(P2-P1)>=2,
    a dot(P2-P3)>=3,
    b dot(P3-P4)>=2,
    f dot(P4-P5)>=1+sin(t),
    e dot(P1-P5)>=2+cos(t).                         (3)

In the chosen a,b coordinates this is precisely
the sharp five-corner system of
FIVE_CORNER_REDUCTION.md. Therefore

    R>=R_hat.                                        (4)

The selected family R_hat admits equality for
its original candidate contact data, so the
conditional lower bound cannot be strengthened.

## 1. Canonical directional corners of any unit square

**Lemma (two-axis point).** For any unit square S,
any orthonormal frame a,b and every choice of
signs sigma,tau in {-1,1}, define

    L_S=2*h_S(a)=2*h_S(b),       1<=L_S<=sqrt(2),
    m_S=1-L_S/2.

Then

    Q_S(sigma,tau)
      =p_S+m_S*(sigma*a+tau*b)                     (5)

belongs to S.

**Proof.** Let u,v be the own orthonormal side axes
of S. The absolute projections
`|u dot a|+|v dot a|` and
`|u dot b|+|v dot b|` are equal,
and both equal L_S: they are
`|cos delta|+|sin delta|` for one
relative frame angle delta. Each of
`|u dot(sigma*a+tau*b)|`,
`|v dot(sigma*a+tau*b)|` is <=L_S.

Hence every local coordinate of
Q_S-p_S has magnitude at most

    m_S*L_S=(1-L_S/2)*L_S
            =1/2-(L_S-1)^2/2 <=1/2.

Thus Q_S lies in the original unit square.
This proves the assertion for all four
choices of signs, **not** only one favored
support vertex. QED.

The identity uses square geometry, not
a common frame assumption. It also
shows that a more tilted square, which
has projected half-width L_S/2>1/2,
has less room to move its canonical
point to either axis: the exact sum of
these two effects is one.

## 2. Four disk points from the chain squares

Put

    L_B=2*h_B(a)=2*h_B(b),
    L_D=2*h_D(a)=2*h_D(b).

Choose the actual vertices of aligned A,E
and the canonical points of rotated B,D:

    P1=p_A+(a-b)/2,
    P2=p_B+(1-L_B/2)*(a+b),
    P3=p_D+(1-L_D/2)*(-a+b),
    P4=p_E-(a+b)/2.                               (6)

They are all points in their respective
packed squares by (5) (and ordinary vertices
for A,E), hence in D_R.

The three outer-chain projections follow
by exact cancellation of the arbitrary
projected widths:

    b dot(P2-P1)
      =b dot(p_B-p_A)+(1-L_B/2)+1/2
      >=(L_B/2+1/2)+(1-L_B/2)+1/2=2,

    a dot(P2-P3)
      =a dot(p_B-p_D)
         +(1-L_B/2)+(1-L_D/2)
      >=(L_B+L_D)/2+1+2-(L_B+L_D)/2=3,

    b dot(P3-P4)
      =b dot(p_D-p_E)+(1-L_D/2)+1/2
      >=(L_D/2+1/2)+(1-L_D/2)+1/2=2.       (7)

Thus **neither B nor D needs a
specified square orientation**.

## 3. The fifth disk point and both oblique projections

For the arbitrary square H put

    L_H=2*h_H(e)=2*h_H(f),

and choose its canonical southwest point

    P5=p_H+(L_H/2-1)*(e+f).                        (8)

This belongs to H by (5), and has

    e dot(p_H-P5)=f dot(p_H-P5)=1-L_H/2.

Because G is an arbitrary unit square,
`h_G(e)>=1/2`. Summing the two
e-directed separators in (2) gives

    e dot(p_A-p_H)
       >=h_A(e)+2*h_G(e)+h_H(e)
       >=(cos t+sin t)/2+1+L_H/2.

The aligned A point P1 has
`e dot(P1-p_A)=(cos t-sin t)/2`.
Thus

    e dot(P1-P5)
       >=(cos t+sin t)/2+1+L_H/2
          +(cos t-sin t)/2+1-L_H/2
       =2+cos t.                                    (9)

Similarly `h_E(f)=(cos t+sin t)/2`, and
the final f-directed separator gives

    f dot(p_E-p_H)
       >=(cos t+sin t)/2+L_H/2.

The aligned E point P4 satisfies
`f dot(P4-p_E)=(sin t-cos t)/2`,
so

    f dot(P4-P5)
       >=(cos t+sin t)/2+L_H/2
          +(sin t-cos t)/2+1-L_H/2
       =1+sin t.                                    (10)

Equations (7), (9), and (10) establish
all five inequalities (3) **using the
same P5 and one coherent e,f frame**.
No corner of a rotated square has been
mistaken for the intersection of two
independent support faces.

The analytical family optimum therefore
gives the sharp conditional bound (4).
QED.

## 4. What remains global, precisely

This proves the full five-corner radius
obstruction for a larger class of
arrangements than previously documented:
among A,B,D,E,G,H only **A and E**
must share the normalized x/y square
orientation; B,D,G,H may rotate
independently. It also suffices that
the three outer-chain inequalities (1)
and three tilted separators (2) are
available; no actual contact graph
or positive stress weights need be
chosen.

The difficult unrestricted implication
remains to show that **every** eight-square
minimizer below R_hat yields these
directed separators with aligned end
squares, or else satisfies an equally
sharp alternate obstruction. In particular,
choosing a different separating axis
for a pair without proving its direction
would be invalid. The condition on A,E
cannot simply be dropped from this
proof: their canonical corner projections
need not supply the two cross-direction
oblique budgets (9)--(10) when they
are themselves tilted. Nothing here
asserts unrestricted R8>=R_hat.
