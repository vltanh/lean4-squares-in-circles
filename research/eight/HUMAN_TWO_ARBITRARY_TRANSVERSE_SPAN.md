# A two-unit transverse span from two arbitrary square orientations

## Theorem

Let S,T be any two unit squares with disjoint open interiors,
and centers p_S,p_T. Let a,b be any orthonormal frame.
Write

    dx=a dot(p_T-p_S),   dy=b dot(p_T-p_S),
    L_S=2h_S(b)=2h_S(a),
    L_T=2h_T(b)=2h_T(a),

where 1<=L_S,L_T<=sqrt(2). If

    |dx|<=1/2,

then their total transverse (b-direction) projected span obeys

    |dy|+(L_S+L_T)/2 >= 2.                           (1)

**Equality is possible only if both squares have side
frames parallel to a,b and |dy|=1.** Conversely such
parallel squares with |dx|<=1/2 and |dy|=1 are
interior-disjoint and attain equality.

No common frame is assumed in the lower bound.
The conclusion is about actual whole-square
projections, not merely centers or circle radii.

## Proof

Rotate to make a horizontal and b vertical.
Put W=(L_S+L_T)/2>=1. Suppose for a contradiction
that

    |dx|<=1/2,  |dy|+W<2.                            (2)

In particular |dy|<2-W. By the separating-axis
theorem, two nonoverlapping unit squares would
have at least one axis n belonging to a side
frame of S or T for which

    |n dot(p_T-p_S)|>=h_S(n)+h_T(n)>=1.             (3)

Choose an axis n of S first. Let c,s be the
absolute horizontal and vertical components
of n. Then 0<=c,s<=1, c^2+s^2=1,
and, because S is a square,

    L_S=c+s.                                       (4)

Equations (2), W>=(L_S+1)/2, and
the triangle inequality give

    2*|n dot(p_T-p_S)|
      < c+(3-L_S)*s
       = c*(1-s)+3*s-s^2
      <= (1-s)+3*s-s^2
       = 2-(1-s)^2
      <=2.                                         (5)

The first strict sign follows from
|dy|<2-W when s>0. If s=0, then
2*|n dot displacement|<=c<=1<2.
Thus every axis owned by S has
projection gap strictly less than one,
contradicting (3). The same proof
applies to axes owned by T, with L_T
in place of L_S and W>=(L_T+1)/2.
Therefore no separating axis exists,
contradicting nonoverlap. This proves (1).

To classify equality, suppose
|dy|+W=2 and the squares are disjoint.
For an axis with 0<=s<1, equation (5)
with non-strict first sign still gives

    2*|n dot displacement|
      <=2-(1-s)^2<2,

so it cannot be a separating axis.
Thus the separating-axis theorem
requires an axis with s=1, i.e. a
vertical side normal of one square,
say S. Therefore L_S=1 and
W=(1+L_T)/2>=1.

Vertical separation requires |dy|>=W,
but equality of the total span says
|dy|=2-W. These force 2-W>=W,
so W<=1. As W>=1, W=1 and L_T=1.
Both squares therefore have the
common horizontal/vertical frame,
and |dy|=1, as claimed. This also
proves the converse equality example.

## Relevance to the eight-square sharp obstruction

The previous scaffold projection lemma
HUMAN_SCAFFOLD_CLOSURE.md obtains a
two-unit vertical span when one square
is parallel to the scaffold and the
center abscissa difference is <=7/8.
The present lemma replaces its
one-parallel premise by **arbitrary
orientations on both squares**, for
the narrower but useful displacement
range |dx|<=1/2.

It can provide the first or third
2-unit projected inequality of the
five-corner chain without assuming
either participating square is
parallel. Together with the sharp
one-square cap center envelope,
it gives two exact geometric tools
for the surviving orientation cases.

The lemma alone does not force
a full five-corner separator pattern,
or the unrestricted R8>=Rhat.
