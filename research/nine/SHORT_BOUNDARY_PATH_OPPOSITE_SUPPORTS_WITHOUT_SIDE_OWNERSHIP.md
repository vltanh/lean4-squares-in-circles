# Opposite parallel supports exclude a short boundary path without endpoint side ownership

Date: October 28, 2026 UTC. Author: root continuation.

**Status: new complete force-free theorem, submitted for separate full
independent review.** Neither support normal need be an axis of its
endpoint square. The proof includes every tilted support vertex and
every original aligned side mean. It has no upper-radius, degree,
force-balance or concurrence premise.

## 1. Complete actual statement

Keep the containing-circle origin O. Let R>=2, and let two through four
distinct actual unit squares contained in its closed disk form a
physically touching path. Their open interiors are disjoint, and each
physically touches the circle. Let L,K be the first and last units.

Assume the actual center directions traverse counterclockwise along
the path with a strictly increasing lift, total advance less than
2*pi, and each successive advance less than pi. This is an actual
geometric order premise, to be proved by a caller.

In an oriented orthonormal chart about O, suppose the original endpoint
support points satisfy

    P_L=(-X_L,h_L),       L subset {x<=-X_L},
    P_K=(X_K,h_K),        K subset {x>=X_K},
    P_L in L, P_K in K,
    X_L,X_K>-1/2,        h_L,h_K>=0,
    X_L+X_K<=1.                                         (1)

They may be actual vertices, arbitrary actual side points, or original
shared-side means including either endpoint. There is no assertion
that East or West is an own axis of a tilted endpoint square.

For each endpoint choose any nonzero nonnegative combination F_i of
its actual physical circle-corner position vectors. Assume

    (F_L)_y>=0,          (F_K)_y>=0.                     (2)

Both physical corners and either possible zero individual coefficient
remain allowed. **Theorem: such a configuration is impossible.**

## 2. A minimum-support point controls the center across every frame

We prove a physical lemma for the right endpoint. Let its actual
minimum-East point be P=(X,h), with X>-1/2 and h>=0. If its actual
center has negative y coordinate, then every physical circle corner
has strictly negative y coordinate. This contradicts (2).

First suppose the square is not aligned. The actual minimum-East face
is a single vertex, so the entire unchanged pose has the form

    K=P+[0,1](c,s)+[0,1](s,-c),
    c,s>0, c^2+s^2=1.                                  (3)

The center height is h+(s-c)/2. A negative center height forces
c>s and 0<=h<(c-s)/2. The lower adjacent corner and opposite corner
then both have negative heights:

    h-c<-(c+s)/2<0,
    h+s-c<-(c-s)/2<0.                                  (4)

The upper adjacent corner P+(c,s) has squared norm larger than P's:

    |P+(c,s)|^2-|P|^2=1+2*X*c+2*h*s>0.                 (5)

For X>=0 this is immediate. For -1/2<X<0 its right side is strictly
greater than 1-c>=0. The opposite corner has squared norm larger
than this upper adjacent corner:

    |P+(c+s,s-c)|^2-|P+(c,s)|^2
      =1+2*X*s-2*h*c
      >1+2*X*s-c*(c-s)
       =s*(2*X+s+c)>0.                                (6)

The last strict sign uses 2*X>-1 and s+c>1. Thus neither P nor its
upper adjacent corner is a farthest corner. Every possible physical
circle corner is among the two negative-height corners in (4).
Every nonzero nonnegative combination has negative y coordinate,
proving the lemma in the entire tilted frame interval.

If the square is aligned, write K=[X,X+1] times [B,B+1], preserving
the entire original side-application interval. Since X>-1/2, the far
normal side is x=X+1. If its center height B+1/2 is negative, the
only farthest tangent coordinate is B<0. Again all physical circle
corners have negative y coordinate. No side point was replaced.

Therefore (2) gives actual center height >=0 in both frame cases.
The horizontal center coordinate is X+w/2>0, because the actual
horizontal width w is at least one. Reflection of the left endpoint
across the y axis gives the identical conclusion there. Its actual
center has negative x coordinate and nonnegative y coordinate.

Write the two actual center angles as

    alpha_L=pi-delta_L,    alpha_K=delta_K,
    0<=delta_L,delta_K<pi/2.                             (7)

The cases of zero center height and both zero angles are retained.

## 3. The real short path forces a small complementary angle

Every physical boundary unit has center radius at least

    r>=R-1/sqrt(2)>=2-1/sqrt(2)>5/4.

Consecutive touching unit centers have distance at most sqrt(2).
Their cosine law therefore gives every actual minor contact angle

    gamma<theta:=acos(9/25).

By (7) and the actual counterclockwise lift, the complete endpoint
advance along the path is pi+delta_L+delta_K. There are at most
three contacts, hence

    delta_L+delta_K<alpha:=3*theta-pi.                  (8)

The exact triple-angle calculation gives

    0<alpha<pi/2,
    cos(alpha)=13959/15625>89/100.

For completeness pi/3<theta<pi/2 follows from 0<9/25<1/2.
The three-angle formula yields the printed cosine, which is positive,
so the a priori interval 0<alpha<pi/2 is consistent and exact.
If the path has at most two contacts its advance is already impossible,
since it is at least pi whereas 2*theta<pi. The same (8) is sufficient
for the remaining case.

## 4. The actual endpoint supports are too far apart

Let r_i be each original endpoint center radius and w_i its actual
horizontal width. That width is at most sqrt(2). From (1) and (7),

    X_i=r_i*cos(delta_i)-w_i/2
       >=(R-1/sqrt(2))*cos(delta_i)-1/sqrt(2).           (9)

For nonnegative x,y with x+y<alpha, the elementary identity

    cos(x)+cos(y)=2*cos((x+y)/2)*cos((x-y)/2)
                >=1+cos(x+y)>1+cos(alpha)

holds also when either or both angles vanish. Sum the two original
support bounds (9), using R>=2 and (8). This gives

    X_L+X_K
      >(2-1/sqrt(2))*(1+cos(alpha))-sqrt(2)
      >(129/100)*(189/100)-71/50
       =10181/10000>1.                                (10)

Both radical comparisons used here are strict and positive:
1/sqrt(2)<71/100 and sqrt(2)<71/50 follow by squaring. The rational
cosine comparison was proved in Section 3. Thus the whole continuous
range has a reserve of more than 181/10000 over the required support
span one. Equation (10) contradicts (1), proving the theorem.

## 5. Relation to the owned-side theorem and exact caller obligations

This theorem has a smaller permitted horizontal support span than the
owned-side result, but it permits arbitrary endpoint frames and even
negative X_i down to the printed strict bound. It does not infer an
owned endpoint side from a normal owned by some third unit.

The related wider-span theorem and the common elementary contact-angle
calculation were fully checked in the preceding source:

| Related source | SHA-256 |
| --- | --- |
| FOUR_BOUNDARY_PATH_OWNED_ENDPOINT_TANGENT_SIGN_OBSTRUCTION.md | 5e8cba82367da03c15710cd6060c3a009323413465a78acaf965f4b07ff29536 |

Every ingredient of the present narrower-span theorem is printed here.
A graph caller must still prove the two actual nonnegative endpoint
heights, both full circle-resultant signs, the support span and the
actual center path order. It cannot discard a third force to obtain a
missing sign. No whole original fine or coarse obligation is closed
by this source alone. No Lean, CI, geometric sampling, changed force,
changed application, omitted physical mask or metadata edit is used.
