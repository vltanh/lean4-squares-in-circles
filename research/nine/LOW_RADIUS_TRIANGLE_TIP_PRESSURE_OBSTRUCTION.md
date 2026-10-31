# A low-radius physical triangle can have a negative degree-two tip

Date: October 25, 2026.

**Status: exact local obstruction, checked by its author and independently
by root with rational arithmetic.** This is a three-square construction, not a nine-square
packing and not a complete selected positive component. It satisfies
physical H/A/K containment, all three physical contacts, and A's genuine
positive degree-two force and torque equations. It demonstrates that
these local hypotheses alone do not imply nonnegative H pressure below
the high-radius interval.

The construction does not assign equilibrium at H or K, add an intact
petal, or supply the other six physical squares. In particular it does
not refute a low-radius block-pressure theorem that uses actual K3/H5,
the remaining physical packing or the full certificate.

## 1. Exact data

Use the original circle origin as the coordinate origin throughout.
Set

    n = (u,v) = (120/241, 209/241),
    j = (-v,u),
    f = (s,c) = (288/337, 175/337),
    g = (-c,s).

Both frames are orthonormal and positively oriented, since

    120^2+209^2 = 241^2,
    288^2+175^2 = 337^2.

Define

    E = su+cv = 71135/81217,
    d = sv-cu = 39192/81217,
    delta = v/E = 70433/71135,
    r0 = s/E = 69408/71135,
    r = 999/1000,
    tau = 1-delta = 702/71135,
    A0 = 1+c(v-u)/(su) = 10027/6912.

Thus E,d>0, 0<delta<1 and 0<r0<r<1. Put

    W = (-1-c+tau*s, s+tau*c),
    b = -(W_x^2+W_y^2)/(2(A0*W_x+W_y)),
    a = A0*b,       q = a^2+b^2.

These definitions involve rational numbers only. The denominator in the
formula for b is negative, so b>0. For direct arithmetic verification,
the simplified values of W and b are

    W = (-36218944/23972495, 4121946/4794499),
    b = 278263902842712/245318937185645.

The large fraction is only the coordinate of this one explicit witness;
there is no interval certificate or coefficient table. Direct positive
cross multiplication gives the convenient small bounds

    329/200 < a < 823/500,
    567/500 < b < 227/200.                         (1)

Consequently

    399/100 < q < 4,

because the sum of the squares of the two lower bounds in (1) is
3991981/1000000>399/100, while the corresponding upper sum is
3997541/1000000<4. Thus q lies strictly inside the original LOW interval

    6241/1600 < q < 17/4.

Define P=(a-1,b-1), T=(a-1,b), z_A=(a,b), and the actual squares

    A = [a-1,a] x [b-1,b],
    H = P + [-1,0]n + [r-1,r]j,
    K = T + [0,1]g + [-delta,1-delta]f.             (2)

All three have side length one.

## 2. The complete physical contact geometry

The normal n points from H to A. The whole H has n-projection at most
n.P; the whole A has n-projection at least n.P. Since u,v>0, P is
A's unique minimum-n vertex. Since r-1<0<r, P is in the relative
interior of H's front side. Hence HA is exactly an H-owned singleton
at P, and the two interiors are disjoint.

The normal g points from A to K. It strictly exposes A's upper-left
vertex T. The point T is in the relative interior of K's minimum-g
side because 0<delta<1. Thus AK is exactly a K-owned upper-left
singleton at T, and the interiors are disjoint.

For HK, let V=T-delta*f. Since n.f=E>0 and n.g=d>0, V is K's unique
minimum-n vertex. The exact relation delta=v/E gives

    V-P = r0*j.

Its n-projection therefore equals n.P. As r-1<r0<r, V belongs to
the relative interior of H's same front side. All H points are on
the lower side of this support and all K points on the upper side.
Consequently HK is an H-owned singleton at V; it is distinct from
HA. This verifies all three contacts and pairwise disjoint interiors
without an assumed contact graph or numerical tolerance.

## 3. Both A and K have unique physical circle corners

The bounds (1) give a,b>1/2. Thus z_A is A's unique farthest corner,
and A is contained in the circle of squared radius q.

The upper-right K corner in the (f,g) frame is

    z_K = T+g+tau*f = z_A+W.

The exact definition of b gives

    |z_K|^2-|z_A|^2
      = 2b(A0*W_x+W_y)+|W|^2 = 0.               (3)

It remains to check that z_K really is K's unique farthest corner.
Let

    x=a-1,    L=xs+bc,    h=-xc+bs.

Then K's f and g intervals are

    [L-delta,L+1-delta],    [h,h+1].

Using (1) and the elementary direction bounds

    s>17/20,    51/100<c<13/25,

gives

    L > (129/200)(17/20)+(567/500)(51/100) > 11/10,
    h > -(323/500)(13/25)+(567/500)(17/20) > 3/5.

Since delta<1, the f-interval midpoint L+1/2-delta is strictly
positive; the g-interval midpoint h+1/2 is positive as well.
Hence the positive endpoint of each interval has strictly greater
absolute value than its other endpoint. Equation (3) is therefore
K's unique largest corner norm. K is contained and physically unique
on the same circle as A.

The whole H is strictly inside that circle. In fact u<1/2, v<87/100
and (1) imply, for every point of H,

    -3/4 < x_H < 2/3,       -3/4 < y_H < 2/3.

For example the minimum coordinates are a-1-u-rv and
b-1-v+(r-1)u; the maximum coordinates are a-1+(1-r)v and
b-1+ru. Substitution of the displayed rational bounds proves all
four inequalities. Thus every H point has squared norm less than
9/8<q. Its circle load is zero in this local data.

## 4. A's original positive forces and torque

Assign A the positive circle force F_A=z_A. Use actual pair magnitudes

    mu = (as+bc)/E > 0,
    gamma = (va-ub)/E > 0.

Positivity of gamma follows from a>b>0 and v>u. The defining ratio
a/b=A0 gives the exact equations

    F_A = mu*n-gamma*g,
    mu*det(P,n) = gamma*det(T,g).                 (4)

Thus A's circle force and its two positive pair forces, applied at the
actual distinct points P,T, satisfy both force and origin-torque balance.
Equivalently their normal lines meet at

    P+(c/E)n = T-(u/E)g,

which is a positive multiple of z_A. No side mean or force application
has been changed.

## 5. The actual tip pressure is strictly negative

H's actual center is

    c_H = P-n/2+(r-1/2)j.

Since r-1/2=499/1000, the bounds (1), u>49/100, v>13/15 and
u<1/2 give

    (c_H)_x
      < 323/500 - 49/200 - (499/1000)(13/15)
      = -59/1875 < 0,

    (c_H)_y
      < 27/200 - 13/30 + 499/2000
      = -293/6000 < 0.

Both coordinates of z_A are positive. Therefore

    c_H dot F_A = c_H dot z_A < 0.                (5)

For orientation only, q is about 3.9942342 and the projection in (5)
is about -0.1172850. These decimals are not proof inputs.

## 6. Consequence for the remaining proof

The physical triangle, its actual side-owner conventions, A2 equilibrium,
the two unique physical circle masks, and complete original containment
can coexist with a negative local tip at low radius. Therefore a proposed
nonnegative-tip lemma whose hypotheses consist solely of these local
conditions is false. The high-radius proof's threshold cannot simply be
removed by improving a scalar estimate under the same local conditions.

The remaining diamond proof can still exploit its genuine K3 equation,
HB/KB contacts, H5 balance, intact petal and all completion squares.
Those conditions are not supplied by this witness. A uniform comparison
for the original block's total pressure remains a possible next theorem;
an arbitrary assignment of missing forces or a claim that this is a
nine-square counterexample would be invalid.

All direction identities, bounds (1), the original circle equality (3),
both balances (4), and the strict signs were checked with exact rational
arithmetic. No Lean compilation, CI or remote write was performed by
the author of this construction.
