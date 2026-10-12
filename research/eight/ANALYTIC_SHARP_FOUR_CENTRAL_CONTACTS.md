# At the exact five-corner radius the central square can touch four neighbors

## Theorem (a genuine sharp-radius equality candidate)

Let R_hat be the *least* disk radius of the five-corner family,
selected by the entirely analytical stationary theorem in
HUMAN_FAMILY_CLOSURE.md. There is an eight-square packing of radius
**exactly R_hat** whose central square C (the unique square containing
zero in its open interior) has **four distinct actual neighbors**.
The outer seven-square actual contact ring remains

    A--B--T--D--E--H--G--A,

and C touches **B, D, T and G**.

This is an exact hand-proved construction within the least
five-corner family. It uses the full analytic parameter bounds,
not rounded stationary coordinates or a numerical root box.

**Crucial global implication.** It is false that every packing
at radius <=R_hat has central actual degree at most two.
Consequently one cannot prove unrestricted optimality by
unconditionally excluding central degree >=3, or by
requiring all equality representatives to have the
two-contact central transmitter. Such rigidity can only
be a *specially selected minimum-contact representative*
statement, with its selection hypothesis retained.

The result does not prove the missing reverse inequality
R_8>=R_hat. It is a sharper construction and equality-case warning.

## 1. Keep the exact five-corner boundary squares and oblique pair

Use the notation of ANALYTIC_EXACT_CONSTRUCTION.md and
HUMAN_FAMILY_CLOSURE.md. Put q=R_hat^2,
e=(c,s), f=(-s,c), with c^2+s^2=1, 0<s<1/5,
and let r,U,v,w,u,k1,k2 be its exact stationary parameters.
We will use only the already analytically proved inequalities

    q>(79/40)^2,  U in (3/2,41/24),
    87/100<u<1,  1/2<v<u<589/1000,
    17/10<r<16/9,  17/10<w<48/25,
    c>49/50,  0<s<1/5,
    1<k1<757/500,  k2=1+c*v-s*(w-1).

Retain unchanged the four standard outer squares

    A=(r-1/2,1/2-u),
    B=(U-1/2,3/2-u),
    D=(U-5/2,3/2-v),
    E=(1/2-w,1/2-v),

and the two e,f-frame squares

    H=P5+(e+f)/2,     G=H+e,
    P5=-k1*e-k2*f.                                      (1)

They fit D_Rhat and satisfy all their existing pair
separations by ANALYTIC_EXACT_CONSTRUCTION.md.
The two middle squares C,T, with horizontal interval

    I=[U-2,U-1],                                        (2)

will be placed at new heights.

## 2. A top-edge point of G lies strictly within the middle strip

The midpoint of G's positive-f edge is

    z_mid=G+f/2=(3/2-k1)*e+(1-k2)*f.                (3)

It has coordinates

    X_mid=c*(3/2-k1)-s*(1-k2),
    Y_mid=s*(3/2-k1)+c*(1-k2).                      (4)

We claim

    U-2<X_mid<U-1.                                   (5)

For the lower bound,
k1<757/500 gives 3/2-k1> -7/500.
Also

    k2-1=c*v-s*(w-1)
        >(49/50)*(1/2)-(1/5)*(23/25)
        =153/500>0.

Thus X_mid> -7/500. As U<41/24,
U-2< -7/24< -7/500, proving the lower
comparison.

For the upper bound, since
k1=2-c*(r-1)+s*u>2-(r-1)>11/9,

    3/2-k1<5/18.

Also k2-1=c*v-s*(w-1)<v<589/1000.
Therefore

    X_mid<5/18+(1/5)*(589/1000)
         < 1/2 <U-1.

This proves (5), so z_mid lies on G's
actual positive-f supporting side **inside
the open middle horizontal strip**.

The uppermost y-coordinate of G is
the y-coordinate Y_top of its positive
(e+f) vertex. As computed analytically
in ANALYTIC_EXACT_CONSTRUCTION.md, equation (12),

    Y_top<-41/260<0.                                 (6)

The midpoint (3) is obtained from this
upper vertex by subtracting e/2,
so

    Y_mid=Y_top-s/2.                                 (7)

We also have

    Y_mid+v
       =s*(s*v+c*(w-1)+3/2-k1)>0,                    (8)

because s>0, w>17/10, c>49/50,
and 3/2-k1> -7/500.

## 3. Move the two middle squares to their extremal contact heights

Consider the compact nonempty horizontal section

    K=G intersect (I x R).

It is nonempty because z_mid belongs to it.
Define the **actual geometric maximum**

    Y=max{y:(x,y) in K}.                            (9)

This is a maximum of y over a compact convex
polygon intersection, not a numerical estimate.
Equations (6)--(8) give the exact strict bounds

    -v<Y_mid<=Y<=Y_top<-41/260.                   (10)

Now place two standard-frame unit squares with
centers

    C=(U-3/2, Y+1/2),
    T=(U-3/2, Y+3/2).                              (11)

They have the same horizontal interval I.
Their respective vertical intervals are

    C: [Y,Y+1],
    T: [Y+1,Y+2].                                   (12)

Hence C,T have disjoint open interiors and
an actual shared horizontal **side** of length one.

## 4. Both middle squares fit the original circle

Because -v<Y<-41/260 and 1/2<v<589/1000,
the center y_C=Y+1/2 obeys

    1/2-v<y_C<1/2-41/260.

The lower end exceeds -89/1000>-1/2 and
the upper end is <1/2. The horizontal
coordinate U-3/2 is in (0,5/24)<1/2.
Thus zero lies in the **open interior**
of C. Every vertex of a unit square
containing zero in its interior has norm
strictly below sqrt(2). Since R_hat>
79/40>sqrt(2), C lies strictly inside
the original circle.

For T, its farthest vertex norm squared is

    (U-1)^2+(Y+2)^2,

since U>3/2 and Y+2>0. Using (10)
and U<41/24,

    max_(z in T)|z|^2
       <(17/24)^2+(479/260)^2
       =(79/40)^2-583/121680
       <R_hat^2.                                        (13)

Thus T also lies **strictly inside**
the original containing circle.

## 5. Every pair remains nonoverlapping, with four central contacts

The six standard squares A,B,C,D,E,T still form
the same three horizontally separated columns:
left D,E; middle C,T; right A,B.
All between-column horizontal separations from
ANALYTIC_EXACT_CONSTRUCTION.md remain unchanged.
Inside the columns, D,E and A,B retain their
original unit-height contacts, while C,T
now touch exactly along their common side (12).
Thus all fifteen pairs of standard squares
remain nonoverlapping.

Their actual contacts with B,D survive with
**positive overlapping side intervals**:

* B and D lie against the two opposite
  vertical sides of the middle column.
* Their vertical intervals are
  B:[1-u,2-u], D:[1-v,2-v].
* By (10), Y>-v, and v<u<1, so
  C's top Y+1>1-v>1-u while its bottom
  Y<0<2-u,2-v.
* T's bottom Y+1<1<2-u,2-v and its top
  Y+2>2-v>2-u.

Consequently both C and T have actual
positive-length side contacts with both B and D.

All pairs among A,B,D,E,H,G remain
as in the original construction.
Pairs of B,D with the two tilted
squares remain separated vertically by
the original proof. The modified T is
also strictly above G,H, since

    min_y T=Y+1>=Y_mid+1
            =Y_top+1-s/2>Y_top

and H has top y-coordinate Y_top-s.
The modified C is **strictly above H**,
because

    min_y C=Y>=Y_mid
            =Y_top-s/2>Y_top-s=max_y H.

It remains to check the pair C,G.
Their x projections can overlap only
inside I, and the definition (9)
gives every point of G within I the
inequality y<=Y, whereas every point
of C has y>=Y. Thus their **open**
interiors do not overlap.

At the maximum (9), some actual point
z in G has x in I and y=Y. It is also
on the bottom horizontal edge of C,
so it belongs to C intersect G.
Hence **C and G actually touch**.
All eight squares are interior-disjoint,
in the same circle, and C touches the
four distinct squares B,D,T,G.

The original seven-square actual cycle
A-B-T-D-E-H-G-A also remains: its
four standard support contacts have
positive interval overlaps by the same
coordinate checks above; E-H, H-G,
G-A, and A-B are unchanged. In particular
the full seven-outer cycle and its two
central side spokes remain present.

## 6. Exact logical lesson for global optimality

This construction works for the actual analytically
selected least-family root q=R_hat^2,
not merely for an upper rational approximation,
and does not rely on any tiny isolating box.
Thus the **sharp equality candidate itself**
supports central actual degree four.

The central two-contact theorem in
HUMAN_CYCLE_ANALYSIS.md applies to a radius
minimizer specifically selected to have
the **fewest actual contacts**. The present
packing instead adds zero-stress-compatible
contacts by moving the two freely sliding
middle squares. It in no way contradicts
the minimum-contact theorem.

Accordingly one must not attempt the
unrestricted inequality R_8>=R_hat by
proving that every packing at R_hat has
central actual degree at most two, or
that a maximum-contact/connected
representative must have a central
degree-two transmitter. Such statements
would be false.

The missing global theorem is still to derive
the five-corner projected obstruction, or an
equally sharp alternative, from *all*
unrestricted minimizers. This construction
does not close that lower-bound gap.
