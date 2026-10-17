# The exact five-corner candidate lies in D0 with seven single-side statuses

## Theorem

Let Rhat be the exactly optimized five-corner family radius
of HUMAN_FAMILY_CLOSURE.md, and choose the explicit
eight-square realization in ANALYTIC_EXACT_CONSTRUCTION.md
with sliders

    z_C=343/1000,  z_T=13431/10000,  eta=0.

Let its central unit square be C. Then its seven
noncentral squares have the **exact mutually exclusive
central-separator status multiplicities**

    R:2 (A,B),   L:2 (D,E),   U:1 (T),   D:2 (G,H),

with **no double-side status and no corner-only status**.

Thus, for the 12-status combinatorial taxonomy,

    number of double-side squares =0,
    number of corner-only squares =0,
    total side memberships S=7.                      (1)

These statuses concern all *available central-owned
side separators*, not merely arbitrarily chosen
separating axes or centers' coordinate quadrants.
The full packing has genuine outer contacts in a
seven-member exterior cycle at this same radius,
as proved in ANALYTIC_SHARP_SEVEN_OUTER_CONSTRUCTION.md.

In particular the D0/S=7 branch in
FORCED_CORNER_EXCEPTION_D2.md is a **real sharp
candidate equality branch**. A global lower-bound
argument must derive R>=Rhat *within* that
branch and permit equality: rejecting it as a
combinatorial type would be false.

## 1. Exact parameters and central-side thresholds

Use the analytical parameters q=Rhat^2,
r,u,U,V,v,w,c,s,k1,k2 in
ANALYTIC_EXACT_CONSTRUCTION.md and
HUMAN_FAMILY_CLOSURE.md. They satisfy

    r>U>3/2,   17/10<r,w<2,
    U<41/24,   87/100<u<1,
    1/2<v<589/1000,
    49/50<c<=1,  0<s<1/5,
    1<k1<757/500,  k2>1/2,  k2<2.

The standard central square C has center

    p_C=(U-3/2,343/1000),

so 0<p_C.x<5/24 and
p_C.y=343/1000. The standard-frame
central/standard square projection
half-width sum is exactly one.
For a square with oblique (e,f) frame,
e=(c,s),f=(-s,c), the central-owned
half-width sum along either central
axis is

    W=(1+c+s)/2>1.                               (2)

A central-owned right/left separator is
available exactly when its center difference
from C has magnitude >= the corresponding
half-width sum, and similarly vertically.

## 2. Five aligned exterior squares

From the exact construction the centers are

    A=(r-1/2,1/2-u),
    B=(U-1/2,3/2-u),
    D=(U-5/2,3/2-v),
    E=(1/2-w,1/2-v),
    T=(U-3/2,13431/10000).

Their center differences relative to C are:

    A: (1+r-U, 157/1000-u),
    B: (1, 1157/1000-u),
    D: (-1, 1157/1000-v),
    E: (2-w-U, 157/1000-v),
    T: (0, 10001/10000).

For A, r>U makes the x difference >1,
while 87/100<u<1 makes its y difference
strictly between -1 and 1.
Thus A has **R only**.

For B, its x difference is exactly one
and 87/100<u<1 places its y difference
strictly inside (-1,1). Thus B has **R only**.

For D, its x difference is exactly minus one.
The interval 1/2<v<589/1000 places its
y difference in (568/1000,657/1000),
so D has **L only**.

For E, the x difference is
2-w-U<2-17/10-3/2=-6/5<-1,
while its y difference 157/1000-v
lies strictly in (-1,1).
Thus E has **L only**.

For T, its x difference is zero and its
y difference is 10001/10000>1, so
T has **U only**.

## 3. The two oblique exterior squares both have D only

The oblique squares H,G use frame e,f and,
at eta=0, have centers

    p_H=(1/2-k1)e+(1/2-k2)f,
    p_G=p_H+e.

The original analytic exact-construction proof,
equations (12)--(13), establishes that the
**topmost vertex height** of G satisfies

    max_(z in G) z_y < -41/260.

The lower central side is at
y=343/1000-1/2=-157/1000.
As -41/260<-157/1000, the entire
G square lies strictly below that
central side. Since H=G-e and
e_y=s>0, H also lies strictly
below it. Therefore both possess
a genuine central-owned **D** separator.

We now exclude any simultaneous central-owned
R or L separators for H,G.

The horizontal center displacement of H
relative to C is

    Delta_H = (1/2-k1)c+(k2-1/2)s
                       -(U-3/2).

The bounds k1>1, c>49/50, k2<2,
s<1/5, U>3/2 show

    Delta_H <-(1/2)*(49/50)+(3/2)*(1/5)<0.      (3)

On the other hand substitute the exact defining
relations

    k1=2-c(r-1)+s*u,
    k2=1+c*v-s(w-1).

A direct expansion using c^2+s^2=1 yields
the **exact identity**

    Delta_H+W
      =(1-c)[2+c-(1+c)*U]
       +c^2*(r-U)
       +s*[1-c*(u-v)]-s^2*(w-1).                (4)

Each term is now controlled without a tiny
root isolating box.

Because U<2, the square bracket in (4)
is greater than -c, so its weighted
contribution is greater than
-c*(1-c)>-s^2.
Also r-U>0 and c^2>0.
Since u-v<1/2, the third term
is >s/2.
Finally w<2 gives
-s^2*(w-1)>-s^2.
Thus

    Delta_H+W >s*(1/2-2*s)>0                 (5)

because 0<s<1/5<1/4.

Equations (3)--(5) yield

    -W<Delta_H<0<W.                             (6)

For G, its horizontal displacement is

    Delta_G=Delta_H+c.

Since c>0 and c<W
(the latter follows from W-c=(1-c+s)/2>0),
equation (6) gives

    -W<Delta_G<W.                                (7)

Thus neither H nor G possesses a central-owned
right or left separating axis. Both possess
**D only**. Together with section 2 this
establishes (1). QED.

## 4. Pattern rejection implications

The candidate lies in the D0/S=7
one-side-only type, with side populations
(2,2,1,2) in R,L,U,D order. This type
is **not** eliminated by any established
central cap or corner capacity theorem.

The separate analytic negative G slider
changes the position and center norm
of G while retaining a full seven-exterior
contact ring. It need not preserve every
single-side status at all slider endpoints,
so this theorem is stated for the
specified eta=0 exact realization.

The result does not prove R8>=Rhat:
it identifies a branch that an eventual
global sharp inequality must **retain**
with equality, rather than discard.
