# Three-square caps force two whole quadrants at offset eleven fiftieths

**Theorem (orientation-independent, new partial case exclusion).**
Let three unit squares with disjoint open interiors lie wholly inside

    D_R intersect {x>=h},

where `R<=99/50` and `h>=11/50`.
Then **one of these same three squares is wholly in
the open upper half-plane `y>0` and another is
wholly in the open lower half-plane `y<0`**.
Thus a triple in the positive x cap supplies two
distinct genuine *whole-square* origin-quadrant
witnesses, one in the northeast and one southeast.

This conclusion holds for completely independent
square frames. It does not identify which of the three
squares has a central-owned separator in the
perpendicular direction: `y>0` is weaker than
`y>=h_U` for an upper central side with h_U>0.

**Corollary (simultaneous perpendicular triples).**
Suppose in an eight-square packing at the exact search
ceiling q<=9789/2500, the central square has three
whole-square members beyond its right side (at offset
h_R) and three whole-square members beyond its upper
side (at offset h_U). If

    h_R>=11/50 and h_U>=11/50,

then **at least one of the seven exterior squares
has the double-side separator status RU**.
In particular a fully *single-side* status pattern with
simultaneous R and U triples is impossible throughout
this positive-offset rectangle. By reflection and
quarter-turn symmetry, the same assertion holds for
any two perpendicular triple sides.

For the pure-single-side type S1=(3+0,3+1) of
SINGLE_SIDE_SEVEN_BRANCHES.md, both triple sides
are perpendicular and there is no double status.
Consequently at least one of its two triple-side
offsets must be strictly less than 11/50. If they
are R and U, writing p_C=(a,b),

    S1 => min(h_R,h_U)<11/50
       => min(a,b)<-7/25.                          (A)

Together with the previous side interval bounds,
this excludes a *continuous rectangle* of the
S1 central-square positions. It does not reject
the entire S1 branch.

## 1. A guaranteed long chord in the middle of the cap

There is nothing to prove unless a square can fit
in the cap. In that case h+1<=R, because every
unit square's projection width in the x direction
is at least one. In particular 0<h<R.

Put

    X=(R+h)/2,     m=(R-h)/2,
    B=sqrt(R^2-X^2).

Every square lies within the vertical strip
[h,R]; at x=X the disk's full vertical chord
is the interval [-B,B]. From R<=99/50
and h>=11/50,

    m <=(99/50-11/50)/2=22/25.                 (1)

Moreover B<33/20, because B^2 increases with
R and decreases with h on 0<h<R, and at the
rational endpoint (R,h)=(99/50,11/50),

    B^2 =1694/625 <1089/400,                    (2)

the positive integer comparison being
`400*1694=677600<680625=625*1089`.

Let S be any one of the three squares.
Write its unsigned orientation angle
0<=theta<=pi/4 and put

    c=cos(theta), s=sin(theta),
    L=c+s, D=c-s,
    cs=(L^2-1)/2.

Then 1<=L<=sqrt(2). Its entire x projection
has length L and lies in [h,R]. Since
X is the midpoint of that containing strip,
the distances from X to either end of
the square's own x projection are both at
least

    L-m.                                             (3)

By (1), L-m>0, so the line x=X crosses
the square away from its extreme x support.
Let ell denote the length of its **actual
vertical chord** at x=X. When s=0,
ell=1. When s>0, elementary intersection
of the vertical line with the square's
four sides gives

    ell=1/c                    if |delta|<=D/2,
    ell=(L/2-|delta|)/(cs)     otherwise,           (4)

where delta is the offset of X from the
square center's x coordinate. In the
second branch (3) gives

    ell >= (L-m)/(cs).                               (5)

## 2. Two uniform chord inequalities

We establish for **every orientation**

    ell>=1,       L-ell<7/20.                         (6)

At the axis-aligned frame ell=1 and L-ell=0.
For s>0, the first branch of (4) gives
ell=1/c>=1 and

    L-ell=c+s-1/c
           =s*(1-s/c)
           <=t*(1-t)<=1/4<7/20,

where t=s/c belongs to [0,1].

In the second branch of (4), we first show
ell>1. Since m<=22/25 it suffices,
by (5), to prove

    L-cs>22/25.                                   (7)

The left side is the concave quadratic
L-(L^2-1)/2 on [1,sqrt(2)], so its
minimum occurs at an endpoint. Its values
are 1 and sqrt(2)-1/2. The second exceeds
131/150 by the elementary rational bound
sqrt(2)>707/500; indeed
707/500-1/2-22/25=17/500>0.
Thus (7) holds, giving ell>1.

For the second claim in the sloping branch,
the inequality ell>L-7/20 is equivalent,
by (5) and cs>0, to

    m < L*(1-cs)+(7/20)*cs.                               (8)

The right side, after substituting
cs=(L^2-1)/2, is

    F(L)=(3*L-L^3)/2+(7/40)*(L^2-1).

Its second derivative is F''(L)=-3L+7/20<0
throughout [1,sqrt(2)], hence its minimum
is at an endpoint. At L=1 it is 1.
At L=sqrt(2) it is

    sqrt(2)/2+7/40
      >707/1000+7/40
      =882/1000
      >22/25=880/1000.                          (9)

Thus F(L)>m for every allowed frame,
proving (8), ell>L-7/20, and the
strict second part of (6).
No orientation grid or tested extremum
is a premise of either inequality.

## 3. The topmost and bottommost square lie wholly in quadrants

At x=X, every square contributes a
vertical chord of length ell_i>=1,
whose **open interval** lies inside
its open square interior. The three
open intervals are pairwise disjoint.
Order them from bottom to top,
I_1,I_2,I_3, within the disk slice [-B,B].

Because each of the first two intervals
has length at least one, the bottom
endpoint of the top chord I_3 is at least

    -B+ell_1+ell_2>=2-B>7/20,                     (10)

by (2). The full square supporting I_3
has total vertical projection width L_3.
Its true lowest y-coordinate is at
least the chord's lower endpoint minus
the unused part of its vertical width:

    min_y(S_3)
       >= lower(I_3)-(L_3-ell_3)
       >7/20-7/20=0,                               (11)

using (6). Thus S_3 lies wholly in
the open upper half-plane y>0.

Similarly the highest point of the
bottom chord I_1 is at most

    B-ell_2-ell_3<=B-2< -7/20.

The entire bottom square can extend
above that chord endpoint by at most
L_1-ell_1<7/20, hence

    max_y(S_1)<0.                                   (12)

Thus S_1 lies wholly in the open
lower half-plane. Together with
their original x>=h>0 cap membership,
they lie wholly in the northeast
and southeast origin quadrants,
respectively. This proves the theorem.

## 4. Corollary for two perpendicular triple sides

Work in the central square C's own frame.
At q<=9789/2500, we have
R<=sqrt(9789)/50<99/50.
Suppose its R and U central sides
each serve three whole squares and
their signed outward offsets both
exceed or equal 11/50.

Apply the just-proved theorem to the
three R squares. It gives a specific
member S_R wholly in x>0,y>0.
Apply it to the three U squares,
with coordinates exchanged. It gives
a specific member S_U wholly in
x>0,y>0.

The k=4 origin-sector replication theorem
HUMAN_ORIGIN_SECTOR_REPLICATION.md proves that
**at most one entire unit square can lie in
any origin quadrant** at this radius.
Thus S_R and S_U must be the **same
actual square**. Since it belongs to both
the original R and U central-side
memberships, its exact status is RU.
If all seven exterior statuses were
single-side, this is impossible.

The offset condition (A) follows by
writing h_R=1/2+a, h_U=1/2+b.
Reflections/rotations treat every
perpendicular choice. QED.

## Exact limitation

The proof makes no claim when one of
the two triple-side offsets falls below
11/50. Such a small-offset side has
more available cap width, and the
fixed-middle-chord estimate used here
no longer establishes L-ell<7/20.
Also the theorem is about *full*
central-owned side membership, not
the sign of square-center coordinates.

In particular it does not prove the
entire S1 type impossible, nor the
unrestricted sharp lower bound
R8>=Rhat. It removes a definite
continuous central-position region
from S1 and every analogous
perpendicular-triple/no-double branch.
