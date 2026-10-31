# The lower boundary neighbor of an aligned low S root has one opposite circle corner

Date: October 27, 2026.

**Status: complete hand local theorem, independently accepted in full
in REVIEW_LOW_S124_LOWER_CENTER_AND_OWNED_RETURN_ROOTED_BLOCKS_2026_10_27.md.
Root review and integration remain separate.** The physical corner screen preserves
every actual lower-neighbor frame and every circle mask. Its additional
center projection conclusion uses the lower neighbor's full original
degree-two star with a real boundary neighbor.

## 1. Exact original scope and unchanged notation

Keep the original nine physical unit squares and their compatible
selected certificate. Let H be a genuine S-leaf root of true degree
three, with both other actual neighbors physically boundary. In the
entire aligned strict-low domain, Sections1--4 of the accepted
S_LEAF_C5_ALIGNED_LOW_RADIUS_EXCLUSION.md give, after reflecting
the actual whole configuration,

    2<R<sqrt(17)/2,
    d=sqrt(R^2-1/4)-1,       14/15<d<1,
    a=1-d,                  0<a<1/15,
    H=[-a,d] times[h-1,h],  29/50<h<2/3,
    L=[d,d+1] times[-1/2,1/2],
    P_B=(-a,h),             n_B=(-c,s),
    P_D=(x,h-1),            n_D=-e_y,
    c,s>0, c^2+s^2=1,      3/10<x<=d,
    c/s=(x+a)/h.                                      (1)

These are consequences of the full true H3 force and torque, the
real leaf and the physical boundary-neighbor cover. They do not
use an all-boundary path. In particular their scope includes both
original S124 placements of the unloaded body.

The same local physical proof makes the lower unit D genuinely tilted.
Put g=1-h, so1/3<g<21/50. Its complete actual frame is

    D=P_D+[0,1](b,-t)+[0,1](-t,-b),
    b,t>0,                 b^2+t^2=1.                 (2)

The original HD application is exactly its top vertex P_D. No order
between b and t is initially assumed. Write

    u=b+t,       v=b-t,       q=b/t>0.

**Physical conclusion.** Every D corner except

    Z_D=(x+v,-g-u)                                     (3)

is strictly inside the original circle. Thus Z_D is D's unique
physical circle corner.

If D additionally has true degree two, positive circle load and an
actual other neighbor C physically touching the circle, then the
following further conclusions hold:

    b>=t,
    n_B dot c_D<0,
    j_B dot c_D<1/2,       j_B=(-s,-c),                (4)

where c_D is D's unchanged actual center. Equality b=t is retained.
No degree or force equation at B or C is used in (4), apart from
C being an actual boundary neighbor needed by the proper-concurrence
theorem at D.

## 2. The real leaf screen and the two immediate corners

The top vertex has squared norm less than
1+(21/50)^2<4. The left adjacent corner is
(x-t,-g-b). Its first-coordinate absolute value is less than d:
x-t>-7/10>-d and x-t<d. Its second-coordinate magnitude is
less than71/50. Consequently

    |(x-t,-g-b)|^2<d^2+(71/50)^2<7541/2500<4.        (5)

Both corners are strictly inside since R>2.

It remains to screen the right adjacent corner

    Z_right=(x+b,-g-t).                               (6)

If x+b<=d, the same bound (5) applies. Otherwise the actual edge
from P_D in direction (b,-t) crosses the real leaf's inner line
x=d. To avoid entering the open real leaf above its lower corner,
its crossing height must be at most-1/2. With

    T=h-1/2>2/25,

this gives the unchanged physical inequality

    x<=d-T(b/t)=d-Tq.                                 (7)

Equality is retained. It is an inequality at the original point,
not a moved application. The two coordinates in (6) therefore obey

    0<x+b<=d-Tq+q/sqrt(1+q^2),
    0<g+t=1/2-T+1/sqrt(1+q^2).                        (8)

The right sides are positive at the actual configuration. Lowering
T to2/25 increases them. For fixed q, the resulting upper squared
norm minus R^2 decreases strictly as d increases: its d derivative is

    2[q/sqrt(1+q^2)-(2/25)q-1]<0.                     (9)

Thus on any range where needed, it suffices to compare at

d0=14/15, T0=2/25. The next section supplies a whole-q proof,
including the limiting small and large directions.

## 3. A short exact three-range right-corner bound

### 3.1. The whole q<=1/2 range

Here b<=1/sqrt(5)<9/20. Without even using (7),

    |Z_right|^2<(d+9/20)^2+(71/50)^2<R^2.

After subtracting R^2=(d+1)^2+1/4, the upper difference is

    -(11/10)d+9689/10000
       < -1733/30000<0.                              (10)

All positive q up to1/2 are covered.

### 3.2. The whole q>=2 range

Here t<=1/sqrt(5)<9/20. Equation (7), T>2/25 and b<1 give

    x+b<d+21/25,       g+t<87/100.

Consequently the upper squared-norm difference is

    (d+21/25)^2+(87/100)^2-R^2
       =-(8/25)d+17/80
       <-517/6000<0.                                 (11)

The actual positive first coordinate makes this squaring step valid
even at an arbitrarily large formal q. The real screen already
excludes any q whose right side in (8) would be nonpositive.

### 3.3. The entire closed middle range 1/2<=q<=2

By (8)--(9), define the exact upper comparison

    A(q)=14/15-(2/25)q+q/sqrt(1+q^2),
    B(q)=21/50+1/sqrt(1+q^2),
    G(q)=A(q)^2+B(q)^2.                               (12)

Both coordinates are positive on this whole interval. Direct
differentiation, using A-qB=14/15-q/2, gives

    G''(q)/2=4/625-N(q)/(1+q^2)^(5/2),
    N(q)=29/50+(14/5)q-(23/25)q^2.                    (13)

N is concave. Its endpoint values are7/4 and5/2, so N>=7/4.
Also (1+q^2)^(5/2)<=25sqrt(5)<225/4. Thus

    G''(q)<2(4/625-7/225)=-278/5625<-1/25.           (14)

At q=1, the exact value and derivative are

    G(1)=(64/75)^2+(21/50)^2+1+(191/150)sqrt(2),
    G'(1)=41/(150sqrt(2))-256/1875.                   (15)

Using sqrt(2)<10/7 gives G(1)<15/4, with rational reserve
2077/78750. The elementary bounds7/5<sqrt(2)<3/2 give

    0<G'(1)<1/10.

The lower and upper reserves are257/5625 and542/13125.
The global Taylor inequality from (14), followed by completing
one square, therefore yields throughout the closed middle interval

    G(q)<=G(1)+G'(1)(q-1)-(q-1)^2/50
         <=G(1)+(25/2)G'(1)^2
          <15/4+1/8=31/8
          <3589/900=(29/15)^2+1/4.                   (16)

The final reserve is203/1800. This is a whole-interval concavity
proof, not a sampled directional estimate. Together (10), (11)
and (16) prove that the actual right adjacent corner is strictly
inside at every original b,t, with all screen equalities retained.

All three other actual corners have now been excluded. Since D is
physically boundary, its only physical circle corner is exactly (3).
No individual zero-weight physical corner has been suppressed.

## 4. The full original D2 star determines the weak tilt sign

Now impose the additional literal local hypotheses for (4): D has
exactly its two positive pair forces, one to the true root H and
the other to an actual physical boundary neighbor C, with positive
circle load. The complete proper-concurrence theorem
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma2.1, applies directly.
Its boundary-neighbor hypothesis is supplied by C, not by H.

The two lines are nonparallel. In the physical unique-corner case
their concurrence q_D lies in the closed actual D and is a positive
multiple of Z_D. The original DH force is North at P_D, so its line
has unchanged first coordinate x. Consequently

    q_D=tau Z_D,       tau=x/(x+b-t)>0.               (17)

Because q_D lies in the contained actual square, |q_D|<=R and
hence tau<=1. Since x>0, (17) proves

    b>=t.                                             (18)

The equality endpoint is intentionally retained: tau=1 would put
the concurrence at Z_D, but does not by itself assert that a
physical contact shares that circle corner. No strict inequality
is inferred from such an unproved sharing claim.

## 5. An exact half-unit bound for D's actual center projection

Let k=c/s=(x+a)/h. By (18), b>=1/sqrt(2)>7/10.
Since x>3/10 and d<1, the actual edge necessarily crosses the
leaf's inner line: x+b>1>d. The genuine screen (7) now applies,
and q=b/t>=1 gives

    x+a<=1-(h-1/2)q<=3/2-h,
    0<k<46/29.                                       (19)

The actual D center is

    c_D=(x+v/2,-g-u/2),
    v>=0,       u<=sqrt(2).

Its first coordinate is positive and its second negative. Thus
n_B dot c_D=-c(x+v/2)-s(g+u/2)<0.
For the other coordinate use x=hk-a:

    j_B dot c_D
       =-s(x+v/2)+c(g+u/2)
       <=[k(1-2h+1/sqrt(2))+a]/sqrt(1+k^2)
        <[(383/700)k+1/15]/sqrt(1+k^2).               (20)

Here h>29/50 and sqrt(2)<99/70 give
1-2h+1/sqrt(2)<383/700. The last scalar function increases
on0<=k<=46/29: its derivative has the sign of
383/700-k/15>0. Its value at the upper endpoint is

    (28457/1050)/sqrt(2957)<1/2,                      (21)

as shown by the exact positive squared reserve

    2957/4-(28457/1050)^2=1305569/275625>0.

This proves both original center inequalities (4), including b=t,
all actual force means and every proper-concurrence endpoint.

## 6. Exact export to the remaining low S124 route

In H--B--X--C--D--H plus the real S leaf, both C and D are true
loaded degree-two bodies and physically boundary. Thus the whole
source, including (4), applies literally. B's remaining return
feature, the actual width of X and the original BX and XC means
have not been used or changed. Both the near-corner and owned-side
upper return domains receive this same lower-neighbor conclusion.

The source by itself does not exclude either remaining route or
the whole S124 family. It supplies the complete physical corner
mask and the exact original center inequalities needed by their
separate callers. All three completion units remain, as do all
original forces and zero-weight physical contacts.

No numerical pose, altered normal, moved mean, shared metadata,
remote write, compilation or CI is a premise of the proof.

