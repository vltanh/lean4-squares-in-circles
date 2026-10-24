# A negative-pressure unique boundary neighbor contacts only near its inner corner

**Status: complete uniform hand geometric implication; root and separate independent
full hand audits passed.** Work in

    79/40 <= R <= sqrt(1105)/16.

Let S be a contained unit square with one physical circle corner z,
and let H be another interior-disjoint unit square which physically
touches S. Assume only

    c_H . z < 0.                                    (1)

No positive degree, load equation, normal owner, frame relation or
secondary minimizer is assumed. Every physical contact point and hence
every actual shared-side application mean is retained.

Choose the outward side frame of S at z, exchanging its two axes so

    z=(a,b),  a>=b>=1/2,  a²+b²=R²,
    S=[a-1,a] x [b-1,b],  z_0=(a-1,b-1).             (2)

The lower coordinate bounds follow by comparing z to each adjacent
corner. The strict unique-mask classification is retained throughout.

**Theorem.** Every actual point p in H intersection S belongs to one
of the two inner faces of S meeting z_0; neither outer face meeting z
can contain such a point. Moreover

    b>3/5,                |p-z_0|<79/160<1/2.        (3)

In the full higher-radius domain R²>=17/4 these strengthen to

    b>19/20,              |p-z_0|<5/38.              (4)

The containing-circle origin is not translated in any estimate.
The root itself also satisfies

    |c_H|² < 9/2-R² < 1.                            (4a)

In particular R²>=17/4 implies |c_H|<1/2, so the circle origin lies
strictly inside the actual H square, in every orientation.

To prove (4a), take any actual contact p. The real square diameters
give |z-p|<=sqrt(2) and |p-c_H|<=1/sqrt(2), hence
|z-c_H|<=3/sqrt(2). But (1) gives

    R²+|c_H|² < |z-c_H|² <= 9/2.

The circle origin is at distance less than1/2 from c_H when
R²>=17/4. Every unit square contains the open radius-1/2 disk
about its center, proving the strict origin-interior consequence.

## 1. An exact contact projection and the complete face restriction

The circumradius of H is 1/sqrt(2). Every p in H intersection S
therefore obeys

    p.z = c_H.z + (p-c_H).z < R/sqrt(2).             (5)

On either outer S face meeting z, however,

    p.z >= R²-max(a,b) >= R²-R > R/sqrt(2),

since R>=79/40>1+1/sqrt(2). This contradicts (5).
Interior-disjoint squares have their contact set in both boundaries.
Hence every such p lies on one of the two inner faces meeting z_0;
the far endpoints of those faces, which also lie on outer faces, are
excluded. This proof applies to the whole actual intersection, not
just a selected force point.

Every point of S also satisfies p.z>=R²-a-b. In particular (5)
gives the necessary strict inequality

    a+b > R²-R/sqrt(2).                              (6)

## 2. Both outward corner coordinates exceed3/5

For 0<t<R/2 define

    f_t(R)=R²-R/sqrt(2)-t-sqrt(R²-t²).

For either fixed t used below and all R>=79/40, we have t<R/2,
sqrt(R²-t²)>R/2 and

    f_t'(R)=2R-1/sqrt(2)-R/sqrt(R²-t²)
            >2R-3>0.                               (7)

At R_0=79/40 and t=3/5, the exact comparisons

    R_0/sqrt(2)<7/5,
    sqrt(R_0²-9/25)<113/60

hold on squaring. They give

    f_(3/5)(R_0)
      >6241/1600 - 7/5 - 3/5 - 113/60
      =83/4800>0.                                  (8)

For fixed R, sqrt(R²-b²)+b increases for 0<=b<=t<R/sqrt(2).
Thus b<=3/5 would give

    a+b <= sqrt(R²-9/25)+3/5 < R²-R/sqrt(2),

by (7)--(8), contradicting (6). This proves b>3/5 and hence a>3/5.

## 3. The complete higher-radius coordinate bound

Take t=19/20 and R_1=sqrt(17)/2. The exact comparisons

    R_1/sqrt(2)=sqrt(17/8)<35/24,
    sqrt(R_1²-(19/20)²)=sqrt(1339)/20<11/6

follow from1224<1225 in denominator576, and1339/400<121/36,
respectively. Therefore

    f_(19/20)(R_1)
      >17/4 - 35/24 - 19/20 - 11/6
      =1/120>0.                                    (9)

Monotonicity (7) and the same increasing-b comparison now imply
b>19/20 for every R>=R_1. This includes the exact R²=17/4 endpoint.

## 4. Every genuine contact is close to the actual opposite corner

Write an actual p in the form

    p=z_0+(s,t),   0<=s,t<=1.

Section1 shows that s=0 or t=0. Combining (5) with its exact
dot product gives

    a*s+b*t < Delta:=a+b-R²+R/sqrt(2).

By a+b<=sqrt(2)R,

    0<Delta <= (3/sqrt(2))R-R².                    (10)

Because p is on one of the two inner faces and a,b>=b, this implies

    |p-z_0| < Delta/b.                             (11)

For the whole window, 3/sqrt(2)<17/8 and the function
R(17/8-R) is decreasing for R>=79/40. Thus

    Delta < (79/40)(17/8-79/40)=237/800.

Together with b>3/5, equation (11) gives

    |p-z_0| < (237/800)/(3/5)=79/160,

as asserted in (3).

If R²>=17/4, the exact function on the right of (10) is decreasing
for R>=R_1. Using the bound in Section3 gives

    Delta <= 3*sqrt(17/8)-17/4
            <3*(35/24)-17/4=1/8.

Since b>19/20, (11) gives |p-z_0|<5/38, proving (4).
Every original mean and its endpoint is subject to these same strict
bounds; none has been replaced by the opposite corner.

## 5. Applications and limits of the conclusion

END_TRIANGLE_RADIAL_NEIGHBOR_OBSTRUCTION.md supplies the premise (1)
for some unique boundary neighbor in the opposite-load C4 attachment.
BOUNDARY_THREE_PATH_RESULTANT_CONE.md strengthens the diamond-hub
domain: one of its genuine degree-two endpoint tips can be labeled A
with a unique circle corner satisfying c_H.z_A<0. The present theorem
therefore applies to that actual H/A intersection in both uses.

The conclusion is a whole geometric restriction, not a replacement
of S by a radial leaf or a claim that all its other positive contacts
are near z_0. Only contacts with the specified negative-pressure H
are constrained. It does not close the whole C4 or diamond attachment,
nor assume the higher-radius bound when R²<17/4. No movement, new
normal choice, numerical sample, Lean compilation or CI is used.

