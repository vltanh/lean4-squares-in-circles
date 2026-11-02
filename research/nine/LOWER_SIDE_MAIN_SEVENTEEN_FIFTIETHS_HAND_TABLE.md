# A lower side outsider forces its inner main above minus seventeen fiftieths

November 2, 2026. Complete original-pair hand reduction and 74-row exact
table. Computer discovery preceded the proof. A separate Fraction replay
imports neither the directed-integer producer nor its arithmetic kernel.
No Lean or CI.

Put

\[
 Q=1105/256,\qquad l=29/60,\quad u=13/12,\quad\rho=91/60.
\]

## 1. Complete physical statement

Retain four original physical unit squares in the closed Q-disk, forming
an actual horizontal projection chain M0,M1,M2,M3. Their frames may be
independent. Let an original outsider S have center

\[
                     -u\le x_S\le-l,\qquad y_S<y_1,
\]

and open interior disjoint from the original M1. Then

\[
                              y_1>-17/50.                 \tag{1}
\]

Horizontal reflection gives the right-side statement. Vertical reflection
gives the corresponding upper-side statement. Consequently a full side
whose two original outsiders lie on opposite sides of its main satisfies

\[
                              |y_M|<17/50.
\]

The theorem needs no main center-cone condition, selected outsider short
link, central outsider, endpoint contact, or orientation restriction
beyond the actual four-chain consequences derived below. In particular
it applies to the original lower side unit in the middle-marker case of
the (2,2,1) occupancy caller.

## 2. The correlated main-position band

Every unit-square center has norm below rho. Indeed, if its norm is r,
one of the original corners has squared norm at least r^2+r+1/2, whereas

\[
                  \rho^2+\rho+1/2-Q=31/57600>0.
\]

Write h_i for horizontal projection halfwidths and

\[
 A_0=-x_0-h_0,\quad A_3=x_3-h_3,\quad h_1=1/2+e.
\]

The center bound and h0,h3>=1/2 give Ai<61/60. The actual main gaps give

\[
 x_1\ge h_1-A_0>h_1-61/60,
\]

\[
 x_1\le A_3-h_1-2h_2<1/60-h_1.
\]

Thus

\[
 0\le e<1/60,\qquad -31/60+e<x_1<-l-e.                  \tag{2}
\]

Suppose contrary to (1) that y1<=-17/50. Reflect both coordinates,
writing the main center as (m,Z) and the side center as (X,Y). Then

\[
 l+e\le m\le31/60-e,\quad l\le X\le u,
 \qquad Y>Z\ge17/50.
\]

Their actual absolute horizontal gap D and positive vertical gap V obey

\[
 D\le d:=\max\{X-l-e,31/60-e-X\}.                       \tag{3}
\]

No main position is reset: this is an upper bound on the one original
gap, obtained from the correlated band (2).

For the folded main and side tangents use tM,t in [0,1], with

\[
 a(t)=(1+t^2)^{-1/2},\quad b(t)=ta(t),
 \quad h(t)=(a(t)+b(t))/2,\quad k(t)=(a(t)-b(t))/2.
\]

The main bound hM<31/60 implies

\[
                  0\le t_M<17/500,
\]

because h increases on [0,1] and

\[
 h(17/500)^2-(31/60)^2=32371/901040400>0.                \tag{4}
\]

## 3. Both original chiralities and all four physical owner axes

For a side chirality s in {-1,1}, its four original corner offsets are

\[
               (h,-sk),\quad(sk,h),\quad(-h,sk),\quad(-sk,-h).
\]

They give the original center-height ceiling

\[
 U_s(X,t)=\min\left(\rho,
        \min_{(d_x,d_y)}\{\sqrt{Q-(X+d_x)^2}-d_y\}\right).
\]

Every radicand is positive on the complete root below. Put

\[
 U=\max\{U_{-1},U_{+1}\},\qquad v=U-17/50.
                                                               \tag{5}
\]

The one original S therefore satisfies V<=v. Taking the larger chirality
ceiling enlarges the physical possibilities; it imposes no new chirality.

For two original square frames, the support sum on any side-axis owner is
one half of 1 plus the absolute cosine and sine of their relative angle.
For folded angles alpha,beta in [0,pi/4], the smaller possible support
over the two chirality relations is

\[
 \sigma(\alpha,\beta)=
 {1+\cos(\alpha-\beta)+|\sin(\alpha-\beta)|\over2}.
                                                               \tag{6}
\]

To verify that opposite chiralities cannot give less, put
p=aM*b and q=bM*a. The difference of their cosine-plus-sine sums is

\[
            -2b_Mb+p+q-|p-q|
                =2\{\min(p,q)-b_Mb\}\ge0,
\]

since aM>=bM and a>=b. Thus (6) is a lower bound for the support of
the actual original pair, whichever of its two squares owns separation.

Taking absolute normal components only increases a center projection.
The separating-axis theorem therefore requires at least one of

\[
 ad+bv-\sigma,\quad bd+av-\sigma,
 \quad a_Md+b_Mv-\sigma,\quad b_Md+a_Mv-\sigma
                                                               \tag{7}
\]

to be nonnegative. This union includes both original owners, both side
axes of each owner, every sign, and both chiralities. No original pair
has been replaced by a new square or an independent orientation.

## 4. Complete exact root and interval rule

The entire contrary family maps into the closed root

\[
 (t_M,t,X)\in[0,17/500]\times[0,1]\times[l,u].             \tag{8}
\]

For each tangent interval, a,k decrease and b,h increase, so their
endpoint evaluations enclose the complete frame range. Formula (6) is
increasing with the absolute angle difference on [0,pi/4]. Its minimum
over a main/side tangent box is therefore 1 if the intervals overlap;
otherwise it occurs at the two closest endpoints. The verifier evaluates
that support from the original endpoint dot product and determinant.

Use this lower support bound, and ordinary outward interval arithmetic
in (3), (5), and (7). Every row below has a strictly negative upper bound
for all four expressions in (7). Its final column is a rational lower
bound, in millionths, for the resulting positive exclusion reserve.
The corresponding 147-node midpoint tree covers (8), with 74 leaves and
maximum depth 15. Both children of every split are retained, including
shared faces. There is no frontier or unproved complement.

The certificate is `lower_side_main_17_50_cover.json`. Its SHA256 is
`666faf930b12b03b0c6c762886fd13833d0834fb246b750691b5257033afb876`.
The independent `verify_lower_side_main_17_50.py` uses Fraction intervals
and outward 80-bit radical enclosures, reconstructs every root and split,
and checks every physical owner margin. Its saved exact report is
`lower_side_main_17_50_fraction_replay.json`.

The least directed-integer production reserve was

\[
                 164669289561283/9223372036854775808>0.
\]

The separate Fraction replay has a slightly stronger positive rational
reserve and verifies all 74 rows. The largest allowed main height is
therefore strictly below 17/50 in the reflected contrary system,
proving (1). Only this stated original-side theorem is closed here; its
use in an occupancy caller is a separate assembly step.

## 5. Printed exact table

| Main tangent interval | Side tangent interval | X interval | Reserve, in millionths |
| --- | --- | --- | ---: |
| [0, 17/500] | [0, 1/128] | [29/60, 67/120] | 3376 |
| [0, 17/500] | [1/128, 1/64] | [29/60, 67/120] | 1521 |
| [0, 17/500] | [0, 1/64] | [67/120, 19/30] | 39200 |
| [0, 17/500] | [1/64, 3/128] | [29/60, 25/48] | 904 |
| [0, 17/500] | [1/64, 3/128] | [25/48, 67/120] | 20488 |
| [0, 17/500] | [3/128, 7/256] | [29/60, 25/48] | 986 |
| [0, 17/500] | [7/256, 1/32] | [29/60, 25/48] | 17 |
| [0, 17/500] | [3/128, 1/32] | [25/48, 67/120] | 18666 |
| [0, 17/500] | [1/64, 1/32] | [67/120, 19/30] | 35822 |
| [0, 17/500] | [1/32, 17/512] | [29/60, 25/48] | 48 |
| [0, 17/1000] | [17/512, 9/256] | [29/60, 25/48] | 8094 |
| [17/1000, 17/500] | [17/512, 35/1024] | [29/60, 25/48] | 492 |
| [17/1000, 17/500] | [35/1024, 9/256] | [29/60, 25/48] | 336 |
| [0, 17/500] | [1/32, 9/256] | [25/48, 67/120] | 18830 |
| [0, 17/500] | [9/256, 37/1024] | [29/60, 25/48] | 147 |
| [0, 17/500] | [37/1024, 19/512] | [29/60, 25/48] | 387 |
| [0, 17/500] | [19/512, 5/128] | [29/60, 25/48] | 120 |
| [0, 17/500] | [9/256, 5/128] | [25/48, 67/120] | 18472 |
| [0, 17/500] | [1/32, 5/128] | [67/120, 19/30] | 36075 |
| [0, 17/500] | [5/128, 21/512] | [29/60, 25/48] | 594 |
| [0, 17/500] | [21/512, 11/256] | [29/60, 25/48] | 1063 |
| [0, 17/500] | [5/128, 11/256] | [25/48, 67/120] | 19472 |
| [0, 17/500] | [11/256, 3/64] | [29/60, 25/48] | 511 |
| [0, 17/500] | [11/256, 3/64] | [25/48, 67/120] | 20397 |
| [0, 17/500] | [5/128, 3/64] | [67/120, 19/30] | 35905 |
| [0, 17/500] | [3/64, 13/256] | [29/60, 25/48] | 1425 |
| [0, 17/500] | [3/64, 13/256] | [25/48, 67/120] | 21243 |
| [0, 17/500] | [13/256, 7/128] | [29/60, 67/120] | 795 |
| [0, 17/500] | [3/64, 7/128] | [67/120, 19/30] | 37103 |
| [0, 17/500] | [7/128, 15/256] | [29/60, 67/120] | 1592 |
| [0, 17/500] | [15/256, 1/16] | [29/60, 67/120] | 2387 |
| [0, 17/500] | [7/128, 1/16] | [67/120, 19/30] | 38293 |
| [0, 17/500] | [0, 1/16] | [19/30, 47/60] | 47870 |
| [0, 17/500] | [1/16, 9/128] | [29/60, 67/120] | 822 |
| [0, 17/500] | [9/128, 5/64] | [29/60, 67/120] | 2396 |
| [0, 17/500] | [1/16, 5/64] | [67/120, 19/30] | 34159 |
| [0, 17/500] | [5/64, 11/128] | [29/60, 67/120] | 3964 |
| [0, 17/500] | [11/128, 3/32] | [29/60, 67/120] | 5528 |
| [0, 17/500] | [5/64, 3/32] | [67/120, 19/30] | 36463 |
| [0, 17/500] | [1/16, 3/32] | [19/30, 47/60] | 57758 |
| [0, 17/500] | [3/32, 7/64] | [29/60, 67/120] | 2282 |
| [0, 17/500] | [3/32, 7/64] | [67/120, 19/30] | 38740 |
| [0, 17/500] | [7/64, 1/8] | [29/60, 67/120] | 5356 |
| [0, 17/500] | [7/64, 1/8] | [67/120, 19/30] | 40989 |
| [0, 17/500] | [3/32, 1/8] | [19/30, 47/60] | 58371 |
| [0, 17/500] | [0, 1/8] | [47/60, 13/12] | 65851 |
| [0, 17/500] | [1/8, 9/64] | [29/60, 67/120] | 8340 |
| [0, 17/500] | [9/64, 5/32] | [29/60, 67/120] | 10384 |
| [0, 17/500] | [1/8, 5/32] | [67/120, 19/30] | 32328 |
| [0, 17/500] | [5/32, 3/16] | [29/60, 67/120] | 3366 |
| [0, 17/500] | [5/32, 3/16] | [67/120, 19/30] | 36666 |
| [0, 17/500] | [1/8, 3/16] | [19/30, 47/60] | 32534 |
| [0, 17/500] | [3/16, 7/32] | [29/60, 67/120] | 6005 |
| [0, 17/500] | [3/16, 7/32] | [67/120, 19/30] | 40952 |
| [0, 17/500] | [7/32, 15/64] | [29/60, 19/30] | 9367 |
| [0, 17/500] | [15/64, 1/4] | [29/60, 19/30] | 11263 |
| [0, 17/500] | [3/16, 1/4] | [19/30, 47/60] | 33602 |
| [0, 17/500] | [1/8, 1/4] | [47/60, 13/12] | 21734 |
| [0, 17/500] | [1/4, 9/32] | [29/60, 19/30] | 2398 |
| [0, 17/500] | [9/32, 5/16] | [29/60, 19/30] | 5111 |
| [0, 17/500] | [5/16, 3/8] | [29/60, 19/30] | 4358 |
| [0, 17/500] | [1/4, 5/16] | [19/30, 47/60] | 34859 |
| [0, 17/500] | [5/16, 3/8] | [19/30, 47/60] | 36411 |
| [0, 17/500] | [3/8, 1/2] | [29/60, 19/30] | 43218 |
| [0, 17/500] | [3/8, 1/2] | [19/30, 47/60] | 1364 |
| [0, 17/500] | [1/4, 5/16] | [47/60, 13/12] | 64513 |
| [0, 17/500] | [5/16, 3/8] | [47/60, 13/12] | 51323 |
| [0, 17/500] | [3/8, 1/2] | [47/60, 14/15] | 46089 |
| [0, 17/500] | [3/8, 1/2] | [14/15, 13/12] | 126408 |
| [0, 17/500] | [1/2, 3/4] | [29/60, 47/60] | 43259 |
| [0, 17/500] | [1/2, 3/4] | [47/60, 14/15] | 7389 |
| [0, 17/500] | [1/2, 3/4] | [14/15, 13/12] | 15502 |
| [0, 17/500] | [3/4, 1] | [29/60, 47/60] | 182524 |
| [0, 17/500] | [3/4, 1] | [47/60, 13/12] | 34330 |
