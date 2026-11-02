# Sharper zero-marker geometry and a central whole-floor subcase

November 2, 2026. Complete hand derivations of the stated conditional
results. No numerical evaluation, mathematical script, Lean, Lake, or CI
is used in this note.

This continues
`SIDE_PAIR_SEVEN_SIXTEENTHS_AND_EQUAL_EXTREME_ROUTING_HAND_PROOF.md`.
We retain its actual horizontal four-chain, strict-radius normalization,
occupancy (L,C,R)=(2,1,2), and both inner mains at the top markers.
The equal-bottom case is its vertical reflection. Write U_L,U_R for
the zero-marker outsiders, B_L,B_R for the bottom-marker outsiders,
and F for the central outsider. Put

\[
 Q=1105/256,\quad \rho=91/60,\quad l=29/60,
 \quad c=221/600,\quad L=503/480.
\]

For a physical unit write h for either coordinate halfwidth,
g=1/(4h), and k=sqrt(1/2-h^2). The preceding note proves

\[
 -7/16<y_{U_i}<227/620,\qquad
 l\le |x_{U_i}|<47/80,
 \qquad y_F<\min(y_{U_L},y_{U_R}).                     \tag{1}
\]

We also retain its genuine physical nonoverlap hypotheses throughout.

## 1. Every zero-marker square has whole top below 41/48

Let M be the main on the same side as U. Its actual-chain bounds give

\[
 1/2\le h_M<31/60,\qquad
 |x_M|>h_M-1/60,\qquad y_M>3/5>|x_M|.
\]

Among the two possible outward-quadrant vertex offsets (h_M,k_M)
and (k_M,h_M), the first has the smaller squared norm because
y_M>|x_M|. At least the smaller one must therefore fit the Q-disk.
Consequently

\[
 y_M\le \sqrt{Q-(|x_M|+h_M)^2}-k_M
       <\sqrt{Q-(2h_M-1/60)^2}-k_M.                    \tag{2}
\]

By (1), the horizontal center gap of U and M is less than 5/48.
Since g_M>15/31, their inset clearance exceeds 3/8. The proved
near-main physical clearance therefore gives

\[
 y_M-y_U\ge g_M+h_U-1/128.
\]

Combining this with (2) yields

\[
 y_U+h_U<K(h_M):=
 \sqrt{Q-(2h_M-1/60)^2}-\sqrt{1/2-h_M^2}
                       -\frac1{4h_M}+\frac1{128}.       \tag{3}
\]

The function K is increasing on [1/2,31/60]. Indeed, put
A=sqrt(Q-(2h-1/60)^2). On this interval A>9/5, because

\[
 Q-(61/60)^2-(9/5)^2=493/11520>0.
\]

Also h/k>=1 and 1/(4h^2)>1/2. Hence

\[
 K'(h)=-\frac{2(2h-1/60)}A+\frac h k+\frac1{4h^2}
      >-61/54+3/2=10/27>0.                            \tag{4}
\]

At h=31/60, use

\[
 \sqrt{Q-(61/60)^2}<29/16,
 \qquad \sqrt{1/2-(31/60)^2}>193/400.
\]

The respective squared reserves are 17/7200 and 359/1440000.
Their difference is bounded by 133/100, so

\[
 K(h_M)<\frac{133}{100}-\frac{15}{31}+\frac1{128}
                  <\frac{41}{48},                    \tag{5}
\]

where the last reserve is 67/297600. We have proved

\[
 \boxed{y_U+h_U<41/48,\qquad y_U<17/48.}               \tag{6}
\]

The first estimate retains the orientation of U; the second only uses
h_U>=1/2.

## 2. The zero centers lie in a narrower horizontal band

Let E be the same-side outer main. Its inset has halfwidth g_E>=15/32
and g_E-|y_E|>c. Since |y_U|<7/16, its vertical center gap V from E obeys

\[
 V-g_E<7/16-c=83/1200.
\]

The radius-1/2 disk inside U is disjoint in interior from this inset.
If D is their horizontal center gap, the exact point-to-inset distance
therefore gives

\[
 D>g_E+\sqrt{1/4-(83/1200)^2}.
\]

The ordering of their x-coordinates is supplied by the established
main and outsider bands. Thus

\[
 |x_U|<L-\sqrt{1/4-(83/1200)^2}<\frac{2211}{4000}.       \tag{7}
\]

For the last comparison, L-2211/4000=2971/6000, and

\[
 1/4-(83/1200)^2-(2971/6000)^2=934/36000000>0.
\]

This fraction also satisfies

\[
 \frac{11}{36}-(2211/4000)^2
                         =3311/144000000>0.             \tag{8}
\]

## 3. Improved central and bottom center heights

Assign F to the zero unit in its own horizontal half-plane, using
either one if x_F=0. Since |x_F|<l<=|x_U|, equation (7) gives
|x_F-x_U|<2211/4000. The two unit inscribed disks and (8) imply

\[
 y_U-y_F>5/6.
\]

The sign is already supplied by (1); alternatively the upper bound
y_F<11/30 and the zero lower bound -7/16 exclude the opposite sign.
By (6),

\[
                         \boxed{y_F<-23/48.}           \tag{9}
\]

Now suppose a bottom-marker unit B has y_B>=-5/8. A unit containing
the marker at height -1 has y_B<=-1+h_B<0, so |y_B|<=5/8.
The same endpoint/inset distance calculation gives

\[
 |x_B|<L-\sqrt{1/4-(77/300)^2}<187/300.                 \tag{10}
\]

Here 5/8-c=77/300, L-187/300=1019/2400, and the last squared reserve
is 22183/5760000. The corresponding zero unit also has |x_U|<187/300
by (7), whereas both centers have |x|>=l. Their horizontal gap is
therefore less than 187/300-l=7/50. The inscribed disks give

\[
 y_U-y_B>\sqrt{1-(7/50)^2}>99/100.
\]

The final squared reserve is 3/10000. The genuine side marker order
supplies y_U>y_B. Using (6),

\[
 y_B<17/48-99/100=-763/1200<-5/8,
\]

a contradiction. Hence

\[
                    \boxed{y_{B_L},y_{B_R}<-5/8.}       \tag{11}
\]

For reference these also strengthen the already proved outward sign
of both F-to-B separators. The absolute center-height differences are
now bounded by

\[
 \max\{91/60-5/8,\ 36/25-23/48\}
       =\max\{107/120,1153/1200\}<1.                   \tag{12}
\]

Thus a separating normal from F toward B_L must point strictly left,
and one from F toward B_R must point strictly right, exactly as before.

## 4. An explicit whole-central-floor subcase

Retain the same-side zero U from Section 3. Since h_F<=1/sqrt(2)<17/24,
that section's center gap gives

\[
                 y_F+h_F<y_U-5/6+17/24=y_U-1/8.        \tag{13}
\]

Consequently

\[
 \boxed{y_U\le1/120\quad\Longrightarrow\quad
                       y_F+h_F<-7/60.}                \tag{14}
\]

In particular, if both zero centers are nonpositive, the central unit
lies wholly below -1/8. After vertical reflection, its whole floor is
strictly above 1/8, and therefore above the 7/60 floor used by the
shared-central-orientation terminal.

If x_F!=0 and (14)'s whole-top conclusion fails, F is in the same
*strict* horizontal half-plane as a zero unit with y_U>1/120. At x_F=0 either
zero may be chosen, so failure there forces both zero centers above
1/120. This is a proved restriction on the remaining case, not a claim
that the whole-top bound holds unconditionally.

## 5. A positive zero center forces h_U<5/8

Suppose y_U>=0. We claim h_U<5/8. Write its absolute side-axis
components as a>=b>=0, a^2+b^2=1, so h_U=(a+b)/2.
Let E again be the corresponding outer main, with inset halfwidth g_E.
Put D=|x_E-x_U| and V=|y_E-y_U|. The known bands give

\[
 D-g_E<\rho-l-15/32=271/480=:d,
 \qquad g_E-V>c-y_U.                                  \tag{15}
\]

Assume h_U>=5/8. The horizontal coordinate axis cannot separate U
from the inset: it would require D-g_E>=h_U>d. The vertical coordinate
axis cannot separate them either, since V<9/16 and g_E+h_U>9/16.
The separating-axis theorem for the physical square and the aligned
inset therefore supplies a normal along a side axis of U. Its
horizontal component must be positive when directed toward E:
a nonpositive one has projection at most V, smaller than the sum of
the two supports. Taking the more favorable vertical sign, the two
possible absolute component orders give

\[
 D-g_E\ge\frac{1/2+(g_E-V)b}{a}
 \quad\hbox{or}\quad
 D-g_E\ge\frac{1/2+(g_E-V)a}{b}.
\]

Here b>0 under h_U>=5/8. Since g_E-V>c-y_U>0, the second lower bound
is at least the first. Indeed their difference has numerator
(a-b){1/2+(g_E-V)(a+b)}. Thus (6) and (15) imply

\[
 da>1/2+(c-y_U)b
       >1/2+(h_U-583/1200)b.                           \tag{16}
\]

Set q=583/1200 and, with a=sqrt(1-b^2), define

\[
 f(b)=da-1/2-\big((a+b)/2-q\big)b.
\]

For b>=1/4, direct differentiation gives

\[
 f'(b)=-a/2-b+q+\frac b a(b/2-d)<-39/400<0.            \tag{17}
\]

For the displayed bound, use a>2/3, b<3/4,
b/2-d<3/8-271/480<0, and b>=1/4.
At h=5/8 the components are

\[
 a_0=(5+\sqrt7)/8,\qquad b_0=(5-\sqrt7)/8>1/4.
\]

The function h=(sqrt(1-b^2)+b)/2 is increasing for 0<=b<=1/sqrt(2),
so h_U>=5/8 entails b>=b_0. At that endpoint,

\[
 f(b_0)=\frac{1689\sqrt7-4495}{19200}<0,
\]

as sqrt(7)<53/20 and 1689(53/20)-4495=-383/20.
Equations (17) and (16) now contradict one another. This proves

\[
                  \boxed{y_U\ge0\quad\Longrightarrow\quad h_U<5/8.}
                                                                  \tag{18}
\]

Thus failure of the central whole-top caller forces a positive,
restricted-orientation zero square on F's own side. The proof does not
replace physical endpoint separation by coordinate separation.

## 6. Exact remaining caller

The equal-extreme occupancy has now been narrowed to two possibilities.
Either the central whole-floor 7/60 premise follows from (14), or its
same-side zero has y_U>1/120 and h_U<5/8. Sections 1--5 prove the
additional whole-top, horizontal-band, and center-height bounds in
both alternatives.

The first alternative still needs the matched physical endpoint
separator to belong to a proved transfer class. The second still
needs a central-floor replacement or a different joint terminal.
No unconditional exclusion of the equal-extreme occupancy, no new
canonical root count, and no unrestricted A.2 closure is claimed.
