# A unit beyond the 59/60 wall has a nearly axial frame and a narrow center strip

**Status: complete proposed force-free theorem, frozen for full root
and independent review.** This is a shorter standalone proof of
the particular wall input used by the current leaf-channel caller;
it does not claim to reconstruct the entire rolled-back general
wall source.

Let \(K\) be any actual unit square in the disk centered at the
origin with radius \(R\), where

\[
 R^2\le Q=\frac{1105}{256}.
\]

Let \(n,j\) be any orthonormal coordinates, of either orientation,
and suppose

\[
                         K\subset\{n\cdot x\ge59/60\}.
\tag{1}
\]

Write \((X,Y)\) for its center in these coordinates. Let \(C,s\)
be its larger and smaller nonnegative own-axis projections on the
\(n\) direction, so

\[
 C\ge s\ge0,\qquad C^2+s^2=1.
\]

**Theorem.**

\[
                  s<\frac1{10},\quad C>\frac{99}{100},
                  \quad |Y|<\frac3{20}.
\tag{2}
\]

No boundary contact, force equation, degree, selected normal, or
second square is needed. In particular (1) need not be an equality
at the actual minimum support, and all side and vertex endpoints
are included.

## 1. The complete frame bound

The actual width in the \(n\) direction is \(C+s\). The largest
\(n\)-coordinate is therefore at least \(59/60+C+s\), and at
most \(R\). The exact rational radius comparison is

\[
 R\le\frac{\sqrt{1105}}{16}<\frac{133}{64},
 \qquad
 \left(\frac{133}{64}\right)^2-Q=\frac9{4096}>0.
\]

Consequently

\[
                  C+s<\frac{133}{64}-\frac{59}{60}
                       =\frac{1051}{960}.
\tag{3}
\]

The function \(s+\sqrt{1-s^2}\) is increasing on
\([0,1/\sqrt2]\). If \(s\ge1/10\), then

\[
 C+s\ge\sqrt{\frac{99}{100}}+\frac1{10}
       >\frac{191}{192}+\frac1{10}
       =\frac{1051}{960},
\]

contrary to (3). The strict square-root comparison follows by
squaring its positive sides. This proves \(s<1/10\), and then
\(C=\sqrt{1-s^2}>\sqrt{99/100}>99/100\).

## 2. Complete center-strip proof, for both tilt signs

Suppose \(|Y|\ge3/20\), and reflect the \(j\) coordinate so
that \(Y\ge3/20\). The actual horizontal half-width is
\((C+s)/2\), so (1) gives

\[
                         X\ge\frac{59}{60}+\frac{C+s}{2}.
\tag{4}
\]

Use the elementary bound

\[
 C=\sqrt{1-s^2}\ge1-s^2\ge1-\frac{s}{10},
\tag{5}
\]

valid on \(0\le s<1/10\). There are exactly two physical tilt
signs, with the axial case common to both.

In the first sign choose inward axis directions \((C,s)\) and
\((-s,C)\). The actual corner obtained by adding half of both
axes to the center has coordinates

\[
 \left(X+\frac{C-s}{2},\ Y+\frac{C+s}{2}\right)
 \ge\left(\frac{119}{60}-\frac{s}{10},\
          \frac{13}{20}+\frac{9s}{20}\right)
\tag{6}
\]

coordinatewise, by (4)--(5). All displayed lower coordinates are
positive. Its squared norm is therefore at least

\[
 \left(\frac{119}{60}-\frac{s}{10}\right)^2+
 \left(\frac{13}{20}+\frac{9s}{20}\right)^2
 =\frac{7841}{1800}+\frac{113}{600}s+\frac{17}{80}s^2.
\tag{7}
\]

In the other sign choose axis directions \((C,-s)\) and
\((s,C)\). The analogous actual upper-far corner is bounded
coordinatewise below by

\[
 \left(\frac{119}{60}+\frac{9s}{10},\
       \frac{13}{20}-\frac{11s}{20}\right).
\tag{8}
\]

The second coordinate is at least \(119/200>0\). Its squared
norm is thus at least

\[
 \left(\frac{119}{60}+\frac{9s}{10}\right)^2+
 \left(\frac{13}{20}-\frac{11s}{20}\right)^2
 =\frac{7841}{1800}+\frac{571}{200}s+\frac{89}{80}s^2.
\tag{9}
\]

Every additional coefficient in (7),(9) is nonnegative, whereas

\[
                         \frac{7841}{1800}>\frac{1105}{256}=Q.
\tag{10}
\]

Both physical frame signs contradict containment of that actual
corner. Reflection proves the other center sign as well, giving
\(|Y|<3/20\). This proves the full theorem.

## 3. Exact leaf-channel caller

In `ROOTED_ALIGNED_OUTER_LEAF_CHANNEL_BRANCH_PRESSURE.md`, the real
loaded unit V satisfies \(\min_V n\cdot x=h>59/60\). The theorem
therefore supplies all three bounds in that source's wall display:
\(|c_V\cdot j|<3/20\), \(C>99/100\), \(s<1/10\).
It keeps both tilt signs until the actual center/force argument in
that source excludes one. It requires no shortening of V's true
force equation, no equality of the auxiliary wall with its actual
support, and no canonical movement.

This gives a short independent proof at precisely that wall height.
It does not assert the stronger 39/40-wall statement of the older
general source or any new graph closure by itself.
