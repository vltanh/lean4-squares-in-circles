# The strict-turn one-radial C6 has no doubly shared return transmitter

Date: October 26, 2026.

**Status: complete analytic physical-subfamily proof, accepted after root
and separate independent saved-source and physical-scope reviews.** See
REVIEW_C6_RADIAL_OPPOSITE_AND_DOUBLE_SHARED_ROOT_2026_10_26.md and
REVIEW_C6_RADIAL_DOUBLE_SHARED_RETURN_BLOCK_2026_10_26.md.
This proof uses the two original radial
port norms and one concave scalar function. It needs no upper bound
\(\theta_S\le3\pi/4\), no prescribed radial weight split, and no
coefficient certificate.

Work in the original radius window
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
                       d=\sqrt{R^2-\frac14}-1.
\tag{1}
\]
The positive component is an alternating all-side C6 with one
physically two-circle-corner loaded square S, two physically unique
loaded squares B,C, and three true unloaded degree-two transmitters.
Keep all nine physical units, every original force and corner weight,
all application means, and every transmitter slider.

Assume that \(\theta_B,\theta_C>\pi/2\), and that the B-to-C
transmitter has a genuine shared side at both loaded endpoints.

**Theorem.** This entire physical core is impossible.

The unconditional local upper-turn bound gives \(\theta_S\ge\pi/2\).
Its equality case is already classified by the complete right-turn
source; its B-to-C endpoints are strict opposite-vertex features,
contrary to the two genuine shares here. Thus the only branch needing
the proof below has all three actual turns greater than \(\pi/2\).

## 1. The actual parallel endpoint frames and their opposite ports

Normalize the unchanged doubly shared channel horizontally, with
positive height H and reserve one. The complete actual endpoint-center
theorem fixes
\[
 \begin{split}
 z_B&=(-a,b),& B&=[-a,1-a]\times[b-1,b],\\
 z_C&=(c,e),& C&=[c-1,c]\times[e-1,e],
 \end{split}
\]
\[
 a,b,c,e>\frac12,\qquad
 a^2+b^2=c^2+e^2=R^2,
\]
\[
 T_B=(1-a,H),\quad T_C=(c-1,H),\qquad a+c=3.
\tag{2}
\]

These are the same first endpoint identities as Section 1 of
[SIX_CYCLE_DOUBLE_SHARED_CHANNEL_EXCLUSION.md](SIX_CYCLE_DOUBLE_SHARED_CHANNEL_EXCLUSION.md).
They use only the two unique endpoints and their actual genuine
interfaces, not the third body's circle mask.

Because each unique turn is strict, its other port must be the
opposite-to-circle vertex:
\[
                       Q_B=(1-a,b-1),\qquad Q_C=(c-1,e-1).
\tag{3}
\]
Its S-incident interface is not shared, since the local strict-turn
cover permits at most one genuine share per unique load. Thus its
actual normal is a strict loaded-vertex normal. The original shared
means in (2), including their side endpoints, remain unchanged.

In the inward own axes \((-1,0),(0,1)\) at B, write the actual
unit normal from S toward B as
\[
                           G_B=(g_x,g_y),\qquad
                  g_x,g_y>0,\quad g_x^2+g_y^2=1.
\tag{4}
\]
The proper concurrence is \(q_B=\tau_B z_B\), \(0<\tau_B\le1\);
its actual normal is proportional to
\[
 (1-(1-\tau_B)a,\ 1-(1-\tau_B)b).
\]
The unchanged common moment has the sign of
\(\det(q_B,(1,0))=-H<0\) in global coordinates. Its value on
the incoming S channel is proportional to
\(-\tau_B(a-b)\). Hence
\[
                                 a>b.
\tag{5}
\]
The reflected endpoint gives \(c>e\) in exactly the same way.

No statement about S's concurrence is needed. Its two original
applications are its distinct strict inner vertices, have unit
distance, and both have norm squared
\[
                            r_0^2=d^2+\frac14=R^2-2d-1.
\tag{6}
\]

## 2. The two far-circle heights have a uniform lower sum

From (5) and the two radius equations,
\[
       a,c>\frac R{\sqrt2},\qquad
       a,c<3-\frac R{\sqrt2}.
\tag{7}
\]
The interval is nonempty because these are original physical
coordinates. Its endpoints are less than R on the window (1).

The function \(f(x)=\sqrt{R^2-x^2}\) is concave for \(0<x<R\).
Therefore \(f(a)+f(3-a)\), also concave, has its minimum over the
closed interval in (7) at an endpoint. It follows that
\[
 b+e\ge
       \frac R{\sqrt2}
        +\sqrt{R^2-\left(3-\frac R{\sqrt2}\right)^2}.
\tag{8}
\]

Both terms admit simple exact rational lower bounds. First,
\[
 \frac R{\sqrt2}>\frac{139}{100},\qquad
 \left(\frac{79}{40}\right)^2
                  -2\left(\frac{139}{100}\right)^2
                          =\frac{1457}{40000}>0.
\tag{9}
\]
Thus \(3-R/\sqrt2<161/100\), and
\[
 R^2-\left(3-\frac R{\sqrt2}\right)^2
       >\left(\frac{79}{40}\right)^2
                       -\left(\frac{161}{100}\right)^2
       >\left(\frac87\right)^2.
\tag{10}
\]
The last squared reserve is \(4709/1960000>0\).
In particular each of b,e is greater than \(8/7>1\), by (7).

Equations (8)--(10) give
\[
                         b+e>\frac{139}{100}+\frac87
                                      =\frac{1773}{700}.
\tag{11}
\]
On the other hand \(d<61/60\), as follows from
\[
 \left(\frac{121}{60}\right)^2-\frac{1041}{256}
                            =\frac{31}{57600}>0.
\]
Consequently
\[
 b+e>\frac{1773}{700}>
                      \frac{151}{60}>d+\frac32,
\tag{12}
\]
where \(1773/700-151/60=17/1050>0\).

## 3. The two original radial norm equations give the opposite bound

In B's own inward axes its opposite vertex Q has coordinates
\((a-1,b-1)\), both positive by Section 2. Equation (4) and
\(a>b\) imply
\[
 \begin{split}
 Q_B\cdot G_B
 &=(a-1)g_x+(b-1)g_y\\
 &>(b-1)(g_x+g_y)\ge b-1.
 \end{split}
\tag{13}
\]
The last inequality uses the positive unit-vector coordinates in (4).

The true reserve-one S-incident transmitter fixes the original
radial port as \(P_B=Q_B-G_B\). Thus
\[
 \begin{split}
 |P_B|^2
 &=R^2+3-2a-2b-2Q_B\cdot G_B\\
 &<R^2+5-2a-4b.
 \end{split}
\tag{14}
\]
The reflected endpoint gives
\[
                         |P_C|^2<R^2+5-2c-4e.
\tag{15}
\]

Both left sides equal the unchanged radial value (6). Adding and
using the exact reserve \(a+c=3\) gives
\[
 2R^2-4d-2
     <2R^2+10-2(a+c)-4(b+e)
     =2R^2+4-4(b+e).
\]
Equivalently,
\[
                                  b+e<d+\frac32.
\tag{16}
\]
This contradicts (12), excluding the complete stated family.

## 4. Scope and relation to the earlier doubly shared argument

The earlier unique-loaded doubly shared channel proof uses a separate
upper bound on the third turn in its short-side-chord argument. The
present proof does not import that upper bound for a physical radial S.
It uses the two exact radial inner-vertex norms instead, so it applies
throughout the full original radial weight interval and every actual
shared mean at B,C.

Only the genuine two-end owner type of the B-to-C transmitter is
excluded here. Its one-owner case, the nonshared mixed opposite/adjacent
types, and cases with one unique turn at most \(\pi/2\) retain their
separate obligations. This source does not declare the unrestricted
one-radial parent closed. No physical unit, force, corner weight,
mask, original mean, or slider is deleted or changed.
