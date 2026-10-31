# Every low adjacent port is incompatible with a strict return owner

Date: October 26, 2026.

**Status: accepted complete analytic whole-family exclusion**, after
full-source and original-row reviews in
REVIEW_C6_RADIAL_LOW_ADJACENT_RETURN_OWNER_ROOT_2026_10_26.md and
REVIEW_C6_RADIAL_LOW_ADJACENT_RETURN_OWNER_C6_2026_10_26.md. The proof treats every original low-turn owner row with an actual
adjacent S-incident application simultaneously. No mean or normal is
replaced. No coefficient packet, parameter grid or sampled pose is used.

Retain the original alternating all-side C6, its physically radial loaded
square S with both individual circle weights positive, the physically
unique loaded squares L and T, all three true reserve-one side transmitters,
all original positive forces, means and endpoints, all transmitter sliders,
and all nine physical units. The zero-individual-radial-weight endpoints
retain their separate accepted exclusion.

Assume that L has turn at most \(\pi/2\), its actual S-incident
application is adjacent to its own circle corner, and the other unique
load T has strict turn and genuinely owns the original return channel.
The actual S-incident application at T is therefore its opposite vertex,
as in the accepted strict A/M/O/T feature cover.

**Theorem.** This entire physical family has no nine-square completion
in the original radius window.

The accepted global geometric theorem gives \(R>2\) for an actual
nine-square completion. It therefore suffices to prove the core
contradiction throughout
\[
 2\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\frac14}-1,\qquad r_0^2=d^2+\frac14.
\tag{1}
\]
No extra unit is removed to obtain this lower radius bound.

## 1. The true radial angles and the actual T-owned chart

The accepted low-turn cover
SIX_CYCLE_ONE_RADIAL_LOW_TURN_FEATURE_COVER.md gives
\[
 \theta_L\le\pi/2,\qquad \pi/2<\theta_T\le3\pi/4,\qquad
 \theta_S=\pi-\alpha-\beta,\qquad \alpha,\beta>0.
\tag{2}
\]
The angles \(\alpha,\beta\) are those of the two actual radial inner
vertex channels, at L and T respectively. Proper force-polygon turns
sum to \(2\pi\), so \(\alpha+\beta\le\pi/4\).
Since L's actual application is an adjacent vertex, the same source's
whole high-radius near-corner theorem gives
\[
               \alpha>\frac12,\qquad
               0<\beta<\pi/4-1/2<\frac27.
\tag{3}
\]
This invokes the actual distance-one application only. An original
mean that happens to equal this vertex retains its original owner label.

At T use the unchanged inward own axes of
SIX_CYCLE_ONE_RADIAL_SINGLE_SHARED_OPPOSITE_RETURN_EXCLUSION.md,
Section 1. Its actual circle corner, return mean, and S-incident
opposite vertex have coordinates
\[
 z=(a,b),\qquad p_{\rm ret}=(a-1,H),\qquad
 Q=(a-1,b-1),
\tag{4}
\]
where
\[
 a>b>\frac12,\quad a^2+b^2=R^2,\quad
 0<H\le b,\quad t=1-H/b\in[0,1).
\]
The actual proper concurrence gives
\[
 X=1-ta>0,\qquad Y=1-tb>0,\qquad
 G=(x,y)=\frac{(X,Y)}{\sqrt{X^2+Y^2}}.
\tag{5}
\]
Here G is the original unit direction from S through its transmitter
toward T. Since \(a>b\) and \(t\ge0\), \(Y\ge X\). Thus, for the
actual angle \(\eta\),
\[
 x=\cos\eta,\quad y=\sin\eta,\qquad
                       \pi/4\le\eta<\pi/2.
\tag{6}
\]
The endpoint \(t=0\), equivalently \(H=b\), is retained; it gives
\(x=y\). Every genuine return mean is still the original mean in (4).

Because T owns its return side, the actual outward return direction
in these same axes is \((-1,0)\). Its scalar product with G is
\(-x\). Consequently the original force turn at T is exactly
\[
                              \theta_T=\pi-\eta.
\tag{7}
\]
If the cycle is indexed in the reverse order, both directed normals
reverse and exchange roles; the same scalar product and the same
turn remain. No actual normal is changed by this coordinate statement.

Combining the complete turn sum with (2),(7) gives the stronger identity
\[
                         \theta_L=\alpha+\beta+\eta.
\tag{8}
\]
This uses the actual T-owned axis and is the additional information
not supplied by the angle-sum inequality alone.

## 2. One uniform angular bound for all low owner rows

Put
\[
                         m=x+y,\qquad n=y-x.
\tag{9}
\]
Equation (6) gives \(m\le\sqrt2\) and \(n\ge0\).
Equations (3),(8) imply
\[
                         \eta<\pi/2-1/2.
\]
Since \(\sin\eta-\cos\eta\) increases on \([\pi/4,\pi/2]\),
\[
 \begin{split}
 n&<\cos(1/2)-\sin(1/2)\\
  &\le
 \left(1-\frac{(1/2)^2}{2}+\frac{(1/2)^4}{24}\right)
       -\left(\frac12-\frac{(1/2)^3}{6}\right)\\
  &=\frac{51}{128}<\frac25.
 \end{split}
\tag{10}
\]
The last reserve is \(2/5-51/128=1/640>0\).
These are signed Taylor bounds at one fixed rational angle, valid
on the displayed nonnegative range. No low-row own angle or actual
return mean has been set to an endpoint.

## 3. Exact circle identity at the opposite T port

The true reserve-one channel gives the actual radial port
\[
                         P=Q-G,\qquad |P|^2=r_0^2.
\tag{11}
\]
In its complete radial-port frame, possibly reflected as a whole,
\[
           P=(d,1/2),\qquad
           G=(-\cos\beta,\sin\beta).
\]
Define the invariant quantities
\[
 w=1-d\cos\beta+\frac12\sin\beta,\qquad
 h=d\sin\beta+\frac12\cos\beta>0.
\tag{12}
\]
Then \(P\cdot G=w-1\) and \(|\det(P,G)|=h\).

The determinant in T's own frame is positive, with its sign fixed
by the original concurrence:
\[
 \begin{split}
 \det(P,G)
   &=ay-bx-(y-x)\\
   &=\frac{(1-t)(a-b)}{\sqrt{X^2+Y^2}}>0.
 \end{split}
\tag{13}
\]
Thus in that frame it equals h, rather than its negative.
Decomposing \(Q=P+G\) along G and its clockwise perpendicular gives
\[
                 a=1+wx+hy,\qquad
                 b=1+wy-hx.
\tag{14}
\]
In particular all signs in (14) are fixed by actual geometry.

Squaring and summing (14),
\[
 R^2=2+2wm+2hn+w^2+h^2.
\]
Also
\[
 w^2+h^2=|P+G|^2=r_0^2+2w-1,\qquad
 R^2-r_0^2=2d+1.
\]
Therefore
\[
                         \boxed{d=w(m+1)+hn.}
\tag{15}
\]
This is the original opposite-port circle equation. It uses no O-type
nonshared return premise; hence it applies to the whole genuine T
mean interval. It does not require \(w>0\).

## 4. Whole-angle scalar contradiction

The radius window (1) gives
\[
                         \frac{187}{200}<d<\frac{61}{60}.
\tag{16}
\]
For the lower comparison the positive-square reserve is
\(15/4-(387/200)^2=231/40000\). For the upper comparison it is
\((121/60)^2-1041/256=31/57600\).

Since \(0<\beta<2/7\), the elementary bounds
\(\sin\beta\le\beta\) and
\(\cos\beta\ge1-\beta^2/2\) give
\[
 w<
 1-\frac{187}{200}\frac{47}{49}+\frac17
                  =\frac{2411}{9800}=:w_*.
\tag{17}
\]
For h the signed cosine upper bound gives
\[
 h<
 \frac{61}{60}\beta+
      \frac12\left(1-\frac{\beta^2}{2}+\frac{\beta^4}{24}\right).
\]
This polynomial increases on \([0,2/7]\): its derivative exceeds
\(61/60-1/7>0\). Thus
\[
 h<\frac{27739}{36015}<\frac{39}{50}=:h_*,
\tag{18}
\]
with exact final reserve \(3527/360150\).

Finally \(m+1\le1+\sqrt2<17/7\), because \(\sqrt2<10/7\).
Using \(w_* >0\), \(h>0\), \(n\ge0\), and (10), equation (15)
implies
\[
 \begin{split}
 d
 &=w(m+1)+hn\\
 &<\frac{2411}{9800}\frac{17}{7}
                  +\frac{39}{50}\frac25\\
 &=\frac{311951}{343000}
  =\frac{187}{200}-\frac{4377}{171500}
  <\frac{187}{200}<d.
 \end{split}
\tag{19}
\]
The replacement of w by its positive upper bound is valid even if
the actual w is negative. This is a single whole-domain contradiction,
with no force-ratio, owner or mean subdivision.

## 5. Stronger corollary for any actual low port with angle \(>1/2\)

The contradiction in Sections 1--4 uses the actual adjacent premise
only to establish \(\alpha>1/2\) in (3). Consequently it proves the
following stronger conditional statement without any further argument:

**Actual-angle corollary.** For any original low-turn unique endpoint L,
if its unchanged S-incident channel angle satisfies \(\alpha>1/2\),
then its strict unique partner cannot be a genuine return owner T.

The actual application at L may be a vertex or an original genuine
mean, including an endpoint. Its original owner label is retained.
The low-turn cover still gives \(\alpha+\beta\le\pi/4\), hence
\(\beta<2/7\); equations (5)--(19) concern only the strict T
endpoint and the original force turns. No distance-one assertion
is made for that more general application.

Together with SIX_CYCLE_RADIAL_STRICT_PARTNER_SMALL_ANGLE_EXCLUSION.md,
which rules out the other strict partner types A, M and O for
\(\beta\le2/7\), this proves that no original low-turn family with
an independently established actual \(\alpha>1/2\) can have a
nine-square completion. Any future use of this corollary must prove
that angle premise for the original mean, rather than moving it to
an adjacent vertex.

## 6. Complete original-row join and limits

The theorem applies whenever the low unique load's actual S-incident
application is adjacent to its circle corner. In the accepted complete
low-turn table, this includes:

- Both S placements in the two-adjacent, non-owner row.
- The actual adjacent S placement in either same-inner-side,
  non-owner row.
- The actual adjacent S placement in either one-owner row.
- Any original shared-mean endpoint that itself has the actual
  adjacent position, without changing the mean's owner label.

It requires none of the row-specific concurrence quadratics or force
ratios. All these rows enter the same argument through their actual
near-corner inequality (3), their original low turn, and the unchanged
strict T partner.

SIX_CYCLE_RADIAL_STRICT_PARTNER_SMALL_ANGLE_EXCLUSION.md already
excludes the strict partner types A, M and O when \(\beta\le2/7\).
Together with that complete local theorem, the present result removes
every strict partner for every actual adjacent low port. This is a
whole original geometric subfamily, not a representative corner case.

Low S-incident opposite vertices, actual interior means that do not
satisfy the near-corner premise, and their original owner placements
remain separate. The physical radial weight endpoints retain their
own accepted proof. No unrestricted one-radial parent gate is claimed
closed by this source alone. No computational certificate, numerical
root, Lean compilation or CI was used.

