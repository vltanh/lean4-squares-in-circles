# Independent review of the both-adjacent radial C6 classification

Date: October 26, 2026.

**Verdict: PASS.** The complete hand proof in
SIX_CYCLE_ONE_RADIAL_BOTH_ADJACENT_PORTS_CLASSIFICATION.md
classifies the stated whole geometric subfamily as the already
classified radial right-turn family. Its strictly obtuse part is
impossible as a six-body core; the accepted full three-slider
completion theorem excludes the remaining equality family.

This review independently checks the physical feature reduction,
the actual one-endpoint coordinates, connected interpolation,
the exact derivative identity and its complete sign argument,
and the equality/classification/completion join. Both original
radial circle weights, including zero endpoints, every original
application mean, genuine shared-side endpoints, all transmitter
sliders and all nine squares remain. No numerical sample,
finite coefficient packet, Lean compilation or CI is used.

## 1. The feature premise is preserved exactly

The added geometric premise is that each actual S-incident port
on a unique loaded unit is a vertex adjacent to its actual unique
circle corner. It is not inferred for an arbitrary mean.
The accepted near-corner angle theorem applies to these actual
distance-one ports, giving the stated strict turns at the two
unique loads in the radial strictly obtuse branch.

I checked the local same-side feature consequence carefully.
If the specified adjacent vertex is incoming, the actual corner
bit is zero. The only permitted share at that body is incoming,
with original mean coordinates \((1-\ell,1)\); adjacency at
the first endpoint forces \(\ell=1\). The other port is
therefore the opposite vertex. The outgoing-adjacent bit-one
case is its exact reflected version. A side-interior opposite
port would require the wrong share direction for the actual bit.

Thus the two actual chords at the unique loads are one. Any
genuine share is S-incident and retains its already specified
adjacent-vertex mean. Its chord-one torque equation gives the
allowed \(3\pi/4\) turn endpoint; it is not relabeled as a
singleton. The B-to-C channel is nonshared at both ends and
uses the actual opposite vertices.

The radial support cover and local distinct-port torque argument
give the two different strict inner vertices at S. Their original
distance is one, and both have squared norm \(d^2+1/4\),
independently of the two original corner weights. No radial
concurrence-containment premise is needed.

## 2. Actual one-endpoint geometry and all its signs

In the original B-to-C channel frame, the opposite ports have
positions \((l,H),(l+1,H)\), with \(H>0\). The two sides into
the left loaded square are
\[
 (-c,s),\quad(-s,-c),\qquad c,s>0,\quad c^2+s^2=1.
\]
Proper unique concurrence on the channel line gives \(s-c\ge0\),
so \(\eta\in[\pi/4,\pi/2)\).
The third concurrence lies strictly below this channel line.
The S-incident port must therefore be the lower adjacent
vertex; its proper distance cannot vanish because an adjacent
vertex is not on the positive radial ray through the actual
far corner.

With \(D=s-c\), \(C=s+c\), \(Z=H+D\) and
\(A=\sqrt{R^2-Z^2}>0\), the actual points and concurrence are
\[
 z=(-A,Z),\quad T=(-A+C,H),\quad Q=(-A+c,H-c),
\]
\[
 t=D/Z,\quad q=(1-t)z,\quad
 V=q-Q=(tA-c,c),\quad L=|V|,\quad G=V/L,\quad P=Q-G.
\]
The sign in \(P=Q-G\) agrees with the unchanged reserve-one
channel from the radial unit into B. The same formulas for C
are reflected in the vertical axis, with the same actual \(R,H\).

The horizontal reserve gives
\((A_B-C_B)+(A_C-C_C)=1\). Since each \(A_i<R\) and
\(C_i\ge1\), it implies
\(A_i-C_i>2-R>-5/64\). The strict comparison
\(R<133/64\) has the displayed reserve \(9/4096\).

The own-axis coordinates
\[
 a=cA+sZ,\qquad b=sA-cZ
\]
are both strictly greater than \(1/2\) at the actual unique
loads. Properness gives \(\lambda=C-tA\ge0\).
Equality would put the concurrence at the opposite vertex and
force the two outward normals to have angle at least \(3\pi/4\),
making the turn at most \(\pi/4\). This contradicts the already
established strict obtuse turn, so \(\lambda>0\).

I directly verified
\[
 a-b=Z\lambda>0,\qquad x=1-ta=c\lambda>0,\qquad
 L^2=x^2+t^2b^2.
\]
All later divisions by \(A,Z,L\) and all signs involving
\(a,b,x\) therefore have their asserted justification.

## 3. The entire interpolation interval is valid

The source does not assume interpolated packings. It fixes the
actual \(R,H\) and interpolates only its explicitly defined
one-variable scalar function.

Because \(D=s-c\) increases with \(\eta\), the condition
\(Z<R\) persists between the two actual endpoint angles.
Squaring the positive quantities in \(CZ>DA\) gives exactly
\[
                    H>D(R/\sqrt2-1).
\]
The coefficient \(R/\sqrt2-1\) is positive, so this properness
condition persists from the larger-angle endpoint to the entire
interval.

On this domain,
\[
 (A-C)'=D-ZC/A<0,\qquad
 a'=-b(1-C/A),\qquad b'=a(1-C/A).
\]
I rederived both identities from the actual definitions. Since
\(A-C\) is decreasing and \(a>0\), the function \(b\) first
increases and then decreases, with either part possibly empty.
Its minimum is therefore at an actual endpoint. Thus \(b>1/2\)
persists everywhere. The identity \(a-b=Z\lambda\) preserves
\(a>b\), and monotonicity also preserves the endpoint lower
bound \(A-C>-5/64\).

This establishes all of the domain needed for the derivative
argument over the full interval, including any point at which
\(A=C\). No physical motion or altered mean is used.

## 4. The actual radial-port norm supplies the cosine lower bound

For each actual endpoint, suppose \(c\le1/4\). I checked the
full chain
\[
 D>7/10,\quad A>59/64,\quad Z<15/8,\quad
 m=tA>413/1200>1/3.
\]
It implies \(G_x>1/\sqrt{10}>3/10\), while
\(A-c>279/320\), giving \(-P_x>75/64\).
This contradicts
\[
 |P|^2=d^2+1/4<4621/3600<(23/20)^2,
 \qquad23/20<75/64.
\]
Both reserves \(7/180\) and \(7/320\) agree exactly.
Thus each actual endpoint has \(c>1/4\). Since cosine is
monotone on the angle interval, the whole interpolation also
has the required lower bound.

## 5. Independent derivation of the exact derivative

In the actual own frame, \(z=av+bu\), \(Q=z-v\), and
\(V=v-tz\). Hence
\[
 L^2=1-2ta+t^2R^2,\qquad
 J=Q\cdot V=(1+t)a-tR^2-1,
\]
\[
                  F=|P|^2=R^2+2-2a-2J/L.
\]
Differentiate these identities at fixed \(R,H\), treating
\(a,t\) as functions of \(\eta\). Clearing the positive
\(L^3\) gives
\[
 \frac{L^3}{2}F'
 =-a'[L^3+(1+t)L^2+tJ]
   +t'[(R^2-a)L^2+J(-a+tR^2)].
\]
Fresh expansion reduces the two brackets to
\[
 L^3+1-t(1+t)a+t^3R^2
       =L^3+tL^2+(1-t)(1-ta),
\]
\[
 (R^2-a)L^2+J(-a+tR^2)=(1-t)(R^2-a^2)=(1-t)b^2.
\]
Substituting \(a'=-b(1-C/A)\) and
\(t'=HC/Z^2>0\) gives exactly the displayed derivative
identity in the source. Its coefficient
\(\mathcal C=L^3+tL^2+(1-t)x\) is strictly positive.

This confirms the derivative algebra independently, including
the sign of its potentially negative first term.

## 6. Complete derivative sign, including \(A<C\)

For \(A\ge C\), the second term in the derivative bracket is
strictly positive, while the first is nonnegative.

For \(A<C\), the source first proves \(c<1/2\) by the
concavity of
\(c\sqrt{R^2-y^2}+sy\) on \(1/2\le y\le R/\sqrt2\).
Both endpoint values are strictly greater than \(C\) if
\(c\ge1/2\), using \(d>9/10>\sqrt3/2\). This contradiction
is valid on the full interpolated domain, where \(a>b>1/2\).

On \(1/4\le c<1/2\), I checked all remaining bounds:

- \(D<23/32\), \(C>6/5\), and
  \(t<7/15\). The exact squared reserve in the last
  comparison is \(18848/4641075>0\).
- \(A>359/320\), hence
  \(Z^2<(7/4)^2-1/400\), giving \(C/Z>24/35\).
- \(C^2<15/8\) and
  \(K_0^2-C^2>3241/1600>2\). These imply
  \(m^2<1/2-(3/2)c^2\).
- \(m>413/2660>1/8\ge c/4\), so
  \(L^2=(m-c)^2+c^2<1/2\).
- Using \(0<x\le L\) and \(0\le t<1\),
  \(\mathcal C<L^3+L<3/(2\sqrt2)<15/14\).
- \(1-C/A>-5/59\), so the negative derivative contribution
  is greater than \(-75/826\).
- \(t'(1-t)b=(1-t)^2(C/Z)b>256/2625\).

Thus the whole bracket is greater than
\[
                 \frac{256}{2625}-\frac{75}{826}
                         =\frac{2083}{309750}>0.
\]
I independently reconstructed all the displayed rational
reserves with Fraction arithmetic. The estimates use no
sampled derivative, parameter partition or unproved monotonicity.
Together with the connected-domain proof, they establish
\(F'>0\) between the two actual endpoints.

## 7. Equal original port norms and the exact equality family

Both actual radial ports have squared norm \(d^2+1/4\).
Thus \(F(\eta_B)=F(\eta_C)\), and strict monotonicity forces
\(\eta_B=\eta_C\). The original reserve equation then gives
\(A=C+1/2\), so the original radial ports are reflections
\((-x,y),(x,y)\), with
\[
                      x=s+1/2+G_x>0.
\]
Their original distance is one, hence \(x=1/2\) and \(G_x=-s\).
Because \(G_y=c/L>0\) and \(G\) is a unit vector, \(G_y=c\)
and \(L=1\). Consequently \(tA=-D\). The already proved
signs \(t,D\ge0\), \(A>0\) force \(t=D=0\), so
\(\eta=\pi/4\).

The two unique concurrences are now their actual circle corners.
Their adjacent/opposite actual ports give turns \(3\pi/4\);
the original turn sum gives \(\theta_S=\pi/2\). This
contradicts the strictly obtuse branch and proves its complete
core exclusion.

The separate accepted right-turn classification covers the
remaining equality endpoint and gives the actual loaded
geometry with \(R^2=5/2+\sqrt2\), retaining all three
original transmitter sliders. I checked the stated scope
of SIX_CYCLE_ONE_RADIAL_RIGHT_ANGLE_FAMILY_COMPLETION.md:
its theorem applies to the entire physically contained,
interior-disjoint three-slider family, allows genuine endpoint
means and additional zero-weight contacts, and gives total
extra capacity at most two. It therefore supplies exactly the
required nine-square contradiction, without a capacity-one
claim for its remaining pocket or a choice of slider.

## 8. Accepted scope and retained residue

The entire stated both-adjacent physical subfamily has no
nine-square completion, and its strictly obtuse part has no
six-body core. Both radial weights remain arbitrary, as do
all original means, masks and transmitter positions. The
proof never asserts an interior radial concurrence.

Cases with an opposite-vertex S-incident port or a
nonendpoint mean on at least one unique unit are outside
the added premise and remain open. This classification
does not close the whole one-radial gate, the full C6
completion problem, the global sharp inequality or its
equality classification. It adds no computational certificate.
