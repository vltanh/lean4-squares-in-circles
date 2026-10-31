# Every enclosed unit lies inside the convex C7 center polygon

**Status:** complete elementary geometric reduction; independent full hand
audit passed. This does not prove
the separate diameter extraction needed for C7 completion.

## 1. The physical C7 center polygon is strictly convex

Let the seven physical circle-touching unit squares satisfy the established
radius window and circular order. Their center radii satisfy

\[
5/4<r_i<91/60,
\]

and any two center directions differ by more than forty degrees. For the
radial unit vector \(u_i\) of center \(c_i\), every other center obeys

\[
u_i\cdot c_j<(91/60)\cos40^\circ<(91/60)(4/5)
=91/75<5/4<r_i.
\]

Thus each center is strictly exposed by its radial direction. The seven
consecutive angular gaps are greater than forty degrees, so each is less
than \(360^\circ-6\cdot40^\circ=120^\circ<180^\circ\). Consequently
the origin is inside the convex hull, and the circular order is its
convex-hull order. The center polygon is therefore strictly convex.
Every edge has length at most \(\sqrt2\), since adjacent actual units touch
and each center is at distance at most \(1/\sqrt2\) from their contact.

For the elementary cosine comparison, if \(\alpha=\arccos(4/5)\), then
\(\cos3\alpha=-44/125>-1/2=\cos120^\circ\), with both angles in
\((0,\pi)\). Hence \(\alpha<40^\circ\).

## 2. A short clear-endpoint chord cannot cross a unit square

Let \(T\) be a unit square. If both endpoints of a segment are at distance
at least \(1/2\) from \(T\), and its length is at most \(\sqrt2\), then
the segment avoids \(\operatorname{int}T\).

Equivalently, every line meeting \(\operatorname{int}T\) cuts
\(K=T+B_{1/2}\) in a chord of length strictly greater than \(\sqrt2\).
Set \(T=[-1/2,1/2]^2\), and by symmetry give the line the direction
\((c,s)=(\cos\theta,\sin\theta)\), \(0\le\theta\le\pi/4\).
The chord-length function of a convex body, as a function of parallel
offset, is concave: interpolate the two interval endpoints on two parallel
lines and apply convexity. For this centrally symmetric body the function
is also even. It therefore suffices to examine a supporting line of
\(T\), through \(p=(-1/2,1/2)\).

On the line \(p+t(c,s)\), the negative exit parameter has magnitude
\(1/(2c)\). If \(s\ge c/2\), the positive exit parameter is \(1/(2s)\).
The total chord length is then

\[
\tfrac12(c^{-1}+s^{-1})\ge\sqrt2,
\]

with equality only at \(c=s=1/\sqrt2\). If \(s<c/2\), the positive
exit is on the radius-half circle about \((1/2,1/2)\), at

\[
t=c+\sqrt{c^2-3/4}.
\]

Here \(c>2/\sqrt5\), and the full chord length is strictly greater than

\[
c+\frac1{2c}\ge\frac{13}{4\sqrt5}>\sqrt2;
\qquad \frac{169}{80}>2.
\]

The central chord is strictly longer than \(\sqrt2\): the central chord
of the square alone has length \(1/c\), and the half-radius disk extends
it by at least one in total. Concavity between the central and supporting
line therefore gives a strict bound on every line meeting the open square.
This proves the claim, including all tangent and edge-length limits.

## 3. Every enclosed unit lies in the center polygon

Let \(T\) be an extra unit enclosed by the physical ring. Every outer
center \(c_i\) is at distance at least \(1/2\) from \(T\), because the
open radius-half disk about \(c_i\) is inside its actual square. Section 2
therefore shows that every center edge avoids \(\operatorname{int}T\).

Choose a contact \(p_i\) between adjacent ring squares. The contact-spoke
curve \(c_i p_i c_{i+1}\) avoids \(\operatorname{int}T\), as do its
replacement center edges. All three sides of the replacement triangle
avoid the connected set \(\operatorname{int}T\). That set is therefore
wholly inside or wholly outside the triangle. The former is impossible:

\[
\operatorname{area}\triangle(c_i,p_i,c_{i+1})
\le\tfrac12(1/\sqrt2)^2=1/4<\operatorname{area}T.
\]

Replacing each pair of spokes by its center edge consequently preserves
the winding about every point of \(\operatorname{int}T\). The enclosing
spoke curve has winding one; hence every interior point of \(T\) is in
the interior of the convex center polygon. Taking closures gives
\(T\subseteq\operatorname{conv}\{c_i\}\).

The enclosure premise follows for C7 completion squares from
`C7_COMPLETION_LOCALIZATION.md`. The argument in this section itself
needs no positive stress.

