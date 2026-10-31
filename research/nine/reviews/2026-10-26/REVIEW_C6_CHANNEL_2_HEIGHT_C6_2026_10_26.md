# Independent full-source review of the remaining channel-2 height bound

Date: October 26, 2026.

**Verdict: PASS for the complete original remaining one-share orbit and the strict actual height \(H_2>1/4\).** This review makes no assertion about the free interval length or whole-pocket completion capacity.

Reviewed in full: SIX_CYCLE_REMAINING_CHANNEL_2_HEIGHT.md.

The physical channel-0 chart, its strict local inequalities and occupied-pocket theorem were already independently read and audited in REVIEW_C6_REMAINING_CAP_0_CAPACITY_ONE_C6_2026_10_26.md. The whole-orbit radius theorem was audited in REVIEW_C6_COMMON_POINT_FERMAT_BOUND_C6_2026_10_26.md. The strengthened quarter-turn arc theorem was independently reviewed at its full new \(H>1/4\) threshold in REVIEW_RADIUS_TWO_CAP_ARC_QUARTER_TURN_C6_2026_10_26.md.

## 1. Original height and necessary inequality

The actual incoming application on \(S_0\) is \((1-a,1-b)\), and the actual outward normal of channel 2 is \((-s,c)\). Their scalar product is exactly
\[
 h=H_2=s(a-1)-c(b-1).
\]
This retains the original application and its actual pocket orientation.

The original force equations \(qs=\kappa b\), \(qc=\kappa a-1\) imply
\[
 q(sa-cb)=b,\qquad qh=H_0.
\]
Consequently \(L=h+s-c=sa-cb>0\) and \(H_0=hb/L\) are exact. The original \(s-c>0\) is available because the genuine \(\ell=1\) endpoint was initially retained and then contradicted by actual closure in the accepted orbit cover.

Substituting the original channel-0 circle identity and the strict local normal inequality gives precisely
\[
 F=C^2-2Ca-(1-h^2/L^2)b^2\le0,\qquad C=2+\sqrt2.
\]
The sign includes \(W=0\), where the relevant identity is equality. No extra mean, force or channel equation is imposed.

## 2. Full scalar comparison domain

Under \(0<h\le1/4\), the rotation formulas
\[
 a=sL+c\sqrt{R^2-L^2},\qquad
 b=s\sqrt{R^2-L^2}-cL
\]
have the correct positive branch because \(ca+sb>0\). At fixed original h,c, increasing only the scalar comparison radius to 2 increases both coordinates. The coefficient \(1-h^2/L^2\) belongs to \((0,1)\). Thus the necessary F decreases, in the claimed direction, and the comparison b remains greater than \(1/2\).

If the two comparison coordinates have \(\bar a\le\bar b\), then \(\bar a\le\sqrt2\), and the displayed expression
\[
 (C-\bar a)^2-4+(h\bar b/L)^2
\]
is strictly positive. This is a complete branch, not an omitted angular endpoint.

For \(\bar a>\bar b\), putting \(k=(s-c)/h\) gives the exact angle formula
\[
 \bar a=2\sin\left(\pi/4+
       \arcsin(h(1+k)/2)-\arcsin(kh/\sqrt2)\right).
\]
The original positive two coordinates place its angle in \((0,\pi/2)\). Hence \(\bar a>\bar b\) is equivalent to the strict ordering of the two arcsine arguments, giving \(0<k<1+\sqrt2\).

At fixed k in this interval, increasing h to \(1/4\) increases the difference of arcsines. The whole comparison angle stays in \([\pi/4,5\pi/12)\), so its sine increases. The quadratic expression in its a argument decreases strictly. These facts justify the reduction to the single scalar function on \(0\le k\le1+\sqrt2\). All comparison radicals remain positive on the entire interval. No interpolated physical packing or changed actual mean is claimed.

## 3. Whole-interval concavity and one tangent

I independently differentiated all three displayed derivatives of the arcsine difference. The larger interval \([0,5/2]\) is valid for both radicals. On this whole interval the first term of the third derivative is less than \(1/200\), while the second is greater than \(1/192\), so the third derivative is strictly negative.

Thus the second derivative decreases and has the asserted uniform upper bound below \(1/400\). The first derivative is concave. Its tangent at \(3/5\), whose slope is strictly negative by the stated positive-square comparison, gives the correct upper bound over the whole interval. The exact rational substitutions establish \(\varepsilon'<-1/20\), with all reciprocal radical directions correct.

On the needed interval, the angle \(\vartheta=\pi/4+\varepsilon\) belongs to \([\pi/4,\pi/2)\), so \(\sin\vartheta\ge\cos\vartheta>0\). The comparison
\[
 \varepsilon''<1/400<(\varepsilon')^2
\]
therefore gives strict concavity of \(\mathfrak a\) everywhere on that interval.

I independently rederived the two radical formulas at \(k=1\) by angle addition. The derivative's second parenthesis is negative, and the source uses the correct paired upper/lower bounds for multiplying it by the positive first factor. The global concave tangent and the separate signs of \(k-1\) justify the two displayed uses of the derivative enclosure. Their small affine reserves remain positive through \(k\le1+\sqrt2<5/2\). The resulting strict affine bound for \(\mathfrak a(k)\) is valid on the entire domain.

## 4. Positive quartic and exact arithmetic

The expression being bounded decreases with its a argument throughout \(0<a<2\), and the affine comparison lies in that interval. After substitution, the coefficient of \(\sqrt2\) is \(4-2\mathfrak l(k)>0\), so replacing it by \(140/99\) gives a strict lower bound with the correct direction.

Using fresh Fraction arithmetic, I independently reconstructed all of the following:

- All six integer reserves in the fixed radical table for \(\sqrt{15}\), \(\sqrt{31}\) and \(\sqrt{465}\).
- The rational reserve \(325183/2231607168\) below \(-1/20\) in the global derivative estimate.
- Both exact rational derivative enclosures at \(k=1\), and their two displayed positive margins from \(-33/500\) and \(-329/5000\).
- Every coefficient of the rational quartic obtained from the affine comparison.
- The complete shifted expansion at \(k=5/4\), including its constant \(35/704\), linear coefficient \(-3013/88000\), and all three coefficients in the quadratic bracket.
- The bracket lower bound \(7579469/15840000\) and its positive reserve \(1243469/15840000\) above \(2/5\).

All displayed identities agree exactly.

For \(y=k-5/4\ge-5/4\), the bracket lower bound uses its positive linear coefficient and nonnegative quadratic term correctly. The remaining constant and absolute-value bounds give the valid completed-square estimate
\[
 P(k)>
 \frac25\left(|y|-\frac1{20}\right)^2+\frac{39}{1000}>0.
\]
Thus the quartic is positive on the larger whole domain \(k\ge0\), with no sign grid or coefficient-subdivision premise. This closes every scalar comparison branch and contradicts the original necessary \(F\le0\) under \(h\le1/4\).

## 5. Exact physical consequence

The conclusion \(H_2>1/4\) applies to the actual channel in every original remaining core. The physical channel-cap theorem places each whole pocket-2 extra in its actual cap, and the accepted radius theorem supplies \(R<2\). Both hypotheses of the strengthened quarter-turn theorem are therefore present.

Every such unchanged extra, at every independent orientation and with any original zero circle weight, has one connected open inner-circle arc of length greater than \(\pi/4\), containing its radial-center point. The source does not infer a common free interval from the height alone. Repeated cap occupancy and the parent C6 completion problem are retained for the separately proved routing and capacity arguments.

No physical square, mask, mean endpoint, force or transmitter slider has been removed. No numerical root, parameter sampling, new certificate packet, Lean compilation or CI is used.

