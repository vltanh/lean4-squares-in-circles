# A low side outsider forces the floor of an upper central unit on its side

November 2, 2026. Complete hand proof. The scalar direction was checked
computationally first; the exact inequalities below cover all orientations.
No Lean or CI.

Retain an actual horizontal four-chain whose consecutive centers also
form a horizontal cone chain, in the closed disk of squared radius
\(Q=1105/256\). Set

\[
 l=29/60,\quad u=13/12,\quad \zeta=2211/4000,
 \quad J=23/150,\quad A_0=18911/59520,
 \quad c_0=A_0-1/10=12959/59520.
\]

## 1. Statement

Let S be an original right-side outsider satisfying

\[
 l\le x_S<u,\qquad y_{M_2}<y_S<3/5.
\]

Let F be a distinct original central outsider satisfying

\[
 0\le x_F\le l,\qquad y_F>y_{M_2}.
\]

Then

\[
                         \boxed{y_F-h_F>1/10.}
 \tag{1}
\]

Horizontal reflection gives the left-sided statement. Vertical reflection
gives the corresponding whole-top statement below a main. S's side need
not be full; no third square on that side is assumed. In particular, the
lemma applies to a sole low side outsider as well as to the zero unit of
a full side.

The original four main cone edges and the endpoint budget give
\(y_{M_2}>-139/120\). The same-side main clearances therefore give

\[
                 y_S>-113/600,
                 \qquad y_F>-7/40.
 \tag{2}
\]

The first uses the unrestricted \(97/100\) half-plane clearance; the
second uses the stronger \(59/60\) central clearance. Both are genuine
physical nonoverlap consequences.

## 2. Side height below seven sixteenths

Suppose \(y_S<7/16\). Equation (2) gives \(|y_S|<7/16\). The
orientation-sensitive endpoint argument in
`ZERO_SIDE_PROXY_EDGE_AND_TOP_HAND_PROOF.md` Sections 1--3 gives

\[
 x_S<\zeta,\qquad x_S-g_S<J.
 \tag{3}
\]

The near-main clearance calculation in that manuscript's Section 4 uses
only S above its main, its center band (3), and the main cone lower bound.
It therefore applies here without a full side and gives

\[
                         y_S+g_S>A_0.
 \tag{4}
\]

Because \(0\le x_F\le l\le x_S<\zeta\), the original two unit
disks have horizontal center gap below \(\zeta\). The comparison
\(\zeta^2<11/36\) gives vertical center gap greater than \(5/6\).
If F were below S, (2) would contradict
\(y_F<7/16-5/6=-19/48\). Thus F is above S, and in fact
\(y_F>129/200\).

Suppose, contrary to (1), that \(T=y_F-h_F\le1/10\). Write
\(a\ge b\ge0\), \(a^2+b^2=1\),
\(h=(a+b)/2\), \(k=(a-b)/2\) for the one original F frame.
Let \(D=x_S-x_F\ge0\), \(V=y_F-y_S>0\), and \(g=g_S\).
Equations (3)--(4) give

\[
                   D-g<J<1/2,
                 \qquad V-g<h-c_0.
 \tag{5}
\]

Neither coordinate axis separates F from S's aligned inset. Every
separating side axis must consequently be owned by F, where its support
is exactly one half. Its vertical component must be positive: otherwise
the separating inequality would require
\(|n_x|(D-g)\ge1/2+g|n_y|\), contrary to (5).

It must point left from the right-hand inset toward F. An upward axis
pointing right has adjusted center projection below \(bh\le1/2\)
when its vertical component is b. When its vertical component is a, that
projection is below

\[
 1/2+b(k-D-g)-ac_0<1/2,
\]

because \(g>1/3\), \(k\le1/2\), and
\((b/a)(k-D-g)<1/6<c_0\). This excludes both inward component orders
and both chiralities.

The aligned case has no remaining side axis and is impossible. Otherwise
put \(t=b/a\in(0,1]\). The two possible outward upward axes give
respectively

\[
 D-g>k+tc_0,
 \qquad D-g>-k+c_0/t.
 \tag{6}
\]

The first contradicts (5): since
\(k\ge(1-t)/(2\sqrt2)>(1-t)/3\) for \(t<1\) and \(c_0<1/3\),
we have \(k+tc_0\ge c_0>J\), including t=1.

For the second, use \(k\le(1-t)/2\) and complete one square:

\[
 t(k+J)\le (J+1/2)t-t^2/2
       \le (J+1/2)^2/2=2401/11250<c_0.
 \tag{7}
\]

But (5)--(6) would require \(t(k+J)>c_0\). This contradiction proves
(1) throughout the low-height case. Every separating axis has been included.

## 3. Side heights from seven sixteenths to three fifths

Now suppose \(7/16\le y_S<3/5\). The endpoint inset and S's
radius-one-half disk give

\[
 x_S<503/480-\sqrt{1/4-(3/5-221/600)^2}<49/80.
 \tag{8}
\]

The positive-root comparison in (8) has squared reserve
\(38839/5760000\). It covers the entire stated height band.

If F were below S, (2) and (8) would give squared center distance

\[
 |c_F-c_S|^2<(49/80)^2+(31/40)^2=1249/1280<1,
\]

contrary to their original disjoint unit disks. Hence F is above S.
Since their horizontal gap is below \(49/80\), their vertical center
gap is greater than \(3/4\); the squared reserve is \(399/6400\).
Using \(h_F\le1/\sqrt2<17/24\),

\[
 y_F-h_F>7/16+3/4-17/24=23/48>1/10.
\]

This completes the second height range and the theorem. No floor, frame,
contact, or separating-axis owner was imposed on either original square.

## 4. Exact arithmetic record

The companion `verify_full_side_occupancy_arithmetic.py` includes the new
scalar and distance reserves. The one-variable inequalities (6)--(7),
all sign exclusions, and the height split above give the complete physical
coverage. This is an extraction lemma, not by itself a whole-mask closure.

## 5. The low unit may itself be central, as far inward as two fifths

The theorem remains true when S's horizontal lower bound is weakened from
\(l\) to \(2/5\):

\[
 2/5\le x_S<u,\qquad y_{M_2}<y_S<3/5,
 \qquad 0\le x_F\le l,\qquad y_F>y_{M_2}.
 \tag{9}
\]

Thus S may be a distinct original central outsider in
\([2/5,29/60]\). No side-column marker assertion is used in this extension.

The endpoint proofs of \(x_S<\zeta\) and \(x_S-g_S<J\) use no
lower side-band bound: they require only S left of the endpoint and
\(|y_S|<7/16\), both still valid. In that low-height case the horizontal
gap from S to M2 is now less than \(7/60\). Its inset margin exceeds

\[
 15/31-7/60=683/1860.
\]

The physical near-main argument, with \(t=b_S/a_S\), gives

\[
 y_S-y_{M_2}\ge g_{M_2}+h_S-
       \max\{0,t(k_S-683/1860)\}.
\]

Using \(k_S\le(1-t)/2\), the loss is bounded by

\[
 \frac12(1/2-683/1860)^2
    =\frac12(247/1860)^2<9/1000,
\]

whose exact reserve is \(6319/34596000\). Consequently (4) is replaced by

\[
 y_S+g_S>A'_0:=1-139/120+15/31-9/1000=14719/46500.
\]

All one-proxy exclusions in Section 2 remain valid with
\(c'_0=A'_0-1/10=10069/46500\). In particular,

\[
 1/6<c'_0<1/3,\qquad c'_0>J,\qquad
 c'_0-2401/11250=2173/697500>0.
\]

Finally \(2/5>l/2\), so for every \(x_F\in[0,l]\) and every
admitted S,

\[
 |x_F-x_S|\le x_S.
\]

Therefore the disk order arguments and the proxy bound \(D-g_S<J\)
are unchanged even when F is to the right of S. In the side-axis proof,
choose the horizontal sign directed from S's inset toward F; the inward
and outward absolute-component calculations are identical. If their center
x-coordinates coincide, either horizontal sign is covered by the same
inequalities and yields the contradiction.

The higher-height argument in Section 3 also uses only
\(|x_F-x_S|\le x_S<49/80\), so it is unchanged. This proves (1)
under the broader original predicates (9), including both central-boundary
values and every physical orientation.
