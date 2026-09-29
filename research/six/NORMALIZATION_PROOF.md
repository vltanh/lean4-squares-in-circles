# Global normalization for n = 6: certified computation and hand proof

This manuscript is imported from the user's proposed replacement for §2.3 of
`research/six/HAND_PROOF.md`. Its source was written against `4fd88f2`.
The integration base is `4d9754c79c90df8b103e7b218dc316bec58dc43e`.
See `NORMALIZATION_INTEGRATION.md` for execution provenance and the precise
boundary between the normalization argument and the existing downstream proof.

**Status and proof boundary.**

- Every item (N16)–(N27) is proved below by hand, modulo the 78 scalar
  inequalities (S1)–(S54) and four exact identities (I1)–(I4).
- Each scalar is an explicit constant comparison or a one- or two-variable
  inequality on a compact interval. The supplied `cert_scalars.py` verifies
  these inequalities with interval arithmetic; the identities follow from the
  definitions, not from numerical equality testing.
- Independent direct searches check the one- and two-square statements:
  Lemmas A, B, C, D1–D2, D4, G and (K4). These searches are not substitutes
  for the displayed hand reductions.
- (K2), (K3), (K5) and (N26) use their scalar inequalities. The last step of
  Proposition A uses the five cyclic marker gaps (N7).
- Inputs are the existing central-square and genuine-marker results in
  §§2.1–2.2, `Seven.marker_arc` in (T4), and the existing Appendix A (A1)
  for the final exclusion (N27). This file does not independently reprove A1
  or the downstream A2 classification, and is not a Lean kernel proof.

**Changes to the former normalization dependency order.**

The stronger central box (N23) is proved first, without sectors, pins, or A2.
The pin-covering theorem then labels the five squares, after which their
windows and order are proved. No horizontal reflection is used. A diagonal
reflection is consumed once to arrange \(\phi_D\le5\pi/4\). The opposite-pair
bound (N26) requires both helpers to be cardinal.

## 0. Setting and notation

Six closed unit squares with pairwise disjoint interiors lie in a disk of
radius \(R\) centered at \(O=0\), where
\[
 R^2\le q_*<Q_0=142559/50000.
\]
By the existing §2.1 exactly one square \(C\) contains \(O\) in its interior.
It is axis-parallel, with center \(c=(c_x,c_y)\),
\(0\le c_x,c_y<1/2\). The remaining five squares are exterior. All six lie
in the closed disk \(D_0\) of radius \(R_0=\sqrt{Q_0}\).

Put
\[
 \rho_0=\sqrt{Q_0-\tfrac14}-\tfrac12,
 \qquad c_0=\rho_0-1,
\]
\[
 U(a)=\sqrt{Q_0-(a+\tfrac12)^2}-\tfrac12,
 \qquad A(u)=\sqrt{Q_0-(u+\tfrac12)^2}-\tfrac12,
\]
\[
 U_0=U(2-\rho_0),\qquad
 X_0=U(1)=\sqrt{Q_0-\tfrac94}-\tfrac12,
 \qquad u_{\max}=R_0/\sqrt2-\tfrac12.
\]
Numerically, \(\rho_0=1.1128174\ldots\), \(U_0=0.4627588\ldots\),
\(X_0=0.2753580\ldots\), and \(u_{\max}=0.6939807\ldots\).
Write \(w(\theta)=(|\cos\theta|+|\sin\theta|)/2\).

The four exact identities are:

- (I1) At \(t_1=\arcsin(1/(2R_0))\), the two branches of \(B\) below
  equal \((\rho_0^2-1/2)/R_0\). Indeed
  \(\sin t_1=1/(2R_0)\), \(\cos t_1=(\rho_0+1/2)/R_0\), and
  \(Q_0=\rho_0^2+\rho_0+1/2\).
- (I2) \(9/4+(X_0+1/2)^2=Q_0\).
- (I3) \((5/2-\rho_0)^2+(U_0+1/2)^2=Q_0\).
- (I4) \((\rho_0+1/2)^2+1/4=Q_0\).

An exterior chart \((\phi,a,b)\) has
\(n=(\cos\phi,\sin\phi)\), \(n^\perp=(-\sin\phi,\cos\phi)\), and
\[
 X=\{x:|x\cdot n-a|\le1/2,\ |x\cdot n^\perp-b|\le1/2\}.
\]
Here \(a\ge u:=|b|\), and \(a\ge1/2\) by exteriority. The genuine Seven
marker is
\[
 m=\phi+\operatorname{sgn}(b)\ell(a,u),\qquad
 \ell(a,u)=\min\left(\tfrac54u,s(a,u),\tfrac\pi4\right),
\]
\[
 s(a,u)=\tfrac\pi6+\tfrac{u-1/2}{3}+\tfrac{3(1-a)}4.
\]
All statements allow every admissible chart, including ties \(a=u\).
The primary direction lies in quadrant E, N, W or S when
\(\phi=k\pi/2+\theta\), \(|\theta|\le\pi/4\), for \(k=0,1,2,3\)
respectively.

## 1. Tools

**(T1) Containment.** For a side frame \((e,f)\) and center
\(P=\alpha e+\beta f\),
\[
 X\subset D_0\iff(|\alpha|+1/2)^2+(|\beta|+1/2)^2\le Q_0.
\]
In a chart this gives \(a\le\rho_0\), \(u\le U(a)\), and
\(u\le u_{\max}\).

**(T2) Separating axes.** Put
\(h_C(v)=c\cdot v+(|v_1|+|v_2|)/2\). Interior disjointness from \(C\)
is equivalent to at least one of:

| separator | inequality |
|---|---|
| OWN | \(a-1/2\ge h_C(n)\) |
| SEC+ | \(b-1/2\ge h_C(n^\perp)\) |
| SEC− | \(-b-1/2\ge h_C(-n^\perp)\) |
| CE | \(P_1-w(\phi)\ge c_x+1/2\) |
| CW | \(P_1+w(\phi)\le c_x-1/2\) |
| CN | \(P_2-w(\phi)\ge c_y+1/2\) |
| CS | \(P_2+w(\phi)\le c_y-1/2\) |

The remaining own-axis alternative is impossible because \(a>0\) and
\(h_C(-n)>0\). CE is precisely containment in the east cap
\(D_0\cap\{x_1\ge1/2+c_x\}\); similarly for the other cardinal caps.

**(T3) Pin criterion.** A point of radius \(r\) and angle \(\theta_q\)
is in \(X^\circ\) exactly when, for \(\delta=\theta_q-\phi\),
\[
 |r\cos\delta-a|<1/2,\qquad |r\sin\delta-b|<1/2.
\]
These are the normal and transverse conditions.

**(T4) Marker point.** Applying `Seven.marker_arc` at the signed label gives
\(M=(\cos m,\sin m)\in X\), since the chart is admissible at \(13/4\).
Thus \(M\) belongs to every closed half-plane containing \(X\).
The half-plane form is `Seven.marker_arc_support`; it avoids identifying the
closed square through an open `ChartCondition`.

**(T5) Diagonal symmetry.** Reflection \((x,y)\mapsto(y,x)\) preserves
\(D_0\), \(c\ge0\) and \([0,c_0]^2\), exchanges east/north and
west/south caps, sends \(\phi\) to \(\pi/2-\phi\) and \(m\) to
\(\pi/2-m\), and permutes the fixed pins by
\(q_E\leftrightarrow q_N\), \(q_W\leftrightarrow q_S\), \(q_D\mapsto q_D\).

## 2. The cap lemma

**Lemma K.** Let \(v\) be a unit vector, \(h\ge0\), and let
\(X\subset D_0\cap\{x\cdot v\ge h\}\) be a unit square. Choose its side
direction \(e\) nearest \(v\), with signed angle
\(\theta\in[-\pi/4,\pi/4]\), and write \(P=\alpha e+\beta f\),
where \(f\) is \(e\) rotated by \(+\pi/2\). Then:

(K1) \(\alpha\cos\theta-\beta\sin\theta\ge h+w(\theta)\).

(K2) \(h\le B(|\theta|)\), where
\[
 B(t)=\begin{cases}
 (\rho_0-1/2)\cos t-(1/2)\sin t,&0\le t\le t_1,\\
 R_0-\cos t-\sin t,&t_1\le t\le\pi/4,
 \end{cases}
 \qquad t_1=\arcsin(1/(2R_0)).
\]
This sharp bound is continuous and strictly decreasing; \(B(0)=\rho_0-1/2\).

(K3) If \(h\ge3/2-\rho_0=1/2-c_0\), then
\[
 |\theta|<2/5,\qquad \alpha>|\beta|,\qquad |\beta|<1/2,
 \qquad \alpha\ge h+1/2.
\]
Thus \(e\) is the chart primary direction, \((a,b)=(\alpha,\beta)\), and
\(u\le U(h+1/2)\le U_0\).

(K4) If \(3/2-\rho_0\le h\le\rho_0-1/2\), then
\((h+1/2)v\in X^\circ\).

(K5) For \(0<t\le2/5\),
\(B(t)<\rho_0-1/2-t/2\).

(K6) If \(h\ge1/2\), then \(|\theta|<1/4\).

*Proof.* (K1) is the projected interval of the square along \(v\).
For (K2), put \(\mathcal A=|\alpha|+1/2\) and
\(\mathcal B=|\beta|+1/2\). Then
\[
 h\le(\mathcal A-1)\cos\theta+(\mathcal B-1)|\sin\theta|,
 \qquad \mathcal A^2+\mathcal B^2\le Q_0,\quad\mathcal B\ge1/2.
\]
The linear maximum is the Cauchy–Schwarz point when
\(R_0|\sin\theta|\ge1/2\), and otherwise the corner
\((\rho_0+1/2,1/2)\). This gives \(B\); (I1) gives continuity. Its
branch derivatives are
\(-(\rho_0-1/2)\sin t-(1/2)\cos t\) and \(\sin t-\cos t\),
negative in the interiors of their respective ranges.

For (K3), (S1), (S1a) give \(t_1<2/5\) and
\(B(2/5)<3/2-\rho_0\). If \(\alpha\le0\), (K1) forces
\(|\beta|\ge(2-\rho_0)/\sin(2/5)>2>R_0\), impossible by (T1).
If \(0<\alpha\le|\beta|\), the constrained linear maximum is on
\(\mathcal A=\mathcal B=R_0/\sqrt2\), so
\[
 h\le(R_0/\sqrt2-1)(\cos\theta+|\sin\theta|)
 \le R_0-\sqrt2<3/2-\rho_0 \quad\text{(S2)}.
\]
If \(|\beta|\ge1/2\), then \(1\le\mathcal B<\mathcal A\).
The angle bound puts the maximum at \((\sqrt{Q_0-1},1)\); hence
\(h\le(\sqrt{Q_0-1}-1)\cos\theta<3/2-\rho_0\) by (S3), again
impossible. Finally (K1) implies
\[
 \alpha\cos\theta\ge h+\tfrac12\cos\theta
 +(\tfrac12-|\beta|)|\sin\theta|\ge h+\tfrac12\cos\theta,
\]
so \(\alpha\ge h+1/2\).

For (K4), reflection in \(\mathbb Rv\) fixes the cap and the piercing
point, so take \(\theta\ge0\). Put \(Z=(h+1/2)v\). The four pin
inequalities follow as follows:

1. \(\alpha-1/2\le\rho_0-1/2<(2-\rho_0)\cos(2/5)
   \le(h+1/2)\cos\theta\), by (S4).
2. \((h+1/2)\cos\theta<\alpha+1/2\), by (K3).
3. \(\beta\ge-U_0>-1/2\ge-1/2-(h+1/2)\sin\theta\), by (S6).
4. Suppose \(\beta\ge1/2-(h+1/2)\sin\theta\). Put
   \(V=\beta+1/2\), \(V_0=1-(h+1/2)\sin\theta\).
   By (S5a), \(V_0>1/2\). Thus \(\beta>0\), and (K1) gives
   \(\alpha+1/2\ge h/\cos\theta+1+V\tan\theta\). Therefore
   \[
   Q_0\ge(h/\cos\theta+1+V\tan\theta)^2+V^2
   \ge G(\theta,h):=(h/\cos\theta+1+V_0\tan\theta)^2+V_0^2,
   \]
   contrary to (S5) on the full rectangle
   \([0,2/5]\times[3/2-\rho_0,\rho_0-1/2]\).

For (K5), on \(0<t\le t_1\),
\[
\begin{aligned}
 \rho_0-1/2-t/2-B(t)
 &=(\rho_0-1/2)(1-\cos t)-(t-\sin t)/2\\
 &\ge t^2[(\rho_0-1/2)(1/2-t^2/24)-t/12]>0
 \quad\text{(S8b)}.
\end{aligned}
\]
On \([t_1,2/5]\), use (S8a). For (K6), (S7), (S7a) give
\(1/4<t_1\) and \(B(1/4)<1/2\). This proves Lemma K.

## 3. Proposition A — the central-square bound (N23), hence (N16)

**Proposition A.** \(\max(c_x,c_y)\le c_0\).

Suppose otherwise. By the symmetry (T5), used only to prove this symmetric
conclusion, assume
\[
 c_0<c_x<1/2,\qquad 0\le c_y\le c_x.
\]
Define
\[
 (\alpha^+,\alpha^-)=
 \begin{cases}
 (\pi/2-5X_0/4,\ \pi/2-5U_0/4),&c_y\le c_0\quad(A1),\\
 (\pi/2,\ 27/50),&c_y>c_0\quad(A2).
 \end{cases}
\]
By (S13), (S14), both sums exceed \(2\pi/3\). Lemma A proves that every
exterior marker avoids \((-\alpha^-,\alpha^+)\). The consecutive markers
on either side of direction zero therefore have a cyclic gap exceeding
\(2\pi/3\), contradicting (N7). This proves (N23). By (S10b),
\(c_0<23/200\), so (N16) follows.

**Lemma A.** Under the hypotheses of A1 or A2, no exterior marker lies in
\((-\alpha^-,\alpha^+)\) modulo \(2\pi\).

### 3.1. Preliminary facts

Throughout, \(c_0<c_x<1/2\), \(0\le c_y\le c_x\), and
\(\phi=k\pi/2+\theta\), \(|\theta|\le\pi/4\).

(a) \(0\le\ell\le\min(5u/4,\pi/4)\). The marker lies between
\(\phi\) and \(\phi+\ell\) for \(b>0\), between \(\phi-\ell\)
and \(\phi\) for \(b<0\), and equals \(\phi\) for \(b=0\).

(b) If \(u\ge1/2\), then \(\ell\ge5/8\). Indeed
\(a\le A(u)\le A(1/2)\), and
\[
 s(a,u)\ge\pi/6+\tfrac34(3/2-\sqrt{Q_0-1})>5/8
 \quad\text{(S19a)}.
\]
The axial and capped terms also satisfy this lower bound.

(c) CW implies \(\cos m<0\) by (T4), because \(c_x-1/2<0\).
It therefore excludes the target arc, which lies in \((-\pi/2,\pi/2)\).

(d) In the W quadrant, the marker belongs to \([\pi/2,3\pi/2]\), outside
the target arc.

(e) CE is impossible: its depth \(1/2+c_x\) exceeds
\(\rho_0-1/2=B(0)\).

(f) OWN is impossible in the E quadrant (Lemma A0). For \(\theta\ge0\),
\(c\cdot n+w(\theta)\) is at least
\((1/2+c_x)\cos\theta+(1/2)\sin\theta\). For \(\theta=-t<0\),
it is at least
\((1/2+c_x)\cos t+(1/2-c_x)\sin t\). Both lower bounds are concave;
their endpoint minima exceed \(\rho_0-1/2\), using
\(1/2+c_x>\rho_0-1/2\) and \(1/\sqrt2>\rho_0-1/2\).
The stronger (S9), \(9/(10\sqrt2)>\rho_0-1/2\), also permits
\(c_y\le c_x+1/10\), needed by the staircase certificate near the diagonal.

(g) The remaining elementary quadrant exclusions are:

| quadrant / separator | consequence and reason |
|---|---|
| N / CS | impossible: \(P_2=a\cos\theta-b\sin\theta\ge a(\cos\theta-|\sin\theta|)\ge0\) |
| S / CN | impossible by the reversed signs |
| E / CN | for \(\theta\ge0\), the needed \((a-1/2)\sin\theta+(u-1/2)\cos\theta\ge1/2\) has maximum at most \(R_0-\sqrt2<1/2\) by (S24); for \(\theta<0\) it requires \(u\ge1\) |
| E / SEC+ | would require \(u\ge1/2+1/(2\sqrt2)>u_{\max}\), by (S25) |
| N / SEC− | would require \(u\ge1/2+(1/2+c_0)/\sqrt2>u_{\max}\), by (S27) |
| S / SEC+ | the same bound as N / SEC− |
| N / SEC+ | \(b\ge1/2\), so \(\ell\ge5/8\). For \(\theta<0\), also \(u\ge1/2+|\sin\theta|/2\), whence \(|\theta|\le\arcsin(2(R_0/\sqrt2-1))<5/8\) by (S19b). Thus \(m>\pi/2\). |
| S / SEC− | \(b<0\), \(u\ge1/2\), hence \(m\le-\pi/4-5/8\) |

The functions in (S15), (S16), (S18), (S20), (S21), (S22), (S28)
vanish at zero, by (I2), (I3), or (I4). Their certificates prove positive
derivative on the stated intervals. For (S22), use the positive derivative
on \([0,3/10]\) and positive value on \([3/10,2/5]\) from (S22b).
Consequently each function is nonnegative throughout its required interval.

### 3.2. Case A1: \(c_y\le c_0\)

**E quadrant.** OWN, CE, CN and SEC+ are excluded above. SEC− requires
\(u\ge1/2+(1/2-c_0)/\sqrt2>u_{\max}\), by (S26). A CS square has cap
depth \(1/2-c_y\ge3/2-\rho_0\); (K3) puts its primary direction within
\(2/5\) of \(-\pi/2\), not in E. CW contradicts (T4), since
\(|m|\le\pi/2\). Thus this quadrant is empty.

**N quadrant.** Write \(\phi=\pi/2+\theta\). We prove
\(m\ge\alpha_1^+=\pi/2-5X_0/4\). The remaining separators are CN,
OWN, SEC+ and CW; the last two are already settled.

For CN, \(h=1/2+c_y\in[1/2,\rho_0-1/2]\), and (K3), (K6) give
\(|\theta|<1/4\), \(a\ge1\).

- If \(b\ge0\), then \(m\ge\pi/2-1/4>\alpha_1^+\), by (S23d).
- If \(b<0\), \(\theta\ge0\), then \(u\le X_0\), giving the claim.
- If \(b<0\), \(\theta=-t<0\), put \(V=u+1/2\). By (K1),
  \(a\ge h/\cos t+1/2+V\tan t\ge1+V\sin t\). Thus
  \((3/2+V\sin t)^2+V^2\le Q_0\). For
  \(W=X_0+1/2-4t/5\), (I2), (S15) give
  \((3/2+W\sin t)^2+W^2\ge Q_0\). Monotonicity in \(V\) forces
  \(V\le W\), so \(t+5u/4\le5X_0/4\), proving the marker bound.

For OWN with \(\theta=t\ge0\),
\(a\ge1/2+(1/2+c_y)\cos t+(1/2-c_x)\sin t\ge1/2+(1/2)\cos t\).
If \(b<0\), (S18) implies
\(U(1/2+(1/2)\cos t)\le X_0+4t/5\), so
\(m\ge\pi/2+t-5u/4\ge\alpha_1^+\). If \(b\ge0\),
\(m\ge\pi/2\).

For OWN with \(\theta=-t<0\), put
\[
 a_N(t)=1/2+(1/2)\cos t+(1/2+c_0)\sin t.
\]
We have \(a\ge a_N(t)\). By (S17a), this is increasing on
\([0,\pi/4]\), and (S17b) gives \(a_N(5X_0/4)>\rho_0\), hence
\(t<5X_0/4\). This suffices for \(b\ge0\). For \(b<0\), (S16)
gives \(U(a_N(t))\le X_0-4t/5\), proving the same bound. Thus in all
N cases \(\alpha_1^+\le m\le\pi\).

**S quadrant.** Write \(\phi=-\pi/2+\theta\). We prove
\(m\le-\alpha_1^-=-\pi/2+5U_0/4\). Only CS, OWN, SEC− and CW
remain; the last two are already settled. For OWN and \(\theta\ge0\),
\[
 a\ge a_S(\theta)=1/2+(1/2-c_0)\cos\theta+(1/2+c_0)\sin\theta.
\]
If \(b\le0\), it suffices that \(\theta<5U_0/4\): for CS use (K3),
(S23c), and for OWN use concavity of \(a_S\) with (S23a,b), which
exclude \([5U_0/4,\pi/4]\).

If \(b>0\), it suffices that \(\theta+5u/4\le5U_0/4\).
For CS with \(\theta\ge0\), (K1) gives
\(a\ge2-\rho_0+V\sin\theta\), \(V=u+1/2\). With
\(W=U_0+1/2-4\theta/5\), (S22), (S22b) imply
\((5/2-\rho_0+W\sin\theta)^2+W^2\ge Q_0\), forcing \(V\le W\).
For CS with \(\theta<0\), use \(u\le U_0\). For OWN with
\(\theta\ge0\), use \(U(a_S(\theta))\le U_0-4\theta/5\) from
(S20). For OWN with \(\theta=-t<0\),
\(a\ge1/2+(1/2-c_0)\cos t\), and (S21) gives
\(U(1/2+(1/2-c_0)\cos t)\le U_0+4t/5\).
Thus \(-\pi\le m\le-\alpha_1^-\) in every S case.
The W quadrant is excluded by (d). This completes A1.

### 3.3. Case A2: \(c_0<c_y\le c_x\)

**N quadrant.** We prove \(m\ge\pi/2\). CN is impossible by cap depth.
OWN with \(\theta<0\) requires
\[
 a>1/2+(\rho_0-1/2)(\cos t+\sin t)\ge\rho_0,
\]
which is impossible. For OWN with \(\theta=t\ge0\),
\(a\ge1/2+(\rho_0-1/2)\cos t\), and (S28) gives
\[
 (1+(\rho_0-1/2)\cos t)^2+(1/2+4t/5)^2\ge Q_0.
\]
Consequently \(u\le4t/5\) and \(m\ge\pi/2\). SEC+ and CW were
settled in (g), (c).

**E quadrant.** Only SEC− and CS remain; we prove \(m<-27/50\).
For SEC− with \(\theta\ge0\),
\[
 u\ge1/2+(1/2-c_y)\cos\theta+(1/2+c_x)\sin\theta
 \ge u_S:=1/2+\sin\theta.
\]
Each term in the label lower bound
\[
 \min\left(5u/4,\pi/6+(u-1/2)/3+3(1-A(u))/4,\pi/4\right)
\]
increases with \(u\). Evaluate it at \(u_S\); (S31) gives
\(m=\theta-\ell<-27/50\). Feasibility limits
\(\sin\theta\le R_0/\sqrt2-1\). For SEC− with \(\theta<0\),
\(u\ge1/2\), so \(m\le\theta-5/8\).

For CS with \(\theta\ge0\),
\(b<-1/2-(a+1/2)\tan\theta\), hence \(u\ge1/2+\sin\theta\)
and (S31) applies. For CS with \(\theta=-t<0\),
\(b<(a-1/2)\tan t-1/2\). If \(b\ge0\), then
\(t>\arctan((1/2)/(\rho_0-1/2))\), and (S32b) yields
\[
 m\le-t+\tfrac54((\rho_0-1/2)\tan t-1/2)<-27/50.
\]
If \(b<0\), then \(u>1/2-(A(u)-1/2)\tan t\), and (S32a) gives
\(t+\ell>27/50\).

**S quadrant.** If \(b\le0\) or \(\theta<0\), then
\(m\le-\pi/4\). Take \(b>0\), \(\theta\ge0\). Only OWN, CS and
CW remain, with CW already settled. For OWN,
\[
 a\ge1/2+(1/2-c_y)\cos\theta+(1/2+c_x)\sin\theta
 \ge a_0:=1/2+\sin\theta.
\]
If \(\sin\theta>\rho_0-1/2\), this is infeasible. Otherwise each label
term is at most its value at \((a_0,U(a_0))\), and (S29) gives
\(\theta+\ell<\pi/2-27/50\). For CS, positive cap depth and (K1)
give \(a>1/2+(1/2+u)\tan\theta\); (T1), (S30) give the same marker
bound. The W quadrant is excluded by (d). Lemma A and Proposition A follow.

The A1 marker bounds can be attained by axis-parallel CN and CS squares.
The direct certificates intentionally use weaker forbidden arcs
\((-0.99,1.22)\) and \((-0.54,1.56)\), whose widths already exceed
\(2\pi/3\). They retain the strict hypothesis \(c_x>c_0\); the face
\(c_x=c_0\) is not excluded.

## 4. Lemma B — chart bounds (N17), axial markers (N20)

Now \(c\in[0,c_0]^2\). Every exterior chart satisfies:

- (B1) \(u<1/2\), so its nearest point to \(O\) is the foot
  \((a-1/2)n\), in the relative interior of the near edge.
- (B2) \(a\ge2-\rho_0\).
- (B3) \(a\le\rho_0\), \(u\le U(a)\le U_0\).
- (B4) \(177/200<a<223/200\), \(u<117/250\), i.e. (N17).
- (B5) \(9a+11u<2\pi+7\), so \(\ell=5u/4\) and
  \(m=\phi+5b/4\), i.e. (N20).
- (B6) Neither secondary separator occurs.

*Proof.* If \(u\ge1/2\), the near corner has norm squared
\((a-1/2)^2+(u-1/2)^2\). On
\(1/2\le u\le a\), \((a+1/2)^2+(u+1/2)^2\le Q_0\), this convex
function is maximized at
\((a,u)=(\sqrt{Q_0-1}-1/2,1/2)\): on the circular boundary it equals
\(Q_0+2-2R_0(\cos\psi+\sin\psi)\), decreasing in the relevant
\(\psi\). Thus the corner norm is at most
\(\sqrt{Q_0-1}-1<3/2-\rho_0\), by (S3). But \(C\) contains the open
disk of radius \(3/2-\rho_0\), so this closed corner is in \(C^\circ\),
forcing interior overlap. This proves (B1).

The foot cannot belong to \(C^\circ\), so its distance is at least
\(3/2-\rho_0\), proving (B2). Containment gives (B3), and (S10a–c)
give (B4).

For (B5), the disk maximizer of \(9a+11u\) lies to the left of
\(a=2-\rho_0\), by (S11a). Hence the constrained maximum is
\(9(2-\rho_0)+11U_0<2\pi+7\), by (S11b). This is exactly the
axial-versus-side inequality, and also \(5u/4<\pi/4\).
Finally a secondary separator needs
\(|b-c\cdot n^\perp|\ge1/2+w\ge1\), impossible because
\(U_0+\sqrt2c_0<1\), by (S12).

## 5. Lemma C — five fixed pins (N19)

The pins have radius \(9/10\) and angles
\[
 q_E:0,\quad q_N:\pi/2,\quad q_W:11\pi/12,\quad
 q_D:5\pi/4,\quad q_S:19\pi/12.
\]
**Lemma C.** Every exterior square contains at least one of these pins in its
interior. Since there are five squares and five pins and a pin cannot belong
to two disjoint interiors, each square contains exactly one. Label the squares
by their pins. This is (N19); no sector theorem is assumed in this labeling.

*Proof.* By (B6), a square is OWN or lies in a cardinal cap. By (T5), it
suffices to treat CE, CW, OWN-E and OWN-W. The normal inequality
\(0.9\cos\delta<a+1/2\) is automatic, since \(a\ge1/2\).

**CE implies \(q_E\).** Here \(h\in[1/2,\rho_0-1/2]\), and
(K3), (K6) give \(|\theta|<1/4\), \(a\ge1\), \(|b|<1/2\).
Reflection across the cap axis fixes the cap and pin, so take \(\theta\ge0\).
The normal lower condition follows from (S35):
\(a\le\rho_0<0.9\cos(1/4)+1/2\). The transverse lower condition follows
from \(b>-1/2\). If the upper condition failed, put
\(V=1-0.9\sin\theta\); the cap inequality and containment would yield
\[
 Q_0\ge G_E(\theta):=(1/(2\cos\theta)+1+V\tan\theta)^2+V^2,
\]
contrary to (S36) on \([0,1/4]\).

**CW implies \(q_W\) or \(q_D\).** Rotate by \(\pi\), so the cap is
east-facing with \(h\in[3/2-\rho_0,1/2]\), while the two pins have
angles \(-\pi/12\), \(\pi/4\). By (K3), \(|\theta|<2/5\),
\(|b|<1/2\). Put \(\delta_W=-\pi/12-\theta\),
\(\delta_D=\pi/4-\theta\). The normal condition for \(q_W\) always
holds by (S37).

(a) If \(-1/2+0.9\sin\delta_W<b<1/2+0.9\sin\delta_W\), use \(q_W\).

(b) If \(b\ge1/2+0.9\sin\delta_W\), use \(q_D\). Its transverse
upper condition follows from \(b<1/2\). Its transverse lower condition
follows from
\[
 0.9[\sin(\pi/12+\theta)+\sin(\pi/4-\theta)]
 =0.9\cos(\theta-\pi/12)<1.
\]
For its normal condition, containment and the lower bound on \(b+1/2\)
give
\[
 a-1/2\le\sqrt{Q_0-(1-0.9\sin(\pi/12+\theta))^2}-1
 <0.9\cos\delta_D \quad\text{(S38)}.
\]

(c) If \(b\le-1/2+0.9\sin\delta_W\), then \(\theta=-t\),
\(\pi/12<t<2/5\). The cap inequality gives
\[
 a\ge h/\cos t+1/2+(1/2-b)\tan t>\rho_0
\]
using \(1/2-b\ge1-0.9\sin(t-\pi/12)\) and (S39), a contradiction.

**OWN-E implies \(q_E\).** The own separator gives
\[
 a\ge a_E(\theta):=1/2+(1/2)\cos\theta+(1/2)|\sin\theta|
 -c_0[\theta<0]|\sin\theta|.
\]
This lower bound increases on \([0,\pi/4]\) and is concave in
\(|\theta|\) on the negative half. By (S41a–c),
\(a_E(3/10),a_E(-5/12),a_E(-\pi/4)>\rho_0\), so
\(-5/12<\theta<3/10\). On this interval (S40a) gives the normal
condition and (S40) gives
\[
 |0.9\sin\theta+b|\le0.9|\sin\theta|+U(a_E(\theta))<1/2.
\]

**OWN-W implies \(q_W\) or \(q_D\).** Write \(\phi=\pi+\theta\).
The own separator gives
\[
 a\ge a_W(\theta):=1/2+(1/2-c_0)\cos\theta
 +(1/2-c_0[\theta>0])|\sin\theta|.
\]
Use the same \(\delta_W,\delta_D\) as for CW.

- \([-\pi/4,-2/3]\) is infeasible by (S42a,b) and concavity.
- On \((-2/3,-\pi/12)\), use \(q_W\). The normal condition is
  (S43a); the transverse upper condition follows from \(b<1/2\), and
  the lower one from (S43):
  \(b\ge-U(a_W(\theta))>-1/2+0.9\sin\delta_W\).
- On \([-\pi/12,\pi/4]\), we have \(\delta_W\le0\le\delta_D\).
  (i) If \(b>-1/2+0.9\sin\delta_D\) and
  \(0.9\cos\delta_D>a-1/2\), use \(q_D\).
  (ii) If \(b\le-1/2+0.9\sin\delta_D\), use \(q_W\). The
  transverse upper condition is the 60-degree identity above, the lower
  condition follows from \(b>-1/2\), and (S44) gives the normal condition:
  \[
  a\le\min\{\rho_0,A(\max(0,1/2-0.9\sin\delta_D))\}
  <1/2+0.9\cos\delta_W.
  \]
  (iii) In the remaining case \(a\ge1/2+0.9\cos\delta_D\).
  By (S45a), this forces \(\theta<-1/30\). Then (S45b) gives
  \(b\le U(1/2+0.9\cos\delta_D)<1/2+0.9\sin\delta_W\).
  The transverse lower condition is as in (ii), and (S45c) gives the
  normal condition because \(|\delta_W|\le\pi/12\). Again use \(q_W\).

This proves Lemma C. The remaining cases follow by (T5), without choosing a
new global normalization.

## 6. Lemma D — separators, windows, normalization and cyclic order

**D1.** The possible central separators of the pin-labeled squares are:

| label | alternatives |
|---|---|
| E | CE or OWN |
| N | CN or OWN |
| W | CW or OWN |
| S | CS or OWN |
| D | CW, CS or OWN |

Secondary separators fail by (B6). A cap square containing a pin in its open
interior requires that pin to lie strictly in the cap half-plane. The fixed
coordinates exclude every other cardinal choice.

**D2.** The primary windows are
\[
 \phi_E\in(-5/12,3/10),\qquad
 \phi_N-\pi/2\in(-3/10,5/12),
\]
\[
 \phi_W-\pi\in(-2/3,5/8),\qquad
 \phi_S-3\pi/2\in(-5/8,2/3),
\]
with \(\phi_D\in(\pi-2/5,3\pi/2+2/5)\). If D is CS, then
\(|\phi_D-3\pi/2|<2/5\).

For E, CE has \(|\theta|<1/4\), and OWN-E has the range proved in §5.
An OWN-N square cannot contain \(q_E\): its projection is less than
\(0.9\sin(3/10)<3/2-\rho_0\), by (S47). An OWN-S square with positive
\(\theta_S\) would need
\(\tan\theta_S>(1/2-c_0)/0.4>\tan(2/3)\), by (S47b), outside the
mirrored OWN range. In the other cases the normal projection is nonpositive.

For W, CW has \(|\theta|<2/5\). OWN-W has \(\theta>-2/3\) by (S42).
For \(\theta\ge5/8\), the pin's transverse condition requires
\(u>0.9\sin(\pi/12+\theta)-1/2\), contradicting containment with
\(a\ge a_W(\theta)\), by (S48). OWN-N is excluded by (S49b) for
\(\theta_N\le0.17\), and (S49) for \(0.17\le\theta_N<5/12\).
OWN-S is excluded by (S50) for \(\theta_S\le0\), and by negative pin
projection for \(\theta_S>0\). OWN-E likewise has negative projection.

For D, cardinal caps give their \(2/5\) windows. OWN-W has
\(\theta>-2/5\) by (S51), with OWN-S symmetric. On N/E axes the pin
projection is nonpositive, including the boundary directions, while
\(a-1/2>0\). N and S windows follow from (T5).

**The single normalization reflection.** If \(\phi_D>5\pi/4\), apply
(T5), sending it to \(5\pi/2-\phi_D<5\pi/4\). This consistently
permutes the pin labels and preserves every established hypothesis. Hence
assume \(\phi_D\le5\pi/4\). D cannot be CS, because
\(3\pi/2-2/5>5\pi/4\). We obtain
\[
 \phi_D=\pi+d,\qquad -2/5<d\le\pi/4.
\]
This is the domain required by P7 and Appendix A. No further global reflection
is available to transfer downstream survivor cases.

**D3 (N21).** Each labeled square uses either OWN or its corresponding
cardinal side: east for E, north for N, west for W and D, south for S. Prefer
the cardinal separator whenever its margin is nonnegative, including ties.

**D4.** \(\phi_W<\phi_D\).

Suppose \(\varepsilon=\phi_W-\phi_D\ge0\). By D2,
\(\varepsilon<5/8+2/5=41/40\). On the primary axes, the inner-side
alternative needs
\[
 a_W\cos\varepsilon-b_W\sin\varepsilon+w(\varepsilon)
 \le a_D-1/2\le\rho_0-1/2,
\]
but the left side is at least
\((5/2-\rho_0)\cos\varepsilon>\rho_0-1/2\), by (S53).
The outer-side alternative needs
\(|P_W|\ge a_D+1\ge3-\rho_0>R_0\), impossible. The other primary
axis is treated in the same way.

On axis \(n_D^\perp\), putting W on the positive side would require
\(q_W\cdot n_D^\perp>q_D\cdot n_D^\perp\). But the reverse sine
difference equals \(\cos(13\pi/12-\phi_D)>0\) on the D window.
Putting W on the negative side would require
\[
 a_W\sin\varepsilon+b_W\cos\varepsilon+w(\varepsilon)
 \le b_D-1/2<U_0-1/2<0,
\]
while its left side is
\((a_W+1/2)\sin\varepsilon+(b_W+1/2)\cos\varepsilon\ge0\).
On \(n_W^\perp\), one direction is excluded by the same pin difference,
now \(\cos(13\pi/12-\phi_W)>0\), and the other by the corresponding
\(|b_D|\le U_0<1/2\) bound. No separating axis remains, a contradiction.

**Corollary (N18).**
\[
 \phi_E<\phi_N<\phi_W<\phi_D<\phi_S<\phi_E+2\pi.
\]
This follows from D2, D4 and (S52a–d):
\[
 3/10<\pi/2-3/10,\quad
 \pi/2+5/12<\pi-2/3,\quad
 5\pi/4<3\pi/2-5/8,\quad
 3\pi/2+2/3<2\pi-5/12.
\]

## 7. Remaining outputs

**N22: one helper per side.** Two squares in the same cardinal cap would both
contain \((h+1/2)v\) in their interiors, by (K4). The depths
\(h=1/2\pm c_x\) or \(1/2\pm c_y\) all lie in
\([3/2-\rho_0,\rho_0-1/2]\). This contradicts disjointness.

**N24: moving pins.** CE gives \(P_E=(1+c_x,0)\in E^\circ\) by (K4).
For OWN-E, use Lemma G below. Obtain \(P_N=(0,1+c_y)\) by (T5).

**Lemma G.** For OWN-E, D2 gives \(-5/12<\theta<3/10\), and
\(a\ge a_E(\theta)\). The lower normal condition for \(P_E\) follows
from (S54a), since
\(a-1/2\le\rho_0-1/2<\cos(5/12)\le(1+c_x)\cos\theta\).
The upper normal condition follows from OWN:
\[
 a+1/2-(1+c_x)\cos\theta
 \ge1/2+(1/2-c_0)|\sin\theta|>0.
\]
For the transverse condition, (S54) gives
\[
 |(1+c_x)\sin\theta+b|
 \le(1+c_0)|\sin\theta|+U(a_E(\theta))<1/2.
\]

**N25.** A cardinal helper has depth at least \(3/2-\rho_0\). By (K3),
its primary deviation is the cap angle and has magnitude less than \(2/5\).

**N26, with its indispensable hypothesis.** If E and W both use their
cardinal sides, then \(|\theta_E|+|\theta_W|<4c_0\); similarly for N,S
when both are cardinal. This is not a statement about arbitrary own/cardinal
opposite pairs. The two relevant downstream applications are P26-1 (E,W
cardinal) and P16 (N,S cardinal).

Indeed cap depth gives
\[
 1/2+c_x\le B(|\theta_E|),\qquad
 1/2-c_x\le B(|\theta_W|).
\]
Adding and applying (K5) yields
\[
 1\le2(\rho_0-1/2)-\tfrac12(|\theta_E|+|\theta_W|),
\]
strict unless both angles vanish. Thus the desired strict bound follows; if
both vanish, their sum is zero and \(c_0>0\).

**N27.** After normalization, D is CW or OWN. Appendix A (A1), applied in
this fixed frame, excludes CW, hence its canonical bit is OWN. Its full
hypotheses must be stated explicitly:

- \(R^2\le Q_0\) and \(c\in[0,c_0]^2\), by Proposition A;
- \(a\le\rho_0\), by B3;
- a west-cardinal D has angle \(|d|<2/5\), by K3;
- if D is west-cardinal, W is own-primary, by N22 and D3;
- an own-primary W has \(w>-2/3\), by (S42), D2;
- \(w<d\), by D4.

These are all established before invoking A1. No A2 result or forbidden
reflection is used. With the existing A1 argument, this completes
(N16)–(N27).

## 8. Certificates and their logical role

The supplied package `normalization_cert` has two independent layers:

1. `cert_scalars.py` checks all 78 scalar inequalities, retaining their S
   identifiers; I1–I4 are merely sanity-checked numerically because their
   proofs are algebraic identities.
2. Direct branch-and-bound checks chart bounds, pins, windows/separator sets,
   cap piercing, own moving pins, W/D order, and the two forbidden-marker
   regions. A direct search is accepted only with no unresolved box.

The original backend is python-flint/Arb at 64-bit working precision. The
supplied `CERT_LOG.md` records the author's results and must not be presented
as a fresh run. Local execution and any alternative arithmetic backend are
recorded separately in `NORMALIZATION_INTEGRATION.md` and the corresponding
replay log.

The forbidden-arc certificates use hand steps (e), (f) to drop CE/OWN in the
E quadrant. They prove the strict domain \(c_x>c_0\), not its boundary.
The A2 staircase boxes may exceed \(c_y=c_x\) by less than \(1/10\), as
permitted by (S9). At \(c_x=c_0\), the axis-parallel east square is a real
counterexample to the forbidden arc; no certificate is claimed there.

All nonconstant scalar obligations are one-variable except (S5), (S30), and
(S32a), which are two-variable. The proof therefore isolates explicit scalar
leaves suitable for subsequent Lean lemmas. It does not turn a Python success
message into a theorem, and it does not claim that the supplied packet audits
the separate downstream A2 proof.
