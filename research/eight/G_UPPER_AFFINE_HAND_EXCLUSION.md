# Candidate word: exclusion of the upper G tangent domain

## 1. The result and its scope

Put

\[
 Q=\frac{3915534138}{10^9}=3.915534138,
 \qquad \gamma=\frac{8977}{10000}.
\]

Consider the seven boundary states in the cyclic order

\[
 (H,G,A,B,T,D,E),\qquad (k_0,\ldots,k_6)=(0,1,0,1,0,1,1).
\]

Each state may independently lie on the outer-circle boundary or on the
boundary imposed by avoidance of the central disk of radius \(1/12\).
Assume the already established physical center-order and frame-concentration
hypotheses:

\[
 \sum_i\delta_i=2\pi,\quad \delta_i>\frac{19}{25},\quad
 \phi_i=\delta_i+\alpha_{i+1}-\alpha_i
 \in k_i\frac\pi2+[-7/10,7/10].                       \tag{1}
\]

Adjacent states satisfy square separation. In the conventions below, the
common-point axis-elimination lemma says that one of the four margins (5)
is nonnegative. The tangent normalization is
\(u_i=\tan\alpha_i\in[-1,1]\).

**Theorem.** There is no such boundary seven-cycle with

\[
                 u_G\ge-\frac1{20},\qquad u_E\le0.       \tag{2}
\]

The reflection and reversal fixing \(E\) allow \(u_E\le0\) to be chosen in
the candidate-word analysis. Consequently, under this choice, every surviving
candidate-word boundary cycle has \(u_G<-1/20\).

The theorem covers all \(2^7\) choices of core or outer boundary states. It
does not assume a particular radial word or a selected separating owner.
Its conclusion concerns the boundary representative. Transferring a statement
to an original packing requires the frame-preserving boundary-reduction and
outer-radius monotonicity interfaces; no preservation of an original center's
tangent during that reduction is asserted here.

## 2. Boundary arcs and the explicit marker table

In its own frame a state has center \((a,-\sigma b)\), where
\(0\le b\le a\), \(v=b/a\in[0,1]\), and \(\sigma\in\{-1,1\}\). Its
signed tangent is \(u=\sigma v\) and
\(\alpha=\sigma\arctan v\). The two boundary curves are

\[
\begin{array}{ll}
 O:&(a+1/2)^2+(b+1/2)^2=Q,\\[2mm]
 C:&a=7/12\quad(0\le v\le6/7),\\
   &(a-1/2)^2+(b-1/2)^2=1/144\quad(6/7\le v\le1).
\end{array}                                                    \tag{3}
\]

The rational input `G_UPPER_AFFINE_HAND_DATA.json` is part of the proof. Its
`arcs` array gives 122 closed subarcs, with fields

\[
 (\text{id},\text{role},\text{kind},\sigma,v_-,v_+,c,p,q).
\]

On that arc the marker is the affine expression

\[
                         L=c+pa+qb.                     \tag{4}
\]

All endpoints and coefficients are rational. Every core arc lies entirely
on its straight side or entirely on its circular corner; in particular,
the exact transition \(6/7\) is retained. The 26 nonempty role/kind/sign
domains under (2) are covered by the declared closed arcs. Their exact union
is checked independently by `audit_G_upper_hand_assembly.py`.

Different formulas are allowed at a shared endpoint. For a particular
seven-cycle choose one containing arc for each vertex, once. Use that
vertex's chosen marker in both incident edges. The pair table covers every
combination of containing arcs, so this convention preserves the cyclic
telescoping identity without a continuity assumption on the piecewise marker.

## 3. Eliminate both state coordinates by elementary support bounds

Write the source as \((a,-\sigma b)\) and the target as
\(R_\phi(A,-\tau B)\). Set
\(W=(1+|\sin\phi|+|\cos\phi|)/2\). The retained signed SAT margins are

\[
\begin{array}{ll}
 M_1=\sigma b+A\sin\phi-\tau B\cos\phi-W,&
 M_2=A-a\cos\phi+\sigma b\sin\phi-W,\\
 M_3=a\sin\phi+\sigma b\cos\phi-\tau B-W,&
 M_4=a-A\cos\phi-\tau B\sin\phi-W.
\end{array}                                                     \tag{5}
\]

Fix an input row, its nonnegative rational multiplier \(\lambda\), and its
chosen margin \(M_j\). For every pair separated on that axis,

\[
 \phi+L_s-L_t-\gamma
 \ge \phi+L_s-L_t-\gamma-\lambda M_j.              \tag{6}
\]

The right side is a sum of a function of the source coordinates, a function
of the target coordinates, and an explicit trigonometric expression in
\(\phi\). Thus both coordinate variables can be removed by lower support
bounds for affine functions on the arcs (3).

Reflection followed by reversal transforms axes 2 and 3 into axes 4 and 1,
respectively. It swaps source and target, changes both signs, and changes
the marker pair to \((-L_t,-L_s)\). The angle \(\phi\) and the pair cost
are unchanged. For normalized axis 1 or 4, writing the target marker as
\(C+PA+TB\), the coefficients of the source and target coordinates are

\[
\begin{array}{c|cc|cc}
 &X_s&Y_s&X_t&Y_t\\ \hline
1&p&q-\lambda\sigma&-P-\lambda\sin\phi&-T+\lambda\tau\cos\phi\\
4&p-\lambda&q&-P+\lambda\cos\phi&-T+\lambda\tau\sin\phi.
\end{array}                                                     \tag{7}
\]

The source coefficients are constant in \(\phi\). The frozen verifier
computes a rigorous lower support for that complete source arc. The target
support mode is declared in the input row and justified by its premise
polynomials. Here are all support rules used.

On a circular arc write

\[
 a=h_0+\sqrt{R_0^2-(b-h_0)^2},\qquad
 r(b)=\frac{b-h_0}{a-h_0},\qquad a'(b)=-r(b),\quad r'(b)>0.
\]

For \(Xa+Yb\):

* If \(X\ge0\), the function is concave, so its minimum is at an arc
  endpoint. The same endpoint rule is immediate on a straight core side.
* If \(Y-Xr\ge0\) at both endpoints, it is nonnegative throughout because
  it is affine in the monotone variable \(r\). The lower endpoint is a
  minimum. Reversing both signs gives the upper-endpoint rule.
* Enlarging a circular arc to its whole circle always gives
  \[
    Xa+Yb\ge h_0(X+Y)-R_0\sqrt{X^2+Y^2}.             \tag{8}
  \]

The input uses only these four modes: `lower`, `upper`, `endpoints`, and
`circle`. No minimization over an unspecified continuum is a remaining
premise. A straight core side is never treated as a circular corner.

For the last radical in (8), each circle row supplies a positive rational
number \(h\). The global identity

\[
 T_h(V)=\frac{5h+15V/h-5V^2/h^3+V^3/h^5}{16},\qquad
 T_h(V)-\sqrt V
 =\frac{(\sqrt V-h)^4(V+4h\sqrt V+5h^2)}{16h^5}\ge0              \tag{9}
\]

holds for every \(V\ge0\). Here \(V=X_t^2+Y_t^2\), so its nonnegativity
is an identity. Substitution of (9) gives a polynomial expression in
\(\sin\phi,\cos\phi,\phi\). It is a lower bound for (6) on the entire
declared angle interval.

## 4. The fixed one-angle polynomial checks

Each row has \(\phi=k\pi/2+r x\), where \(r\in\{-1,1\}\) and
\(0\le x\le7/10\). Thus

\[
\begin{array}{c|cc}
k&\sin\phi&\cos\phi\\ \hline
0&r\sin x&\cos x\\
1&\cos x&-r\sin x,
\end{array}
\qquad W=\frac{1+\sin x+\cos x}{2}.                  \tag{10}
\]

For \(0\le x\le7/10\), the alternating Taylor inequalities give

\[
 \sin x=x-\frac{x^3}{6}+\frac{x^5}{120}-\frac{x^7}{5040}
                 +\eta\frac{x^9}{9!},\quad 0\le\eta\le1,
\]
\[
 \cos x=1-\frac{x^2}{2}+\frac{x^4}{24}-\frac{x^6}{720}
                  +\frac{x^8}{40320}-\zeta\frac{x^{10}}{10!},
                  \quad0\le\zeta\le1.                           \tag{11}
\]

Ordinary rational interval arithmetic on coefficients encloses the result
pointwise after (11). The error parameters need not be constant in \(x\):
at each point they belong to the declared coefficient intervals. Taking
the lower endpoint of every power coefficient therefore gives a lower
polynomial, since \(x\ge0\). This step uses no derivative of a Taylor
remainder.

For every fixed rational interval \([l,h]\), the change of variable
\(x=l+(h-l)t\) and the elementary power-to-Bernstein identity express this
lower polynomial as

\[
 \sum_{j=0}^n b_j\binom nj t^j(1-t)^{n-j},\qquad0\le t\le1.
                                                               \tag{12}
\]

Every coefficient is rational. Nonnegative coefficients prove a premise
on the whole interval. Strictly positive coefficients prove the strict
cost bound on the whole interval. The verifier uses exact integer
denominator clearing to compute (12); this changes the arithmetic cost,
not the formula or its bound.

The fixed table contains 9,796 scalar rows. They give 27,035 premise or
cost polynomials, containing 188,461 nonnegative coefficient lower bounds.
Every cost polynomial has strictly positive coefficients. The least
printed strict cost coefficient is at least

\[
                 \frac{91258797}{25000000000000}>0.              \tag{13}
\]

`G_UPPER_AFFINE_HAND_COMPACT_REPORT.json` records, in input-row order,
the degree and a lower bound for every Bernstein coefficient of each
premise and cost polynomial. The full coefficient lists are determined by
the rational input and frozen verifier. Their full replay output has
SHA-256

```
edd61f0a534eb780894d884b7b0fcbae9d8d1e0901d32ce51d70605b0dbd2724
```

The table is a large finite polynomial certificate. Its proof mechanism is
the elementary support and polynomial argument above. Neither a numerical
optimizer nor an adaptive subdivision process is part of its verification.

## 5. Exhaustive angle coverage and cyclic contradiction

The physical gap hypotheses imply

\[
 \frac{19}{25}<\delta_i<\frac{710}{113}-6\frac{19}{25}.          \tag{14}
\]

If a source arc has \(\alpha_s\in[s_-,s_+]\) and a target arc has
\(\alpha_t\in[t_-,t_+]\), then all relevant frame angles lie in

\[
 \left[\frac{19}{25}-s_++t_-,\;
       \frac{710}{113}-\frac{114}{25}-s_-+t_+\right]
 \cap\left(k\frac\pi2+[-7/10,7/10]\right).                     \tag{15}
\]

Outward rational bounds for the arc endpoint arctangents and \(\pi\)
make (15) an explicit rational interval on each half-angle branch.
The frozen verifier checks every original source-arc/target-arc/axis/half
chain. Independently, `audit_G_upper_hand_assembly.py` recomputes all
arctangent bounds with a different rational root mesh and checks the
interval unions again. There are 8,876 nonempty required chains. Every
one is covered by closed fixed intervals. This includes all four original
axes before normalization.

Now choose containing arcs for the seven vertices as in Section 2. For
each adjacent pair choose an axis with nonnegative margin in (5). Its
corresponding fixed row proves

\[
                         \phi_i+L_i-L_{i+1}>\gamma.
\]

Summing and using both telescoping identities gives

\[
 2\pi=\sum_i\phi_i
     =\sum_i(\phi_i+L_i-L_{i+1})
     >7\gamma=\frac{62839}{10000}.
\]

But

\[
 \frac{62839}{10000}-\frac{710}{113}
       =\frac{807}{1130000}>0,\qquad 2\pi<\frac{710}{113}.
\]

This contradiction proves the theorem.

## 6. Reproduction and immutable proof inputs

The committed proof consists of this manuscript, the rational input, the
frozen verifier, the compact report, and the independent assembly audit.
The full 13 MB arithmetic output is a reproducible output rather than a
second proof input. From this directory:

```sh
python replay_G_upper_hand.py
python audit_G_upper_hand_assembly.py
```

The first command reconstructs the full coefficient output, checks its
recorded SHA-256 and the entire compact report, and optionally writes the
full output with `--save-full`. The second checks all rational state and
angle unions, the table scope, the hashes, and the exact cyclic reserve.
It works with the compact report alone. It also checks the full output's
hash if that optional output is present.

The manifest `G_UPPER_AFFINE_HAND_MANIFEST.json` binds the immutable files.
Discovery fits, failed proposal tables, and intermediate angle refinements
are excluded from that manifest and from the theorem's assumptions.
