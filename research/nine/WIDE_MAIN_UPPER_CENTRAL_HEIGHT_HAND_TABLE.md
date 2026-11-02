# An upper central original stays above minus seven fortieths

November 2, 2026. Computer-assisted discovery followed by a complete exact
table and the physical hand reduction below. No Lean or CI.

Put \(Q=1105/256\), \(l=29/60\), and \(\rho=91/60\).
Retain four original physical unit squares A,B,C,D in horizontal
center-cone order inside the closed Q-disk. The outer projection links
A--B and C--D are actual; the middle link may be actual or weak. Retain
an original central square F, distinct from the mains, with

\[
             |x_F|\le l,\qquad y_F>\max(y_B,y_C).
\]

**Theorem.**

\[
                              y_F>-7/40.                 \tag{1}
\]

No selected outsider chain, second outsider, low-floor premise, or
occupancy count is assumed. The proof includes arbitrary independent
original frames and every touching boundary in the closed disk.

## 1. Retain the accepted original-pair height bound

The complete physical reduction in Sections 2--4 of
`WEAK_MIDDLE_UPPER_CENTRAL_PAIR_REPLACEMENT_HAND_PROOF.md` gives a lower
bound for the first upper central center before it uses a second upper
central square. We use exactly that bound, without the second square.
Here are its formulas and all original-frame parameters.

For each main M set

\[
 g_M=1/(4h_M),\quad \eta_M=h_M+g_M-1,
 \qquad V=\eta_B+\eta_C.
\]

The outer-actual endpoint theorem gives
\(1/2\le h_B,h_C<13/20\), \(0\le V<1/30\), and the main bands

\[
 b_-=h_B-61/60<x_B<1/60-g_B-\eta_C=b_+,
\]

\[
 c_-=g_C+\eta_B-1/60<x_C<61/60-h_C=c_+.
                                                        \tag{2}
\]

For two folded original frames \(s=(a,b)\), \(t=(c,d)\), with
\(a\ge b\ge0\), \(c\ge d\ge0\), and unit side axes, define

\[
 \sigma(s,t)=(1+ac+bd+|ad-bc|)/2\ge1.
\]

This is a lower bound for the original pair's support sum on any owned
separating axis, for either chirality relation. For a horizontal gap
bound D let

\[
 K(s,t,D)=\min_{(p,q)\in\{(a,b),(b,a),(c,d),(d,c)\}}
                  \max(0,(\sigma-pD)/q),               \tag{3}
\]

with the exact zero-component convention: an owner with \(q=0\) is
omitted if \(\sigma-pD>0\), and contributes zero otherwise. Physical
nonoverlap implies \(|\Delta y|\ge K(s,t,D)\). The function K is
nonnegative and nonincreasing in D. All signs and original owners are
retained in this necessary bound.

For x=xF set

\[
 L=\min_{z\in\{b_-,b_+\}}[-z+K(B,F,|x-z|)],
 \quad R=\min_{z\in\{c_-,c_+\}}[z+K(C,F,|x-z|)],
\]

\[
 K_B=K\left(B,F,\max_{z\in\{b_-,b_+\}}|x-z|\right),
 \quad K_C=K\left(C,F,\max_{z\in\{c_-,c_+\}}|x-z|\right),
\]

\[
 M=K(B,C,c_+-b_-),\qquad
 Y_{\rm mid}=M-129/80+\min(-b_++K_C,c_-+K_B).
\]

Then the accepted physical reduction proves

\[
 y_F\ge Y:=\max\left\{-3/10,-129/80+L,-129/80+R,
 -379/240+(16/9)V+(L+R)/2,Y_{\rm mid}\right\}.        \tag{4}
\]

The individual terms respectively use the own-half clearance, the two
outer cones and endpoint diagonal bounds, the summed endpoint resource,
and both possible height orders of the original B/C physical pair.
The main-position endpoint minimum is justified by concavity of the
complete clearance expression on the admitted horizontal gap range.
The original zero-owner boundary at gap one is included explicitly.
Thus (4) uses only A,B,C,D,F on the present hypotheses.

## 2. Four live parameters and a complete exact cover

For a main of halfwidth h, its folded components are

\[
 a=h+\sqrt{1/2-h^2},\qquad b=h-\sqrt{1/2-h^2}.
\]

For F write \(t_F=b_F/a_F\in[0,1]\), so
\(a_F=1/\sqrt{1+t_F^2}\), \(b_F=t_Fa_F\).
Reflect horizontally to make \(x_F\ge0\), exchanging the two mains
when necessary. The entire remaining closed root is

\[
 (h_B,h_C,t_F,x_F)\in
 [1/2,13/20]^2\times[0,1]\times[0,29/60].             \tag{5}
\]

`upper_central_height_candidate.json` is a complete binary midpoint
partition of (5). Its two terminal conclusions are:

| Strict conclusion | Number of leaves |
|---|---:|
| \(V>1/30\), excluding the orientation box | 18 |
| \(Y>-7/40\) | 2,671 |
| Total | 2,689 |

The tree has 5,377 nodes and maximum depth 23. It includes every root
endpoint, every shared bisection face, and every zero-slope frame.

`verify_upper_central_height.py` reconstructs the complete tree and
(2)--(4), importing only the already reviewed exact shape and
original-pair-clearance helper. It imports no producer or discovery
code. Its exact rational box endpoints are enclosed by directed
64-bit integer intervals; square roots are enclosed by integer square
roots. Lower height resources are rounded downward, distance arguments
upward, and the complete original-owner minimum downward.

The complete exact replay passed all 2,689 leaves, with least reserve

\[
                   4079836963653481/553402322211286548480>0.
\]

The certificate SHA-256 is
`007aa80cc2a5f57c18e20d9ee0fd1c9676fbb0fd34c64cff7b28bb74dcdea968`.
The checker SHA-256 is
`0090523bf3027b674b51089e137f15ba6ee46ee40d9bd59e3d81010ec05b974c`.
The exact replay and four rejected changed-root, illegal-axis,
missing-child, and false-terminal controls are recorded beside the
certificate. Numerical exploration is not a premise.

An original configuration has V<1/30, so its leaf gives the second
conclusion. Equation (4) then proves (1). This is a reusable physical
height lemma; it does not itself close a marked nine-square mask.
