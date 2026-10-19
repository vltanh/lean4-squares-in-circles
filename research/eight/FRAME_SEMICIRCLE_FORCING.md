# The seven-cycle width obstruction excludes M6 as well as M5

This is an exact elementary consequence of frame-circle geometry. The continuous seven-state cost certificate has now been completed; see [FOUR_TYPE_BOUNDARY_PAIR_CERTIFICATE.md](FOUR_TYPE_BOUNDARY_PAIR_CERTIFICATE.md).

## Lemma

Take any finite cyclic sequence of unoriented square frames, represented on the circle of circumference

\[
L=\pi/2.
\]

For each edge let \(d_i\in[0,L/2]\) be the geodesic frame distance and let

\[
h(d)=\frac{\cos d+\sin d-1}{2},\qquad U=\sum_i h(d_i).
\]

If \(U<\sqrt2-1\), all frames lie in one open arc of length \(\pi/4\). Equivalently, if the frames do not lie in any open 45-degree frame window, then \(U\ge\sqrt2-1\).

## Proof

The function \(h\) is concave on \([0,\pi/4]\), vanishes at zero, and has endpoint value \(h(\pi/4)=(\sqrt2-1)/2\). Therefore

\[
h(d)\ge\frac{2(\sqrt2-1)}{\pi}\,d.
\]

The assumed strict upper bound for \(U\) implies

\[
\sum_i d_i<L.
\]

Choose a shortest signed increment \(\varepsilon_i\in[-L/2,L/2]\) for each cyclic edge. Since the frame sequence closes, \(\sum_i\varepsilon_i=kL\) for an integer \(k\). But

\[
|k|L\le\sum_i|\varepsilon_i|=\sum_i d_i<L,
\]

so \(k=0\). Thus the increments form a closed lifted polygon on the real line. If its maximum and minimum lifted frame values differ by \(D\), its total variation is at least \(2D\), because a closed walk must travel from the minimum to the maximum and back. It follows that

\[
D\le\frac12\sum_i d_i<L/2.
\]

All frame values therefore belong to one real interval of length less than \(L/2\), and their images on frame space belong to an open arc of length \(L/2=\pi/4\). This proves the lemma.

## Consequence for the completed disk/core cycle certificate

The boundary-state certificate and its hand odd-cycle lemma prove, for every admissible seven-state adjacent-pair cycle,

\[
\sum_i\delta_i-\beta U+\beta(\sqrt2-1)>2\pi
\]

for some \(\beta>0\). In any actual packing the exterior centers are cyclically ordered, so \(\sum_i\delta_i=2\pi\). The certificate therefore forces \(U<\sqrt2-1\). The lemma puts all seven exterior square frames in an open 45-degree window.

Consequently the maximal closed 45-degree window among all eight square frames contains at least seven labels. **Both majority classes M5 and M6 are excluded by the same certificate.** No condition on the omitted central frame is needed. The surviving majority classes are M7 and M8.

The radial boundary reduction is valid for every actual seven-square exterior ring, independent of majority class. The completed universal inequality therefore closes both M5 and M6, conditional only on the separately proved central-core input. The assembled proof and its remaining computer dependencies are recorded in [GLOBAL_EXTERIOR_FRAME_WINDOW.md](GLOBAL_EXTERIOR_FRAME_WINDOW.md).
