# Exterior frames lie in an arc shorter than 7/10 radians

Assume the radius-\(1/12\) central-core input at
\(Q=9789/2500\), and the completed four-type boundary-pair certificate.
Then the seven exterior square frames of every actual packing at
\(q\le Q\) lie in a common orientation arc of length strictly less than
\(7/10\) radians. Orientations are taken modulo \(T=\pi/2\).

This is a consequence for every packing under the ceiling, including the
remaining M7 and M8 branches. It does not use an M5/M6 assumption.

## Physical ring cost budget

Take the exterior centers in their ordinary cyclic order. The central-core
and disk bounds give every successive directed center gap
\(3/5<\delta_i<\pi\), with \(\sum_i\delta_i=2\pi\).
The fixed-holonomy radial-boundary reduction preserves the genuine
neighbor SAT conditions, all seven frame differences, and this sum.
It needs no low-cost hypothesis when the fixed holonomy is \(2\pi\): a
first gap reaching \(\pi\) would force the other six gaps to sum to
\(\pi\), whereas they are each larger than \(3/5\).

Let

\[
U=\sum_{i=0}^{6}(w_i-1),\qquad
w_i=\frac{1+|\cos(\theta_{i+1}-\theta_i)|+
|\sin(\theta_{i+1}-\theta_i)|}{2}.
\]

After reduction, the certified pair inequalities and the hand odd-cycle
lemma give

\[
2\pi-\frac9{50}U\ge\frac{6209669}{10^6}.
\]

The reduction preserved all frame differences, so this also bounds the
original physical ring's width sum. Using \(\pi<355/113\),

\[
U<\frac{8307403}{20340000}
<\frac{408427}{10^6}
<\frac{70}{169}<\sqrt2-1.
\tag{1}
\]

## Lifting the orientation tour to a short interval

Put \(h=T/2=\pi/4\) and

\[
g(d)=\frac{\cos d+\sin d-1}{2},\qquad 0\le d\le h.
\]

This is increasing and concave, with \(g(0)=0\) and
\(g(h)=(\sqrt2-1)/2\). The width excess of two frames is exactly
\(g(d)\), where \(d\) is their shorter orientation-circle distance.
Concavity gives

\[
g(d)\ge\frac{g(h)}h d.
\]

Choose a signed shorter increment \(x_i\in[-h,h]\) for each edge of the
orientation tour. Its total is an integer multiple of \(T\). By (1),

\[
\sum_i|x_i|\le\frac{h}{g(h)}U<2h=T.
\]

Consequently that integer multiple is zero. The increments define a closed
real lift of the seven-frame tour. If \(L\) is the difference between its
largest and smallest lifted values, the total variation is at least
\(2L\). Hence \(L<h\), and all frames lie in one orientation arc of
length \(L\).

The function \(g\) composed with shorter circle distance is a metric.
Indeed, concavity and \(g(0)=0\) imply subadditivity when the sum of two
distances is at most \(h\). When their sum exceeds \(h\), the displayed
chord lower bound gives a sum of costs at least \(g(h)\), which bounds
every direct cost. Apply this triangle inequality to the two portions of
the cyclic tour joining the extreme lifted frames. Since \(L<h\), their
shorter circle distance is \(L\), and therefore

\[
U\ge2g(L)=\cos L+\sin L-1.
\tag{2}
\]

## Rational terminal bound

At \(z=7/10<h\), alternating Taylor bounds give

\[
\begin{aligned}
\cos z+\sin z-1
&>\left(1-\frac{z^2}{2}+\frac{z^4}{24}-\frac{z^6}{720}\right)
 +\left(z-\frac{z^3}{6}+\frac{z^5}{120}-\frac{z^7}{5040}\right)-1\\
&=\frac{2945220061}{7200000000}
>\frac{8181}{20000}
>\frac{8307403}{20340000}.
\end{aligned}
\]

Because \(\cos L+\sin L-1\) is increasing on \([0,h]\), equations
(1) and (2) imply \(L<7/10\). This proves the stated common-arc cover.

The angle \(7/10\) radians is about \(40.1\) degrees; the rational angle
is the theorem's constant. All steps after the boundary-pair cost budget
are analytic, with explicit rational terminal arithmetic.
