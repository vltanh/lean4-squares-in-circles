# A sharper entry cut for a genuine negative EH1 witness

## 1. Local scope

Put
\[
 Q=\frac{9789}{2500},\qquad K=\frac{13}{12},\qquad
 h=\frac7{10},\qquad T=\frac{61}{250}.
\tag{1}
\]
Let E have nonpositive tangent and lie on its true-core boundary,
and let H be a sorted outer state at Q with positive tangent.
Suppose the actual EH1 projection is feasible at error \(-t<0\),
where \(t\le h\), while the actual EH0 projection is not feasible.

Then E is flat core and the sharper bounds are
\[
 a_E=\frac7{12},\qquad
 0\le b_E<
 \sqrt{Q-(K+\sin t)^2}-\cos t-\frac12
 <\frac{39}{250}-\frac{63}{100}t,
 \qquad 0<t<T.
\tag{2}
\]
The first strict inequality in (2) is the exact local contact
bound. No statement about the DE owner, its error, or a frame
order is required. The same conclusion applies after a necessary
local transport whenever these actual E/H hypotheses are retained.

## 2. The exact contact bound

Section 2.1 of
[the mixed negative-E reduction](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md)
gives
\[
 a_E=\frac7{12},\qquad b_E<\frac{39}{250},\qquad t<\frac14,
\tag{3}
\]
and, writing \(D=b_E+1/2\), its strict contact-vector comparison is
\[
 Q>1+K^2+D^2+2(D\cos t+K\sin t)
   =(D+\cos t)^2+(K+\sin t)^2.
\tag{4}
\]
All terms needed to take the square root are positive. Solving
(4) for \(b_E\) proves the exact middle bound in (2).

## 3. A rational upper bound on the angle

At \(b_E=0\), the right side of (4) equals
\[
 f(t)=K^2+\frac54+\cos t+2K\sin t.
\tag{5}
\]
This function increases on \([0,h]\), since
\[
 f'(t)=2K\cos t-\sin t
 >\frac{13}{6}\frac{19}{25}-\frac{13}{20}>0.
\tag{6}
\]
The whole-interval sine and cosine bounds in (6) are the elementary
Taylor bounds already used in
[the global D-circle proof, Section 2](HAND_G3_GLOBAL_D_IS_OUTER.md).

For a nonnegative variable x, define
\[
 C_{10}(x)=\sum_{j=0}^{5}\frac{(-1)^j x^{2j}}{(2j)!},
 \qquad
 S_{11}(x)=\sum_{j=0}^{5}\frac{(-1)^j x^{2j+1}}{(2j+1)!}.
\tag{7}
\]
Both are lower bounds for cosine and sine on \([0,h]\).
At the single rational point T,
\[
 K^2+\frac54+C_{10}(T)+2K S_{11}(T)-Q
 =
 \frac{14903348574738759576231490793701}
 {8157348632812500000000000000000000}>0.
\tag{8}
\]
Consequently \(f(T)>Q\). Equations (4)--(6), together with
\(b_E\ge0\), force \(t<T\). This is an analytic monotonicity
argument on the whole angle interval.

## 4. A linear tangent cut

Define
\[
 B(t)=\sqrt{Q-(K+\sin t)^2}-\cos t-\frac12.
\tag{9}
\]
The radical is positive on \([0,1/4]\). We show
\[
                         B'(t)<-\frac{63}{100}.
\tag{10}
\]
Set \(y=\sin t\), so \(0\le y<1/4\). After squaring positive
quantities, (10) is equivalent to \(P(y)>0\), where
\[
\begin{split}
 P(y)
 &=(K+y)^2\left(1+\frac{3969}{10000}+\frac{63}{50}y\right)
             -Q\left(y+\frac{63}{100}\right)^2\\
 &=\frac{76784149}{900000000}
   -\frac{321217}{750000}y+\frac{2113}{10000}y^2
   +\frac{63}{50}y^3.
\end{split}
\tag{11}
\]
Here \(P''(y)>0\) for \(y\ge0\), and
\[
 P'(1/4)=-\frac{8099}{93750}<0,\qquad
 P(1/4)=\frac{39154}{3515625}>0.
\tag{12}
\]
Thus P decreases and stays positive on the whole interval
\([0,1/4]\), proving (10).

Finally
\[
 K^2+\left(\frac32+\frac{39}{250}\right)^2-Q
                  =\frac{781}{2250000}>0
\tag{13}
\]
shows \(B(0)<39/250\). Integrating (10) from zero to t gives
the final bound in (2).

This local cut supplies an interval and a tangent bound for a
genuine negative EH1 witness. It makes no cycle-exclusion claim
on its own.
