# The entire core/core pair regime

This is a whole-domain pair bound for the core marker family used in the
four-type hand conversion. It covers all signed representatives and all
separating axes at once. No relative-frame-angle strip is excluded.

Let \(g=269343/250000=1.077372\), and choose any
\(7\le K\le8\). In particular the rational choice
\(K=7506931/10^6\) is allowed. On the positive core boundary put

\[
 \ell_C(a,b)=K(7/12-a)+gb,\qquad
 \psi_C=\arctan(b/a)-\ell_C(a,b).                             \tag{1}
\]

Use the odd extension of \(\psi_C\) for negative signed states. The
positive core consists of the side

\[
 a=7/12,\qquad 0\le b\le1/2,
\]

and the corner

\[
 a=1/2+\sqrt{1/144-(b-1/2)^2},
 \qquad 1/2\le b\le c_C:=1/2+\sqrt2/24.
\]

**Theorem.** If two such core-boundary squares have disjoint interiors,
and their positive directed center-angle gap is \(\delta\), then

\[
 \delta-\frac9{50}h(\phi)+\psi_C(j)-\psi_C(i)
 >\frac{14033}{15000}>\frac{23}{25}=.92.                     \tag{2}
\]

Here \(\phi\) is any consistent true frame difference and
\(h(\phi)=(|\cos\phi|+|\sin\phi|-1)/2\). The assertion applies
to every choice of the axis that separates the two squares.

## 1. A uniform marker bound

We first prove for every positive core state

\[
 -\frac9{50}<\psi_C<\frac9{50}.                              \tag{3}
\]

The same bound then holds for the odd extension.

On the side write \(x=12b/7\), so \(0\le x\le6/7\), and put
\(\kappa=7g/12\). The function \(\arctan x\) is concave on
\([0,\infty)\), so its tangent at \(x=3/4\) gives

\[
 \arctan x\le\arctan(3/4)+\frac{16}{25}(x-3/4).
\]

The alternating arctangent series gives

\[
 \arctan(3/4)<.644.
\]

For example its upper partial sum through degree 17 is less than .644.
Since \(16/25-\kappa>0\), it follows that

\[
 \psi_C<.644-\frac{12}{25}
       +(\frac{16}{25}-\kappa)\frac67
 =\frac{608599}{3500000}<\frac7{40}.                         \tag{4}
\]

The lower alternating bound \(\arctan x\ge x-x^3/3\) gives

\[
 \psi_C\ge x(1-\kappa-x^2/3)\ge0,                           \tag{5}
\]

because \(1-\kappa-(6/7)^2/3>0\).

On the corner put \(d=b-1/2\) and
\(e=a-1/2=\sqrt{1/144-d^2}\). Then
\(0\le d\le e\). Differentiating \(\alpha=\arctan(b/a)\),
and using \(d/e\le b/a\), gives

\[
 \frac{d\alpha}{db}
 =\frac{a+b(d/e)}{a^2+b^2}\le\frac1a<\frac95.              \tag{6}
\]

The final inequality follows from
\(a\ge c_C>5/9\). Also the circle equation gives

\[
 \frac7{12}-a=\frac1{12}-e
 =\frac{d^2}{1/12+e}\ge6d^2.                                \tag{7}
\]

Starting at the side/corner junction and using (4), (6), and (7),

\[
 \psi_C
 <\frac7{40}+(\frac95-g)d-6Kd^2
 \le\frac7{40}+\frac{(9/5-g)^2}{24K}
 <\frac7{40}+\frac1{300}<\frac9{50}.                       \tag{8}
\]

The penultimate comparison already follows from \(K\ge7\).

For the lower corner bound, the marker increases with \(b\), since
its derivative is \(K(d/e)+g>0\). Its maximum is therefore
\(K(7/12-c_C)+gc_C\). As \(K>g\) and
\(c_C>67/120\),

\[
 \ell_C<K/40+67g/120
 <8/40+\frac{67}{120}\frac{11}{10}
 =\frac{977}{1200}.                                        \tag{9}
\]

Here \(c_C>67/120\) follows from \(\sqrt2>7/5\).
On this same corner \(\alpha\ge\arctan(6/7)>2/3\): the
lower arctangent partial sum through degree 7 suffices. Consequently

\[
 \psi_C>\frac23-\frac{977}{1200}
 =-\frac{59}{400}>-\frac9{50}.                              \tag{10}
\]

Equations (4), (5), (8), and (10) prove (3).

## 2. The two center rays are separated by more than \(4/3\)

Every core-boundary center has norm less than \(4/5\). On the side
its squared norm is at most \(85/144<16/25\). On the corner use
the triangle inequality in
\((a,b)=(1/2,1/2)+(e,d)\):

\[
 \sqrt{a^2+b^2}\le\frac{\sqrt2}{2}+\frac1{12}<\frac45.
\]

Each unit square contains the open disk of radius \(1/2\) centered
at its center. Thus disjoint square interiors imply center distance
at least one. If the two positive center radii are \(r,s<4/5\),
the cosine law gives

\[
 \cos\delta\le\frac{r^2+s^2-1}{2rs}\le\frac7{32}.          \tag{11}
\]

For the second inequality, the displayed function increases with each
of \(r,s\) when they are below one; substitute \(r=s=4/5\).

The lower cosine Taylor polynomial through degree six gives

\[
 \cos(4/3)>1-\frac{(4/3)^2}{2}
             +\frac{(4/3)^4}{24}-\frac{(4/3)^6}{720}
 =\frac{7709}{32805}>\frac7{32}.                            \tag{12}
\]

If \(0<\delta\le4/3\), monotonicity of cosine on \([0,\pi]\)
contradicts (11)--(12). Hence \(\delta>4/3\), even when the
directed gap was not assumed in advance to be at most \(\pi\).

## 3. Finish without inspecting any separating-axis branch

For every \(\phi\),

\[
 0\le h(\phi)\le\frac{\sqrt2-1}{2}<\frac{21}{100}.
\]

Combining this with (3) and \(\delta>4/3\) gives exactly

\[
 \delta-\frac9{50}h+\psi_C(j)-\psi_C(i)
 >\frac43-\frac9{50}\frac{21}{100}-\frac9{25}
 =\frac{14033}{15000}>\frac{23}{25}.
\]

This proves the entire core/core entry of the proposed four-type table.
The other entries still require their own whole-domain arguments.
\(\square\)
