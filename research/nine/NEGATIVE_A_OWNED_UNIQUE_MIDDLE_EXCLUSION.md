# Complete side-owned negative endpoint exit when the unique middle owns AB

**Status: complete continuous-domain hand exclusion; root and separate independent full source, geometry and exact audits passed.** Work with the same selected physical certificate and the original forces, applications, shared means, physical masks, and completion squares.

In the actual ABC attachment let A and B be physically unique boundary squares with true positive pair-degree two and positive circle loads. C physically touches the circle and has its actual positive return contact with H. H retains its true degree four and intact loaded HXY petal. Assume \(c_H\cdot z_A<0\).

**Theorem.** The entire family in which HA is an A-owned singleton is impossible on
\[
                       79/40\le R\le\sqrt{1105}/16.
\]
More generally, the same conclusion holds for an A-owned HA of either length whenever the actual AB normal is B-owned. Every original HA shared mean is retained in this conditional extension.

The high-radius part \(R^2\ge17/4\) is already excluded by NEGATIVE_UNIQUE_ENDPOINT_TIP_OWNED_HIGH_RADIUS.md. We prove the complete remaining lower interval. The proof uses the exact return reduction in NEGATIVE_A_OWNED_UNIQUE_MIDDLE_RETURN_DOMAIN.md and then shows that no physically loaded C can own its remaining BC contact.

## 1. The original B concurrence fixes the remaining BC direction

Set \(q=R^2,\ q_0=(79/40)^2\), and use the frame and notation of the return reduction:
\[
 \begin{gathered}
 q_0\le q<17/4,\quad x=a-1,\quad
 \frac34<x<\frac{13}{16},\quad
 \frac{79}{100}<b<\frac9{10},\\
 T=(x,b),\quad g=(-u,v),\quad f=(v,u),\\
 0<u<\frac18,\quad v>\frac{99}{100},\quad u^2+v^2=1,\\
 h=T\cdot g,\quad L=T\cdot f,\quad
 \frac23<h<x,\quad L>\frac{297}{400},\\
 0<k<\frac15,\quad \delta=1-k,\quad \beta=L+k,\\
 B=T+[0,1]g+[-\delta,k]f,\qquad
 P=T-\delta f.
 \end{gathered}
\tag{1}
\]
Here P is the actual BC singleton, and its normal is C-owned. The actual B concurrence is
\[
 q_B=T+\varepsilon g,\qquad
 \varepsilon=\frac{L-hk}{L+k}
             =1-\frac{k(h+1)}{\beta},
 \qquad\frac59<\varepsilon<1.
\tag{2}
\]
Every quantity in (1)--(2) is the original physical one. In particular the true B force and moment equations force the BC line through q_B and P. The normal from B into C therefore points along
\[
                      P-q_B=-\varepsilon g-\delta f.
\]
This sign also follows from the strict negative g and f components already proved in the return reduction. Define
\[
 \chi=\frac{\varepsilon}{\delta},\qquad
 e=\frac{\chi g+f}{\sqrt{1+\chi^2}},\qquad
 j=Je=\frac{g-\chi f}{\sqrt{1+\chi^2}}.
\tag{3}
\]
Thus the actual normal from C into B is e, and e is an axis of C. C lies on the side \(e\cdot X\le e\cdot P\). No C force equation or C mask assumption has been used.

## 2. The entire remaining normal interval is 3/4<chi<1

First,
\[
 \beta=xv+bu+k
       <\frac{13}{16}+\frac9{80}+\frac15
       =\frac98.
\tag{4}
\]
Since \(h>2/3\), we have \(h+1>\beta\). The exact identity
\[
                    \delta-\varepsilon
                    =\frac{k(h+1-\beta)}{\beta}>0
\tag{5}
\]
gives \(\chi<1\).

For the other endpoint, direct expansion of (2) gives
\[
 \beta(4\varepsilon-3\delta)
      =L+k(3L-4h-3)+3k^2.
\]
Using \(L>297/400\), \(h<13/16\), and \(0<k<1/5\), the right side is greater than
\[
 F(k)=\frac{297}{400}-\frac{1609}{400}k+3k^2.
\]
On the entire interval \(0\le k\le1/5\),
\[
 F'(k)\le-\frac{1129}{400}<0,\qquad
 F(1/5)=\frac{29}{500}>0.
\]
Hence \(4\varepsilon>3\delta\), and
\[
                              \frac34<\chi<1.
\tag{6}
\]

## 3. Uniform coordinates of the actual C side application

Put
\[
 \alpha=P\cdot e
        =\frac{\chi h+\beta-1}{\sqrt{1+\chi^2}},
 \qquad
 \ell=P\cdot j
      =\frac{h-\chi(\beta-1)}{\sqrt{1+\chi^2}}.
\tag{7}
\]
We prove, throughout the full domain,
\[
                         \frac14<\alpha<\frac34,
                         \qquad 0<\ell<\frac45.
\tag{8}
\]

For the upper bound on alpha, (1), (4), and (6) give
\[
 \chi h+\beta-1<\frac{13}{16}+\frac18=\frac{15}{16},
 \qquad \sqrt{1+\chi^2}>\frac54.
\]
Therefore \(\alpha<3/4\).

For its lower bound, retain the original coupled coordinate inequality
\[
                  x+b=a+b-1>\frac{2q}{3}-1
                       \ge\frac{3841}{2400}.
\tag{9}
\]
Also \(b-x>-9/400\). By \(3/4<\chi<1\),
\[
 \begin{split}
 x+\chi b
 &=\chi(x+b)+(1-\chi)x\\
 &>\frac34+\chi\left(\frac{3841}{2400}-\frac34\right)
 >\frac{4441}{3200}.
 \end{split}
\]
The numerator in (7) has the exact form
\[
 \chi h+\beta-1
   =v(x+\chi b)+u(b-\chi x)+k-1.
\]
Here \(b-\chi x>b-x>-9/400\), \(u<1/8\), and \(k>0\), so
\[
 \chi h+\beta-1
 >\frac{99}{100}\frac{4441}{3200}
      -\frac9{3200}-1
 =\frac{118759}{320000}.
\]
Since \(\sqrt{1+\chi^2}<\sqrt2<10/7\),
\[
 \alpha>\frac{831313}{3200000}
        =\frac14+\frac{31313}{3200000}>\frac14.
\tag{10}
\]

For ell, (4) and \(0<\chi<1\) imply
\[
 h-\chi(\beta-1)>h-\frac18>0.
\]
For its upper bound use \(h<x\) and \(\beta>L>xv>(99/100)x\):
\[
 \begin{split}
 \ell
 &<\frac{x+\chi\{1-(99/100)x\}}{\sqrt{1+\chi^2}}\\
 &<\frac{13/16+(313/1600)\chi}{\sqrt{1+\chi^2}}
   =:\Psi(\chi).
 \end{split}
\]
The second inequality uses \(1-(99/100)\chi>0\). On the entire interval \(\chi\ge3/4\),
\[
 \Psi'(\chi)
 =\frac{313/1600-(13/16)\chi}{(1+\chi^2)^{3/2}}<0.
\]
Thus
\[
                     \ell<\Psi(3/4)
                           =\frac{6139}{8000}
                           <\frac45,
\tag{11}
\]
with exact reserve \(261/8000\). This proves (8).

## 4. Every C corner is strictly inside the circle

C owns the BC normal e from C toward B. Its support side through the actual point P has e coordinate alpha. Hence every C corner has e coordinate either alpha or alpha-1. By (8), both have absolute value strictly less than \(3/4\).

Its j-coordinate interval has length one and contains the original value ell. Consequently every C point has j coordinate between ell-1 and ell+1. Since \(0<\ell<4/5\), every C corner has j coordinate of absolute value strictly less than \(9/5\). No side offset or endpoint is omitted.

Every corner W of C therefore satisfies
\[
 |W|^2<
 \left(\frac34\right)^2+\left(\frac95\right)^2
 =\frac{1521}{400}
 <\frac{6241}{1600}=q_0\le q,
\tag{12}
\]
where the final strict reserve is \(157/1600\). This makes C physically circle-clear, contradicting its physical boundary mask. It excludes both unique and radial C, independently of every individual circle weight and every HC owner or original shared mean.

## 5. Singleton and shared HA scope

For an A-owned singleton HA, the already selected fixed-tip theorem at A forces the strict northwest AB edge to be B-owned. Sections 1--4 therefore close the complete lower-radius family; the existing high-radius theorem supplies the remaining radii.

The same proof applies if HA is genuinely shared and AB is actually B-owned. In the return reduction, singleton HA was used to obtain that B ownership and to identify Q as an H vertex. Once B ownership is supplied as an actual hypothesis, all subsequent estimates use only the unchanged endpoint concurrence and the support inequality \(H\subset\{y\le b-1\}\). Its bound \(Q\cdot z_A<(a+b)/2\) was already proved for every shared mean in NEGATIVE_UNIQUE_ENDPOINT_OWNED_CONTACT_DOMAIN.md. The proof never uses an H vertex after that statement. Thus all HA means remain unchanged, and the same B frame, full outgoing feature exclusion, and C corner contradiction apply.

This does not remove an actual free AB in the shared-HA case. It closes exactly the B-owned AB branch, as well as every A-owned singleton HA. True degree two at A and B is essential; no middle degree-three transfer is asserted. The actual H return was used in the preceding outgoing-feature proof, and every H petal force and completion square remains. No HB chord, force deletion, new post-extraction selection, sampled pose, numerical angle partition, compilation, or CI is used.
