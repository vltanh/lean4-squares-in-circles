# An adjacent port and an arbitrary original shared mean force the radial right-turn family

Date: October 26, 2026.

**Status: complete analytic physical-subfamily proof, accepted after root
and separate independent saved-source and physical-scope reviews.** See
REVIEW_C6_RADIAL_MEAN_FAMILIES_ROOT_2026_10_26.md and
REVIEW_C6_RADIAL_ADJACENT_MEAN_AND_SMALL_RATIO_2026_10_26.md.
The new scalar input is
[SIX_CYCLE_RADIAL_MEAN_DERIVATIVE_SMALL_RATIO.md](SIX_CYCLE_RADIAL_MEAN_DERIVATIVE_SMALL_RATIO.md).
No numerical or finite coefficient certificate is a premise.

Work in the same original radius window and alternating all-side C6
as
[SIX_CYCLE_ONE_RADIAL_TWO_SHARED_MEANS_STRICT_TURN_CLASSIFICATION.md](SIX_CYCLE_ONE_RADIAL_TWO_SHARED_MEANS_STRICT_TURN_CLASSIFICATION.md):
one physical two-circle-corner loaded unit S, two physical-unique
loaded units B,C, three actual unloaded degree-two side transmitters,
and three remaining physical squares. Retain all original forces,
both radial corner weights, every actual mean, and all three sliders.

The premises of this source are:

* \(\theta_B,\theta_C>\pi/2\);
* one original S-incident application is the actual vertex adjacent
  to its unique circle corner;
* the other original S-incident interface is a genuine shared side,
  with its full actual mean.

The adjacent application may itself be a genuine mean already at
that vertex. The arbitrary shared mean is not moved to an endpoint.

**Theorem.** The core belongs to the complete right-turn family,
\(\theta_S=\pi/2\) and \(R^2=5/2+\sqrt2\). The accepted full
three-slider completion theorem then excludes three extra squares.
Thus its strictly obtuse radial-turn part is impossible as a core.

## 1. The two actual endpoint charts share the same parameters

The unconditional local upper-turn theorem gives
\(\theta_S\ge\pi/2\). Its equality case already has the complete
classification and completion exclusion. Consider the branch
\(\theta_S>\pi/2\).

The same strict-turn owner cover used in the two cited classification
sources forces both B-to-C applications to be the actual opposite
vertices. Its transmitter has no loaded-side-axis owner at either
end. Normalize it as

\[
 T_B=(l,H),\quad T_C=(l+1,H),\quad H>0.
\tag{1}
\]

For either endpoint use the left chart, with reflection at C:

\[
 c=\cos\eta,\quad s=\sin\eta,\quad
 \frac\pi4\le\eta<\frac\pi2,\quad
 v=(-c,s),\quad u=(-s,-c),
\]
\[
 D=s-c,\quad C=s+c,\quad Z=H+D,\quad
 A=\sqrt{R^2-Z^2}>0,\quad t=D/Z,
\]
\[
 z=(-A,Z)=av+bu,\quad
 a=cA+sZ,\quad b=sA-cZ,\quad
 T=(-A+C,H).
\tag{2}
\]

The actual physical domain gives \(a,b>1/2\), and properness gives
\(\lambda=C-tA>0\), hence

\[
 a-b=Z\lambda>0,\qquad 1-ta=c\lambda>0.
\tag{3}
\]

All these statements are the actual local charts proved in
Sections 1--3 of
[SIX_CYCLE_ONE_RADIAL_BOTH_ADJACENT_PORTS_CLASSIFICATION.md](SIX_CYCLE_ONE_RADIAL_BOTH_ADJACENT_PORTS_CLASSIFICATION.md)
and Sections 1--2 of the two-mean classification. Their local
derivations use only the feature at the endpoint in question and
the opposite-vertex channel at the other end, which both hold here.
They do not require the other endpoint to have the same feature.

For the actual adjacent port, denoted A below,

\[
 Q_A=z-v,\qquad
 V=v-tz=(tA-c,c),\quad L=|V|>0,\qquad
 P_A=Q_A-\frac VL,\qquad F_A=|P_A|^2.
\tag{4}
\]

For the actual shared mean, denoted M,

\[
 \ell=1-tb\in(0,1],\quad
 Q_M=T+\ell u,\quad
 P_M=Q_M-v=(a-2)v+(1-t)b\,u,
\]
\[
                         F_M=(a-2)^2+(1-t)^2b^2.
\tag{5}
\]

Both actual radial ports have the unchanged norm

\[
                 F_A(\eta_A)=F_M(\eta_M)
                     =r_0^2:=d^2+\frac14,
 \qquad d=\sqrt{R^2-\frac14}-1.
\tag{6}
\]

The common B-to-C reserve is

\[
                        A_A+A_M=1+C_A+C_M.
\tag{7}
\]

## 2. A mean-port root bounds the common channel height

The pointwise mean-root proof in Section 3 of the two-mean
classification applies directly to the single endpoint M in (5).
It only uses that endpoint's actual norm (6), not a second mean.
It gives

\[
 a_M<\frac{211}{120},\qquad b_M>a_M/2,\qquad
                         \eta_M<\frac\pi3.
\tag{8}
\]

In addition,

\[
 b_M^2>\left(\frac{79}{40}\right)^2
                 -\left(\frac{211}{120}\right)^2
              >\left(\frac{89}{100}\right)^2,
\tag{9}
\]

where the last squared reserve is \(1511/90000>0\).
The inverse coordinate relation in (2) gives

\[
                 H=Z-D=(a_M-1)s+(1-b_M)c.
\tag{10}
\]

Here \(a_M>4/3\). If \(b_M\ge1\), (10) gives
\(H<a_M-1<91/120<4/5\). If \(b_M<1\), both coefficients
in (10) are positive, and Cauchy's inequality gives

\[
 H^2\le(a_M-1)^2+(1-b_M)^2
       <\left(\frac{91}{120}\right)^2
           +\left(\frac{11}{100}\right)^2
       <\left(\frac45\right)^2.
\tag{11}
\]

The final reserve is \(19019/360000>0\). Thus, uniformly,

\[
                               0<H<\frac45.
\tag{12}
\]

## 3. The common reference angle is in the full comparison domain

Fix the actual R,H and define the reference angle \(\eta_0=\pi/4\).
Use a subscript 0 for (2) at this angle. Then

\[
 D_0=t_0=0,\quad Z_0=H,\quad C_0=\sqrt2,\quad
 A_0=\sqrt{R^2-H^2},
\]
\[
                a_0=\frac{A_0+H}{\sqrt2},\qquad
                b_0=\frac{A_0-H}{\sqrt2}.
\tag{13}
\]

The reference is a scalar comparison point, not a replacement of
the actual configuration. Equation (12) and the radius window give

\[
 A_0>\frac95,\qquad b_0>\frac1{\sqrt2}>\frac12,
\tag{14}
\]

since
\[
 \left(\frac{79}{40}\right)^2
      -\left(\frac45\right)^2-\left(\frac95\right)^2
                        =\frac{33}{1600}>0.
\]

Also \(R<133/64\), and therefore

\[
 a_0^2=\frac{R^2}{2}+HA_0
       <\frac{1105}{512}+\frac45\frac{133}{64}
       =\frac{9781}{2560}<4.
\tag{15}
\]

Thus \(a_0<2\). Properness and all required positive denominators
hold at \(\eta_0\), where \(\lambda=C_0>0\).

Both formulas (4)--(5) have the identical value at this reference:
since \(t_0=0\), \(L_0=1\), and \(V_0=v_0\),

\[
 P_{A,0}=P_{M,0}=z_0-2v_0,\qquad
 F_{A,0}=F_{M,0}=:F_0.
\tag{16}
\]

## 4. The mean norm decreases from the reference to its actual root

Consider the whole interval \([\pi/4,\eta_M]\) at fixed R,H.
The connected-domain proof from the two-mean source applies with
one endpoint replaced by (13). Specifically, D increases;
\(0<Z<R\) persists; and

\[
 \lambda>0\quad\Longleftrightarrow\quad
                  H>D(R/\sqrt2-1)
\tag{17}
\]

persists from its actual upper endpoint. Hence \(a>b\), and
\(a=cA+sZ>0\). The identities

\[
 (A-C)'<0,\qquad b'=a(1-C/A),\qquad a'=-b(1-C/A)
\tag{18}
\]

first give the endpoint minimum of b, and then the endpoint maximum
of a. By (8), (14), and (15), throughout this interval

\[
 \frac43<a<2,\qquad b>\frac12,\qquad
                 0<\frac ba<1,\qquad \frac47<\frac cs\le1.
\tag{19}
\]

The lower bound on a uses \(a>b\) and \(R\ge79/40\);
the bound on \(c/s\) uses \(\eta_M<\pi/3\).

The exact derivative identity is

\[
 F_M'=2b\left[
 (1-C/A)\{2-a(2t-t^2)\}
                  -\frac{HC}{Z^2}(1-t)b\right].
\tag{20}
\]

With \(u_0=c/s\), \(r=b/a\), this is the same scalar bracket
as the two complementary analytic derivative sources. On \(r\ge1/2\),
use
[SIX_CYCLE_RADIAL_TWO_MEAN_DERIVATIVE_ANALYTIC.md](SIX_CYCLE_RADIAL_TWO_MEAN_DERIVATIVE_ANALYTIC.md).
On \(r\le1/2\), use
[SIX_CYCLE_RADIAL_MEAN_DERIVATIVE_SMALL_RATIO.md](SIX_CYCLE_RADIAL_MEAN_DERIVATIVE_SMALL_RATIO.md).
Their complete hypotheses follow from (19); both cover \(r=1/2\).
Thus

\[
                              F_M'<0
\tag{21}
\]

on the whole interval. In particular

\[
              r_0^2=F_M(\eta_M)\le F_0,
\tag{22}
\]

with equality only if \(\eta_M=\pi/4\).

## 5. The adjacent norm increases from the same reference

For the other endpoint, (7), \(C_M\ge1\), and \(A_M<R\) give

\[
                    A_A-C_A>2-R>-\frac5{64}.
\tag{23}
\]

The pointwise norm-root argument in Section 4 of the both-adjacent
classification uses only its adjacent port, its norm (6), and
this lower bound. It therefore gives

\[
                              c_A>\frac14
\tag{24}
\]

for the present endpoint, without any assumption that its neighbor
has an adjacent port.

On the whole interval \([\pi/4,\eta_A]\), the same connected-domain
argument gives \(Z<R\), \(\lambda>0\), \(a>b\), and \(a>0\).
Equation (18) and the endpoint bounds \(b_0>1/2,\ b_A>1/2\)
give \(b>1/2\) throughout. Since \(A-C\) decreases, (23) persists,
and (24) gives \(c>1/4\) throughout.

These are exactly the hypotheses of the local derivative calculation
in Sections 5--6 of the both-adjacent source:

\[
 F_A'=\frac{2b}{L^3}
 \left[(1-C/A)\mathcal C+
                       \frac{HC}{Z^2}(1-t)b\right],
\]
\[
 \mathcal C=L^3+tL^2+(1-t)(1-ta)>0.
\tag{25}
\]

For clarity, the hypotheses imported there are the original radius
window, \(H>0\), \(0\le t<1\), \(a>b>1/2\),
\(1-ta>0\), \(c\ge1/4\), and \(A-C>-5/64\).
Each has just been proved on the entire comparison interval.
That local scalar proof has no requirement that either endpoint of
the interval be another actual adjacent-port root.

If \(A\ge C\), (25) is immediately positive. If \(A<C\), the
accepted proof uses elementary concavity to obtain \(c<1/2\);
its uniform estimates make the bracket greater than
\(2083/309750>0\). Thus

\[
                              F_A'>0
\tag{26}
\]

on the whole interval, and

\[
              r_0^2=F_A(\eta_A)\ge F_0,
\tag{27}
\]

with equality only if \(\eta_A=\pi/4\).

## 6. The full original mixed feature family closes

Equations (22) and (27) force equality throughout:

\[
                \eta_A=\eta_M=\pi/4,\qquad F_0=r_0^2.
\tag{28}
\]

Both reconstructed actual S-outward normals are therefore the two
reflected \(45^\circ\) axes, which are perpendicular. The actual
radial turn is \(\theta_S=\pi/2\), contradicting the strictly
obtuse branch. At the retained equality endpoint, the genuine mean
has its original value \(\ell=1\); it has not been converted into
a singleton interface.

The complete classification in
[SIX_CYCLE_ONE_RADIAL_RIGHT_TURN_CLASSIFICATION.md](SIX_CYCLE_ONE_RADIAL_RIGHT_TURN_CLASSIFICATION.md)
and the entire completion domain in
[SIX_CYCLE_ONE_RADIAL_RIGHT_ANGLE_FAMILY_COMPLETION.md](SIX_CYCLE_ONE_RADIAL_RIGHT_ANGLE_FAMILY_COMPLETION.md)
now give the stated radius and exclude three extra units with every
original slider. This proves the theorem.

## 7. Exact consequence for the full strict-turn owner cover

Consider any one-radial all-side alternating C6 with all three turns
greater than \(\pi/2\). At each unique load its actual S-incident
port has the exhaustive local alternatives:

* the actual adjacent-to-circle vertex;
* a genuine shared mean on the inner side;
* the actual opposite-to-circle vertex.

Indeed, without a loaded-axis owner the two ports are the two inner-side
vertices. If S owns the unique loaded-axis interface, its original
port is a genuine mean and the B-to-C port is opposite. If the
B-to-C channel owns that axis, the S-incident port is opposite.
The endpoint overlap between the first two alternatives is retained.
No arbitrary shared mean at an endpoint is assigned a new label.

If neither S-incident application is an actual opposite vertex,
the pair is covered by exactly one of the following existing
whole-family conclusions, allowing their harmless endpoint overlap:

| Actual pair | Complete source |
| --- | --- |
| Adjacent / adjacent | The both-adjacent classification, including its full right-turn completion join |
| Adjacent / genuine mean | Sections 1--6 of this source |
| Genuine mean / genuine mean | The two-shared-means strict-turn classification |

All three exclude the strictly obtuse branch. Consequently every
surviving strict-turn one-radial core must have **at least one actual
S-incident application equal to its unique neighbor's opposite
circle-corner vertex**.

This is a reduction of the full local feature cover on the stated
strict-turn domain. Cases with one unique turn at most \(\pi/2\),
and the strict-turn opposite-vertex alternatives, remain explicit
obligations. The unrestricted one-radial parent is not declared closed.
No original square, force, corner weight, physical mask, mean, or
transmitter slider has been removed.
