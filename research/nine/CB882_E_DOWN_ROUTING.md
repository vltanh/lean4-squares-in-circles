# Height and physical-axis routing when E lies below A

This chapter proves necessary conditions on the entire E-below-A
alternative of the original Cb882 caller. It does not impose a small
neighborhood of an optimizer or the local sharp terminal. The final
physical A/E separator has a complete three-case cover.

The chapter does not exclude that alternative. All nine originals,
their independent frames and physical pairs remain in the caller.

Put Q=1105/256 and rho=91/60. Retain the original main and short
links, the Cb882 normalization theta_A>=0, and all the hypotheses
of [the whole-domain localization](CB882_GEOMETRIC_REDUCTION.md).
Corner contacts in the closed Q-disk are allowed. The hypotheses
needed in the estimates below are the already proved bounds

\[
 x_A+h_A+2h_B<\frac1{16},\qquad
 x_A<-\frac{23}{16},\qquad
 \frac12\le h_A<\frac{37}{64},\qquad h_B\ge\frac12,
 \qquad |c_P|<\rho.                                      \tag{1}
\]

Here h_P is the coordinate projection halfwidth of P and
g_P=1/(4h_P) is its actual contained aligned-inset halfwidth.
In particular g_P<=1/2 and g_P>7/20. The first two inequalities
in (1) follow from the original CD insets and the unary inset bound,
then the actual BC and AB links. The bound h_A<37/64 is proved
in [the endpoint-inset chapter](00100_ENDPOINT_INSETS_ARE_VERTICAL.md).

## 1. A whole-parent bound on the upper side of A

**Lemma.** Throughout the stated parent, including both endpoint
height orders,

\[
                         y_A-g_A<-\frac14.             \tag{2}
\]

Write A's canonical frame as u_A=(alpha,beta),
v_A=(-beta,alpha), where alpha>=beta>=0 and
alpha^2+beta^2=1. Put

\[
 h=h_A=\frac{\alpha+\beta}{2},\qquad
 k=\frac{\alpha-\beta}{2}=\sqrt{\frac12-h^2}.
\]

The actual corner c_A+(-u_A+v_A)/2 has coordinates
(x_A-h,y_A+k). The vector (-31,12) has squared norm 1105.
Its support inequality for the closed Q-disk is therefore exactly

\[
                  -31(x_A-h)+12(y_A+k)\le\frac{1105}{16}.
                                                               \tag{3}
\]

Using x_A+h+2h_B<1/16 and h_B>=1/2 in (3) gives

\[
                         12y_A<40-62h-12k.             \tag{4}
\]

For h in [1/2,37/64], consider

\[
 F(h)=62h+12\sqrt{\frac12-h^2}+\frac3h.
\]

On this interval k>=sqrt(679)/64>26/64, so h/k<37/26.
Also 3/h^2<=12. Hence

\[
 F'(h)=62-12h/k-3/h^2
       >62-12\frac{37}{26}-12=\frac{428}{13}>0.
\]

At h=1/2 the value is 43. Since 12g_A=3/h, (4) yields

\[
                   12(y_A-g_A)<40-F(h)\le-3.
\]

This proves (2). In particular g_A<=1/2 gives the useful
whole-parent consequence

\[
                              y_A<\frac14.             \tag{5}
\]

The strict signs in (2) and (5) come from (1), which is strict even
for a closed Q-disk. No strict corner clearance was assumed.

## 2. Consequences on the complete E-below-A alternative

Assume precisely the downward inset order

\[
                         y_A-y_E\ge g_A+g_E.            \tag{6}
\]

The endpoint-inset theorem has already shown that this and its
upward counterpart cover all original A/E pairs. From (2),

\[
                   y_E<-\frac14-g_E<-\frac35.          \tag{7}
\]

If x_E<=-7/5, then (7) would imply

\[
 |c_E|^2>\left(\frac75\right)^2+
              \left(\frac35\right)^2
          =\rho^2+\frac{71}{3600},
\]

contrary to (1). Therefore x_E>-7/5. Define the actual center
differences toward E by

\[
                  d=x_E-x_A,\qquad k_0=y_A-y_E.
\]

The lower bound for x_E and (1), followed by the complete
endpoint-inset lemma, give

\[
             \frac3{80}<d<g_A+g_E\le1,
             \qquad k_0\ge g_A+g_E>0.                 \tag{8}
\]

There is also a useful bound in the diagonal direction. By (1)
and (5), x_A+y_A<-19/16. Cauchy--Schwarz and the center disk
give x_E+y_E>-rho sqrt(2). The rational comparison

\[
       \left(\frac{13}{6}\right)^2-2\rho^2
                         =\frac{169}{1800}>0
\]

therefore proves

\[
 k_0-d=(x_A+y_A)-(x_E+y_E)
       <-\frac{19}{16}+\frac{13}{6}=\frac{47}{48}.      \tag{9}
\]

These are consequences of the complete alternative (6), with no
new height ordering involving C, G, H or I.

## 3. All physical A/E axes reduce to three cases

The original physical pair A,E has an actual owned signed side-axis
normal n pointing from A toward E, with

\[
                     n\cdot(d,-k_0)\ge R_{AE}\ge1.     \tag{10}
\]

First, a unit normal n=(n_x,n_y) with n_y>=0 cannot satisfy
(10): by (8),

\[
                  n_xd-n_yk_0\le d<1.                 \tag{11}
\]

Second, a downward-left canonical primary normal has the form
n=(-a,-b), with a>=b>=0. If b=0 its projection is negative.
If b>0, equations (8)--(9) give

\[
 -ad+bk_0=b(k_0-d)-(a-b)d
                       <\frac{47}{48}b\le\frac{47}{48}<1.
                                                               \tag{12}
\]

Such a normal also cannot satisfy (10).

For A the tilt is nonnegative. Its normals +u_A and +v_A
have nonnegative vertical component, while -u_A is a primary
normal of the form excluded by (12). Thus its only remaining
normal is -v_A.

For E with nonnegative tilt, the same argument leaves only -v_E.
For E with nonpositive tilt, the normals with negative vertical
component are +u_E and -v_E. Its other two signed axes have
nonnegative vertical component and are excluded by (11).
The zero-tilt primary normal is horizontal and therefore impossible;
retaining that empty endpoint in a closed case does not remove any
physical configuration.

Consequently the following is a complete cover of the original
physical A/E separator in (6):

| Actual owner | Normal toward E | Required orientation restriction |
|---|---|---|
| A | -v_A=(beta_A,-alpha_A) | Already theta_A>=0 |
| E | -v_E=(beta_E,-alpha_E) | Either canonical sign |
| E | +u_E=(alpha_E,beta_E) | theta_E<=0 |

The owned inequalities are, respectively,

\[
 \beta_A d+\alpha_A k_0\ge R_{AE},\qquad
 \beta_E d+\alpha_E k_0\ge R_{AE},\qquad
 \alpha_E d-\beta_E k_0\ge R_{AE}.                    \tag{13}
\]

Each line uses the same two original squares and their actual frame
components. Both original owners are retained. The cases may overlap;
the cover requires completeness, not uniqueness.

## 4. Continuation boundary

For a finite hand table, (2) is the whole-parent affine row
y_A-g_A<=-1/4. On the entire downward alternative, (7)--(9)
can likewise be weakened to closed rational rows. The three roots
in Section 3 can replace the eight general signed A/E owner-axis
roots, provided the primary E root retains theta_E<=0.

No contradiction for all three roots is supplied here. In particular
the chapter does not yet prove E above A, the full local sharp guard,
or emptiness of the whole Cb882 original.
