# E below A forces F above B

Retain the whole original Cb882 caller and assume the downward A/E
inset alternative

\[
                         y_A-y_E\ge g_A+g_E.
\]

Then the original B/F insets satisfy

\[
                         y_F-y_B\ge g_B+g_F.             \tag{1}
\]

Here h_P is the coordinate projection halfwidth of the physical unit
square P, and g_P=1/(4h_P) is its contained aligned-inset halfwidth.
The conclusion follows by excluding the other B/F order with the two
original C/F incircles. No physical frame is identified with another.

## 1. Necessary bounds before choosing the B/F order

Write p=x_C and rho=91/60. The
[whole-domain localization](CB882_GEOMETRIC_REDUCTION.md) and
[inner-frame theorem](00100_INNER_FRAME_AND_DOWNWARD_CONE.md) give

\[
 \frac{29}{60}<p<\frac{57}{80},\qquad
 x_B>-\frac{31}{60},\qquad g_B>\frac{37}{80}.
                                                               \tag{2}
\]

Every original center has norm less than rho, every h_P>=1/2,
and every g_P>7/20. The new
[E-down endpoint bound](CB882_E_DOWN_ENDPOINT.md) is

\[
                          x_E+h_E>-\frac{11}{16}.       \tag{3}
\]

The actual EF and FG links therefore imply

\[
 x_F\ge x_E+h_E+h_F>h_F-\frac{11}{16}\ge-\frac3{16},
 \qquad
 x_F\le x_G-h_F-h_G<\rho-1=\frac{31}{60}.             \tag{4}
\]

Combining (2) and (4) gives

\[
 -\frac1{30}<x_C-x_F<\frac9{10},
 \qquad |x_C-x_F|<\frac9{10}.                          \tag{5}
\]

The [whole-parent G-order theorem](CB882_G_ABOVE_D.md) gives
y_G-y_D>=g_D+g_G. Since y_D-y_C>2/3 and the FG center cone
gives y_G-y_F<=x_G-x_F, it follows that

\[
 \begin{aligned}
 y_F-y_C
 &\ge (y_D-y_C)+g_D+g_G-x_G+x_F\\
 &>\frac23+\frac7{10}-\frac{91}{60}-\frac3{16}
   =-\frac{27}{80}.
 \end{aligned}                                         \tag{6}
\]

These deductions use no B/F height choice.

## 2. The lower B/F order makes C and F overlap

The [complete B/F inset theorem](CB882_BF_VERTICAL.md) shows that
(1) and its downward counterpart exhaust the original B/F pair.
Suppose the downward counterpart holds:

\[
                         y_B-y_F\ge g_B+g_F.             \tag{7}
\]

The BC center cone gives y_B-y_C<=p-x_B. Therefore (2) and (7)
yield

\[
 \begin{aligned}
 y_F-y_C
 &\le p-x_B-g_B-g_F\\
 &<\frac{57}{80}+\frac{31}{60}
       -\frac{37}{80}-\frac7{20}
   =\frac5{12}.
 \end{aligned}                                         \tag{8}
\]

Since 27/80<5/12, (6) and (8) give |y_F-y_C|<5/12.
Together with (5), this implies

\[
 |c_F-c_C|^2
 <\left(\frac9{10}\right)^2+\left(\frac5{12}\right)^2
 =\frac{3541}{3600}<1.
\]

The two original squares C,F each contain an open disk of radius
1/2, so their center distance is at least one. This contradiction
excludes (7), proving (1).

All radius and contact boundaries are retained; the strict coordinate
bounds used above hold even in the closed Q-disk. The argument does
not exclude the remaining E-down, F-above-B alternative.
