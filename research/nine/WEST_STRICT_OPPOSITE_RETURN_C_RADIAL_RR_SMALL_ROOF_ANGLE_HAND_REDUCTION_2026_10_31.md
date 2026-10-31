# The C-radial opposite return forces every radial/radial survivor below sin(alpha)=1/6

Date: October 31, 2026 UTC.

**Status: complete hand reduction on the entire original stated chart.**
For every original opposite-return C-radial configuration with
`sin(alpha)>=1/6`, the exterior aperture satisfies `cot(Theta)>5/12`.
The exact radial/radial side bridge forces the strict reverse inequality
in the same-nine radius window. Thus every surviving radial/radial side
case has `sin(alpha)<1/6`. This is a whole continuous comparison, not a
pose check. The complementary small-angle case remains separate.

## 1. Literal physical entry and retained cap

Retain all original nine units, positive graph A--V--D--C--N--B--A
with chord AD, full A3/D3/V2/B2/C2/N2 stars, physical circle masks,
individual nonnegative circle coefficients, actual applications and
means. V is physically radial. The owner and return are the original
West/strict, A-owned perpendicular-singleton, opposite-D-vertex case.
Condition on C physically radial along its original exterior axis.

Use the complete hand chart and definitions in Sections 1--2 of
`WEST_STRICT_OPPOSITE_RETURN_C_RADIAL_ACUTE_APERTURE_AND_UNIQUE_B_COMPLETE_HAND_EXCLUSION_2026_10_31.md`.
In particular

    c=cos(alpha)>3/4, s=sin(alpha)>0,
    0<alpha<pi/4,
    117/125<d<61/60,
    R^2=(d+1)^2+1/4,
    q=(u-v)/b>0,
    B0=d*s+c/2,
    0<t<=1/2, t=m*q*B0,
    phi=atan((s+q)/c),
    Theta=pi/2+atan(m)-phi.

Here q is the original hub force ratio, not cot(Theta). The same-nine
R>2 entry is the printed analytic measure route cited in that source;
no historical numerical measure certificate is a premise.

The actual radial-C support, with its genuine original port retained,
gives

    d<=Dcap(alpha,q),
    W=sqrt(q^2+2*q*(c+s)+2),
    W_C=sqrt(1+2*q*s+q^2),
    Dcap(alpha,q)
      ={[q^2+q*(c+3*s)+2]/W+(q*c)/2}
                                  /[W_C+1+q*s].             (1)

The cited source proves `u-v>8/25`, hence `v<3/5`, directly from
the same actual support. On that entire region Dcap strictly decreases
with alpha and strictly increases with q. Decreasing alpha or increasing
q from an actual case keeps v<3/5, so those comparison paths are valid
throughout. The same source already proves q>1 and Theta<atan(3),
without using either B/N or C/N equation.

## 2. The whole range s>=1/6 has q>123/100

Assume s>=1/6. Were q<=123/100, the complete cap monotonicities give

    d<=Dcap(alpha,q)
       <=Dcap(arcsin(1/6),123/100).                         (2)

At this one scalar comparison write

    c0=sqrt(35)/6, q0=123/100.

Every terminating decimal below is the displayed exact rational. Positive
squaring gives

    .986<c0<.9861,
    W^2=3.9229+2.46*c0>6.34846>(2.5196)^2,
    W_C^2=2.9229>(1.709)^2,
    1+q0/6=1.205.                                         (3)

For the first lower bound one may use `5.916^2=34.999056<35`;
for the first upper bound, `.9861^2=.97239321>35/36`.
The other square comparisons are
`(2.5196)^2=6.34838416` and `(1.709)^2=2.920681`.

The numerator in (1) at (2) is

    (4.1279+1.23*c0)/W+.615*c0.

Its first term is strictly less than 2.12, since

    4.1279+1.23*(.9861)=5.340803
                  <2.12*(2.5196)=5.341552.

Its second term is less than `.615*(.9861)=.6064515<.607`.
The denominator in (1) is greater than `1.709+1.205=2.914`.
Thus the entire comparison is

    Dcap(arcsin(1/6),123/100)
        <2727/2914<117/125,                                (4)

where the final exact cross-multiplied reserve is
`2914*117-2727*125=63>0`. Equations (2),(4) contradict the
original d>117/125. Therefore over the whole original range s>=1/6,

    q>123/100.                                             (5)

No root of the original full roof equation has been selected or removed.

## 3. The same complete range has cot(Theta)>5/12

For fixed d, B0 increases strictly with alpha, since its derivative
`d*c-s/2` is positive on the original range. Consequently s>=1/6 gives

    B0>(117/125)/6+sqrt(35)/12>649/1000.                    (6)

The last comparison uses `sqrt(35)>5.916` from (3): the two terms
are greater than .156 and .493 respectively. The original full V
torque, t<=1/2, (5) and (6) imply

    m=t/(q*B0)<50000/79827<627/1000.                       (7)

The final comparison has the positive integer reserve
`79827*627-50000000=51529`.

Also c<=sqrt(35)/6<987/1000 on this entire angle range. Hence

    tan(phi)=(s+q)/c
       >(1/6+123/100)/(987/1000)=4190/2961.                (8)

Let g=tan(phi). The function `(g-m)/(1+g*m)` strictly increases
with g and strictly decreases with m on the present positive domain.
The bounds in (7),(8) in particular give g>m, so
`0<phi-atan(m)<pi/2`. The inequality

    (g-m)/(1+g*m)>5/12

is equivalent to `g*(12-5*m)>5+12*m`. At the respective endpoints
of (7),(8) its exact comparison is

    (4190/2961)*(1773/200)>3131/250.

After multiplying by the positive common denominator and cancelling
50, its numerator reserve is

    4190*1773*5-3131*2961*4
       =37144350-37083564=60786>0.                         (9)

The original exterior-angle identity therefore gives

    cot(Theta)=tan(phi-atan(m))>5/12                        (10)

for every original C-radial configuration with s>=1/6. This local
aperture statement uses no physical radial premise at B or force equation
at N. Their full original equations remain present in the caller.

## 4. The radial/radial side caller, including the parallel means

Now also assume B is physically radial along its original exterior axis
b_ext, and retain the original side transmitter N. The preceding whole
C-radial theorem gives `0<Theta<atan(3)<pi/2` before this split. The
full endpoint cone gives its unchanged direction n in the closed cone
between b_ext and c_ext.

First exclude the two parallel endpoints with the actual means intact.
If n=b_ext, write w=Jrot(b_ext), z=Jrot(c_ext). The actual C/N
application is its strict supporting inner corner

    U=-d*c_ext+(1/2)*z,

whereas the B/N application may be any original shared-side mean

    T=d*b_ext+eta*w, -1/2<=eta<=1/2.

The complete original side identity is T-U=b_ext. Projecting it onto
w gives

    eta=d*sin(Theta)+(1/2)*cos(Theta)>1/2,

because `d>1/2>(1/2)*tan(Theta/2)`. This contradicts the full original
mean interval. At n=c_ext the same calculation with the endpoint roles
exchanged gives the identical contradiction. No mean has been moved to
a vertex in these parallel cases.

The actual side channel is therefore strict. Put delta=Theta/2.
Its actual two radial inner corners have difference

    T-U=d*(b_ext+c_ext)
                    +(Jrot(b_ext)-Jrot(c_ext))/2.

This is a positive multiple of the angle bisector. Since the original
side length is one, it gives exactly

    2*d*cos(delta)-sin(delta)=1,
    r=tan(delta)=d-1/(4*d).                                (11)

The positive solution follows by substituting the usual half-angle
formulas or by squaring `2*d=sqrt(1+r^2)+r`; all quantities are positive.
The map d -> d-1/(4d) strictly increases. Already at d=117/125 its
value is

    39131/58500>2/3,

with numerator reserve `117393-117000=393` after multiplying by 3.
Thus every actual radial/radial side has r>2/3. Since it is acute,
r<1 and

    cot(Theta)=(1-r^2)/(2*r)<5/12.                          (12)

The last function strictly decreases with r, and its value at 2/3 is
5/12. Equations (10),(12) are incompatible whenever s>=1/6.

Therefore the entire original radial/radial side feature, including
both former parallel-mean endpoints, has the necessary strict bound

    sin(alpha)<1/6.                                       (13)

The remaining smaller-angle cases are not excluded by this manuscript.
All original stars, physical circle vertices, individual coefficients,
side means, contact geometry and completing squares are retained. Every
comparison is a displayed continuous derivative or exact rational
calculation. No external proof script, Lean or CI is involved, and no
original ledger flag changes for this reduction alone.
