# Independent review of the radial two-opposite-port nonshared-return exclusion

Date: October 26, 2026.

**Verdict: PASS for the complete stated physical core subfamily.** Reviewed
`SIX_CYCLE_ONE_RADIAL_TWO_OPPOSITE_PORTS_SINGLETON_CHANNEL_EXCLUSION.md`
end to end, including its current saved correction to the circle-branch
proof order. The theorem excludes two actual S-incident opposite vertices
when both unique turns are strictly greater than 90 degrees and the
B-to-C transmitter has no genuinely shared endpoint. The other owner
and lower-turn placements are not included.

## 1. Original feature chart and the corrected branch order

The strict-turn local cover gives an adjacent B-to-C vertex at each
unique body, since the actual S-incident port is opposite and the
return-channel interface is nonshared. These are strict loaded-vertex
features. The actual force polygon gives H>0 and the proper radial
concurrences on the original return-channel line. The radial square
retains its two actual distinct inner vertices and their common norm.

In the initial source, the negative circle-corner branch was justified
by saying the corner lay farther left than its center before c>s had
been established. In this adjacent-return chart that displacement is
(s−c)/2, so this proof order needed correction. The author applied the
following complete argument before choosing the square root, and I
verified it in the saved source:

- Write z=a v+b u in the actual orthonormal axes, with a,b>1/2.
- Its height is Z=H+s, t=s/Z is in (0,1), and q=(1−t)z has height H.
- The original opposite port Q has height H−c, so V=q−Q is nonzero.
  The actual strict inward vertex normal and properness give X,Y>0
  in V=Xv+Yu, X=1−ta, Y=1−tb.
- The unchanged common moment has the negative sign of det(q,e_x)=−H.
  Since det(v,u)=−1, this gives a>b, hence X<Y.
- The strict unique turn gives G_x<0, or cX>sY. Therefore c>s.
  Consequently z_x=−ca+sb<0.

Only then is A=−z_x>0 defined as the positive circle square root.
This removes the dependency cycle and preserves the original normal,
mean and owner. I recovered all subsequent formulas from this chart:
X=cb/Z, Y=1−sb/Z, 0<sb/Z<sc≤1/2, and
P=Q−V/|V|. In particular all denominator and properness signs used
later follow from original physical quantities.

## 2. Complete local norm-root proof of A>c

Assuming A≤c gives a≤1+(s/c)b≤1+b, hence
0<a−b≤1 and a+b≥sqrt(2R²−1). Since a>b, the physical circle
radius gives a>R/sqrt(2)>1.

The inward normal coefficients satisfy X<Y and cX>sY. Thus
G=sin(phi)v+cos(phi)u with eta<phi<pi/4. The source's lower
bound on Q·G is valid for both signs of b−1: when b≤1 the
linear trigonometric function is strictly increasing, and when b≥1
it is nonnegative and concave. Its minimum is therefore at one of
the endpoints, giving exactly

    Q·G ≥ min{Z−(c+s), (a+b−2)/sqrt(2)}.

The displayed positive-definite square proves
c²+2cs<13/8. Together with c+s<10/7 this yields Z−(c+s)>3/8
under A≤c. The two lower bounds for a+b then prove both alternatives
of a+b+Q·G>2+d. I independently reconstructed all three exact reserves:

    89/1400, 551/1600, 59/250.

Every squared comparison has positive sides. Finally
|P|²=R²+3−2(a+b)−2Q·G is strictly below the actual radial-port
norm R²−2d−1, a contradiction. Thus every actual norm root has A>c,
without a force-ratio bound or a numerical root enclosure.

## 3. Connected interpolation and the original norm derivative

At fixed actual R,H, increasing s preserves 0<Z<R between the actual
endpoint angles. The precise equivalence

    b>0 iff Z>sR iff H>s(R−1)

has positive squaring sides and persists from the larger endpoint
angle. It gives (A−c)'=−b/A<0. Since that larger actual endpoint
has A>c, the whole interval does. The independently checked derivative
identities are

    a'=b(1−c/A), b'=−a(1−c/A), t'=Hc/Z².

Thus a−b increases and stays positive from its smaller actual endpoint.
All X,Y,L signs persist from their exact formulas. No interpolated
packing or altered application is asserted.

For h=a+b, I separately expanded

    L²=2−2th+t²R²,
    J=(1+t)h−tR²−2,
    F_O=R²+3−2h−2J/L.

Differentiation first in h,t gives the source's two partial derivatives.
The brace in the h derivative equals
L³+tL²+(1−t)(2−th)>0, because 2−th=X+Y>0. Substitution of
h'=−(a−b)(1−c/A) yields the exact positive derivative in (29).
Every factor is strict on the full connected interval. Equal actual
radial-port norms therefore force equal original endpoint angles.

## 4. Symmetry uses the actual radial unit chord and circle mask

The true return-channel reserve gives A=c+1/2 after symmetry.
The reconstructed ports have x=1/2+s−k/L, with k/L<1. Thus x>−1/2;
the original radial inner chord of length one selects x=1/2 and excludes
the negative root. It follows that k/L=s and c/L=c, so L=1 and
k=s. Hence tA=c−2s>0, and the scalar ratio u=s/c lies strictly in
(0,1/2), with Z=uA/(1−2u).

The actual two S-outward normals are (-s,c),(s,c), both with positive
vertical component. The physical radial square is therefore below its
horizontal inner side, fixing its port height to y=−d. This gives
H=2c−d and Z=2c+s−d. No radial-concurrence containment is used.

## 5. Exact one-variable circle obstruction

I independently reconstructed the original common circle equation
using A=1/2+c, M=1+c(2+u), c=1/sqrt(1+u²), and d+1=M−Z.
After multiplying by 1+u², I expanded the rational and radical parts
separately by exact polynomial convolution. Both residuals are zero,
giving exactly

    E(u)=−4+9u+8u²+5u³
          +sqrt(1+u²)(−3+8u+5u²).

At U=9/28, the two polynomial values are −2515/21952 and 69/784;
the positive-square reserve for E(U)<0 is 2206960. On 0≤u≤U,
the source correctly separates the sign of the second polynomial:
if it is nonpositive the first polynomial already gives negativity;
if it is positive, monotonicity of all three factors compares to E(U).
This proves u>U without any sampled root or monotonicity assertion
across a changing sign.

The exact radial coordinate d(u) has the stated form. Its first
bracket decreases strictly; if that bracket is nonpositive, d<0 is
already impossible. Otherwise both factors of its product are positive
and decreasing from U to the actual u, while the subtracted fraction
increases. Thus d(u)<d(U)<91/100. I independently checked the final
square reserves 1983/108125 and 101/40000, the latter proving the
contrary original-radius inequality d>91/100. The core is contradicted.

## 6. Accepted physical scope

The right-turn endpoint is handled by the complete accepted
classification, whose actual unique S-incident applications are adjacent,
not opposite. The remaining strictly obtuse branch is excluded directly
by this proof. All original radial corner weights, true transmitter
reserves and sliders, selected normals, physical contacts and remaining
squares are retained.

This accepts the full stated two-opposite/nonshared-return physical
subfamily. A shared B-to-C mean has a different chart and is not frozen
to an adjacent endpoint here. Cases with one unique turn at most 90
degrees also remain explicit. No unrestricted one-radial parent or
larger gate is declared closed. No angle grid, coefficient packet,
Lean compilation, CI or numerical sign premise was used in this audit.
