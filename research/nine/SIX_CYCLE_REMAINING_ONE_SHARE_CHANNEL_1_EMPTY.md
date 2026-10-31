# The channel between the two nonshared loads has an empty exterior cap

Date: October 26, 2026.

**Status: accepted complete whole-domain hand completion restriction
after independent saved-source and physical-scope reviews in
REVIEW_C6_REMAINING_CHANNEL_1_EMPTY_ROOT_2026_10_26.md and
REVIEW_C6_ONE_SHARE_CHANNEL_1_EMPTY_C6_2026_10_26.md.** For the
remaining canonical all-unique one-share C6, the entire exterior
pocket of channel 1 is empty. The proof covers all original positive
force ratios, shared means, and transmitter positions, including
their physical endpoints. It uses no coefficient certificate,
numerical premise, or angular subdivision.

Retain all nine actual unit squares, the common selected certificate,
every original positive force, the physical unique-corner masks and
actual means, all three original unloaded transmitters and their
true degree-two equations, all three extra squares, and the radius
window

\[
                  K:=79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

The result leaves the central region and exterior pockets 0 and 2
coupled. It does not assume that two exterior extras occupy distinct
pockets or assert a completed three-extra capacity bound.

## 1. The actual nonshared channel and its direction cones

Use the complete residual domain in
`SIX_CYCLE_ONE_SHARE_FULL_ORBIT_COVER_AND_RESIDUE.md`. Its canonical
corner word is \(\chi=(1,1,0)\), and the sole genuine share is
the outgoing interface \(S_0W_0\). Loaded units 1 and 2 are
nonshared, joined by the actual side-normal transmitter \(W_1\).

Use the unchanged notation

\[
 \alpha_i=\theta_i-\pi/2\in(0,\pi/4],\quad
 \sum_i\alpha_i=\pi/2,\quad
 s_i=\cos\alpha_i,\quad c_i=\sin\alpha_i,
\]
\[
 A_i=s_i-c_i,\quad h_i=s_i+c_i,\quad
 n_0=(1,0),\quad n_1=(-c_1,s_1),\quad n_2=(-c_0,-s_0).
\tag{2}
\]

Normalize only the common positive force scale to \((1,p,q)\).
The actual nonshared support directions are

\[
 u_1=\frac{(1+ps_1,1+pc_1)}{|(1+ps_1,1+pc_1)|},
\]
\[
 u_2=\frac{q(-h_0,-A_0)+p(-s_1,-c_1)}
              {|q(-h_0,-A_0)+p(-s_1,-c_1)|}.
\tag{3}
\]

The first positive-vector cone puts \(\arg u_1=\phi\) in
\([\alpha_1,\pi/4]\). The second puts
\(\arg u_2=\pi+\psi\), where

\[
                 \pi/4-\alpha_0\le\psi\le\alpha_1.
\tag{4}
\]

This interval is ordered because \(\alpha_2\le\pi/4\).
Set

\[
        a=\phi-\alpha_1\ge0,\qquad
        b=\alpha_1-\psi\ge0.
\]

Then the complete angular consequence is

\[
                  a+b=\phi-\psi\le\alpha_0\le\pi/4.
\tag{5}
\]

No preferred force ratio is used in these cone bounds.

## 2. Exact circle-corner coordinates and the correct chord branch

Take the actual channel frame with horizontal unit direction
\(n_1\) and outward vertical direction \(N_1=-Jn_1\).
The original ports and reserve-one transmitter equation are

\[
       P_1=p_1^+=(l,H),\qquad
       P_2=p_2^-=(l+1,H),\qquad H>0.
\tag{6}
\]

Here \(H\) is the **actual channel height** above the circle
center, not the trigonometric quantity \(h_1\) from (2).
Positivity and the outward sign in (6) are those of the proper force
polygon and actual channel-cap theorem. The origin has only been
rotated, not translated.

Put \(v_i=-Ju_i\). Since unit 1 has bit one, its actual
unique physical circle corner is \(z_1=P_1+v_1\). Since unit
2 has bit zero, its actual circle corner is \(z_2=P_2+v_2\).
From the angles in (3)--(5), their components in this channel frame
are exactly

\[
       v_1=(-\cos a,\sin a),\qquad
       v_2=(\cos b,\sin b).
\]

Consequently

\[
 z_1=(l-\cos a,H+\sin a),\qquad
 z_2=(l+1+\cos b,H+\sin b),\qquad |z_1|=|z_2|=R.
\tag{7}
\]

Both corner heights are positive, because \(H>0\) and
\(a,b\ge0\). This explicitly fixes the positive midpoint
branch in the following calculation.

Write

\[
 m=(a+b)/2\in[0,\pi/8],\qquad
 t=(a-b)/2,\quad |t|\le m,
\]
\[
 C=\cos m,\quad S=\sin m,\quad
 U=1+2C\cos t>0,\qquad V=-2C\sin t,
\]
\[
                    D=|z_2-z_1|=\sqrt{U^2+V^2}.
\tag{8}
\]

The midpoint of two points on the centered circle is perpendicular
to their chord and has norm \(\sqrt{R^2-D^2/4}\). Its vertical
coordinate is \(H+S\cos t>0\); the upward unit perpendicular
has vertical component \(U/D\). Hence the exact identity is

\[
            H=\frac UD\sqrt{R^2-D^2/4}-S\cos t.
\tag{9}
\]

In particular no negative midpoint branch or unproved choice of the
minor exterior arc is hidden in (9).

## 3. A uniform lower height from the whole angular domain

The chord formula in (8) gives

\[
 D^2=1+4C^2+4C\cos t\le(1+2C)^2\le9<4R^2.
\tag{10}
\]

Also, with \(\sigma=1/\sqrt2\),

\[
 \frac{|V|}{U}
 \le\frac{2C\sin m}{1+2C\cos m}
 \le\frac{\sigma}{2+\sigma}
 <\frac3{11}<\frac7{24}.
\]

Here \(m\le\pi/8\) gives \(2C\sin m\le\sigma\)
and \(1+2C^2\ge2+\sigma\); the strict comparison uses
\(\sigma<3/4\). Thus

\[
                              \frac UD>\frac{24}{25}.
\tag{11}
\]

Combining (9)--(11) and \(S\cos t\le S\), we obtain

\[
 H>F_R(m):=\frac{24}{25}
          \sqrt{R^2-(1/2+\cos m)^2}-\sin m.
\tag{12}
\]

This lower bound decreases throughout \(0\le m\le\pi/8\).
Indeed

\[
 F_R'(m)=\frac{24}{25}
 \frac{(1/2+\cos m)\sin m}
      {\sqrt{R^2-(1/2+\cos m)^2}}-\cos m<0.
\]

For a direct whole-interval estimate, its radical denominator exceeds
\(5/4\), because

\[
                 K^2-9/4-25/16=141/1600>0.
\]

Moreover \(\sin m<2/5\) and \(\cos m\ge\sigma>7/10\).
The positive term of the derivative is therefore less than
\((3/2)(2/5)/(5/4)=12/25<7/10\), proving the strict sign.

Use the fixed elementary estimates
\(\cos(\pi/8)<37/40\) and \(\sin(\pi/8)<39/100\).
For the former, the squared comparison reduces to
\(400\sqrt2<569\), with squared reserve \(3761\).
For the latter, \(\sqrt2>7/5\) implies
\(\sin^2(\pi/8)<3/20<(39/100)^2\), with final reserve
\(21/10000\). Therefore (12) gives

\[
 H>\frac{24}{25}\sqrt{R^2-(57/40)^2}-\frac{39}{100}.
\tag{13}
\]

## 4. The lower height exceeds the exact whole-unit cap threshold

The exact contained-unit support threshold is

\[
                         d_R=\sqrt{R^2-1/4}-1.
\tag{14}
\]

Every whole unit square contained in the disk and in an outward
half-plane of height \(h\) requires \(h\le d_R\), by the
sharp support bound in `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md`,
Section 1, also used in `SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md`.
This bound covers every orientation of the additional square and
does not assume it carries a positive circle multiplier.

Define the difference between (13) and (14):

\[
 g(R)=\frac{24}{25}\sqrt{R^2-(57/40)^2}
                  +\frac{61}{100}-\sqrt{R^2-1/4}.
\]

It increases on the entire radius window. The positive-root
comparison in its derivative is justified by

\[
 (57/40)^2-\frac{144}{625}
                  -\frac{49}{625}R^2
 \ge\frac{233891}{160000}>0,
\tag{15}
\]

where the right side substitutes \(R^2=1105/256\). This is
exactly the squared condition
\((24/25)^2(R^2-1/4)>R^2-(57/40)^2\), so \(g'(R)>0\).

At the lower endpoint,

\[
 g(K)=\frac{12}{125}\sqrt{187}+\frac{61}{100}
                                      -\frac{\sqrt{5841}}{40}.
\]

The two fixed radical bounds
\(\sqrt{187}>1367/100\) and
\(\sqrt{5841}<7643/100\) have positive squared reserves
\(1311/10000\) and \(5449/10000\), respectively. Hence

\[
 g(K)>\frac{12}{125}\frac{1367}{100}+\frac{61}{100}
                    -\frac{7643}{4000}
       =\frac{1157}{100000}>\frac1{100}.
\tag{16}
\]

Equations (13)--(16) prove the uniform whole-family bound

\[
                        \boxed{\ H>d_R+1/100.\ }
\tag{17}
\]

## 5. Empty actual pocket and the coupled completion residue

`SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md` places every whole extra
in the actual exterior channel-1 region in
\(D_R\cap\{N_1\cdot x\ge H\}\). By (14) and (17),
no unit square fits in this cap. The **entire actual channel-1
pocket is therefore empty**, including every subdivision by extra
zero-weight physical contacts. No individual circle weight of an
additional square has been assumed positive.

This also strengthens the universal occupied transmitter rectangle
from the residual-domain source: its inward width satisfies
\(w_1\ge H-d_R>1/100\). Every original allowed transverse
position of \(W_1\) contains that rectangle. It is not permissible
to move the actual transmitter to a preferred slider endpoint.

Central capacity at most one is already proved for the full family.
Thus the three original extras now have the following complete
necessary allocation cover, with exterior counts ordered as
\((k_0,k_2)\):

| Central extras | Counts in the two remaining actual pockets |
| --- | --- |
| 0 | \((3,0),(2,1),(1,2),(0,3)\) |
| 1 | \((2,0),(1,1),(0,2)\) |

In particular repeated occupancy of one pocket remains explicitly
present. Excluding all these coupled allocations, with the original
transmitter intervals, is still the remaining three-extra completion
problem. This theorem supplies no unproved whole-cap capacity for
pocket 0 or pocket 2, and does not infer that the central region is
empty.

The one-radial family, global sharp inequality, equality
classification, and earlier prerequisite-chain audit retain their
separate obligations. No numerical proof premise, coefficient
certificate, Lean compilation, CI, or workflow dispatch was used.
