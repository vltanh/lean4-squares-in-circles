# A forbidden BT owner globally forces the A sign

## 1. The global statement

Assume the actual G0--G2 seven-cycle at squared radius
\[
q\le Q=\frac{9789}{2500},
\]
with its common real frame interval of length less than \(7/10\).
Then
\[
\boxed{\text{an original BT axis 0 or 1 feasible}
             \quad\Longrightarrow\quad y_A>0.}
\tag{1}
\]
Here a signed own-frame center is \((a,-y)\). There is no
mismatch bound, tangent cut, sign normalization on E, or
assumption about another quarter owner in (1). Every original
weak witness and every tied owner is included.

The result is about the complete forbidden-BT branch. It does not
exclude that branch after A has positive sign, so it does not by
itself prove global BT owner rigidity.

More generally, the proof applies to any consecutive zero and
quarter edges in this same seven-cycle: a quarter owner 0 or 1
forces the source of the preceding zero edge to have positive
signed tangent. Section 9 records the reflected implication.

## 2. Suppose A has nonpositive sign

Work first on the fixed-witness G0 boundary cycle at Q. Put
\[
L_0=\frac{447}{800},\quad U_0=\frac{283}{200},\quad
R=\sqrt Q,\quad R_0=\sqrt{Q-\frac14},\quad a_0=R_0-\frac12 .
\]
The common unsigned G1 marker F satisfies
\[
F_O(a,b)\le\frac25(a-a_0)+\frac{111}{100}b
\tag{2}
\]
on every outer chart, with either marker at a chart junction.
For a core point, \(b\le1/2\) implies
\[
F_C(a,b)=1.077372b\le\frac{111}{100}b.
\tag{3}
\]
These are the unchanged whole-chart bounds proved in
[the global DE note](HAND_G3_GLOBAL_D_OWNER_BY_CYCLIC_MARKER.md),
Section 2. On both radial kinds,
\[
a>L_0,\quad a<U_0,\quad |(a,b)|<U_0,\quad b<9/10.
\tag{4}
\]
A core point has \(a\le7/12\).

Suppose \(y_A=-b_A\le0\). The global zero-primary exclusion
leaves AB only axes 0 and 2. The
[global zero-owner sign theorem](HAND_G3_GLOBAL_ZERO_OWNER_SIGN_RIGIDITY.md)
excludes its axis 0, so its retained axis is 2 and \(y_B=-b_B<0\).
The generic quarter-owner theorem in Section 11 of the global DE
note gives \(y_T=b_T>0\).

Let \(v=d_{AB}\), \(x=d_{BT}\), and write
\[
W(z)=\frac{1+\cos z+|\sin z|}{2}.
\]
The actual inequalities are
\[
a_A\sin v-b_A\cos v+b_B\ge W(v),
\tag{5}
\]
and one of
\[
\begin{aligned}
P_0&=-b_B+a_T\cos x+b_T\sin x\ge W(x),\\
P_1&=a_T+a_B\sin x-b_B\cos x\ge W(x).
\end{aligned}
\tag{6}
\]
Equation (5) implies \(v>0\): for \(v\le0\), its left side is
at most \(b_B<9/10<W(v)\). Consequently
\[
0<v<7/10,\qquad |x|<7/10.
\tag{7}
\]
If \(x\ge0\), the common real frame interval also gives
\[
v+x<7/10.
\tag{8}
\]

We will prove the unboosted two-edge charge
\[
\boxed{
C=\frac\pi2+v+x-F_A-F_T>\frac{19}{10}.
}
\tag{9}
\]
All internal B markers have canceled. The five other original G1
edges will then contradict the full cyclic angular budget.

### Two preliminary reductions retain the actual radial kinds

If A were core with \(b_A>1/2\), (5) would be impossible:
\[
a_A\sin v-b_A\cos v+b_B
<\frac7{12}\frac{13}{20}-\frac12\frac34+\frac9{10}
=\frac{217}{240}<1.
\]
Together with (2)--(3), this proves in every remaining A state
\[
F_A\le\lambda b_A,\qquad \lambda=\frac{111}{100}.
\tag{10}
\]

For BT0, T cannot be core, because its projection is at most
\(|(a_T,b_T)|\le7\sqrt2/12<1\).
For BT1 with \(x\ge0\), add (5), multiplied by \(\cos x\), to
its inequality in (6). If T were core, the resulting left side
would be at most
\[
\frac7{12}
+U_0\{\sin x+\sin v\cos x\}
\le\frac7{12}+U_0\frac{13}{16}
=\frac{16637}{9600}<\frac74.
\tag{11}
\]
Indeed, (8) gives
\[
\sin x+\sin v\cos x
=\sin(v+x)+\sin x(1-\cos v)
\le\frac{13}{20}\left(1+\frac14\right)=\frac{13}{16}.
\]
But the two widths are at least \(1+\cos x>7/4\).
Therefore T is outer in both cases, and (2) gives
\[
F_T\le\eta(a_T-a_0)+\lambda b_T,\qquad \eta=\frac25.
\tag{12}
\]
The negative-error BT1 case will instead be reduced directly to BT0.

## 3. Constants and a common one-variable reserve

We use the exact rational constants
\[
\begin{gathered}
m=\frac9{20},\quad
\kappa=\frac{\lambda\eta}{2m}=\frac{37}{75},\quad
\nu=\frac{\lambda^2}{2m}=\frac{1369}{1000},\quad
\rho=\frac{\lambda^2}{4m}=\frac{1369}{2000},\\
\gamma=\frac{\lambda^2+\eta^2}{4m}=\frac{13921}{18000},
\quad b=\lambda(U_0-\tfrac12)=\frac{20313}{20000},
\quad k=mQ+\frac{\lambda^2}{4m}-2\lambda=\frac{5663}{25000},\\
A=\frac{263}{250},\qquad R_+=\frac{1979}{1000}.
\end{gathered}
\tag{13}
\]
There is no numerical fit in these definitions. Elementary
positive squaring gives
\[
R<R_+,\qquad R_0>\frac{957}{500};
\]
the second squared reserve is \(551/250000\).
Using \(\pi/2>157/100\),
\[
\frac\pi2+\eta R_0-\frac{19}{10}+\lambda-\kappa
>A+\frac1{3750}>A.
\tag{14}
\]

Define
\[
F_0(v)=(v+A)\cos v-b\sin v-\gamma\cos^2v-k.
\tag{15}
\]
Then, on the entire interval \(0\le v\le7/10\),
\[
\boxed{F_0(v)>\frac3{500}.}
\tag{16}
\]

For \(0\le v\le1/2\), use
\[
\cos v\ge1-v^2/2,\quad \sin v\le v,\quad
\cos^2v\le1-v^2+v^4/3.
\]
They give
\[
F_0(v)\ge
A-\gamma-k-(b-1)v+(\gamma-A/2)v^2-v^3/2-\gamma v^4/3.
\]
Replacing \(v^3\le v^2/2\), \(v^4\le v^2/4\) and then
\(v\le1/2\), \(v^2\le1/4\), with the negative coefficient
retained in its correct direction, yields
\[
F_0(v)\ge
A-\gamma-k-\frac{b-1}{2}
+\frac14\left(\frac{11\gamma}{12}-\frac A2-\frac14\right)
=\frac{594023}{21600000}>\frac3{500}.
\tag{17}
\]
For \(1/2\le v\le7/10\),
\[
F_0'(v)=(1-b)\cos v-
               \{v+A-2\gamma\cos v\}\sin v<0,
\]
since
\[
\frac12+A-2\gamma=\frac{47}{9000}>0.
\]
It therefore suffices to check \(v=7/10\). The sixth-degree
cosine lower bound, fifth-degree sine upper bound, and
\[
\cos^2v\le1-v^2+\frac{v^4}{3}
                     -\frac{2v^6}{45}+\frac{v^8}{315}
\]
give the exact endpoint bound
\[
F_0(7/10)>
\frac{1092205922669}{162000000000000}>\frac3{500}.
\tag{18}
\]
This proves (16).

## 4. Original BT axis 0: one retained T circle

Write \(c_v=\cos v\), \(s_v=\sin v\),
\(c_x=\cos x\), \(s_x=\sin x\).
Adding (5) to BT0 cancels the same actual \(b_B\).
Using (10), (12), and \(a_A<U_0\), we obtain
\[
C\ge\frac\pi2+v+x+\eta a_0+
\frac{\lambda}{c_v}\{W(v)+W(x)-U_0s_v\}
-\left(\frac{\lambda c_x}{c_v}+\eta\right)a_T
-\left(\frac{\lambda s_x}{c_v}+\lambda\right)b_T.
\tag{19}
\]
The actual T corner disk supplies support for the last two terms,
regardless of the signs of their coefficients.

For any vector z,
\[
R|z|\le mQ+\frac{|z|^2}{4m}.
\tag{20}
\]
Apply (20) after multiplying (19) by \(c_v>0\), and use (14).
Expanding the two force components gives
\[
c_v(C-19/10)>F_0(v)+X(v,x),
\tag{21}
\]
where
\[
X(v,x)=c_vx+(\lambda-\kappa c_v)(\cos x-1)
                   +\lambda\max(\sin x,0)-\nu c_v\sin x.
\tag{22}
\]
This identity uses the original weak contact, its exact width cusp,
and the same original T circle.

For \(x\ge0\),
\[
\frac{\partial X}{\partial x}
=c_v-(\lambda-\kappa c_v)\sin x
                  +(\lambda-\nu c_v)\cos x>\frac1{100}.
\tag{23}
\]
To verify it, use
\[
c_v>\frac34,\quad
0<\lambda-\kappa c_v<\frac{37}{50},\quad
\lambda-\nu c_v\ge-\frac{259}{1000},\quad
\sin x<\frac{13}{20};
\]
the lower comparison is
\(3/4-(37/50)(13/20)-259/1000=1/100\).
Thus \(X(v,x)\ge0\).

For \(x=-z<0\), (5) first gives the uniform B bound
\[
b_B\ge\frac12+\frac12\cos v-\frac{183}{200}\sin v
>\frac{11673}{40000}>\frac{29}{100}.
\tag{24}
\]
Here \(\cos(7/10)>191/250\) and
\(\sin(7/10)<129/200\) follow from their alternating Taylor bounds.
BT0 then implies
\[
\frac{183}{200}\cos z-\frac12\sin z>\frac{79}{100}.
\]
The left side strictly decreases on \([0,7/10]\), and its
fourth/cubic Taylor upper bound at \(23/100\) is less than
\(79/100\), with reserve \(6278949097/480000000000\).
Consequently \(z<23/100\).

Equation (22) now reads
\[
X(v,-z)=-c_vz+(\lambda-\kappa c_v)(\cos z-1)
                                      +\nu c_v\sin z.
\]
Its derivative in z is
\[
c_v(\nu\cos z-1)-(\lambda-\kappa c_v)\sin z
>\frac{30299}{400000}>0,
\tag{25}
\]
by \(c_v>3/4\), \(\cos z>97/100\),
\(\sin z<23/100\), and the same \(37/50\) bound.
Thus \(X(v,-z)\ge0\) as well. Equations (16), (21)
prove (9) for every original BT0 witness.

## 5. Original BT axis 1 with nonpositive error

The case \(x=0\) is already BT0, because its two projections agree.
Let \(x=-z<0\), and suppose BT1 is feasible while BT0 is not.

Put
\[
k_B=a_B+\tfrac12,\quad l_B=b_B+\tfrac12,\quad
X_T=a_T+\tfrac12,\quad Y_T=b_T+\tfrac12,\quad
t_z=\tan(z/2).
\]
The B bound (24) used only AB, so it remains valid here.
In particular
\[
k_B>\frac{847}{800},\qquad l_B>\frac{79}{100},
\qquad k_B\ge l_B.
\tag{26}
\]
The original BT1 inequality gives
\[
X_T\ge X_*=1+l_B\cos z+k_B\sin z.
\tag{27}
\]
Moreover
\[
P_1-P_0
=(a_T+b_B)(1-\cos z)-(a_B-b_T)\sin z>0
\]
implies
\[
Y_T>Y_*-t_z(X_T-X_*),\qquad
Y_*=k_B\cos z-l_B\sin z>0.
\tag{28}
\]
The last positivity follows from \(k_B\ge l_B\) and
\(\cos z>\sin z\). The comparison vector satisfies
\[
X_*-t_zY_*=1+l_B+k_Bt_z>0.
\]
Thus (27)--(28) imply
\[
(X_*,Y_*)\mathbin{\cdot}
\bigl((X_T,Y_T)-(X_*,Y_*)\bigr)>0.
\]
Completing the squared distance gives
\[
\begin{aligned}
X_T^2+Y_T^2
&>X_*^2+Y_*^2\\
&=1+k_B^2+l_B^2+2(l_B\cos z+k_B\sin z)\\
&\ge k_B^2+(l_B+1)^2\\
&>\left(\frac{847}{800}\right)^2+
                  \left(\frac{179}{100}\right)^2
=Q+\frac{262049}{640000}>Q,
\end{aligned}
\tag{29}
\]
a contradiction.

Hence original BT0 is also feasible whenever BT1 with \(x<0\)
is feasible under the putative A sign. Section 4 applies to that
actual original axis and gives (9). No new axis has been substituted
into a hypothetical packing: its original feasibility has just been
proved from the retained BT1 witness.

## 6. Original BT axis 1 with positive error: retain B and T together

Now \(v,x\ge0\), \(v+x\le7/10\), and T is outer by (11).
Set
\[
p=\frac{\lambda}{\cos v},\qquad r=p\cos x>0.
\]
Use AB with weight p and BT1 with weight r in the marker bound
(10), (12). The exact forces on B and T are
\[
f_B=(r\sin x,p-r\cos x)
       =p\sin x(\cos x,\sin x),\qquad
f_T=(r+\eta,\lambda).
\tag{30}
\]
In particular \(|f_B|=p\sin x\). Applying the two original
corner disks gives
\[
\begin{split}
C\ge{}&\frac\pi2+v+x+\eta R_0
+p\{1+\tfrac12\cos v-(U_0-\tfrac12)\sin v\}\\
&+\tfrac12\lambda+r(1+\sin x)
-R\{p\sin x+\sqrt{(r+\eta)^2+\lambda^2}\}.
\end{split}
\tag{31}
\]
Apply (20) to the second norm after multiplication by \(\cos v\).
For the first norm use \(R<R_+\). Expanding exactly and using
(14) yields
\[
\cos v\,(C-19/10)>F(v,x),
\tag{32}
\]
where
\[
\begin{split}
F(v,x)={}&F_0(v)+\cos v\,x
+(\lambda-\kappa\cos v)(\cos x-1)\\
&+\rho\sin^2x+\lambda\sin x(\cos x-R_+).
\end{split}
\tag{33}
\]
The next section proves \(F>0\) on its whole triangle.
This retains the actual shared B circle; replacing B by its
independent primary maximum would not give this estimate.

## 7. A continuous positivity proof on the triangle

We prove
\[
F(v,x)>0\qquad(v,x\ge0,\ v+x\le7/10).
\tag{34}
\]
The proof uses a rectangle bound, concavity in v, and one harmonic
boundary function. There is no subdivision into angle states.

### 7.1 The small rectangle

For \(v\le1/4\), the Taylor argument of Section 3 gives the
slightly sharper bound
\[
F_0(v)\ge A-\gamma-k-\frac{b-1}{4}.
\tag{35}
\]
Indeed, the remaining coefficient of \(v^2\) is at least
\(47\gamma/48-A/2-1/8>0\).

For \(v\le1/4\), \(\cos v\ge31/32\) and
\[
\lambda-\kappa\cos v\le\frac{1517}{2400}.
\]
Write \(Y=F-F_0\). When also \(x\le9/20\), use
\[
\begin{gathered}
1-\cos x\le x^2/2,\qquad
\sin^2x\ge x^2-x^4/3,\\
\sin x\cos x\ge x-\frac23x^3,\qquad
\sin x\le x-x^3/6+x^5/120.
\end{gathered}
\]
Substitution in (33), followed by \(x\le9/20\), gives
\[
Y\ge-\frac{5897}{50000}x+\frac3{20}x^2.
\tag{36}
\]
The available quadratic coefficient before replacing it by \(3/20\)
is \(14624469299/96000000000\); its excess is
\(224469299/96000000000>0\).
Completing one square in (36) and using (35) gives
\[
F(v,x)\ge\frac{112479923}{4500000000}>\frac1{50}>0
\tag{37}
\]
on this complete rectangle.

### 7.2 All remaining points reduce to the slanted boundary

Differentiating (33),
\[
F_v=(1-b)\cos v+
\{2\gamma\cos v-A-(v+x)-\kappa(1-\cos x)\}\sin v.
\tag{38}
\]
For \(x\ge9/20\), its bracket is negative. The exact lower
reserve supplied by
\[
\kappa\left(\frac{x_0^2}{2}-\frac{x_0^4}{24}\right)
-\{2\gamma-A-x_0\},\qquad x_0=\frac9{20},
\]
is \(1246843/288000000>0\).
Thus \(F_v<0\) there. At fixed x, its minimum is on
\(v=7/10-x\).

For the other part, \(x\le9/20\) and \(v\ge1/4\),
\[
F_{vv}=F_0''(v)-\cos v\{x+\kappa(1-\cos x)\}\le F_0''(v).
\]
Here
\[
\begin{aligned}
F_0''(v)&=(b-2)\sin v-(v+A)\cos v+2\gamma\cos(2v),\\
F_0'''(v)&=(b-3)\cos v+
                     \{v+A-8\gamma\cos v\}\sin v<0.
\end{aligned}
\]
The final sign follows from \(b<3\),
\(v+A\le7/10+A<6\gamma\), and \(\cos v\ge3/4\).
Taylor bounds at \(v=1/4\) give
\[
F_0''(1/4)\le-\frac{2037353}{13824000}<0.
\]
Thus F is concave in v on
\([1/4,7/10-x]\). Its minimum is at the left endpoint,
already covered by (37), or on \(v+x=7/10\).

### 7.3 The one remaining boundary is a second harmonic

Let \(d=7/10\) and \(B(v)=F(v,d-v)\), \(0\le v\le d\).
Angle addition expresses it exactly as
\[
B(v)=P\cos v+J\sin v+U\cos(2v)+V\sin(2v)+C_0,
\tag{39}
\]
where the constant \(C_0\) need not be estimated and
\[
\begin{aligned}
P&=d+A+\kappa+\lambda\cos d-\lambda R_+\sin d,\\
J&=-b+\lambda\sin d+\lambda R_+\cos d,\\
U&=\tfrac12\{-\gamma-\kappa\cos d
                         -\rho\cos(2d)+\lambda\sin(2d)\},\\
V&=-\tfrac12\{\kappa\sin d+\rho\sin(2d)
                                      +\lambda\cos(2d)\}.
\end{aligned}
\tag{40}
\]
The elementary Taylor enclosures
\[
\begin{gathered}
.764<\cos d<.765,\quad .644<\sin d<.645,\\
.169<\cos(2d)<.171,\quad .985<\sin(2d)<.986
\end{gathered}
\]
give, by direct substitution,
\[
\begin{gathered}
1.67<P<1.69,\qquad 1.37<J<1.39,\\
-.09<U<-.08,\qquad -.592<V<-.589.
\end{gathered}
\tag{41}
\]

These bounds prove \(B'''>0\) on the entire interval. For
\(0\le v\le3/20\),
\[
B'''(v)\ge-1.39-.72(.3)+8(.589)(.95)
=\frac{1794}{625}>0.
\]
For \(3/20\le v\le7/10\), use \(\cos(2v)>0\),
\(\sin(2v)\ge\sin(.3)>.295\), and
\(\sqrt{1.69^2+1.39^2}<2.2\) to obtain
\[
B''''(v)<2.2-16(.589)(.295)
=-\frac{7251}{12500}<0.
\]
Consequently \(B'''\) decreases on this latter interval. Its
endpoint bound from (41) is
\[
B'''(7/10)>
1.67(.644)-1.39(.765)-.72+8(.589)(.169)
=\frac{44229}{500000}>0.
\]
This establishes the asserted global sign.

Therefore \(B'\) is convex. The same endpoint bounds give
\[
B'(7/10)<
-1.67(.644)+1.39(.765)+.18-2(.589)(.169)
=-\frac{7803}{250000}<0.
\]
The nonpositive sublevel set of a convex \(B'\) is an interval
containing its right endpoint. It follows that B can first increase
and then decrease, or decrease throughout; its minimum is at an
endpoint.

One endpoint is \(B(7/10)=F_0(7/10)>3/500\).
At the other, direct substitution in (33) gives
\[
\begin{split}
B(0)\ge{}&A-\gamma-k+\frac7{10}
-(\lambda-\kappa)(1-.764)\\
&+\rho(.644)^2+\frac{\lambda}{2}(.985)
-\lambda R_+(.645)\\
={}&\frac{91145339}{4500000000}>\frac1{50}.
\end{split}
\]
Thus B is positive on its whole interval. Along with Sections
7.1--7.2 this proves (34), and hence (9) for BT1 with positive error.

## 8. Close the actual cycle and transfer to original centers

Sections 4--7 prove (9) for either putative forbidden BT owner
under \(y_A\le0\). On each of the other five original edges, G1 gives
\[
\phi_j+\ell_j-\ell_{j+1}
>\frac{8833}{10000}+\frac9{50}h(|d_j|)
\ge\frac{8833}{10000}.
\]
Use the same common marker at every shared vertex. Summing with
the unboosted two-edge charge (9) yields
\[
2\pi>\frac{19}{10}+5\frac{8833}{10000}.
\]
This is impossible, because
\[
\frac{19}{10}+5\frac{8833}{10000}-\frac{710}{113}
=\frac{7529}{226000}>0,\qquad 2\pi<\frac{710}{113}.
\]
No separate return metric estimate is needed for this two-edge proof.

For original contained centers, retain the putative original BT
witness and the offending weak A sign, then apply G0's fixed-witness
boundary reduction and expansion to Q. These operations preserve
the original weak witness, the real frames, and the signed radial
ray. The global zero-primary and sign theorems then supply the AB2
witness and the B/T signs used above. Choose the common G1 marker
once on the resulting boundary cycle and apply the contradiction.
Thus (1) holds for original centers, including weak ties and
\(y_A=0\).

## 9. Generic propagation through a zero--quarter pair

The proof used only that AB is a zero edge and BT a quarter edge;
their names played no role. Thus, whenever a zero edge \(I\to J\)
is followed by a quarter edge \(J\to K\),
\[
\boxed{\text{an original quarter axis 0 or 1 feasible}
                 \Longrightarrow y_I>0,\quad y_K>0.}
\tag{42}
\]
The K sign is the already proved generic quarter implication.

There is a reflected companion. If a quarter edge \(I\to J\)
is followed by a zero edge \(J\to K\), local reflected reversal
exchanges endpoints, negates signed tangents, and preserves each
actual error. The original quarter axes 2/3 become 0/1; the
zero axes exchange 0 and 2. The path marker difference and total
physical angular increment are unchanged. Applying the same local
two-edge estimate and its original five-edge return therefore gives
\[
\boxed{\text{an original quarter axis 2 or 3 feasible}
                 \Longrightarrow y_I<0,\quad y_K<0.}
\tag{43}
\]
This is a calculation on the retained original path, not the
construction of a different global cycle.

For the surviving seven-cycle, (42) gives \(y_H>0\) when GA has
axis 0/1 and \(y_A>0\) when BT has axis 0/1. Equation (43) gives
\(y_B<0\) when GA has axis 2/3 and \(y_D<0\) when BT has axis 2/3;
it also gives \(y_G<0\) when EH has axis 2/3.

All circle supports, masses, derivative signs and endpoint
comparisons are explicit above. No state cover, angle mesh,
sampled minimum, generated acceptance result, Lean compilation
or CI result is a premise.
