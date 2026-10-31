# Mixed two-share C6, placement 01: Cauchy reduction and fixed endpoint signs

Date: October 26, 2026.

**Status: complete scalar reduction and two fixed scalar lemmas, accepted
after independent full-source and physical-scope review.** See
`REVIEW_C6_MIXED_01_COMPLETE_JOIN_ROOT_2026_10_26.md`.
The source proves a necessary lower bound for
the full mixed-01 virial gap and verifies two fixed endpoints with a
uniform positive rational margin. The whole-domain argument taking the
gap to these endpoints is proved separately in
`SIX_CYCLE_MIXED_01_COMPLETE_EXCLUSION.md`; the two endpoint signs
alone are not represented as a whole-orbit proof.

The actual mixed-01 domain and unchanged physical identities are those
of `SIX_CYCLE_MIXED_01_CLOSURE_REDUCTION.md`. All nine physical units,
actual means, positive forces and shared-mean endpoints remain present.

## 1. Eliminate one full positive force ratio by Cauchy's inequality

Use the force normalization `(mu_0,mu_1,mu_2)=(1,p,q)` from
the cited source, and abbreviate

\[
 a=c_0,\quad b=c_1,\quad s=\sqrt{1-a^2}=s_0,
 \quad t=\sqrt{1-b^2}=s_1,
\]
\[
 c_2=st-ab,\quad s_2=sb+at,\quad h_0=a+s,\quad h_1=b+t,
 \quad K=\frac{79}{40}.
\tag{1}
\]

The sole nonshared support norm obeys the triangle inequality

\[
 E_2=\sqrt{p^2+2q^2+2pqh_2}\le p+\sqrt2q.
\tag{2}
\]

The two force norms involving `q` can be written as norms of
vectors with positive coordinates:

\[
 D_0=|(q+a,s)|,\qquad D_2=|(q+pc_2,ps_2)|.
\]

Their triangle inequality gives

\[
 D_0+D_2\ge
 \sqrt{(2q+a+pc_2)^2+(s+ps_2)^2}.
\tag{3}
\]

Put

\[
 w=1+\sqrt2+a+s,\qquad
 v=\sqrt{4K^2-w^2}>0,
 \qquad D=\sqrt{1+p^2+2pb}=D_1.
\tag{4}
\]

Here `w<=1+2sqrt(2)<79/20=2K`; the last strict comparison
follows by squaring `2sqrt(2)<59/20`, whose positive reserve is
`281/400`. All square roots in (1)--(4) therefore have their stated
positive meanings over the complete original domain.

Apply Cauchy's inequality with vector `(w/2,v/2)`, of norm `K`,
to the vector in (3). Since `w^2+v^2=4K^2`,

\[
 K(D_0+D_2)
 \ge wq+\frac w2(a+pc_2)+\frac v2(s+ps_2).
\tag{5}
\]

The exact numerator in the cited source and (2) give
`N<=2+h_1+3p+wq`. Hence the following gap bound holds for every
positive `q`, without deleting or specializing that force:

\[
 \boxed{\quad
 K(D_0+D_1+D_2)-N\ge G(p,a,b),\quad}
\]
\[
 G(p,a,b)=KD-2-(b+t)-3p
              +\frac w2(a+pc_2)+\frac v2(s+ps_2).
\tag{6}
\]

No sampled minimizer or sufficient-packing assumption enters (6).

## 2. The two fixed endpoint values

Let `r=1/sqrt(2)` and `P=1+r`. The endpoint lemmas are

\[
 G(P,5/9,4/9)>\frac1{40},
 \qquad
 G(9/4,r,1-r)>\frac1{40}.
\tag{7}
\]

Only the following coarse radical interval is needed:

\[
             \frac{707}{1000}<r<\frac{708}{1000}.
\tag{8}
\]

Its squared lower and upper reserves are respectively
`151/1000000` and `1264/1000000`, both positive. All estimates
below are direct rational consequences of (8), positive square
comparisons, and the definitions in (1)--(4).

### 2.1. Endpoint with `p=P`, `a=5/9`, `b=4/9`

At this endpoint,

\[
 s=\sqrt{56}/9,\qquad t=\sqrt{65}/9,
 \qquad D^2=\frac{61}{18}+\frac{26}{9}r.
\tag{9}
\]

The following deliberately coarse bounds are sufficient:

| Quantity | Lower bound | Upper bound |
| --- | --- | --- |
| `p` | `1707/1000` | `1708/1000` |
| `s` | `831/1000` | `832/1000` |
| `t` | `895/1000` | `896/1000` |
| `D` | `233/100` | not needed |
| `w` | `19/5` | `761/200` |
| `v` | `53/50` | not needed |
| `c_2` | `62/125` | not needed |
| `s_2` | `433/500` | not needed |

For completeness, squaring the endpoints for `s` and `t` against
`56/81` and `65/81` proves their four inequalities directly.
For `D`, insert the lower bound on `r` in (9); its squared
reserve above `(233/100)^2` is `73/30000`. The bounds on
`w=1+2r+5/9+s` follow by addition. The displayed upper bound
on `w` gives

\[
 4K^2-(761/200)^2-(53/50)^2=\frac7{8000}>0,
\]

which proves the bound on `v`. Finally

\[
 \frac{831}{1000}\frac{895}{1000}-\frac{20}{81}
                      -\frac{62}{125}
       =\frac{13469}{16200000}>0,
\]
\[
 \frac49\frac{831}{1000}+\frac59\frac{895}{1000}
                      -\frac{433}{500}
       =\frac1{1800}>0
\]

prove the lower bounds on `c_2` and `s_2` from (1). All
quantities multiplied in the positive terms of (6) are positive.
Use the lower bounds there and the upper bounds in the subtracted
terms. The exact result is

\[
\begin{aligned}
 G(P,5/9,4/9)
 &>K\frac{233}{100}-2-\frac49-\frac{896}{1000}
        -3\frac{1708}{1000}\\
 &\quad+\frac{19}{10}
       \left(\frac59+\frac{1707}{1000}\frac{62}{125}\right)
       +\frac{53}{100}
       \left(\frac{831}{1000}
                     +\frac{1707}{1000}\frac{433}{500}\right)\\
 &=\frac{11451047}{450000000}
  =\frac1{40}+\frac{201047}{450000000}>\frac1{40}.
\end{aligned}
\tag{10}
\]

### 2.2. Endpoint with `p=9/4`, `a=r`, `b=1-r`

Now

\[
 s=r,\quad t=\sqrt{2r-1/2},\quad
 w=1+4r,\quad v^2=\frac{2641}{400}-8r,
 \quad D^2=\frac{169}{16}-\frac92r.
\tag{11}
\]

The following bounds follow from (8):

\[
 t>\frac{239}{250},\quad t<\frac{479}{500},
 \quad b+t<\frac{1251}{1000},
 \quad D>\frac{543}{200},
\]
\[
 w>\frac{957}{250},\quad v>\frac{121}{125},
 \quad c_2>\frac{117}{250},\quad s_2>\frac{441}{500}.
\tag{12}
\]

The positive squared reserves for the two bounds on `t` are
`1/15625` and `441/250000`. The positive squared reserves for
the displayed bounds on `D` and `v`, after inserting the upper
bound on `r`, are respectively `211/40000` and `369/250000`.
The bound on `b+t` is the sum of `b<293/1000` and
`t<479/500`. For the remaining two terms, (1) becomes
`c_2=r(t-b)` and `s_2=r(t+b)`. The lower estimates give

\[
 \frac{707}{1000}
     \left(\frac{239}{250}-\frac{293}{1000}\right)
       -\frac{117}{250}=\frac{741}{1000000}>0,
\]
\[
 \frac{707}{1000}
     \left(\frac{239}{250}+\frac{292}{1000}\right)
       -\frac{441}{500}=\frac{21}{62500}>0.
\]

Substitution into (6), again keeping the sign of every term, yields

\[
\begin{aligned}
 G(9/4,r,1-r)
 &>K\frac{543}{200}-2-\frac{1251}{1000}-3\frac94\\
 &\quad+\frac{957}{500}
       \left(\frac{707}{1000}+\frac94\frac{117}{250}\right)
       +\frac{121}{250}
       \left(\frac{707}{1000}+\frac94\frac{441}{500}\right)\\
 &=\frac{32451}{1000000}
  =\frac1{40}+\frac{7451}{1000000}>\frac1{40}.
\end{aligned}
\tag{13}
\]

These two checks are fixed elementary radical inequalities. They
introduce no numerical sign premise, polynomial coefficient packet,
angular mesh, force-ratio mesh, Lean compilation or CI action.

## 3. The separate complete logical join

The endpoint values (7) alone do not imply `G>0` on the original
continuous domain. The separately proved force and angular
monotonicities, including the directional boundary lemma, establish
that all actual mixed-01 parameters reach these endpoints with the
correct inequality direction. The full join and the physical
contradiction `R<79/40` are in
`SIX_CYCLE_MIXED_01_COMPLETE_EXCLUSION.md`.

All such full-domain hypotheses, including the exact projection `X`,
the strict angular consequence `H>0`, and the strict force bound
`p>1+r`, remain explicit in the cited closure-reduction source.
No original gate changes merely from the two endpoint evaluations.
