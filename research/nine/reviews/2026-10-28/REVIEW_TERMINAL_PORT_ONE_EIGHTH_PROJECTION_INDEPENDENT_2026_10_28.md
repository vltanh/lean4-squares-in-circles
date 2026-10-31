# Independent complete review: terminal-port one-eighth projection theorem

Date: October 28, 2026 UTC.

**Outcome: PASS.** The full closed-domain scalar theorem is proved as stated. Its Section 6 physical invocation is valid conditionally on the stated actual unique-V chart, the separately supplied entry bounds, and the original numerical radius bound `R^2 <= 1105/256`. No original physical remainder is excluded by this review beyond that conditional projection conclusion.

**Independent-author status.** This review was performed by the separately spawned reviewer `/root/projection_audit`. I did not contribute to the theorem's discovery, its projection strategy, its bounds, or the writing of the proposed proof. I read the entire frozen proposed proof and the entire sole direct physical source afresh. The calculations and sign checks below were independently reconstructed; the proposed proof's verification claims were not accepted as substitutes for verification.

## 1. Frozen inputs and scope

| Input | SHA-256 |
| --- | --- |
| `/workspace/scratch/a6cd5be3396b/recovered_house/TERMINAL_PORT_POSITIVE_DOT_ONE_EIGHTH_PROJECTION_BOUND.md` | `7ccc1db3095fbbdf63968fd25bc0d0b45cffa688d71408490462f68178a683a4` |
| `/workspace/scratch/a6cd5be3396b/lean4-squares-in-circles/research/nine/TERMINAL_HUB_AXIS_TIP_OWNED_POSITIVE_DOT_FULL_MASK_ENTRY.md` | `1e9e597ad4b13995909cdac5d204b111d20ef305768fe6d44def11264e4a4c49` |

Both hashes were checked directly against the complete files. This is an audit of every mathematical step and every stated endpoint of the scalar proof, together with the exact Section 6 substitution and its logical scope. The full physical source was read, including its distinctions between unique V, physical-two V, and the different W masks. Only the actual chart, U3 identity, unique-V torque, and terminal-port identities are invoked here. The physical source's other exclusions and its own downstream dependencies are not silently imported into the scalar theorem.

Verification used hand-proof reasoning, Python `fractions.Fraction`, and exact arithmetic in pairs representing `u + v sqrt(46)`. It used no floating-point evaluation, numerical optimizer, angle or pose sampling, Lean, CI, or computational geometric certificate. Neither frozen input, the repository, shared ledgers, nor remote state was edited.

## 2. Domain, denominators, and the exact b interval

The domain is

```
a,b >= 0, a^2+b^2=1,
z >= 1, r >= 12/31,
kappa=a-zb >= 2/5,
tau=(r-1+kappa)/(r+z) >= 0.
```

Thus `r>0`, `r+z>0`, and `r+1>0`. Since `b>=0` and `z>=1`,

```
a-b >= a-zb >= 2/5.
```

Squaring `a>=b+2/5` is valid because both sides are nonnegative. Substitution of `a^2=1-b^2` gives

```
50b^2+20b-21 <= 0,
0 <= b <= b_*=(sqrt(46)-2)/10.
```

The other quadratic root is negative, so no nonnegative component is omitted. The strict comparison `b_*<12/25` is equivalent to `sqrt(46)<34/5`; both sides are positive, and the exact squared excess is `6/25`. Consequently `b<1/2`, and `a>0` throughout the entire scalar domain. All later uses of `1/a` are legitimate. Also `b_*>2/5`, since `sqrt(46)>6`, so the three stated subintervals have precisely the intended coverage.

There is no upper bound on r and none is needed. The proof does not assume compactness in r or z, or existence of a numerical minimizer. At b=0 the unbounded z direction is explicitly handled below.

## 3. Exact baseline reduction and the global polynomial comparison

Direct expansion of `G=-e+3f` gives

```
G=4-a^3-3a-b-3b^3 + zb(1+a^2-3ab) + z tau
 =G0+zbH+z tau.
```

Using `a^2=1-b^2`, the proposed `H` has the equivalent form

```
H=2-b^2-3ab.
```

Because `b<1/2` and `a<=1`, both `b^2<1/4` and `3ab<3/2` hold. Therefore `H>1/4>0`; no strictness from an open physical contact is used.

The baseline simplifies exactly:

```
F=G0+bH
 =4-a(4+2b^2)+b-4b^3.
```

It follows that

```
G=F+(z-1)bH+z tau >= F.
```

Every added term is nonnegative on the closed domain, including z=1, b=0, and tau=0.

The comparison `a<=1-b^2/2` is also valid at b=0: its right side is positive and its square exceeds `a^2` by `b^4/4`. Since `4+2b^2>0`, replacing a by this upper bound reverses no sign incorrectly. The exact multiplication

```
(1-b^2/2)(4+2b^2)=4-b^4
```

then yields `F>=P=b+b^4-4b^3`. This comparison introduces no new orientation choice and no physical assumption.

## 4. Small interval, including b=0 and every z endpoint

For `0<=b<=1/5`, put `N=r+a-1`. The definition and nonnegativity of tau give `N>=zb>=b`. If `b>0`, then `N>0`; if `b=0`, the circle relation and nonnegativity force `a=1`, so `N=r>0`. Thus `N+br>0` in all cases.

The retained rational term is exactly

```
z tau = z(N-zb)/(r+z)
      = (N+br)z/(r+z)-bz.
```

Since `H-1=a(a-3b)`, this proves the displayed exact reduction

```
G(z)=G0+ab(a-3b)z+(N+br)z/(r+z).
```

On the entire interval, `a^2>=24/25` and `9b^2<=9/25`, hence `a>3b`. Differentiation at fixed a,b,r gives

```
dG/dz=ab(a-3b)+r(N+br)/(r+z)^2 > 0.
```

The second term is strictly positive even at b=0. The interval from 1 to the actual z retains `N-tb>=N-zb>=0` for each intermediate t, so tau remains nonnegative. It also retains `a-tb>=a-zb>=2/5`; the kappa constraint is preserved as well. Therefore the comparison to z=1 is legitimate throughout the complete stated domain:

```
G(z)>=G(1)=F+(r+a-1-b)/(r+1).
```

The r derivative is exactly `(2+b-a)/(r+1)^2>0`, because `a<=1`. Thus replacing r by `12/31` supplies a lower bound. This rational comparison is valid algebraically irrespective of any additional physical constraint. In fact, even its z=1 comparison point remains in the tau domain: using `a>=1-b^2`,

```
12/31+a-1-b >= 12/31-b-b^2 >= 114/775 > 0.
```

The lower bound `a>=1-b^2` follows from `0<=1-b^2<=1` and `a=sqrt(1-b^2)`. Further,

```
F>=b-4b^3>=21b/25.
```

Combining these bounds gives exactly

```
G>=12/43+(128/1075)b-(31/43)b^2=Q0(b).
```

Here `21/25-31/43=128/1075`; the negative quadratic coefficient is correct. The second derivative is `-62/43<0`, so concavity gives a minimum at an endpoint of `[0,1/5]`. The endpoints are

```
Q0(0)=12/43,
Q0(1/5)=1473/5375,
Q0(0)-Q0(1/5)=27/5375>0.
```

The resulting strict reserve over `1/8` is exactly `6409/43000`.

For an additional explicit endpoint check, b=0 forces `a=1`, `kappa=1`, and `G=zr/(r+z)`. The preceding argument gives `G>=12/43`; hence that endpoint does not depend on a division by b or an omitted strict inequality. Actual tau=0 configurations with b>0 are included because the entire comparison uses tau>=0.

## 5. Middle closed interval

On `[1/5,2/5]`, differentiation of `P=b+b^4-4b^3` gives

```
P''=12b(b-2)<0.
```

Concavity on this complete closed interval makes the minimum an endpoint value. Both displayed values independently expand to

```
P(1/5)=P(2/5)=106/625.
```

Consequently `G>=106/625>1/8`, with exact reserve `223/5000`. Both shared interval endpoints are retained. This part requires neither z>1 nor tau>0.

## 6. Final closed interval and the exact radical endpoint

For `2/5<=b<=b_*`, the strict upper bound `b<12/25` gives

```
a^2>1-(12/25)^2>(7/8)^2.
```

The squared excess in the last comparison is exactly `159/40000`, so `a>7/8`. Differentiating the complete F, with `a'=-b/a`, gives

```
F'=b(4+2b^2)/a-4ab+1-12b^2
  =6b^3/a+1-12b^2.
```

The cancellation uses `a^2=1-b^2`; no term has been dropped. Its whole-interval estimate is

```
F'<6(12/25)^3/(7/8)+1-12(2/5)^2
  =-17681/109375<0.
```

The strict first comparison is justified at every point, including the interval endpoints, by `b<12/25` and `a>7/8`. The estimate of the negative term uses `b>=2/5` in the correct direction. Thus `F(b)>=F(b_*)` for all b in this last interval.

At the endpoint,

```
a_*=(sqrt(46)+2)/10,
b_*=(sqrt(46)-2)/10.
```

These are positive and satisfy exactly `a_*^2+b_*^2=1` and `a_*-b_*=2/5`. Independent arithmetic in `Q(sqrt(46))` gives

```
F(b_*)=(538-77sqrt(46))/125,
F(b_*)-1/8=(4179-616sqrt(46))/1000.
```

Hence strict positivity is exactly equivalent to `sqrt(46)<4179/616`. Both comparison sides are positive, and

```
(4179/616)^2-46=185/7744>0.
```

This proves the strict reserve without decimal approximations. The exact boundary is also consistent with the scalar constraints: taking z=1 and r=3/5 gives kappa=2/5 and tau=0, with `3/5-12/31=33/155>0`. This is an algebraic verification of the stated closed endpoint, not a physical pose claim or a sampled proof.

## 7. Exhaustiveness and strictness

The closed intervals `[0,1/5]`, `[1/5,2/5]`, and `[2/5,b_*]` cover the complete derived b range. Each proves a bound strictly above `1/8`, using exact positive rational quantities or the exact positive radical comparison. The endpoints b=0, z=1, kappa=2/5, tau=0, and r=12/31 are therefore all included whenever jointly feasible. The theorem does not require these different equalities to be simultaneously feasible in every subinterval.

There is no reliance on an open physical-domain reserve, an unproved orientation restriction, a force bound, or an upper bound on r. No limiting argument is needed at an infinite variable value; the inequalities hold for each real r and z in the stated domain.

## 8. Literal physical substitution and its conditions

The sole physical source was read in full. Its relevant quantities are the original positive a,b,c,d, the actual normals and applications, and

```
K=ad+bc>0,
L=ac-bd>0,
h=bc/K,
rho=a-(L/K)(b+tau).
```

The U3 identity `h=bc/K` follows from the full original force relation `mu b=nu d`, West magnitude `mu a+nu c`, and torque `(mu a+nu c)t=mu a`, giving `t=ad/K` and `h=1-t`. It does not identify the distinct VW and UW magnitudes.

For the unique V mask, the actual full torque gives

```
X(1-rho)=Y(1-tau).
```

This matches the torque of the actual contact points `P=(X-1,Y-1+rho)` and `M=(X-1+tau,Y-1)` together with the unique-corner resultant proportional to `(X,Y)`. The physical-two V mask has only the weaker source inequality and is not being assigned this equality.

Set `z=L/K` and `r=Y/X` as in the projection note. This z is the explicitly redefined ratio, not the W-coordinate also called z elsewhere in the physical source. Exact inversion of the K,L definitions gives

```
d=aK-bL=K(a-zb)=K kappa,
c=bK+aL=K(b+za),
h=b^2+zab.
```

Also `rho=kappa-z tau`, whereas unique-V torque gives `rho=1-r+r tau`. Equating them proves

```
tau=(r-1+kappa)/(r+z).
```

All denominators are positive in the actual chart. The actual relative-interior contact gives tau>0, which is sufficient for the closed scalar premise.

In the positively oriented frame `(-k,n)`, the actual V and terminal application are

```
V=[-Y,1-Y] x [X-1,X],
S=(-A,B),
A=Y-1+rho+b-ha,
B=X-1-a-hb.
```

The source identity `S=P-(1,h)` directly reproduces these coordinates. No application point is moved. Substituting the verified h and rho into `e=A-Y` and `f=B-X+2` gives

```
e=-1+rho+b-ha
 =a^3+b-1-z[b(1+a^2)+tau],
f=1-a-hb
 =1-a-b^3-zab^2,
```

which are exactly the scalar theorem's definitions.

The high-Y invocation additionally requires the caller's original radius window `R^2<=1105/256`, the actual circle equation `X^2+Y^2=R^2`, and the separately proved bounds `z>=1`, `kappa>=2/5`, and `Y>=3/4`. Then

```
X^2<=1105/256-9/16=961/256=(31/16)^2,
X<=31/16,
r=Y/X>=(3/4)/(31/16)=12/31.
```

Here X is positive, so the square-root and division steps are legitimate. The radius upper bound is a caller premise, not a conclusion of the sole physical source, whose broader local hypotheses and separate plus-mask radius range must not be confused with this numerical window. The projection note explicitly invokes that radius upper bound conditionally; this review does not infer it from the entry file.

With those premises, every scalar assumption is literal, and the actual terminal projection satisfies `-e+3f>1/8`. No Y<1 condition is used. No claim is made for a physical-two V torque equation, or for entry bounds that have not been separately proved. In particular this result does not establish actual V open-arc membership, a terminal-angle comparison, an occupied cap, an angular route, or a completion allocation.

## 9. Exact arithmetic and final disposition

Every printed rational reserve and endpoint value was independently recomputed exactly: `6/25`, `128/1075`, `12/43`, `1473/5375`, `6409/43000`, both instances of `106/625`, `223/5000`, `159/40000`, `-17681/109375`, and `185/7744`. The radical endpoint expansion, the radius subtraction, and `r>=12/31` were also checked with exact arithmetic. The continuous proof is furnished by the displayed algebra, monotonicity, and concavity arguments; arithmetic checking is corroboration of their constants.

**Final disposition: PASS, with the physical invocation retaining its explicit caller premises.** No algebraic, derivative, sign, endpoint, coverage, or scope defect was found in the frozen scalar theorem. This independent review creates no additional original geometric closure and grants no change to an original fine/coarse flag, physical mask, force, mean, normal, true degree, or completion ledger.
