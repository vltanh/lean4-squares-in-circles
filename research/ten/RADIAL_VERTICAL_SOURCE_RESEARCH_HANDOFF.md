# Unfinished radial-source branch with a vertical endpoint

**Status: historical research lead, completed.**
The formulas have now been checked and the subdivision completed in
[RADIAL_VERTICAL_SOURCE_EXCLUSION.md](RADIAL_VERTICAL_SOURCE_EXCLUSION.md),
with a full 248-leaf rational certificate and no unresolved cells.
The text below records the earlier incomplete exploration.

Original status: NOT PROMOTED. This is an unfinished parameter reduction and
interval exploration, not an exclusion theorem. Research was frozen for
handoff with unresolved cells. No whole case or support row is closed
by this note.

The remaining vertical-endpoint case in the both-unique-D-endpoint
branch has a radial C and strict source vertices in row V_V. Use a
common-edge frame

```text
e=(a,b),       m=(−b,a),       a²+b²=1,       0<b<a,
C=[−1/2,1/2]*e+[L,L+1]*m,
9/10<L<17/16,       R²=(L+1)²+1/4.
```

A's direction is vertical and B's direction is `n_B=(−r,s)`, with
`0<r<s`, `r²+s²=1`. Strict support gives `b<r`. The two contacts are
`Q_A=−e/2+L*m` and `Q_B=e/2+L*m`. Matching them with the D-endpoint
coordinates gives

```text
alpha=r+a−sqrt(2)>=0,
U=1+sqrt(2)−r−a/2,       W=2+b/2,
u=U+L*b,       H_A=W−L*a,
v=1+r+a/2−L*b,
H_B=1+s−L*a−b/2.
```

The two endpoint circle equations are linear in L after cancellation of
the quadratic term. They give the necessary equality `L_A=L_B=L`, where

```text
L_A=(U²+W²−5/4)/(2*(W*a+1−U*b)),
L_B=[2+2*(r+s)+a*(1+r)−b*(1+s)]
     /[2*(1+b*(1+r)+a*(1+s))].
```

A's vertical-contact torque fixes `z=−h=H_A*(L*b+a/2)/u`. B's torque
then requires

```text
T=(u*H_B−H_A*(L*b+a/2))*(v*s−H_B*r)
  −u*H_B*(s−r)=0.
```

These formulas were derived during exploration. They have not received
a full independent audit as an assembled branch reduction.

The saved script
[explore_radial_vertical_source.py](explore_radial_vertical_source.py)
uses rational half-angle variables

```text
b=2x/(1+x²),       a=(1−x²)/(1+x²),
r=2y/(1+y²),       s=(1−y²)/(1+y²),
x in [0,5/12],     y in [1/5,5/12],
sqrt(2) in [140/99,99/70].
```

It bisects parameter intervals and tries necessary-condition rejections,
including `L_A−L_B` having a fixed sign or T being strictly positive.
At the saved depth limit it visited 403 nodes, rejected 172 leaves, and
left **30 unresolved cells**. Its output is exploratory. In particular,
it is not a complete finite certificate, and neither its reduction nor
its rejection rules have been independently audited.

The next step is to audit the displayed identities and then either
complete a covered exact parameter exclusion or find a shorter analytic
sign argument for T. The unresolved cells must not be discarded.
