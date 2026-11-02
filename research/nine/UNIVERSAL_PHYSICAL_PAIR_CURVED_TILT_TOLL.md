# A stronger physical pair cap for small shoulder tilts

November 2, 2026. Complete hand reduction and 860-row exact cover, with a
separate directed-integer replay. This companion strengthens the accepted
linear shoulder-tilt loss where the original shoulder is close to aligned.
No Lean or CI.

## 1. Physical statement

Use the unrestricted original-pair hypotheses and constants of
`UNIVERSAL_PHYSICAL_PAIR_SHOULDER_TILT_TOLL.md`:

\[
 Q=1105/256,\quad a=46,\quad b=27/2,\quad k=207/16,
 \quad T=211/4.
\]

For the original shoulder B and chosen horizontal direction e put

\[
 \alpha_B=\max\{|e\cdot u_B|,|e\cdot v_B|\},\qquad
 \beta_B=\min\{|e\cdot u_B|,|e\cdot v_B|\},
\]

so \(\alpha_B^2+\beta_B^2=1\), \(\alpha_B\ge\beta_B\ge0\).
Define

\[
                  \Phi(\alpha,\beta)=6\beta-b(1-\alpha).
\tag{1}
\]

Then two original physical unit squares M,B in the closed Q-disk, with
disjoint open interiors, satisfy

\[
 \boxed{a[-e\cdot c_M-h_M(e)]
       +b[-e\cdot c_B-h_B(e)]+\Phi(\alpha_B,\beta_B)\le T.}
\tag{2}
\]

No bound on either center, original orientation, floor, separator owner,
or chain is added. For a smaller disk the inequality is strict.
Combining (2) with the companion linear theorem allows the stronger toll

\[
             \tau_B=\max\{2\beta_B,\Phi(\alpha_B,\beta_B)\}.
\tag{3}
\]

## 2. The same four frame candidates remain exhaustive

Retain the support quantities H,P_M,P_B and the E,N,D functions from
Sections 2--3 of the companion proof. The only new issue is minimizing
\(P_B-\Phi\) over the original B orientation.

The triangle inequality for centered support gives

\[
 h_B(be-kn)+k h_B(n)\ge b h_B(e),
\]

and hence

\[
 P_B\ge2b h_B(e)=b(\alpha_B+\beta_B).
\tag{4}
\]

On any interval of fixed projection signs and fixed folded-angle branch,
\(P_B-\Phi\) is a linear sine/cosine expression plus the constant b.
Its second derivative is

\[
 -P_B+6\beta_B+b\alpha_B
       \le -(b-6)\beta_B\le0.
\tag{5}
\]

Thus it is concave on every such interval. The possible interval endpoints
are exactly the same four frame candidates: alignment with e,n,be-kn,
or the 45-degree folded-angle boundary. Equality in (5) at an aligned
endpoint causes no loss of coverage; concavity, rather than strict
concavity, is all that is needed. The same physical owner split applies:
if M owns n, test those four B candidates; if B owns n, test the three
unmodified E,N,D candidates for M while retaining B's actual owned frame.

Write \(c=e\cdot n\), \(s=\sqrt{1-c^2}\), and put

\[
 (\alpha_N,\beta_N)=(\max(|c|,s),\min(|c|,s)),
\]

\[
 (\alpha_D,\beta_D)=
 {1\over L_b(-c)}(\max(b-kc,ks),\min(b-kc,ks)).
\tag{6}
\]

The e-aligned toll is zero. In the 45-degree frame it is
\((6+b)/\sqrt2-b\). Consequently it suffices to prove

\[
 \begin{array}{ll}
 G_0=T-H+E_a(c)+N_b(-c)-\Phi(\alpha_N,\beta_N),\\
 G_1=T-H+N_a(c)+N_b(-c)-\Phi(\alpha_N,\beta_N),\\
 G_2=T-H+D_a(c)+N_b(-c)-\Phi(\alpha_N,\beta_N),\\
 G_3=T-H+N_a(c)+D_b(-c)-\Phi(\alpha_D,\beta_D),\\
 G_4=T-H+N_a(c)+P_{45}(c)-(6+b)/\sqrt2+b
 \end{array}
\tag{7}
\]

are nonnegative on \([-1,1]\), together with the already proved e-aligned
entry \(T-H+N_a+E_b(-c)\ge0\). This is the complete physical
owner/candidate union, including both signs of c and both original
chiralities.

## 3. The two scalar rows meeting equality at c=0

Use \(H(c)\le H(0)+(k/2)c\), \(s\ge1-c^2\), and the same
constant identities as in the companion proof. On \(|c|\le1/32\),
\(\beta_N=|c|\), \(\alpha_N=s\), so
\(\Phi=6|c|-b(1-s)\). The exact near-zero N branches give

| Row and sign | Exact lower bound |
|---|---|
| G0, \(0\le c\le1/32\) | \((33/512)c\) |
| G0, \(-1/32\le c\le0\) | \((6945/512)|c|\) |
| G1, \(0\le c\le1/32\) | \((1027/32)c\) |
| G1, \(-1/32\le c\le0\) | \((401/32)|c|\) |

The coefficients are respectively

\[
 k/2-6-k/32,\quad k/2+b-6-k/32,
 \quad a-k/2-6-a/32,\quad k/2+b-6-a/32.
\]

All are positive. These formulas include c=0 and both collar boundaries.

## 4. Complete exact complement table

`universal_pair_curved_tilt_toll_cover.json` covers all remaining closed
intervals. Its seven roots, leaf counts, and rounded-down rational lower
bounds are as follows.

| Row | Closed root interval | Strict leaves | Replayed lower bound at every leaf |
|---|---|---:|---:|
| G0 | \([-1,-1/32]\) | 17 | \(19445/10^6\) |
| G0 | \([1/32,1]\) | 275 | \(36/10^6\) |
| G1 | \([-1,-1/32]\) | 26 | \(17592/10^6\) |
| G1 | \([1/32,1]\) | 19 | \(203752/10^6\) |
| G2 | \([-1,1]\) | 428 | \(37/10^6\) |
| G3 | \([-1,1]\) | 68 | \(77938/10^6\) |
| G4 | \([-1,1]\) | 27 | \(48224/10^6\) |

There are 1,713 nodes and 860 strict leaves, maximum depth 16. The
producer `certify_universal_pair_curved_tilt_toll.py` uses exact Fraction
intervals, with outward 80-bit roots, and both the piecewise scalar and
absolute-support expressions for N,D. Every midpoint split retains both
closed children; no unresolved interval or discarded endpoint remains.

The independent `verify_universal_pair_curved_tilt_toll.py` reconstructs
the complete cover with outward 64-bit integer dyadic intervals. It imports
neither producer nor producer interval evaluator; its N,D penalties are
calculated from the absolute support expressions. It verifies all four
analytic collar coefficients and every printed rational table bound.
The least exact reserve is

\[
                  21015472069061/576460752303423488>0.
\]

Certificate SHA256:
`9ba10374718180ebdc4fe1d95675f898c4b549919785ad2d5f8bf62142617cb0`.
The report is `universal_pair_curved_tilt_toll_replay.json`. Four damaged
root/split/channel/leaf controls were rejected and recorded separately in
`universal_pair_curved_tilt_toll_negative_controls.json`.

The analytic neighborhood and these complete strict tables prove (7),
and the original physical support reduction proves (2).

## 5. Use in the middle-main resource without a new angle variable

For an existing original-shoulder tangent t, use

\[
 \alpha=(1+t^2)^{-1/2},\quad\beta=t\alpha,
 \quad\tau=\max\{2\beta,6\beta-b(1-\alpha)\}.
\]

The shared main-tilt bounds in Section 5 of the companion theorem now have
the individual deductions \(\tau_L/92,\tau_R/92\), the summed deduction
\((\tau_L+\tau_R)/92\), and the adaptive opposite-load additions
\(\tau_R/46,\tau_L/46\). These are simply the algebraic consequences
of the two inequalities with the *same original shoulder* tolls retained.

The function \(6\sin\theta+b\cos\theta-b\) is concave on the folded
angle range. Therefore its minimum over any tangent interval is at one of
the two endpoint angles. This supplies an exact interval lower bound using
the already available endpoint frames, with no independent replacement
orientation. The linear toll is increasing in t; taking the maximum of
the two valid lower bounds remains valid for (3).

This theorem is a reusable physical inequality. It does not assert the
unfinished seven-unit exclusion or change any mask count by itself.
