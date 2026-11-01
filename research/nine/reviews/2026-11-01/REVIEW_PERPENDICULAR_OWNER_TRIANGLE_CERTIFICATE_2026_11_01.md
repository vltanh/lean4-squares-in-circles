# Independent review and replay: perpendicular-owner triangle certificate

Reviewed November 1, 2026 by a noncontributor to the original physical theorem
and certificate generator. The reviewer independently derived the physical
elimination, inspected the arithmetic kernel and full root cover, replayed the
generator, and implemented a separate certificate traversal and arithmetic
reconstruction without importing the generator.

**Verdict: accepted as an exact, independently reviewed computer-assisted
feature theorem.** The specified perpendicular-owner, own-exit physical chart
forces \(R>25/12\). The review found no gap in the original-force transfer,
original mean equations, strict inequality direction, limiting-angle treatment,
root coverage, outward square-root enclosures, or finite certificate traversal.
It is not a Lean verification or a proof that every remaining owner pattern
belongs to this chart.

## 1. Exact source pins

| Source | SHA-256 |
| --- | --- |
| [Physical theorem and root contract](../../computer_assisted/PERPENDICULAR_OWNER_SINGLE_FREE_TRIANGLE_EXACT_EXCLUSION_2026_11_01.md) | `415287a53b5f90e3c5439161459ede14a71309b29bc4adfd3f62f80631c283ee` |
| [Certificate generator](../../computer_assisted/verify_perpendicular_single_free_triangle.py) | `7f20ea36c20550d996dbcc3467bdc9ec9f1ff58fd82e4e0472bf503b00d595ad` |
| [Complete stored certificate](../../computer_assisted/perpendicular_single_free_triangle_certificate.json) | `80163adabea7bd279db5f911f110219bf45ffb9217812f52473c03a05ba5cf70` |
| [Independent certificate checker](../../computer_assisted/verify_perpendicular_certificate_independent.py) | `104a7cd31c55d49bf698c7d415b881771bda1632f199a7450c76b1dd797853a9` |

The independently regenerated certificate has the same SHA-256 as the stored
certificate, byte for byte. The manuscript pin includes the reviewed reporting
correction from “nonempty” to “variance-certified” leaves and the explicit
statement that certification does not prove physical feasibility of a leaf.
Its mathematical argument and executable certificate are unchanged. These
pins precede any later evidence-label-only adoption changes.

## 2. Independent physical transfer

The stated chart retains three actual unloaded squares, their full original
positive triangle and one original positive outside exit at each. The two
\(C\)-owned contacts are \((1,s)\), \((t,1)\), with \(0<s,t<1\). Their
positive forces may initially be written \((a,0)\), \((0,b)\). The complete
\(C\)-translation forces its outside vector to \((-a,-b)\), whose actual
application on \(C\) is \((0,0)\). Full torque there gives \(tb=sa\).
Thus the single positive rescaling \(a/t=b/s\) makes the original vectors
exactly \((t,0)\), \((0,s)\). No force or application is dropped.

Equality of the unchanged AB vertex,
\(p_A+u_A=p_B+u_B\), gives precisely

\[
 t=1-\cos\alpha+\cos\beta,
 \qquad s=1+\sin\alpha-\sin\beta.
\]

The determinant of the two stated original own-exit normals is
\(\det(v_A,v_B)=\sin(\beta-\alpha)=\Delta>0\). Solving their full summed
translation gives the manuscript's positive \(z_A,z_B\) formulas.

The two torque signs were independently checked about the original AB vertex.
At \(A\), \(\det(u_A,v_A)=-1\): its original \(C\)-force contributes
\(-t\sin\beta\), and its actual exit contributes
\((1-\tau_A)z_A\). At \(B\), \(\det(u_B,v_B)=+1\): the corresponding moments
are \(s\cos\alpha\) and \((\tau_B-1)z_B\). Therefore the exact original means
are the two displayed cancelled expressions for \(\tau_A,\tau_B\).
Their range constraints \(0\le\tau_A,\tau_B\le1\) are genuine support-mean
conditions, not freely chosen replacement points.

At every outside contact, adding its unit normal to the original minimum-
support point stays in the same actual unit square, component by component
in its own frame. Consequently all three displayed \(w_A,w_B,w_C\) are actual
points of the unchanged original disk. This remains true when outside terminals
coincide. The equal-weight identity

\[
 \frac{|w_A-w_B|^2+|w_B-w_C|^2+|w_C-w_A|^2}{9}\le R^2
\]

is exact. A strict lower bound above \(625/144\) has the claimed exclusion
direction, and \(625/144-1105/256=55/2304>0\).

## 3. Complete root coverage and limiting cases

Every original angle pair lies in \(0<p<q<1\), with
\(p=\tan(\alpha/2)\), \(q=\tan(\beta/2)\). The two compact rectangles and the
analytic tail cover the entire larger ordered closed triangle:

| Region | \(p\) | \(q\) |
| --- | --- | --- |
| Analytic tail | \([0,1/20]\) | \([10/11,1]\) |
| First compact root | \([0,1/20]\) | \([0,10/11]\) |
| Second compact root | \([1/20,1]\) | \([0,1]\), retaining \(p\le q\) |

The roots overlap on their boundaries, leaving no uncovered face. The only
point where both \(t,s\) vanish is \((0,1)\), entirely inside the analytic tail.
On the first compact root, order implies \(t\ge21/221\) and
\(s\ge1/221\). On the second compact root, order and \(p\ge1/20\) imply
\(t\ge1-\cos(2\arctan(1/20))>0\) and
\(s\ge\sin(2\arctan(1/20))>0\). The cancelled mean denominators and the norm
denominator are consequently positive throughout both compact physical domains.

At \(p=q\), the cancelled means extend continuously to one. The enclosure
uses that boundary only to enlarge the strict original domain; it does not
assert a finite original stress there. Division by an interval containing
zero is never accepted: the generator subdivides instead.

The analytic tail does not evaluate the undefined normalized vector at
\((0,1)\). Its proof permits **every** negative-quadrant unit vector there,
and arbitrary original means in \([0,1]\). This safely covers all original
strict approaches and every possible limiting direction without selecting a
ratio for \(t/s\).

## 4. Analytic tail checked exactly

The rational endpoint bounds imply \(\sin\alpha\le1/10\) and
\(\cos\beta\le1/10\), hence \(\cos\alpha,\sin\beta\ge99/100\).
Nonnegative original means therefore give
\(w_{A,x},w_{B,y}\ge149/50\). If \(R\le25/12\), both disk-center coordinates
are at least \(L=269/300>0\).

For any negative-quadrant unit point \((-u,-v)\),
\(u,v\ge0\), \(u+v\ge1\). Its squared distance from that disk center is at
least \(2L^2+1+2L\). The exact strict reserve is

\[
 2\left(\frac{269}{300}\right)^2+1
 +2\left(\frac{269}{300}\right)-\frac{625}{144}
 =\frac{5497}{90000}>0.
\]

Thus the entire tail has a complete analytic contradiction, including every
original side mean and every negative unit-direction limit.

## 5. Arithmetic kernel and independent certificate reconstruction

The interval kernel was inspected operation by operation. Products use all
endpoint combinations; squares include zero when the interval crosses zero;
positive reciprocals reverse endpoints. The half-angle sine/cosine endpoints
are monotone on the declared domain. For \(p\le q\), the angle difference lies
in \([0,\pi/2]\), so the stated sine-difference endpoint bounds are outward.
Intersections with \([0,1]\) preserve every actual contact-position or original
mean value.

For square roots, the floor/ceiling integer construction is accompanied by
exact checks of \(\ell^2\le q_{\rm lo}\) and \(u^2\ge q_{\rm hi}\). The
reciprocal of the resulting positive norm interval therefore encloses the
normalized original \(C\)-exit point. No floating-point rounding enters.

In addition to replaying the original generator, the reviewer wrote a separate
checker with no import of that generator. It:

- Reconstructs both exact roots and every closed midpoint split from binary
  addresses, requiring both children and no unused or duplicate records.
- Verifies each stored leaf box equals its reconstructed descendant box.
- Checks every order-empty leaf by the strict interval inequality
  \(p_{\rm lo}>q_{\rm hi}\).
- Recomputes all component enclosures and every stored rational variance
  lower bound independently, obtaining exact equality with all recorded values.
- Checks every variance reserve is strictly greater than \(1/6000\), and
  independently checks the tail's scalar reserve and report metadata.

The executed independent reconstruction passed:

| Compact root | Nodes | Strict variance leaves | Empty-order leaves | Maximum depth |
| --- | ---: | ---: | ---: | ---: |
| First | 143 | 72 | 0 | 10 |
| Second | 755 | 369 | 9 | 15 |
| **Total** | **898** | **441** | **9** | **15** |

No position-empty, mean-empty, unresolved, tolerance, or sampled leaf was used.
The exact finite split tree covers both full compact roots on the ordered
domain; the analytic tail covers the remaining region.

## 6. Reproduction and adoption boundary

From the repository root, with ordinary Python and assertions enabled:

```bash
python research/nine/computer_assisted/verify_perpendicular_single_free_triangle.py --certificate /tmp/perpendicular_triangle_replay.json
python research/nine/computer_assisted/verify_perpendicular_certificate_independent.py
```

The independent checker optionally accepts a certificate path as its first
argument. Both programs use Python's standard library only.

This review validates the full radius obstruction at the exact stated chart
and owner hypotheses. A caller must still establish that its original selected
certificate has this chart, including the own-axis exits and perpendicular
\(C\)-owned returns. No force or application may be reselected during that
join. Other owner masks and full original-parent adoption remain separate
obligations. No Lean, Lake, or CI was used.
