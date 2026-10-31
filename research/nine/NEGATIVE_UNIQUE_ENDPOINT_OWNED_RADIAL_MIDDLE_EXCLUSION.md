# A negative A-owned endpoint cannot have a physical radial middle neighbor

**Status: complete all-radius hand exclusion; author, root and separate
independent full proof audits passed.** Work throughout
\[
                  79/40\le R\le\sqrt{1105}/16,\qquad q=R^2.
\]
Let A have exactly two positive pair neighbors H,B and a positive
load at its unique physical circle corner z. B has two physical
circle corners, with every original nonnegative individual weight
retained. H and B may have arbitrary additional positive forces.
Assume \(c_H\cdot z<0\) and that the actual HA normal is a side
axis of A. Every actual shared HA mean and all other physical
squares remain. No HB contact is assumed.

**Theorem.** This entire A-owned HA family is impossible, including
every singleton and every genuine shared HA interface, on the full
radius interval.

## 1. The complete previously proved contact feature

NEGATIVE_UNIQUE_ENDPOINT_OWNED_CONTACT_DOMAIN.md proves, in the
actual A frame,
\[
 z=(a,b),\quad A=[a-1,a]\times[b-1,b],\quad a^2+b^2=q,
\]
that its outgoing AB normal g is strictly northwest, its contact is
exactly \(T=(a-1,b)\), and its actual support is strictly positive.
The same full-window theorem excludes every radial-B side-axis
owner: the three nonpositive minimum supports contradict that sign,
and the inner radial side makes A circle-clear by the complete
radial-inner-face lemma. These conclusions retain the unchanged HA
mean and do not use B's force equation.

Thus g is not a B side axis. Its B support must be a vertex, so T
would be an actual B vertex.

## 2. The exact physical vertex radii contradict that feature

Put \(d=\sqrt{q-1/4}-1\). A physical radial B has two outer circle
vertices, which no other contained unit can share, and two inner
vertices, each with squared norm
\[
                         d^2+1/4=q-2d-1.
\]
Physical uniqueness of A gives \(b>1/2\), hence
\[
                     a<\sqrt{q-1/4}=d+1.
\]
But the unchanged A contact has squared norm
\[
                    |T|^2=q-2a+1>q-2d-1=d^2+1/4.
\]
It is neither an inner B vertex nor a shareable outer one. This
contradiction proves the theorem.

In the triangle-attached ABC orbit, the entire A-owned/shared HA
portions of both radial-middle masks SUS and SUU are therefore
excluded at every radius, including below \(R^2=17/4\). The other
HA owners retain their separate theorems and residual domains.
The argument also allows a higher-degree middle B, since only A
uses a degree-two equation. It changes no H force, physical mask,
individual zero weight, original mean or completion square.
No numerical pose, new normal choice, Lean compilation or CI is used.
