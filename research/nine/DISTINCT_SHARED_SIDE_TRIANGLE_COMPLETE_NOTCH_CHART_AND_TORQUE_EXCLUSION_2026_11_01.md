# Distinct shared-side triangle: exhaustive notch chart and exact torque exclusion of the corner-to-side branch

November 1, 2026. PR #11 continuation. **Evidence at construction: H.** The geometry and vector agents independently obtained the same radius-free torque contradiction in Section 4. A noncontributor review is requested for the complete manuscript.

## 1. Exact original hypotheses

Retain one original physical contact-force-and-torque certificate on the same actual packing. Three actual unit squares A,B,C are entirely selected-circle-unloaded, have positive triangle edges AB,BC,CA and exactly one original positive outside exit at each. All original applications and shared-side means are retained. Outside actual terminals can repeat and have arbitrary frames, loads, degrees and other contacts. At point-only original contacts retain the established strict singleton-normal convention.

Suppose the three actual squares have **no common physical point**, but at least one pair has a positive-length physical shared-side contact. This manuscript proves a complete finite geometric chart for this entire feature, including the exceptional endpoint and the genuine corner-to-side branch. It then excludes the latter branch by the full original torque equations, independently of any disk radius.

No vertex-to-side contact may be silently converted to a vertex-to-vertex one. In particular the initial full-side notch chart with two adjacent C vertices is not exhaustive by itself; the additional parameter lambda below is necessary.

## 2. Every such physical triple is in one of three precise notch charts

Choose a shared-side pair as A,B. Their frames are parallel. By one rigid motion, reflections and exchange of A,B, write

    A=[0,1] x [0,1],
    B=[1,2] x [s,s+1],       0<=s<1.

The original AB mean remains (1,m), with s<=m<=1. The case s=0 would make A union B a rectangle. Any segment joining a point of C intersect A to a point of C intersect B then passes through their full common edge; convexity of C would give a common point of all three squares. Hence s>0.

All three frames cannot be parallel: three pairwise-intersecting axis-aligned rectangles have a common point, because their three horizontal intervals have a common intersection and so do their three vertical intervals. Thus C has a nonparallel frame. Its pair intersections with A and B are point-only, since a positive boundary segment would force its frame to be parallel as well. Denote the two unique actual points by p and q, respectively.

### 2.1 The points must occupy one actual notch

The segment [p,q] lies in C. It crosses the line x=1 outside the shared segment {1} x [s,1]; otherwise its crossing point would belong to all three squares. Its crossing therefore has height above 1 or below s. Rotation by pi about (1,(s+1)/2), followed by exchanging A and B, exchanges these two possibilities while preserving the displayed chart. Choose the upper notch.

Then necessarily

    p=(x,1),       0<=x<1,
    q=(1,y),       1<y<=s+1.                       (1)

Indeed, if q had first coordinate strictly greater than 1, the segment would enter B's open interior immediately after crossing x=1: the crossing height is strictly below q's height and hence below or equal to s+1, and strictly above 1>s. Therefore q has first coordinate 1 and height above 1. The same segment would enter A's open interior immediately after p if p had height below 1. It follows that p lies on A's top side. The endpoints x=1 or y=1 would already be common points and are excluded.

### 2.2 The two contacts lie on one actual C edge

Because C is nonparallel to A and B, choose its inward axes as

    u=(c,h),       v=(-h,c),
    c>0, h>0,     c^2+h^2=1.

Let P be its bottommost vertex. Its rightmost vertex is P+u, and its rising lower-right edge is

    P+[0,1]u.

If p is in the interior of A's top side, its unique outward support normal is North, and the minimum-North point of C is exactly P. If p is A's upper-left vertex, its retained strict normal points Northwest. For any Northwest vector n=(-alpha,beta), alpha,beta>0, one has n dot v=alpha h+beta c>0; consequently a minimizing point of C must have v-coordinate zero and lies on the displayed edge.

Similarly, if q is in the interior of B's left side, its unique outward normal is West, so it is exactly C's rightmost vertex P+u. If q is B's upper-left vertex, the same Northwest-normal calculation puts q on the displayed edge. Thus both p and q lie on this one unit segment, in that order.

The possibility p=(0,1) is impossible: its horizontal separation from q would be 1, whereas the horizontal extent of the displayed unit segment is c<1. Therefore p lies in the **interior** of A's top side and is exactly P. We have

    q=P+lambda u,       0<lambda<=1.               (2)

If lambda<1, q is not C's rightmost vertex and hence cannot lie in the interior of B's left side. It must be B's upper-left vertex. Combining (1)--(2) yields the following exhaustive table.

| Type | Exact actual geometry | Original AC and BC contact feature |
| --- | --- | --- |
| I: strict side owner | lambda=1, P=(1-c,1), q=(1,1+h), 0<h<s<1 | AC: A top-side interior/C bottom vertex, normal North. BC: B left-side interior/C right vertex, normal West from B. |
| II: corner-to-side | 0<lambda<1, s=lambda h, P=(1-lambda c,1), q=(1,1+s)=P+lambda u | AC: A top-side interior/C bottom vertex, normal North. BC: B upper-left vertex/C edge interior, normal (-h,c) from B. |
| III: vertex endpoint | lambda=1, s=h, P=(1-c,1), q=(1,1+s)=P+u | AC: A top-side interior/C bottom vertex, normal North. BC: B upper-left vertex/C right vertex, retaining its original strict common normal. |

In every row the entire actual third square is

    C=P+[0,1]u+[0,1]v.

The inequalities c,h>0 include every nonparallel orientation modulo quarter turns. The omitted angular endpoints are parallel frames, already incompatible with no common point. The classification includes all AB means m in [s,1]. Type III must not inherit the West normal of Type I: its original point-only selected normal can be a different strict common normal.

## 3. Original force and application data for Type II

Retain arbitrary positive original magnitudes

    AB=t>0,      AC=a>0,      BC=b>0.

The complete physical support features in Type II force the original oriented vectors and applications to be

    A-to-B: t(1,0),        at (1,m),       s<=m<=1;
    A-to-C: a(0,1),        at P=(p,1),     p=1-lambda c;
    B-to-C: b(-h,c),       at q=P+lambda u=(1,1+s).

The BC direction is forced because the actual B vertex lies in the **interior** of C's edge parallel to u. It is not a convenient reselected normal. Also s=lambda h and 0<lambda<1.

The complete original translations then force the three positive outside vectors:

    E_A=(-t,-a),
    E_B=(t+bh,-bc),
    E_C=(-bh,a+bc).

In particular A's original outside application is its strict Southwest corner (0,0), and B's is its strict Southeast corner (2,s). At C the own-frame components are

    E_C dot u = ah > 0,
    E_C dot v = b+ac > 0.

Thus C's original outside application is exactly P+u+v. All these are consequences of the actual support equations; none is selected after the fact.

## 4. The full B and C torques contradict one another

The complete B torque about (0,0), retaining the original application (1,m), is

    det((1,m),(-t,0))
      + det((1,1+s),b(-h,c))
      + det((2,s),(t+bh,-bc)) = 0.

Expanding gives

    (m-s)t+b(h-c)=0,
    b(c-h)=(m-s)t>=0.

Since b>0, this forces c>=h.

Now take C's complete torque about its actual bottom vertex P. The AC application is P and contributes zero. Its BC application is P+lambda u, with inward force b(h,-c)=-b v, and contributes -lambda b. The outside application is P+u+v and contributes

    det(u+v,E_C)
      = E_C dot v - E_C dot u
      = b+a(c-h).

Therefore the original C equation is exactly

    (1-lambda)b+a(c-h)=0.                          (3)

But 1-lambda>0, b>0, a>0 and c-h>=0. Its left side is strictly positive. This contradiction excludes the entire Type II contact family, including every original mean m, every positive magnitude ratio and arbitrary outside terminals, without any bound on the disk radius.

For reference the unchanged A torque is t m=a p, consistent with the support derivation but not needed for the final contradiction. No original equation has been replaced by a shortened two-force star.

## 5. Exact result and integration boundary

Section 2 is an exhaustive physical classification of every no-common-point three-square triangle having any positive-length internal shared side. Type II is now completely excluded by the exact full-moment contradiction (3).

Type I and the strict-normal endpoint Type III are separate full domains. Their exclusion requires their corresponding complete arguments; the present manuscript does not declare them closed merely from the table. Once all three rows are proved, the entire distinct-contact shared-side family is excluded, with the common-point family already handled separately.

This does not cover a triple whose three physical intersections are all singletons. No original coarse/fine gate count changes on the strength of this document alone. No numerical sample, tolerance, solver infeasibility claim, Lean or CI has been used.
