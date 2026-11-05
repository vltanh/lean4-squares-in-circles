# Shared sharp boundary terminal for A c744 and B462

This is a complete conditional theorem for the unchanged original-nine
`001/00` caller. It supplies a genuine neighborhood of the aligned
closed-Q control. It does **not** by itself close either entire original
cell; their complementary domains require complete proofs.

## 1. Literal seven-original substitution

Retain nine original, independently oriented physical unit squares
`A,B,C,D,E,F,G,H,I`, every corner and every pairwise nonoverlap condition.
Retain the original actual links `AB,BC,EF,FG`, all five center-cone
comparisons, and the strictly weak comparison

\[
x_D-x_C<h_C+h_D.
\]

Write `Q=1105/256`. The normalized original caller supplies the already
proved shoulder orders `y_E>y_A` and `y_G>y_D`. These orders must be
retained or independently checked; they are not new assumptions silently
added to an original cell.

Apply Sections 1–7 of
`research/nine/ALL_SIGN_CORRELATED_CORNER_ROW_HAND_STRENGTHENING.md` with
the following substitution:

| Source theorem label | Physical original here |
|---|---|
| A | A |
| H | B |
| I | I |
| D | D |
| E,F,G | E,F,G |

These are seven distinct original squares. The source theorem is stated
for seven distinct physical squares and does not require its labels H
and I to be the two squares omitted by the original marked chain. Thus
this substitution is literal. The original C and H remain physical and
can have arbitrary frames and positions allowed by the original caller.

Set

\[
U_{ABID}=|y_B-y_A|+|y_I-y_B|+|y_D-y_I|.
\]

Any one of the following three rows is sufficient:

| Bound on all seven `|beta|` for A,B,I,D,E,F,G | Bound on `U_ABID` |
|---|---|
| `1/30` | `11/30` |
| `1/50` | `9/20` |
| `1/200` | `53/100` |

The first two rows are printed specializations in the source. The third
is a fresh exact specialization of its general rational criterion, with
`L=7/10`. All criterion checks pass, and its final positive coefficient is

\[
\varepsilon=
\frac{58049449601280546655747607}{327651328921587200064000000}>0.
\]

Together with `x_B<=x_I<=x_D`, any row excludes the original strict
caller for every `q<Q`. It also excludes a configuration with the same
explicit hypotheses at closed Q if the original CD bit remains strictly
weak.

## 2. Complete proof, including the equality face

The original actual AB comparison gives `x_A<x_B`. If `x_I=x_B` or
`x_I=x_D`, the corresponding vertical gap has magnitude at most
`U_ABID<1`. The centers of two interior-disjoint unit squares have
distance at least one, because their open radius-one-half incircles
are disjoint. Thus either x equality is impossible. The order needed
by the seven-square theorem is therefore strict:

\[
x_A<x_B<x_I<x_D.
\]

All its other hypotheses are now literal: the actual EFG projection
chain, the two upward shoulder orders, the seven independent physical
frames and corners, and every physical pair among these seven originals.
The source theorem gives `q>=Q`, contradicting `q<Q`.

For the closed-Q equality face, the same theorem forces the seven
selected originals to be aligned and `x_D-x_A=3`. The original marked
links and CD cone-inset inequality give

\[
3=x_D-x_A\ge h_A+2h_B+h_C+g_C+g_D
 =2+h_C+g_C\ge3.
\]

Here A,B,D have already been forced aligned. The final inequality is
the exact identity

\[
h_C+g_C-1=h_C+\frac1{4h_C}-1
          =\frac{(2h_C-1)^2}{4h_C}\ge0.
\]

Equality forces C aligned as well. Then the original CD cone-inset
comparison reads `x_D-x_C>=g_C+g_D=1=h_C+h_D`, contradicting the retained
strict weak bit. Thus no positive distance from the weak/actual boundary
is needed, and no positive numerical reserve is substituted for this
equality argument.

## 3. An explicit neighborhood of the exact control

The common aligned control has

\[
y_A=y_B=y_I=y_D=-1/16,\quad x_I=1/2,
\]

with all seven selected slopes zero. The following closed cylinder
contains a neighborhood of these values:

\[
1/4\le x_I\le3/4,\qquad
-9/80\le y_A,y_B,y_I,y_D\le-1/80,
\]

and all seven selected folded signed slopes satisfy `|tan(theta)|<=1/30`.
The latter implies `|beta|<=1/30`. The three height gaps are each at most
`1/10`, so `U_ABID<=3/10<11/30`.

For B462 the freshly replayed prefix gives

\[
x_B\le-452125/1048576<1/4,
\qquad x_D\ge6684432029724121/5000000000000000>3/4.
\]

The exact numerator bounds should be read from the frozen replay state
when used by a checker; the terminal only needs the displayed strict
comparisons. For another caller, including A c744, check these two order
bounds directly or retain `x_B<=x_I<=x_D` in the terminal guard.

No cylinder is imposed on original C or H. No cylinder on the centers
of E,F,G is needed beyond the original physical caller and the two
proved shoulder orders. In particular, this terminal covers continuous
families of placements of the two omitted originals, not merely one
isolated aligned point.

## 4. Exact fixed complementary cover

Use the first parameter row, `b=1/30` and `U0=11/30`. Let `e_i=|beta_i|`,
the existing physical absolute-frame variable. The complement of the
terminal hypotheses is covered by the following **fixed 17 closed
domains**:

1. `x_I<=x_B` or `x_I>=x_D` — two domains.
2. For each of the seven selected originals, `e_i>=b` — seven domains.
   This is one affine guard in the existing physical variable `e_i`;
   its meaning remains exactly the absolute value of that original's
   signed frame component. It covers both signs without a new choice.
3. For each `(s1,s2,s3)` in `{-1,1}^3`,

   \[
   s_1(y_B-y_A)+s_2(y_I-y_B)+s_3(y_D-y_I)\ge U_0
   \]

   — eight domains.

The maximum of the eight signed height expressions is exactly
`U_ABID`. Every failure of a terminal hypothesis therefore lies in
one of these domains. Equality faces are included in both sides where
appropriate, which is harmless. This is a single complete finite cover,
not a sequence of discarded boundary neighborhoods.

If the independently certified original bounds imply `x_I<x_D`, the
second order domain is empty, leaving **16 closed complementary domains**.
An absolute-frame escape may be eliminated only when the exact original
caller proves it empty. The same derivation
works for each parameter row. Combining the three terminal rows can
enlarge the accepted region, but does not permit dropping a complement.

## 5. Current evidence and acceptance scope

The exact aligned control lies in the closed relaxations of both
`negative-462e78d2e2d8be05` and `positive-c744bc031d40ee64`; it fails the
original strict CD bit. Its membership has been checked against the
respective unchanged paths and certified bounds. For B462, the exact
control also satisfies every one of the 69,817 rows in the current
whole-parent quadratic discovery model. A positive-reserve exclusion of
that closed model is consequently impossible.

The theorem above proves the local strict-boundary exclusion needed by
both callers. Whole-original closure additionally requires exclusion of
every complementary domain retained by a complete cover. Until that
assembly is finished, both original cells remain OPEN and no mask count
changes.

## 6. A second row and the continuous aligned slider family

The same accepted theorem can also use the original row A,H,I,D and the
same E,F,G. This is the literal original source labeling. It leaves B,C
unrestricted. The equality argument again uses
`3>=1+2h_B+h_C+g_C>=3`, forcing B,C aligned and contradicting strict CD.
The helper checks both row choices separately against the same state;
one valid complete row guard suffices for that state.

For AHID the three orders `x_A<=x_H<=x_I<=x_D` must all be checked;
unlike ABID, the first does not follow from an original actual link.
Its unconditional fixed complement has 18 closed domains: three order
escapes, seven absolute-frame escapes, and eight signed-height escapes.
The exact original bound `x_I<x_D`, when available, eliminates one of
these domains. Combining row choices means proving the intersection of
their complementary conditions, never silently discarding one of them.

This second choice matters for B462. Swapping B and H in the aligned
control preserves its complete path, all current certified intervals,
and all 12,817 rebuilt affine base rows. It has `U_ABID=2` but
`U_AHID=0`. Thus the complement of only the ABID terminal still contains
a real closed-Q boundary point.

There is also a continuous family with all frames aligned, all other
centers equal to the original control, and

\[
y_B=-1/16-t,\qquad y_H=-17/16-t,\qquad
0\le t\le t_*:=\frac{\sqrt{849}-25}{16}.
\]

All pairwise nonoverlap conditions and original center-cone comparisons
remain true. The farthest H corner has squared norm
`1+(25/16+t)^2`, so the displayed interval ends exactly when that corner
reaches Q. The four outer controls A,D,E,G already attain Q throughout.
The original CD horizontal gap remains one and its strict weak bit
remains false. At `t=1/4`, the two earlier parameter rows do not apply:
`U_ABID=1/2` and `U_AHID=5/2`.

The third parameter row covers the **entire** slider family, with strict
room in its hypotheses. Indeed,

\[
U_{ABID}=2t\le\frac{\sqrt{849}-25}{8}<\frac{53}{100},
\]

because `849<(731/25)^2`, with exact squared reserve `3736/625`.
All seven selected frame components are zero, strictly below `1/200`.
The endpoint horizontal and shoulder orders are strict. Consequently
this is genuine neighborhood coverage of every member of the family,
including its terminal H-circle-contact face. It is not a deletion of
one sampled point or a positive-clearance assumption.

Any future positive-reserve-only complementary search must retain both
row choices and account for these parameter ranges. These controls are
not a classification of every possible closed-Q boundary configuration.
