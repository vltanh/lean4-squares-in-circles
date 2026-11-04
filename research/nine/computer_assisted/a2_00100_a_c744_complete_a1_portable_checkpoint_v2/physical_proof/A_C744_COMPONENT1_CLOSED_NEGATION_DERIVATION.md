# A c744: the consequence of excluding complement 1

This note records the implication to use after a fresh exact replay has proved the entire closed complement 1. It does not assert that the current numerical tree is complete.

Let P be the unchanged original cell positive-c744bc031d40ee64, with original path

```
[['angle',3,1],['angle_cut',[0,'0'],0],['inward_row_escape',[7,8],[4]]]
```

P retains the nine original squares, all original corner and pair constraints, the five marked cones, actual AB/BC/EF/FG links, and the strict weak CD link. Its component-1 parent is the complete closed domain

\[
E_1:\quad y_B-y_D\le -3/5.
\]

If an independently replayed complete 4/8/2 tree excludes P intersect E1, every physical point of P satisfies y_B-y_D > -3/5. Weakening this strict relation gives the necessary original-wide affine inequality

\[
y_D-y_B\le3/5.
\]

In the original 54-variable indexing, the exact sparse row is

```
coefficients = [[3, '-1'], [7, '1']]
rhs = '3/5'
```

No descendant SAT choice, orientation cut, selected physical proxy, or child interval is transported. The new row is valid on every descendant of P because the excluded source domain covers its entire component. The weak inequality includes the shared equality face; the source exclusion is the stronger closed statement.

The source checker must be frozen before this new row is introduced and must not dispatch its future row prefix. Its fresh replay must bind the exact original ID/path, component 1, unchanged whole parent, the displayed closed domain, the complete tree manifest, every source node, every closed cover, and zero remaining open leaves. A saved PASS report alone is not a premise.

## Effect inside complement 3

Complement 3 separately supplies

\[
y_B+y_D-2y_I\le-3/5.
\]

Adding the new original-wide inequality gives

\[
2y_D-2y_I\le0,
\]

hence y_D <= y_I on that component. This latter relation is conditional on component 3. It must not be promoted to an original-wide bound. The numerical context can obtain it by a nonnegative sum of the two exact rows; only the first, original-wide row needs a new proof-bound attachment.
