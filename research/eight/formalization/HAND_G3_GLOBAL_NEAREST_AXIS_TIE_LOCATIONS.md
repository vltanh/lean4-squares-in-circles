# Only the positive H and negative D diagonals can be nearest-axis ties

## 1. Statement

Use the actual G0--G2 seven-cycle, with role order
\((H,G,A,B,T,D,E)\), quarter word
\(k=(0,1,0,1,0,1,1)\), common real frame spread below
7/10, and physical center gaps greater than 19/25.
Write a canonical own-frame center as \((a,-y)\), with
\(a\ge b=|y|\).

**Nearest-axis tie theorem.** The five roles G,A,B,T,E
are strictly sorted:
\[
                        a_i>b_i\qquad(i=G,A,B,T,E).
                                                               \tag{1}
\]
A tie at H can only have positive tangent, and a tie at D
can only have negative tangent. These two remaining tie
locations admit the exact surviving-word recoding described
in the diagonal-D note and its reflected counterpart.

There is no hypothesis on the original separating owners,
on a mismatch sum, on any other transverse sign, on radial
kinds, or on frame order. In particular this theorem is
available before the global quarter-owner capture.

## 2. Changing an actual nearest-axis representative

Suppose a=b at one actual center. At positive tangent y=b,
decrease its directed square-axis representative by pi/2.
At negative tangent y=-b, increase that representative by
pi/2. Each operation chooses the other nearest axis of the
same physical square. The center and square do not move;
the new canonical coordinates are respectively
\[
              (a^{\rm new},y^{\rm new})=(b,-a),
                     \qquad(b,+a).
\]
Because a=b, the new representation is still sorted.
The actual core/outer state, all physical center gaps, all
real frame lifts modulo pi/2, and the existence of every
original forward separator remain unchanged.

If the representative integer changes by +1, its incoming
quarter increment increases by 1 and its outgoing increment
decreases by 1. For a change by -1 these two changes reverse.
The complete G2 word theorem includes both choices at every
nearest-axis tie, so it applies to each such new word.

## 3. Ties creating a negative quarter increment

The following signs put a -1 on an incident original zero
edge after the alternate nearest-axis choice:
\[
                 H-,\quad G+,\quad A-,\quad B+,
                         T-,\quad D+.
                                                               \tag{2}
\]
For example H- lowers its outgoing HG increment from 0 to
-1, while G+ lowers its incoming HG increment from 0 to -1.
The other two zero edges give the four remaining cases.

Such an increment is impossible independently of any later
word classification. With canonical local angles
\(\alpha_i\in[-\pi/4,\pi/4]\), it would give
\[
 \delta_i=d_i-\pi/2+\alpha_i-\alpha_{i+1}
                    \le d_i<7/10<19/25,
\]
contrary to the unchanged physical gap bound. Thus every
tie in (2) is excluded.

## 4. The four remaining internal-role ties give excluded binary words

The other sign at G,A,B,T changes the word as follows.
The words are written in the unchanged H,G,A,B,T,D,E edge
order, before any cyclic relabeling.

| Actual tie | New quarter word | Excluded G2 class |
|---|---|---|
| G- | 1001011 | 0010111 |
| A+ | 0011011 | 0011011 |
| B- | 0110011 | 0011011 |
| T+ | 0100111 | 0010111 |

The first three class identifications use only rotation;
the fourth uses reversal followed by rotation. The complete
strict exclusions in
HAND_SHORT_WORD_COMPLETE_WITHOUT_TABLES.md and
HAND_WRONG_0011011_COMPLETE_WITHOUT_TABLES.md cover all
radial kinds, weak contacts and original forward witnesses.
Their hypotheses are preserved by this representation
change. These four ties are therefore impossible.

At E-, the new word is 0101020; at E+, it is 0101002.
Each contains one increment 2. The four whole-word
exclusions in Section 4.1 of
HAND_QUARTER_WORD_SELECTION_WITHOUT_TABLES.md exclude
every admissible such word. These last two ties are also
impossible. This proves (1).

## 5. The two remaining boundary representations

At H+ the new word is 1101010, a rotation of the surviving
word. At D- it is 0101101, also a rotation of that word.
Consequently the preceding strict word exclusions do not
exclude these two boundaries.

The exact D- projection and role maps, including every
original witness and the E-sign renormalization, are proved
in HAND_G3_DIAGONAL_D_NEAREST_AXIS_RECODING.md. Reflection
gives the counterpart at H+. The present result asserts
only the exhaustive location restriction on actual
nearest-axis ties; it does not supply a deformation to one
of the two remaining diagonals.

For original centers before radial boundary reduction,
the same conclusion follows because that reduction and
the expansion to Q preserve each signed radial ray and
physical frame. A tie or strict transverse sign is thus
preserved. No mesh, numerical acceptance result, scalar
case table, Lean compilation or CI is used here.
