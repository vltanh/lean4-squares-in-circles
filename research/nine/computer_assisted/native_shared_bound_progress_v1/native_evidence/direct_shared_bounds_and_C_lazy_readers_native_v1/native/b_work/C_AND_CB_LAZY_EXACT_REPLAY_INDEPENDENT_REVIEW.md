# Independent review of the C887 and Cb882 bounded-memory exact readers

I compared `verify_cb882_height_four_lazy_tree.py` and `verify_c887_ownerfree_physical_lazy_tree.py` against their frozen eager predecessors, and reviewed the corresponding shared-height-bound lazy wrappers. The accompanying JSON pins every reviewed source.

**The changes pass this storage, coverage and dispatch review.** No arithmetic or source replay was repeated for this review. Cb's separate actual158-deduction lazy attachment has already passed and matches its eager report on the stated physical/coverage fields; C887's first actual lazy attachment remains a separate gate.

Both core diffs remove only the eager dictionary of every parsed numerical payload. The complete input inventory is still hashed up front. At each visit the selected node file is rehashed before parsing. Its exact bound record is checked against the inherited certified state, and only then is its large parsed payload released before child recursion. Terminal labels are captured before release. The remaining audits contain the same scalar summaries and certified states as before.

The complete proxy alternatives, eight separating-axis alternatives, and two closed angle sides are unchanged. Pair/cut validity, exact parent/depth/restriction checks, all sibling visits and `visited == set(nodes)` remain. An OPEN child does not short-circuit traversal of its siblings. All recorded source hashes are rechecked at completion. No exclusion can follow merely from a numerical status or an omitted file.

For Cb, the wrapper pins the frozen predecessor hash and requires `CURRENT.BASE.BASE is FROZEN` before replacing precisely that base-module reference with LAZY. The existing outer shared-height and consequence adapters subsequently install their final Checker/Adapter on that base as before. The reference is restored in `finally`.

For C887, the wrapper pins the frozen predecessor hash and verifies the expected old-core object. It temporarily replaces that object's replay entry. At the actual call, after all outer row wrappers have installed their final adapter classes, it copies exactly those Checker/Adapter objects into LAZY and invokes the unchanged arithmetic cover with bounded-memory payload reads. This preserves the entire existing layered literal/source dispatch and its occurrence counters. The original replay entry is restored in `finally`.

Both wrappers require the lazy-result flag and include the eager source, lazy source and wrapper hashes in the final dependency report. Existing fresh source replays and forbidden-producer-import checks remain in place. No source change or additional arithmetic repetition is requested by this review, and no original or mask credit is asserted.
