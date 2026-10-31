# Root review: direct-contact components retain positive circle loads

Date: October 30, 2026 UTC.

**Verdict: PASS for the complete source and every stated graph consequence.**

Reviewed source:
DIRECT_CONTACT_COMPONENTS_OF_RETAINED_STRESS_CONTAIN_POSITIVE_LOADS_2026_10_30.md

SHA256: `5b91a3b7e7f55317c706bdc6c1b65fd2bd0e99ce823411d5cbe73378dc8e151d`.

I read the entire manuscript and reconstructed its retained-graph
definition, suppression, complete force sum and edge-count conclusion.
The main theorem is self-contained. Its optional comparison with the
loaded-long-endpoint theorem is a literal same-stress join to that
separately fully reviewed source.

## 1. The retained graph has the right domain

Retained vertices consist of positive circle-load bodies and unloaded
positive-degree bodies that are not degree-two transmitters. An unloaded
degree-one body cannot balance its sole nonzero force. Unloaded degree-zero
physical squares are correctly excluded from this graph claim; their
physical packing restrictions are still retained. A loaded isolated
vertex, if present, already satisfies the direct-component conclusion.

Full force balance on each genuine unloaded degree-two body propagates
equal magnitudes and one signed normal. A maximal such run cannot form
an all-unloaded cycle or return to the same retained endpoint: summing
its strictly positive support gaps would telescope to zero displacement.
The finite graph therefore suppresses into channels with two distinct
retained endpoints. Every original force is represented; distinct
parallel runs remain separate channels.

For each channel the exact endpoint center projection is
h_i+h_j+sum_internal 2h_S>=1+k. The center bound |c|<91/60 implies
k<=2. The principal argument only needs the distinction k=0 versus
k>=1 and does not use discrete internal orientations or torque.

## 2. Summing the full unloaded equations gives a strict contradiction

Let S be a connected component of the direct-channel spanning graph
and suppose every retained vertex in S is unloaded. Dot its complete
endpoint force equation with its actual center and sum over S.

Every internal retained channel e combines its two endpoint terms to
-mu_e*g_e<0. This includes an internal subdivided channel, and every
parallel channel is counted with its own magnitude and full support gap.
Nothing is omitted merely because its internal physical squares are not
vertices of the retained subset S.

Any channel leaving S must have at least one internal body; otherwise
its other endpoint would belong to the same direct component. Orient
its normal from i in S to j outside. Its one remaining term is

    mu_e*n_e.c_i=mu_e*(n_e.c_j-g_e)
                 <mu_e*(91/60-2)=-29mu_e/60<0.

The endpoint norm bound and gap>=2 justify the strict sign independently
of the channel's direction. Every term present is therefore negative,
and at least one occurs because every unloaded retained vertex has a
positive incident force. This contradicts the zero sum of its complete
unloaded force equations. Each direct-contact component must contain a
positively circle-loaded vertex.

## 3. The global count and whole-family implications

If b counts loaded retained vertices, h counts unloaded retained hubs
and c_0 counts direct-contact components, then c_0<=b. A spanning forest
of the direct-contact graph has b+h-c_0>=h edges, so the actual direct
retained contact count satisfies e_0>=h. Parallel non-direct channels
were retained in the preceding force argument and do not affect this
forest count.

Every unloaded retained hub has a path of direct retained contacts to
a positive load. In particular, a hub cannot have all its incident
channels subdivided, and no nonempty group of directly joined unloaded
hubs can be separated from all remaining retained vertices solely by
subdivided channels. These consequences cover arbitrary degrees, blocks,
articulations and graph sizes, on the same original stress.

The theorem neither says every shorter channel has loaded endpoints nor
transfers a degree pattern from another selected certificate. It does
not require a plane embedding, a lower-radius window or endpoint moment
balance. It closes the declared whole graph features without asserting
that an original coarse parent has no other allowed retained graph.

## 4. Verification limits

The negative outgoing margin is exactly -29/60 times its positive
magnitude, and every internal support gap is strictly positive.
No numerical search, pose sample, Lean compilation, CI or new packing
certificate is used. The separate full annular_capacity review is
recorded in REVIEW_DIRECT_CONTACT_COMPONENT_LOAD_THEOREM_ANNULAR_INDEPENDENT_2026_10_30.md.
Unrestricted optimality, equality and the remaining larger-parent
assemblies are not claimed closed.
