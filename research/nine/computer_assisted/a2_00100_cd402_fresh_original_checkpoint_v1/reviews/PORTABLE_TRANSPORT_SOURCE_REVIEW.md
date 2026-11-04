# Cd402 checkpoint transport source review

The three new transport and orchestration files pass review for the frozen
Cd402 OPEN checkpoint. They preserve mathematical source and certificate
bytes, invoke the unchanged accepted C transport in worker-script mode, and
check the actual fresh Cd402 reports before issuing the outer receipt. This
review adds no original-cell or mask credit.

The accompanying JSON binds the reviewed sources, delta manifest, alias map,
proof declaration and cold receipt. The delta archive is
`ac370a5d945796f2566263d0733ce330eaabc7c816a2043ae5128750697de650`.
It contains 40 files, including its manifest; all 39 manifest-listed delta
files were hash-checked here. The frozen delta and materialized packet were
not changed, and no arithmetic replay or numerical search was repeated.

## Thin delta and materialization

The builder pins the published C base input manifest. Every reused logical
filename must retain the same payload location and SHA-256; every new payload
is copied byte for byte from its native source. The resulting alias map
preserves all 2,008 inherited file aliases and all inherited directory aliases
and adds 34 new file aliases. The complete alias map has no duplicate payload
targets. The actual frozen delta and alias-map paths are relative and remain
inside their declared roots.

The materializer checks the base manifest hash, all base input hashes and all
delta input hashes before constructing a fresh output folder. It omits the
old alias file and installs the new alias map. Reused payloads may be hard
linked because no inherited payload is edited. Any existing destination from
the delta must have the same digest. The old base inventory is retained as
`C_BASE_INPUT_MANIFEST.json`, a new input manifest describes the materialized
packet, and the inherited base hashes are checked again at completion.

The new files do not rewrite Python sources, coefficients, parent paths,
literal arithmetic records or accepted theorem tables. Their role is
filename transport and byte-preserved inventory assembly.

## Fresh exact jobs and scope checks

The replay wrapper requires the packet and output to be outside the old
workspace and requires a fresh output directory outside the packet. It checks
the packet's input hashes, pins the unchanged C transport to
`d7d9b17da9091cb7920e5964618303c93ae2689a8528381091b35f3ee4c2cb28`,
and invokes two isolated `-B -S` worker-script jobs: the whole-original bound
checker and the complete OPEN seed checker.

Each child must exit successfully. The wrapper then reads the mathematical
report written by that exact Cd402 checker, verifies its original identifier
and original path, checks that no numerical producer was imported, checks
closed shared-face retention and zero credit, and compares all expected
status and count fields. It rehashes the packet inputs again before writing
the outer receipt. Saved native reports are not substituted for either job.

The inspected cold receipt has SHA-256
`7dd4ff783f9d388ad3b92479bcaf2bc7e1f80649e469ea4b5c6e5046f2854096`.
Its two referenced reports were hash-checked and both bind
`negative-d4021ade840b985c` and the unchanged Cd402 original path. The bound
report certifies an OPEN whole-original state; the seed report certifies a
complete cover containing one OPEN leaf. Neither proves exclusion.

## Legacy transport labels

The inherited transport's child receipts retain C887/Cb882 `original_ids`
labels from its earlier package. Those labels are transport metadata. The new
wrapper does not use them to establish Cd402 premises or closure. Its outer
receipt is based on the actual exact Cd402 reports described above, whose
checkers reconstruct and verify Cd402 directly. The publication README should
retain this distinction so the reused transport labels are not mistaken for
an additional original, a transferred height consequence, or proof credit.

The accepted mathematical checker and its whole-original attachment remain
the authority. This transport review confirms preservation and orchestration
of those fixed inputs, with the original still OPEN.
