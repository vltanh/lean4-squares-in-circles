# Independent review of the finite A165 existing-row delta

The byte and source review passes for the frozen delta whose input manifest is
`f3778cf2b2a583cdce4bacb8691add8a7d14b1d5a6c1256d6b7d0965fb8b1781`.
This review reads the complete builder and materializer and checks the actual
44 packet files, all 165 previous payloads, and all six included replacements.
The independent byte audit observed session 64919 exit 0; its report is
`996314429e4dd22504134fe8b42c3b26765aa2d6691f5332c01fec525d12c563`.

The source tree is exactly manifest
`4469ce8ceda7692f49faa58ece25872c0448fbd8fc86447acb6facf0cd4e2283`.
The continued manifest is exactly
`5c06610c0f8e4e317707b4f352277a2530d39e7f3cb63dfc5b03089571ccd98c`.
The 159 omitted payloads remain exact aliases to that previous tree. The six
included payloads are indices 151, 152, 154, 156, 157 and 163. Their complete
initial states and every prior round remain equal to the source. Their only
changed payload fields are `rounds`, `final`, and the suffix provenance field
`existing_correlated_row_suffix`; the manifest's branch fields are unchanged.

The materializer verifies the complete packet inventory and rejects symlinks,
absolute member names, traversal outside the packet, changed previous records,
wrong report identity, omitted nodes and unexpected changed indices. It writes
only into a new absent output directory, uses exclusive file creation, and
checks every resulting node and manifest hash. Its byte-only default does not
run an arithmetic checker. The builder's declared six-record selection is
independently checked by the materializer's complete 165-entry walk.

The exact suffix report
`eee73dfe46135c506568026e92bb32e16cbbd5751bb26b87768504fe3175061d`
is matched literally to the continued manifest. It records 12 fresh rounds,
10 deductions and 19 premises, while explicitly reusing the previous full
165-node arithmetic. The resulting cover remains 118 excluded leaves and
14 OPEN leaves. The packet states this scope clearly and retains the earlier
failed preparation and its narrow correction separately.

This review does not repeat either old or new arithmetic and does not run the
materializer. It accepts the source and byte-preservation contract at the
declared native delta scope. It supplies no new geometric theorem, whole
original closure, mask closure, or cold self-contained proof claim.
