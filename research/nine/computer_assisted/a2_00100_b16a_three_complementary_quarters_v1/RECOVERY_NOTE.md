# Recovered B16a complementary proof publication

The complete I20/I31/I33 packet was committed locally as
`a16650c9656f9b1bc1bb7f45d15e4e2897561098` on another checkout. It was absent
from PR #11 head `a9f6a2e3bf989ccdbdfed0af7a66f2d3d8522a5d`. This publication
adds the original seventeen new files unchanged and retains the current branch
ledger and its accepted D821 closure. Historical status snapshots in the packet
remain historical.

The complete 367-member immutable archive was read and its SHA256 checked.
A fresh relocated replay again excluded all three complete original quarters,
checking all 360 new inputs and 507 pinned prior inputs. The new receipt is
`RECOVERY_FRESH_PORTABLE_RECEIPT.json`. The extracted older native packet had
one modified current-register snapshot; only the relocated copy was restored
from the immutable archive before replay. Every frozen input then matched.

The independent `RECOVERY_LITERAL_TABLE_AUDIT.json` checks the complete
31-node/23-leaf cover and its literal terminal arithmetic. The old proof
archive, sources, prior and portable receipt are unchanged.

Together with the eleven previously recovered quarter exclusions, B16a now
has fourteen reproducible exclusions; only I21/I22 remain OPEN. This restores
proof availability and does not itself close an original cell. The live
register is still 222 CLOSED / 9 OPEN, and whole masks are 8 CLOSED / 24 OPEN.
All shared closed faces, original definitions and strict-radius scope are
unchanged. No Lean, Lake or CI.
