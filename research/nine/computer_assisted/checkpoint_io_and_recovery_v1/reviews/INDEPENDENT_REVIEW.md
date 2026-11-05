# Independent source review: atomic JSON checkpoints

The frozen helper `ac_work/tree/atomic_json_checkpoint.py`, SHA-256
`2f17219f8689b343f7f1c29e7a314272bd5ace8d25fbee11f58cd20b44543eb3`,
correctly implements its stated single-file preservation contract under the
existing one-writer-per-checkpoint assumption. I read the full helper, the
control generator, the eight recorded control results, and the hand note, and
independently rehashed every member of its source freeze. I did not rerun
filesystem mutation controls or change a numerical driver during the storage
pause.

The helper writes the established `json.dump(..., indent=2)` serialization and
one newline through an exclusively created sibling temporary file. A partial
serialization cannot truncate the previous destination. The file is flushed,
its mode is set, and its data is fsynced before `os.replace`. A successful
same-directory replacement is atomic at the pathname. The parent directory
is then fsynced. Existing regular-file permission modes are retained; new
files use the explicit documented mode 0644. A symlink or another nonregular
destination is rejected before staging.

Before replacement, a serialization, flush, chmod, file-fsync, or replacement
failure leaves the old destination inode and bytes in place. The staging file
is retained for diagnosis, and the exception is propagated. If a directory
fsync fails after replacement, the new destination already exists. The helper
reports this distinction rather than claiming that the old file remains. It
checks the installed inode against the staged inode before attempting to
retain a diagnostic hardlink, and records any inability to preserve that link
without concealing the primary error.

The eight recorded controls exercise ENOSPC before and during serialization,
file-fsync failure, replacement failure, ordinary success with mode and fsync
order checks, new-file creation under a restrictive umask, failure after
replacement during directory fsync, and symlink rejection. Their assertions
match the documented contract. The checks use disposable fixtures and preserve
the helper source bytes. This review accepts the source and those recorded
controls; it does not claim a second execution of the controls.

The limitation stated in the hand note is essential: this is not a transaction
over a mathematical node and its manifest. A crash between those two successful
writes can leave their recorded hashes out of agreement. Exit-time integrity
audit and, when necessary, explicit exact reconstruction remain required. A
future immutable driver must propagate `OSError` out of its outer search and
checkpoint boundaries; catching it as an ordinary failed branch and continuing
the search would defeat the requested stop-on-storage-failure behavior.

No physical row, proof arithmetic, interval cover, accepted count, or frozen
proof input changes through this helper preparation. New driver versions must
bind the helper source and retain their existing mathematical replay gates.
The source review is not a numerical restart authorization or an approval to
edit a previously frozen driver.
