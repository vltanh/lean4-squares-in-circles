"""Atomically replace one JSON checkpoint, preserving its previous bytes on write failure.

This is one-file durability, not a transaction over a node and its manifest.
An error is always propagated. Failed temporary files are retained for diagnosis.
"""
from pathlib import Path
import json
import os
import stat
import tempfile


def _same_inode(first, second):
    return (first.st_dev, first.st_ino) == (second.st_dev, second.st_ino)


def write_json(path, value):
    """Write the ordinary indent=2 JSON plus newline through an exclusive sibling.

    Existing regular-file permissions are preserved; a new file is mode 0644.
    A write/flush/file-fsync/replace error leaves the prior destination in place.
    If directory fsync fails *after* replacement, the new destination is present;
    the raised error explicitly records this fact and a diagnostic link is kept
    when possible. Callers must propagate OSError and audit node/manifest hashes.
    """
    destination = Path(path)
    directory = destination.parent
    try:
        old = destination.lstat()
    except FileNotFoundError:
        old = None
    if old is not None and not stat.S_ISREG(old.st_mode):
        raise ValueError("Atomic checkpoint destination must be a regular file.")
    mode = stat.S_IMODE(old.st_mode) if old is not None else 0o644
    directory_fd = os.open(directory, os.O_RDONLY | os.O_DIRECTORY)
    temporary = None
    staged_stat = None
    replaced = False
    descriptor = None
    try:
        descriptor, name = tempfile.mkstemp(
            prefix=destination.name + ".atomic-", suffix=".tmp", dir=directory)
        temporary = Path(name)
        stream = os.fdopen(descriptor, "w", encoding="utf-8", newline="\n")
        descriptor = None  # The text stream now owns it.
        with stream:
            json.dump(value, stream, indent=2)
            stream.write("\n")
            stream.flush()
            os.fchmod(stream.fileno(), mode)
            os.fsync(stream.fileno())
            staged_stat = os.fstat(stream.fileno())
        os.replace(temporary, destination)
        replaced = True
        os.fsync(directory_fd)
    except BaseException as error:
        # os.replace removes the staging name. If its subsequent directory
        # fsync failed, recreate only a link to that exact installed inode.
        retained = temporary is not None and os.path.lexists(temporary)
        retention_error = None
        if replaced and not retained and temporary is not None:
            try:
                current = destination.lstat()
                if (staged_stat is None or not stat.S_ISREG(current.st_mode)
                        or not _same_inode(current, staged_stat)):
                    raise RuntimeError("Installed checkpoint inode changed before diagnosis.")
                os.link(destination, temporary, follow_symlinks=False)
                linked = temporary.lstat()
                if not _same_inode(linked, staged_stat):
                    raise RuntimeError("Diagnostic link does not match installed checkpoint.")
                retained = True
            except BaseException as diagnostic_error:
                retention_error = repr(diagnostic_error)
        if hasattr(error, "add_note"):
            error.add_note(
                "Atomic JSON checkpoint: destination_replaced=" + str(replaced)
                + "; diagnostic_temp=" + str(temporary)
                + "; diagnostic_temp_retained=" + str(retained)
                + ("; diagnostic_retention_error=" + retention_error
                   if retention_error is not None else ""))
        raise
    finally:
        if descriptor is not None:
            os.close(descriptor)
        os.close(directory_fd)

