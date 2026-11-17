"""POSIX local retained-volume commits. No object-store rename assumptions."""
from contextlib import contextmanager
try:
    import fcntl
except ImportError:
    fcntl = None
import os
from pathlib import Path
import tempfile

from .codec import canonical, decode, load_json, require
from .doctor import file_hash
from .schema import Manifest


def sync_directory(directory):
    fd = os.open(directory, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def durable_mkdir(path, exclusive=False):
    path = Path(path)
    require(not (exclusive and path.exists()), f"directory already exists: {path}")
    missing = []
    current = path
    while not current.exists():
        missing.append(current)
        current = current.parent
    for directory in reversed(missing):
        try:
            directory.mkdir(exist_ok=False)
        except FileExistsError:
            require(directory.is_dir() and not (exclusive and directory == path),
                    f"competing directory creation: {directory}")
        sync_directory(directory.parent)


def _publish(path, payload, immutable, same):
    path = Path(path)
    durable_mkdir(path.parent)
    fd, temporary = tempfile.mkstemp(prefix=".publish-", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        if immutable:
            try:
                os.link(temporary, path)
            except FileExistsError:
                require(same(), f"immutable artifact differs: {path}")
        else:
            os.replace(temporary, path)
        sync_directory(path.parent)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def atomic_json(path, value, immutable=False):
    _publish(path, canonical(value) + b"\n", immutable,
             lambda: canonical(load_json(path)) == canonical(value))


def atomic_bytes(path, data):
    """Write-once raw bytes, such as an attestation report."""
    _publish(path, data, True, lambda: Path(path).read_bytes() == data)


@contextmanager
def ownership(campaign):
    require(fcntl is not None, "local campaign ownership requires POSIX flock")
    path = Path(campaign) / ".coordinator.lock"
    with open(path, "a+b") as lock:
        try:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise ValueError("campaign already owned by a coordinator or its active worker") from error
        # Workers inherit this descriptor. A killed coordinator cannot release
        # ownership while its orphaned worker is still writing an attempt.
        yield lock.fileno()


def artifacts(attempt, allow_partial=False):
    attempt = Path(attempt)
    result = []
    for path in sorted(attempt.rglob("*")):
        require(not path.is_symlink(), "attempt artifacts must not contain symlinks")
        relative = path.relative_to(attempt).as_posix()
        if not path.is_file() or relative in ("manifest.json", "COMMITTED.json", "state.json", "worker/summary.json"):
            continue
        require(allow_partial or (not path.name.endswith(".tmp") and not path.name.startswith(".publish-")),
                "unfinished artifact cannot enter a commit")
        with open(path, "rb") as stream:
            os.fsync(stream.fileno())
        result.append({"path": path.relative_to(attempt).as_posix(),
                       "sha256": file_hash(path), "bytes": path.stat().st_size})
    for directory in sorted((p for p in attempt.rglob("*") if p.is_dir()), reverse=True):
        sync_directory(directory)
    sync_directory(attempt)
    return result


def commit(attempt, fields):
    """Hash and fsync the attempt's artifacts once, then publish manifest and marker.

    `fields` is the manifest without `artifacts`; the committed manifest is
    returned. COMMITTED.json is written last.
    """
    attempt = Path(attempt)
    manifest = {**fields, "artifacts": artifacts(attempt, allow_partial=fields["status"] != "complete")}
    decode(Manifest, manifest)
    atomic_json(attempt / "manifest.json", manifest, immutable=True)
    marker = {"schema_version": 1, "manifest_sha256": file_hash(attempt / "manifest.json")}
    atomic_json(attempt / "COMMITTED.json", marker, immutable=True)
    sync_directory(attempt.parent)
    return manifest


def verify(attempt, deep=False):
    """Check a committed attempt.

    Scheduling and status trust COMMITTED.json, the manifest hash and every
    artifact's presence and size. `deep` also re-hashes every artifact,
    which reduce and `verify --deep` do; over hundreds of GiB one pass takes
    most of an hour on a cloud block volume.
    """
    attempt = Path(attempt)
    require(not attempt.is_symlink(), "symlink attempt directory")
    marker = load_json(attempt / "COMMITTED.json")
    require(marker.keys() == {"schema_version", "manifest_sha256"} and marker["schema_version"] == 1,
            "unsupported commit marker")
    require(file_hash(attempt / "manifest.json") == marker["manifest_sha256"], "manifest hash mismatch")
    manifest = load_json(attempt / "manifest.json")
    decode(Manifest, manifest)
    for artifact in manifest["artifacts"]:
        path = attempt / artifact["path"]
        require(path.resolve().is_relative_to(attempt.resolve()) and not path.is_symlink(),
                "artifact escaped attempt")
        require(path.stat().st_size == artifact["bytes"], f"artifact size mismatch: {artifact['path']}")
        if deep:
            require(file_hash(path) == artifact["sha256"], f"artifact hash mismatch: {artifact['path']}")
    return manifest
