#!/usr/bin/env python3
"""Fetch and verify the jpeg2000-lean test corpus (Plan.md section 8; docs/corpus.md).

Run from anywhere as:   python3 -I scripts/fetch-corpus.py [options]

  (no options)     download every manifest file missing from corpus/files/ (or present
                   with the wrong size/SHA-256), then verify every selected file.
  --check          verify only: no network; every selected file must be present and match
                   its manifest size and SHA-256.  Exit status 1 and a list of failures
                   otherwise.
  --role ROLE      select files having ROLE (repeatable): conformance-stream,
                   reference-decode, jp2, benchmark, notice.
  --only TEXT      select files whose path contains TEXT (repeatable).
  --root DIR       use DIR instead of corpus/files/ (e.g. to check a copy elsewhere).
  --list           print the selected entries (role, size, path) and exit.

Python standard library only.  Paths resolve relative to this script's parent directory,
not the current directory.  Downloads go to a temporary name next to the target, are
checked for size and SHA-256, and only then renamed into place; a mismatching download is
deleted and reported.  Downloaded bytes are only hashed, never parsed or executed.
urllib honours HTTPS_PROXY / https_proxy.
"""
import argparse
import hashlib
import json
import os
import sys
import time
import urllib.error
import urllib.request

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST = os.path.join(REPO, "corpus", "manifest.json")
DEFAULT_ROOT = os.path.join(REPO, "corpus", "files")
USER_AGENT = "jpeg2000-lean-corpus-fetch/0.1"
ALLOWED_URL_PREFIX = "https://raw.githubusercontent.com/"
ROLES = ("conformance-stream", "reference-decode", "jp2", "benchmark", "notice")


class OversizeError(Exception):
    """The server sent more bytes than the manifest size."""


def sha256_of(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def local_path(root, entry):
    """Target path of an entry; rejects absolute paths and '..' components."""
    rel = entry["path"]
    parts = rel.split("/")
    if rel.startswith("/") or "\\" in rel or any(p in ("", ".", "..") for p in parts):
        raise ValueError("unsafe path in manifest: %r" % rel)
    return os.path.join(root, *parts)


def verify(path, entry):
    """None if the file matches, else a short reason."""
    if not os.path.isfile(path):
        return "missing"
    size = os.path.getsize(path)
    if size != entry["size"]:
        return "size %d, expected %d" % (size, entry["size"])
    digest = sha256_of(path)
    if digest != entry["sha256"]:
        return "sha256 %s, expected %s" % (digest, entry["sha256"])
    return None


def download(entry, dest):
    """Download entry to dest via a temp file; returns None or an error string."""
    url = entry["url"]
    if not url.startswith(ALLOWED_URL_PREFIX):
        return "URL outside %s: %s" % (ALLOWED_URL_PREFIX, url)
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    tmp = dest + ".part"
    last = None
    for attempt in range(3):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=120) as r, open(tmp, "wb") as f:
                n = 0
                while True:
                    chunk = r.read(1 << 16)
                    if not chunk:
                        break
                    n += len(chunk)
                    if n > entry["size"]:
                        raise OversizeError("more than the expected %d bytes" % entry["size"])
                    f.write(chunk)
            bad = verify(tmp, entry)
            if bad is not None:
                os.unlink(tmp)
                return "downloaded file rejected (%s); deleted" % bad
            os.replace(tmp, dest)
            return None
        except OversizeError as e:
            if os.path.exists(tmp):
                os.unlink(tmp)
            return "downloaded file rejected (%s); deleted" % e
        except (urllib.error.URLError, IOError, TimeoutError) as e:
            if os.path.exists(tmp):
                os.unlink(tmp)
            last = e
            code = getattr(e, "code", None)
            if code is not None and 400 <= code < 500:
                body = ""
                try:
                    body = e.read(2000).decode("utf-8", "replace").strip()
                except Exception:
                    pass
                return "HTTP %d %s" % (code, body)
            time.sleep(2 * (attempt + 1))
    return "download failed: %s" % last


def main(argv):
    ap = argparse.ArgumentParser(description="Fetch and verify the jpeg2000-lean corpus.")
    ap.add_argument("--check", action="store_true", help="verify only, no network")
    ap.add_argument("--role", action="append", choices=ROLES, help="select by role (repeatable)")
    ap.add_argument("--only", action="append", metavar="TEXT", help="select paths containing TEXT")
    ap.add_argument("--root", metavar="DIR", help="files directory (default corpus/files)")
    ap.add_argument("--list", action="store_true", help="list selected entries and exit")
    args = ap.parse_args(argv)

    with open(MANIFEST, encoding="utf-8") as f:
        manifest = json.load(f)
    entries = manifest["files"]
    if args.role:
        entries = [e for e in entries if set(args.role) & set(e["roles"])]
    if args.only:
        entries = [e for e in entries if any(t in e["path"] for t in args.only)]
    root = os.path.abspath(args.root) if args.root else DEFAULT_ROOT

    if args.list:
        for e in entries:
            print("%-38s %10d  %s" % (",".join(e["roles"]), e["size"], e["path"]))
        print("%d entries, %d bytes" % (len(entries), sum(e["size"] for e in entries)))
        return 0
    if not entries:
        print("no manifest entries selected", file=sys.stderr)
        return 2

    failures = []
    fetched = 0
    if not args.check:
        todo = []
        for e in entries:
            dest = local_path(root, e)
            bad = verify(dest, e)
            if bad is not None:
                if bad != "missing":
                    print("present but wrong (%s), re-fetching: %s" % (bad, e["path"]))
                    os.unlink(dest)
                todo.append(e)
        for i, e in enumerate(todo, 1):
            print("[%d/%d] fetching %s (%d bytes)" % (i, len(todo), e["path"], e["size"]), flush=True)
            err = download(e, local_path(root, e))
            if err is not None:
                failures.append((e["path"], err))
            else:
                fetched += 1

    failed_paths = {p for p, _ in failures}
    verified = 0
    total = 0
    for e in entries:
        if e["path"] in failed_paths:
            continue
        bad = verify(local_path(root, e), e)
        if bad is None:
            verified += 1
            total += e["size"]
        else:
            failures.append((e["path"], bad))

    for path, why in failures:
        print("FAIL %s: %s" % (path, why))
    mode = "check" if args.check else "fetch"
    print("%s: %d files verified (%d bytes) under %s; %d fetched; %d failed"
          % (mode, verified, total, os.path.relpath(root, REPO) if root.startswith(REPO) else root,
             fetched, len(failures)))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
