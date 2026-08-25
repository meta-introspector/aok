"""Decode the PNG carriers back to the zkPoP package — no secrets required.

The carriers are self-describing: every frame carries a fixed header
(`magic | version | index | nData | nTotal | payloadLen | shardLen | crc32`)
followed by its erasure-code shard, and the geometry (quiet margin, cell size,
threshold rule) is documented in `carrier.py`.  Any `nData` of the `nTotal`
carriers therefore rebuild the exact package, using nothing but this repository:
no manifest, no keys, no per-instance parameters.

Usage:

    python3 tools/decode_carriers.py artifact/carriers/shard-0{0,1,2,3}.png

    python3 tools/decode_carriers.py            # uses any 4 carriers it finds

What comes out is `package.bin`: a zlib-compressed JSON manifest holding the
*public* side of the argument — the statement list and Merkle root, the Pedersen
commitment, the Schnorr transcript, and the digests.  The withheld proof bodies
are not in there and cannot be: the commitment is perfectly hiding
(`ZkPoP.pedersen_perfectly_hiding`) and every accepting transcript is exactly
the witness-free simulator's output (`ZkPoP.Schnorr.real_eq_sim`).  Decoding the
images recovers the public artifact, never the private witness.
"""

from __future__ import annotations

import glob
import hashlib
import json
import os
import sys
import zlib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import carrier
import gf256

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CARRIERS = os.path.join(ROOT, "artifact", "carriers")


def decode(paths: list[str]) -> bytes:
    """Rebuild the package from carrier images, dropping any that fail CRC."""
    frames = {}
    for p in paths:
        fr = carrier.read_carrier(p)
        if fr is None:
            print(f"  ! {os.path.basename(p)}: CRC failed, dropped")
            continue
        frames[fr["index"]] = fr
        print(f"  + {os.path.basename(p)}: shard {fr['index']} "
              f"({len(fr['shard'])} bytes) of {fr['n_data']}-of-{fr['n_total']}")
    if not frames:
        raise SystemExit("no readable carriers")
    any_frame = next(iter(frames.values()))
    n_data, n_total = any_frame["n_data"], any_frame["n_total"]
    if len(frames) < n_data:
        raise SystemExit(f"need {n_data} carriers, got {len(frames)}")
    chosen = dict(sorted(frames.items())[:n_data])
    return gf256.decode({i: f["shard"] for i, f in chosen.items()},
                        n_data, n_total, any_frame["payload_len"])


def main(argv: list[str]) -> int:
    paths = argv[1:] or sorted(glob.glob(os.path.join(CARRIERS, "*.png")))[:4]
    print(f"reading {len(paths)} carrier(s)")
    payload = decode(paths)
    print(f"package: {len(payload)} bytes, sha256 {hashlib.sha256(payload).hexdigest()}")
    manifest = json.loads(zlib.decompress(payload))
    print(f"manifest keys: {sorted(manifest)}")
    stmts = manifest.get("statements", [])
    print(f"public statements: {len(stmts)}")
    for s in stmts[:5]:
        print(f"  - {s if isinstance(s, str) else s.get('name', s)}")
    if len(stmts) > 5:
        print(f"  … and {len(stmts) - 5} more")
    out = os.path.join(ROOT, "artifact", "package.decoded.bin")
    with open(out, "wb") as fh:
        fh.write(payload)
    print(f"written to {os.path.relpath(out, ROOT)}")
    ref = os.path.join(ROOT, "artifact", "package.bin")
    if os.path.exists(ref):
        with open(ref, "rb") as fh:
            same = fh.read() == payload
        print(f"identical to artifact/package.bin: {same}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
