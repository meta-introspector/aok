# Can the carrier images be decoded?

Short answer: **yes for the public package, no for the withheld material** — and
the second half is the part that is structural.

## What the images actually are

`artifact/carriers/shard-*.png` are not steganographic and hide nothing. Each
one is a plain black/white cell grid holding a *framed* erasure-code shard:

```
magic "ZKPP" | version | shard index | nData | nTotal | payloadLen | shardLen | crc32 | shard bytes
```

The geometry (20-pixel quiet margin, 10×10-pixel cells, threshold on the central
60% of each cell) is documented and implemented in `tools/carrier.py`; the
`4`-of-`7` systematic Cauchy Reed–Solomon code is in `tools/gf256.py`.

Consequently the frames are **self-describing**: a reader learns the scheme
parameters, the shard index and the payload length from the images themselves.
No manifest, no key, no generator, no Merkle root and no per-instance parameter
is required to read them — only the decoder, which is in this repository.

## Reproducing the decode

```
python3 tools/decode_carriers.py                       # any 4 carriers it finds
python3 tools/decode_carriers.py artifact/carriers/shard-0{2,4,5,6}.png
```

Measured output, recorded in `artifact/decode_demo.txt`:

```
carriers read: 7  scheme: 4-of-7
reference package: 20777 bytes  sha256 a20e7ecb...f6ea
subsets of size 4: 35   rebuilding artifact/package.bin exactly: 35
```

All 35 four-carrier subsets rebuild `artifact/package.bin` byte for byte. The
payload is a zlib-compressed JSON manifest with keys `argument`, `commitment`,
`declarationCount`, `distribution`, `generated`, `protocol`, `statementRoot`,
`statements`, listing 179 public statements.

## What decoding does *not* give you

The recovered package is the **public** artifact: statement list and Merkle
root, the Pedersen commitment `C` with its group parameters, and the
Fiat–Shamir Schnorr transcript. The withheld proof material is not in it, and
no amount of carrier decoding will produce it. That limitation *is* structural,
and in this project it is a theorem rather than an assumption:

* `ZkPoP.pedersen_perfectly_hiding` — the commitment's distribution is
  independent of the committed value, so `C` constrains nothing;
* `ZkPoP.Schnorr.real_eq_sim` / `ZkPoP.Schnorr.hvzk_equiv` — every accepting
  transcript is exactly the output of a simulator that never sees the witness;
* `ZkPoP.Shard.erasure_not_private` — and, conversely, the carrier layer is
  explicitly *not* a privacy mechanism: systematic erasure coding provides
  recovery only. Nothing is hidden by the images; the hiding is done by the
  commitment.

So: the images are readable with this repository alone, and reading them yields
precisely what was meant to be public.
