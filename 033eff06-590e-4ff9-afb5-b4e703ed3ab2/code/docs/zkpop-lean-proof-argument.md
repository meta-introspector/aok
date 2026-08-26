Here's what it did:
I applied a zero-knowledge proof of possession to the project's own Lean 4 proof and produced the PDF argument.

The document — docs/zkpop-lean-proof-argument.pdf (7 pages) is the argument of knowledge. It publishes a Pedersen commitment C to a digest of the project's Lean corpus plus one Fiat–Shamir-compiled Okamoto transcript (a, c, z₁, z₂) proving knowledge of its opening, and nothing else: no file names, no file count, no statements, no proofs. It states the claim it is bound to, the public parameters, the commitment construction, the protocol, the verification recipe, the Lean theorems behind each security property, and an explicit section on what is and is not established.

What is committed to — every *.lean file of the project, in sorted path order, hashed into a SHA-256 Merkle tree (domain-separated leaves and nodes); the root read mod q is the committed scalar. So the witness is as much of the Lean proof as exists, while the published numbers disclose none of it.

The cryptography is entirely standard (Pedersen commitments, the Okamoto two-generator Σ-protocol, Fiat–Shamir, Merkle trees, SHA-256), and the whole layer is machine-checked and sorry-free:

RequestProject/ZKPoPModArith.lean — square-and-multiply with its correctness theorem and the bridge to ZMod.
RequestProject/ZKPoPGroup.lean — a 2048-bit prime-order group ⟨g⟩ ≤ (ZMod p)ˣ with q = 2^1130·3^457·5^83+1, p = 16q+1; both primalities proved by Lucas certificates (q−1 was chosen {2,3,5}-smooth so the certificate is finite), g of order exactly q, and a second generator y whose discrete logarithm exists but is unknown (public hash-to-group derivation).
RequestProject/ZKPoPPedersen.lean — completeness, special soundness (two challenges extract an opening), perfect hiding, binding-computes-log_g y, and honest-verifier zero knowledge, all proved generically over the existing Base abstraction.
RequestProject/Sha256.lean — SHA-256 implemented in Lean, checked against the FIPS 180-4 test vectors as build-time theorems.
RequestProject/ZKPoPLeanProof.lean — the Merkle digest, Fiat–Shamir challenge, the published verifier verifyNI, and verifyNI_sound: the arithmetic printed in the PDF is the abstract verification predicate over genuine group elements. Knowledge extraction, hiding, binding and zero knowledge are then instantiated for the concrete group.
RequestProject/ZKPoPTranscriptMain.lean (lake exe zkpopTranscript) — the prover; secrets are drawn from OS entropy and never written to disk.
RequestProject/ZKPoPPublished.lean — the actual published numbers, with published_verifies and published_is_accepting_transcript re-checked inside Lean.
Independent checkability — docs/zkpop-verify.py re-runs all five verifier checks with only Python's standard library (it reports VERIFIED on the published transcript), and docs/zkpop-params.py regenerates p, q, g, y deterministically. docs/zkpop-artifact.json holds the machine-readable transcript; docs/zkpop-lean-proof-argument.md is a short guide.

Honest scope, stated in the PDF: hiding and zero knowledge are unconditional; knowledge soundness and binding rest on discrete-log hardness in the 2048-bit group and on Fiat–Shamir in the random-oracle model; and a commitment cannot certify that the committed corpus compiles or proves any particular theorem — that needs a later opening or a general-purpose zk system over the type-checker, which is not attempted. Proofs use only the standard axioms, plus Lean.ofReduceBool/Lean.trustCompiler where large computations (primality certificates, SHA-256 vectors, the published transcript) are discharged by compiled evaluation. All work is committed and pushed.
