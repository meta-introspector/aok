Here's what it did:
The paper is finished, built, verified, and pushed.

The deliverable
paper/zk-provenance.pdf (18 pages, source paper/zk-provenance.tex) — Zero-Knowledge Proof of Provenance: presenting a machine-checked artifact without revealing it. It is authored only as "the holder of the public key of §6"; no further identifying information appears in it.

The paper argues the title claim honestly. A proof of possession alone is not a proof of provenance, so the missing piece was built first: the possession protocol is AND-composed (shared challenge, in the standard Cramer–Damgård–Schoenmakers style) with a Schnorr proof of knowledge of an identity key, and a public release anchor is bound into the challenge. The paper then presents that mechanism, shows every part of it running, and states precisely what is and is not claimed.

New formal content
RequestProject/Zk/Provenance.lean (712 lines, 26 named theorems, 7 kernel-checked examples). The registered results:

Completeness — a holder of both the artifact and the identity secret always produces an accepted proof (provenance_valid), and the same for the non-interactive published file, for any challenge function (provNIVerify_provNIProve).
Special soundness — two accepting transcripts on one pair of first moves at different challenges yield both an opening of the statement and the identity secret; neither half is answerable alone because the challenge is shared (identity_and_opening_of_special_sound, and for published proof objects identity_and_opening_of_provenance_pair).
Zero knowledge — holders of any two artifacts publish exactly the same set of proofs, so nothing artifact-dependent is disclosed (provenance_reveals_nothing), upgraded from a set equality to an equality of distributions by provenanceFibreEquiv.
provenance_meaning — the three combined: what an accepting pair establishes and nothing more.
harness_zk_provenance — the same three instantiated at this port's own published claim.
PublishedProvenance.decode_encode — the provenance wire format is lossless.
Supporting work: RequestProject/Zk/Wire.lean gained the PublishedProvenance format ("dsh-zkprov/1") with its checker, encoder, renderer and decoder; RequestProject/Zk/Publish.lean gained provenance and verify-provenance CLI commands and an identity secret read from the environment.

"It runs"
scripts/paper-transcripts.sh regenerates every transcript in paper/transcripts/ from real runs, and the paper includes them verbatim: publishing and checking a possession proof, the JSON file itself, four tamper variants (all correctly refused), the provenance proof and its verification, the declaration count, the full build with its in-kernel axiom audit, and the repository's own check list.

Verified state
lake build clean (8383 jobs); the audit inside it reports 13,192 theorems and 22,304 definitions depend only on propext, Classical.choice, Quot.sound — no sorryAx, no added axiom.
scripts/checks.sh --fast: all 13 checks ok, including the holes check (no sorry, no axiom, no @[implemented_by]).
Every theorem registered above independently re-checked with #print axioms: standard axioms only.
The figures quoted in the paper (253 modules, 128,565 lines, 5,071 theorems, 2,094 examples) match the recorded run, and every name in the paper's index of formal statements resolves to a real declaration.
Disclosure policy
Nothing about the port's contents is revealed. Only public literature is cited: Goldwasser–Micali–Rackoff, Schnorr, Pedersen, Okamoto, Cramer–Damgård–Schoenmakers, Fiat–Shamir, Bellare–Rogaway, Pointcheval–Stern, Karp–Rabin, Lean 4 and mathlib, and in related work in-toto, Sigstore, EasyCrypt, CryptHOL and SSProve. The one reference to the system the port is of is cited by its published title and URL solely to identify what the public description refers to.

Honest caveats, stated in the paper's "What is not claimed"
The hiding property is information-theoretic but binding is computational; the group and hash used in the shipped demonstration are illustrative rather than a production instantiation; the Fiat–Shamir transform's random-oracle soundness is cited, not formalised (only completeness of the non-interactive file is a theorem, and it holds for an arbitrary hash); and that the party holding the published key is the party a reader believes it to be is a fact about how that key was published, not a theorem.

Docs updated to match (PLAN.md, ZKPOP.md, README.md, a new VERIFICATION.md §45, all three generated SVGs). ARISTOTLE_SUMMARY.md was left untouched. Everything is committed and pushed.
