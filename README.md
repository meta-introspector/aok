# Combined Reference Document AOK

## Table of Contents

- [PROJECT.md](#project-md)
- [BOOTSTRAP_TASK.md](#bootstrap-task-md)
- [unified-crypto-methodology.md](#unified-crypto-methodology-md)
- [AokInterface.lean](#aokinterface-lean)
- [ZkPoPCore.lean](#zkpopcore-lean)
- [FoldedReconstruction.lean](#foldedreconstruction-lean)
- [bootstrap_transport.py](#bootstrap-transport-py)

---

## PROJECT.md

# zkpop-core-v2 — Standard API, assembled by transport

**Status:** proposed (not yet built/checked)
**Assembled from:** agda-zkpop-v1, mojo-zkpop-v1, nodejs-zkpop, zk-pop-solana-lean4-v1
  (transport costs 1, 1, 2, 1 — see transport solve in conversation)
**Excluded:** mog-zk-pop-v1 (content-bearing modulus; stays its own project, referenced not merged)

## What this is

A single `ZkPoPGroup` / `ZkPoPArgument` interface (see `ZkPoPCore.lean`, sketch)
that the four transport-selected papers implement instead of each restating
its own commitment scheme. Completeness / special-soundness / perfect-HVZK
are proved once, generically, against the interface — not per instance.

## What this is not

- Not yet compiled or kernel-checked. This is a design sketch, written to
  make the interface concrete enough to build against, not a machine-checked
  artifact.
- Not a re-verification of the four source papers' underlying corpora —
  those are intentionally withheld (that's the point of zkPoP), so this
  entry inherits their claims about the group/modulus choice from their
  published prose, same as the transport plan did. If any of those papers'
  actual Lean development used a different concrete group than stated, this
  registry entry would be wrong and needs correcting from the source, not
  from this document.
- Not a merge of the 27 existing UUID projects — added as an independent,
  new entry so nothing existing is overwritten.

## Honest trust ledger

| Property | Status |
|---|---|
| Group axioms (Ristretto255) | Standard, citable (RFC 9496) — not reproved here |
| Completeness/soundness/HVZK | Proved generically elsewhere against `Base`; this interface is designed to let 4 papers cite that proof instead of restating it — proof of *this specific reuse* not yet done |
| Declared parameters vs. verified | Declared only (source withheld); flagged explicitly, not glossed over |
| mog exclusion | Deliberate — its modulus is the theorem's content, not swappable |

## Next steps to make this real rather than a sketch

1. Get `ZkPoPCore.lean` compiling against Mathlib with a real `Ristretto255`
   instance of `ZkPoPGroup` (the one load-bearing proof obligation).
2. For each of the 4 included papers, write the ~5-10 line `ZkPoPArgument`
   instance that plugs its existing (already-proved) `prove`/`verify` into
   the shared interface, rather than reproving anything.
3. Confirm via the kernel that the generic completeness/soundness/HVZK
   theorems specialize correctly to each instance (should be near-free if
   step 1-2 are done correctly — this is what "generic over `Base`" buys you).
4. Register `zkpop-core-v2` in `projects/PROJECTS.md` and `manifest.json` as
   a new, additive project once step 3 is kernel-checked, not before.


---

## BOOTSTRAP_TASK.md

# BOOTSTRAP_TASK — find a good-enough transport plan, not a perfect one

**Follows the dotagents task pattern** (SYSTEM.md/AGENTS.md/SKILL.md/boot.sh) —
this is that task's SYSTEM.md-equivalent instruction.

## Objective

Given the current `PROJECTS` feature table in `bootstrap_transport.py`, produce
an assignment of each project to a `ProjectKind` (and, for `zkArgument`
projects, a crypto rung) that is **cheap enough to trust, not provably
minimal**. Do not treat this as an exhaustive-search or exact-ILP problem
once the project count grows — the LP relaxation already in
`bootstrap_transport.py` is the intended method, and "good enough" is defined
below, not "global optimum."

## What "good enough" means here (stopping rule)

Accept a solve's output without further search if **all** of the following hold:

1. **No content-bearing project is misclassified.** Any project whose
   `modulus_is_content = True` (or equivalent declared-content flag) must
   land on `contentArgument`, full stop — this is a hard constraint, not a
   cost to trade off, the same way `mog`'s sporadic modulus was non-negotiable.
2. **Every `zkArgument` assignment clears the 128-bit floor.** Check this as
   a constraint before accepting the LP's cost-minimizing choice — don't let
   a cost-0 shortcut (like the earlier `nodejs → rung1` bug) slip through.
3. **Total solve cost is not the cheapest theoretically possible, just not
   obviously wasteful** — e.g., don't accept a solve where two projects with
   near-identical declared features get routed to different rungs for no
   stated reason; do accept a solve that's a few cost-units off some
   hypothetical optimum if all constraints above hold.
4. **Every `publishOnly` assignment corresponds to a project with no
   published claim yet**, re-checked against `PROJECT.md`'s own
   "Arguments Published" field, not assumed.

If any of 1–4 fails, fix the cost function or feature table and re-solve —
don't hand-patch the output.

## Explicit non-goals

- Do not re-verify any project's withheld source to "improve" the feature
  table's accuracy beyond what's declared in its published prose. That
  verification is structurally unavailable (zkPoP withholds source by
  design) and pretending otherwise defeats the point of flagging it.
- Do not force the Nova/Groth16 `FoldedExecution`/`Decider` layer onto any
  project that hasn't stated a distributed, untrusted-peer reconstruction
  requirement. It applies only where that requirement is real.
- Do not chase commutativity, exact optimal transport cost, or a fully
  populated cost-function justification before re-running — those are
  real follow-ups (noted in the conversation), not blockers on accepting a
  good-enough bootstrap now.

## Procedure

1. Update `PROJECTS` in `bootstrap_transport.py` with any new/changed
   declared features.
2. Run the LP solve.
3. Check the four conditions above against the output.
4. If all pass: check in the result as the new `projectFit` snapshot in
   `AokInterface.lean`, replacing the previous snapshot wholesale (it's
   generated, not hand-edited — see prior comment in that file).
5. If any fail: adjust cost function or feature table (not the output),
   re-run from step 2.
6. Re-run only when a project's declared features actually change or a new
   project is added — not on a schedule, not "to see if it improves."


---

## unified-crypto-methodology.md

# Unified Crypto Methodology for the aok / ZKPoP Corpus

## 1. Current state (as found across the 27 published arguments)

| Component | Instances found | Problem |
|---|---|---|
| Group for Schnorr/Pedersen/Okamoto/CDS | (a) custom 2048-bit MODP safe-prime group, `q` picked {2,3,5}-smooth for a finite Lucas certificate; (b) 2^521−1 Mersenne-modulus group (Lucas–Lehmer) | Two different, bespoke finite-field DL groups. Both need their own primality certificate re-verified per paper. Both are ~5–10x larger and slower than an elliptic-curve group at equivalent security. |
| Second generator (`h` in Pedersen) | "public hash-to-group derivation," described in prose, not a fixed spec | No single, reusable, standardized derivation — every paper could in principle derive it differently. |
| Transcript / Fiat–Shamir | Hand-written `H(context‖C‖t‖root)`-style strings, varying paper to paper | Classic source of soundness bugs (weak vs. strong Fiat–Shamir, missing statement-binding, missing domain separation). Nothing enforces the same binding rule everywhere. |
| Hash function | SHA-256 (FIPS 180-4, verified against test vectors in Lean) — consistent, this one's fine | — |
| Merkle tree | Domain-separated leaves/nodes, SHA-256 — consistent, fine | — |
| Recursion/self-hosting layer | Abstract "outer proof verifies inner proof" model | Protocol-agnostic — inherits whatever the base group provides. Good design, just needs one base group to inherit from. |
| Distribution (N-of-M PNG carriers) | Erasure-coded, threshold reconstruction | Carriers aren't individually bound into the same Merkle/commitment root, so partial-carrier authentication isn't as tight as it could be. |
| Non-cryptographic content | Monster-group divisor/amicable-pair arithmetic, FRACTRAN/CRT GPU overlays, Tesla-369 numerology | Legitimate as the *statement being proved in zero knowledge* (fun demo content) — but only one paper (the self-hosted one) explicitly ledgers this apart from the security argument. The rest don't draw the line as clearly. |

**Bottom line:** the security-relevant crypto is textbook-correct wherever it's spelled out, but it is duplicated ~5 different ways instead of shared, and the numerology/group-theory "flavor" content isn't consistently fenced off from the trust boundary.

## 2. Unified crypto core (replace both ad hoc groups)

Adopt **one** canonical group for every Schnorr / Pedersen / Okamoto / CDS instance across all projects:

- **Group:** Ristretto255 — a prime-order group built on Curve25519's group, with no cofactor headaches and constant-time, misuse-resistant encoding. (Curve448/Decaf448 as the "128-bit+" option if you want a second security tier instead of the 2048-bit MODP group's tier.)
- **Why it replaces both existing groups:** it's smaller (32-byte elements vs. 256-byte MODP elements), faster, has no custom primality certificate to maintain (the curve parameters are already standardized and audited), and gives you one security proof to write instead of two.
- **Second generator `h`:** derive it once, centrally, via RFC 9380 `hash_to_curve` with a fixed domain-separation tag (e.g. `"aok-zkpop-v1-generator-h"`). Every paper imports this constant instead of re-deriving it.
- **Lean formalization path:** since the Sigma-protocol proofs (completeness, special soundness, HVZK) are already generic over an abstract `Base` group typeclass, you don't re-derive those theorems. You write **one** new instance proof — "Ristretto255 satisfies the group axioms + hard-discrete-log/DDH assumption used by `Base`" — and every existing theorem (Schnorr, Pedersen, Okamoto, CDS-OR) specializes to it automatically. This is the highest-leverage single change: one proof obligation upgrades all 27 papers' crypto layer at once.

## 3. Unified transcript / Fiat–Shamir

Replace the hand-rolled `H(context‖C‖t‖root)` strings with a single transcript construction (Merlin/STROBE-style) used everywhere:

1. Bind the protocol name and version first (`"aok-zkpop/1"`).
2. Absorb every public parameter (group, generators, statement/Merkle root, environment hash, checker identifier) before any prover message.
3. Absorb each prover message (`C`, `t`, etc.) in a fixed order.
4. Derive the challenge only after all of the above — this is "strong" Fiat–Shamir, which is what your knowledge-soundness proofs actually need (weak Fiat–Shamir, which only hashes the last message, is a known way these arguments silently lose extractability).

This becomes one shared Lean module + one shared library per target language, instead of a bespoke hash string per paper.

## 4. Unified trust ledger template

Take the "minimality ledger" / "honest trust ledger" pattern already used in the self-hosted paper and make it mandatory for every argument, with identical fields:

- Axioms used (should stay at Lean's standard three, plus `ofReduceBool`/`trustCompiler` only where compiled evaluation is explicitly declared)
- Which properties are unconditional (hiding, HVZK) vs. computational (binding/soundness — under discrete-log hardness in Ristretto255, Fiat–Shamir in the ROM)
- What the arithmetic *statement* is (Monster divisors, amicable pairs, whatever) — explicitly labeled as content, not security
- What's reused vs. new per paper

This turns 27 differently-worded trust sections into one comparable, auditable table.

## 5. Consolidation of the repo itself

Right now each UUID directory re-implements its own crypto layer per language port (agda, mojo, nodejs, Solana/Lean4, CompCert, etc.). Structurally:

- Factor the group + transcript + Merkle logic into **one audited core** (Lean4 reference implementation + generated/ported bindings), rather than 27 independent implementations.
- Per-language ports become thin bindings that call the core's test vectors to prove interoperability, not independent reimplementations of Pedersen/Schnorr from scratch.
- This cuts your actual audit surface from "~5 bespoke crypto stacks across 27 papers" to "1 crypto core + N thin, mechanically-checked bindings."

## 6. Distribution layer hardening

Bind the N-of-M PNG carrier shares into the same commitment root used by the argument (e.g., Merkle-leaf per carrier, root folded into the Fiat–Shamir transcript). That way a tampered or substituted carrier is detected the same way a tampered statement is, rather than being a separate, unauthenticated erasure-coding layer.

## 7. What does *not* change

- SHA-256 for hashing/Merkle trees — already consistent and FIPS-verified, no need to touch it.
- The recursion/self-hosting abstraction — it's protocol-agnostic and correctly designed; it just inherits the upgraded base group automatically once step 2 is done.
- The choice to prove fun arithmetic facts (Monster divisors, amicable pairs) in zero knowledge — keep it, just keep it clearly outside the security-relevant crypto core per the ledger in §4.


---

## AokInterface.lean

```lean
/-
  Two-tier interface for the whole aok system, not just zkpop.

  Tier 0 (Publishable) is universal -- every project (zkpop, monster, lean4,
  dotagents, dasl) already satisfies it via aok-publish.py / manifest.json.
  Nothing new to build; this just names the existing shape.

  Tier 1 (Argument) is for projects that make a checkable CLAIM about
  something -- a subset of projects, not all of them. ZkPoPArgument (see
  ZkPoPCore.lean) is one refinement of Argument, for claims whose evidence
  must stay hidden. Plain arguments (evidence public) are the other.

  dotagents does NOT get a Tier-1 instance below, on purpose: it has not
  published a claim, only tooling. Giving it a fake Statement/verify pair
  would be the same error as forcing mog's content modulus onto a generic
  crypto rung -- inventing structure the project doesn't actually have.
-/

/-- Tier 0: universal. Mirrors manifest.json's existing entry shape exactly,
    so this is a description of what already exists, not a migration. -/
structure Publishable where
  uuid      : String
  project   : String
  title     : String
  tags      : List String
  sha256    : String
  files     : List String
  author    : String
  published : String   -- ISO timestamp, as already stored

/-- Tier 1: for projects making a checkable claim. Deliberately minimal --
    `Evidence` is a type parameter so a project chooses whether its evidence
    is public (plain argument) or must stay hidden (zk argument, see
    ZkPoPArgument, which additionally requires `[ZkPoPGroup G]` and routes
    Evidence through a commitment). -/
class Argument (Statement Evidence : Type) where
  verify      : Statement → Evidence → Bool
  contentOnly : Bool   -- true if this claim's parameters ARE its content
                        -- (e.g. mog's sporadic modulus) and must not be
                        -- swapped for a "better" generic choice

/-- Per-project fit. GENERATED, not hand-maintained -- see
    bootstrap_transport.py. This block is the checked-in snapshot of that
    script's last solve; regenerate it whenever a project's declared
    features change or a new project is added. Do not hand-edit this list
    the way an earlier draft of this file did. -/
inductive ProjectKind
  | zkArgument      -- evidence hidden
  | contentArgument -- evidence public but IS the claim
  | plainArgument   -- evidence public, ordinary check
  | publishOnly     -- Tier 0 only, no Tier-1 claim yet

-- GENERATED by bootstrap_transport.py, total cost 5.0 -- do not hand-edit.
def projectFit : List (String × ProjectKind × Nat) := [
  ("agda-zkpop-v1",       .zkArgument,      1),
  ("mojo-zkpop-v1",       .zkArgument,      1),
  ("nodejs-zkpop",        .zkArgument,      2),
  ("zk-pop-solana-lean4", .zkArgument,      1),
  ("mog-zk-pop-v1",       .contentArgument, 0),
  ("monster",             .contentArgument, 0),
  ("dasl",                .plainArgument,   0),
  ("dotagents",           .publishOnly,     0),
  ("lean4",               .publishOnly,     0)
]

```

---

## ZkPoPCore.lean

```lean
/-
  ZkPoPCore: a standard API that every zkPoP argument (agda, mojo, nodejs,
  solana-lean4, and future instances) implements, instead of each paper
  restating its own commitment/protocol from scratch.

  This does NOT reprove completeness/soundness/HVZK per instance. Those are
  proved once, generically, against the `ZkPoPGroup` interface. An instance
  only has to prove it satisfies the interface -- exactly the move the
  transport plan identified as low-cost (cost 1-2 per source) for four of
  the five source papers.
-/

/-- The group interface every concrete instantiation (Ristretto255, or in
    principle any other group) must satisfy. This is the ONE thing that
    changes when you swap crypto cores; nothing downstream re-proves. -/
class ZkPoPGroup (G : Type) where
  op        : G → G → G
  inv       : G → G
  id        : G
  q         : Nat                       -- group order (must be prime)
  q_prime   : q.Prime
  g h       : G                         -- two generators; h via fixed hash-to-group, NOT ad hoc
  h_indep   : True                      -- placeholder: "discrete log of h w.r.t. g is unknown"
  hard_dl   : True                      -- placeholder: discrete-log hardness assumption

/-- A statement being argued: a Merkle root over the withheld corpus, plus
    the environment/checker identifiers every paper already publishes. -/
structure ZkPoPStatement where
  merkleRoot   : ByteArray
  envHash      : ByteArray
  checkerId    : ByteArray

/-- A witness: the digest/scalar the prover actually knows, never disclosed. -/
structure ZkPoPWitness (G : Type) [ZkPoPGroup G] where
  m : Nat   -- the committed scalar (e.g. Merkle root mod q)
  r : Nat   -- Pedersen blinding factor

/-- The transcript, built by ONE shared strong-Fiat-Shamir routine, not a
    per-paper hash string. Binds protocol name + all public params + all
    prover messages BEFORE the challenge is derived. -/
structure ZkPoPTranscript (G : Type) where
  protocolTag : String := "aok-zkpop/2"
  statement   : ZkPoPStatement
  commitment  : G
  announcement: G
  challenge   : Nat
  responses   : Nat × Nat

/-- L5 Session: the actual protocol exchange (commitment, challenge,
    response). Swappable independently of the L4 guarantee below -- e.g.
    Schnorr vs. a different Sigma-protocol shape, same guarantee. -/
class ZkPoPSession (G : Type) [ZkPoPGroup G] where
  commit   : ZkPoPWitness G → G
  prove    : ZkPoPWitness G → ZkPoPStatement → ZkPoPTranscript G
  verify   : ZkPoPStatement → ZkPoPTranscript G → Bool

/-- L4 Transport: the delivery GUARANTEE a session must satisfy, proved
    once, generically, against any [ZkPoPSession]. Swapping the session
    (L5) does not require reproving this; swapping the guarantee's strength
    (e.g. adding post-quantum soundness later) does not require touching L5. -/
class ZkPoPTransportGuarantee (G : Type) [ZkPoPGroup G] (S : ZkPoPSession G) where
  completeness      : ∀ w s, S.verify s (S.prove w s) = true
  special_soundness : ZkPoPTranscript G → ZkPoPTranscript G → ZkPoPWitness G
  perfect_hvzk      : True  -- placeholder: simulator distribution = real distribution

-- ZkPoPArgument (previous version) = ZkPoPSession + ZkPoPTransportGuarantee
-- bundled together. Kept as a convenience alias, not the primary interface:
class ZkPoPArgument (G : Type) [ZkPoPGroup G] extends ZkPoPSession G where
  extract : ZkPoPTranscript G → ZkPoPTranscript G → ZkPoPWitness G

/-- Registry entry: what each paper actually instantiates. This is the
    diagonalized manifest row, expressed as data instead of prose. -/
structure ZkPoPInstance where
  name          : String
  groupChoice   : String   -- "Ristretto255" | "2^521-1 Mersenne (content)" | "sporadic-order (content)"
  transportCost : Nat      -- from the LP solve
  contentBearing: Bool     -- true only when the modulus IS the theorem (e.g. mog)

def registry : List ZkPoPInstance := [
  ⟨"agda-zkpop-v1",        "Ristretto255", 1, false⟩,
  ⟨"mojo-zkpop-v1",        "Ristretto255", 1, false⟩,
  ⟨"nodejs-zkpop",         "Ristretto255", 2, false⟩,
  ⟨"zk-pop-solana-lean4",  "Ristretto255", 1, false⟩,
  ⟨"mog-zk-pop-v1",        "sporadic-order (content)", 1, true⟩
]

```

---

## FoldedReconstruction.lean

```lean
/-
  Folded reconstruction across untrusted peers.

  This is NOT a refinement of the existing N-of-M PNG carrier scheme --
  that scheme tolerates erasure (missing shares), not corruption (wrong
  shares from an adversarial peer). This interface is strictly stronger and
  should be treated as a new primitive, not a drop-in upgrade.

  Two separable concerns, each its own typeclass on purpose (same reasoning
  as splitting ZkPoPSession from ZkPoPTransportGuarantee): reconstruction
  and folding are independently swappable and should not be bundled.
-/

/-- A single slice of execution contributed by one (possibly adversarial)
    peer/thread, bound to a commitment so a wrong slice is detectable, not
    just missing. -/
structure ExecSlice where
  threadId    : Nat
  commitment  : ByteArray   -- binds this slice's content
  merklePath  : List ByteArray  -- authenticates commitment against the global root
  payload     : ByteArray   -- the slice itself (opened only on reconstruction)

/-- L4-analogue for reconstruction: the guarantee is "t-of-n authenticated
    slices reconstruct the execution, and any slice failing its own
    Merkle path is REJECTED, not silently included." This is what turns
    erasure-coding into Byzantine fault tolerance -- the authentication,
    not the erasure code itself. -/
class ByzantineReconstruction (n t : Nat) where
  globalRoot   : ByteArray
  authenticate : ExecSlice → Bool          -- checks merklePath against globalRoot
  reconstruct  : List ExecSlice → Option ByteArray
                                            -- succeeds iff ≥ t authenticated slices present
  -- guarantee to prove: ∀ slices, (authenticated slices).length ≥ t →
  --   reconstruct slices = some (true execution), independent of what the
  --   remaining n-t peers (up to fully adversarial) contributed.

/-- Folding: combine per-slice execution proofs into one proof whose size
    does not grow with the number of threads. Concretely: Nova-style
    relaxed-R1CS folding, `U' = fold U1 U2` via a Fiat-Shamir challenge `r`
    and cross-term correction. This is ASSOCIATIVE under tree-shaped
    reduction (any balanced binary tree of pairwise folds over the
    authenticated slice set gives a sound final instance) -- it is NOT
    commutative as a raw binary op, since each fold step has a "running"
    and an "incoming" role with an asymmetric cross-term. Tree-shaped
    associativity, not commutativity, is what lets untrusted peers'
    slices fold correctly regardless of arrival order. -/
class FoldedExecution (RelaxedInstance : Type) where
  fold       : RelaxedInstance → RelaxedInstance → RelaxedInstance  -- Nova fold step
  proveSlice : ExecSlice → RelaxedInstance
  -- guarantee to prove:
  --   1. tree-associativity: for any two balanced binary trees T1, T2 over
  --      the same authenticated slice multiset, foldTree T1 = foldTree T2
  --      up to relaxed-instance equivalence (NOT claiming `fold` itself is
  --      commutative -- only that the final folded result is tree-shape-
  --      independent, which is the actual property Nova needs and gives).
  --   2. soundness transports through fold: if U1, U2 are each sound
  --      (satisfy their relaxed R1CS relation), fold U1 U2 is sound.
  --      Same "soundness transports, is not created" statement the
  --      self-hosted paper already makes about ordinary recursion.
  --   3. a single unauthenticated/corrupted slice's `proveSlice` output
  --      must make every subsequent fold containing it unsound -- folding
  --      must not average a bad slice's error away.

/-- The decider: wraps the single final relaxed R1CS instance (after all
    folding is done) into one short, pairing-based SNARK -- Groth16 -- so
    the verifier never touches relaxed-R1CS objects directly. This is the
    only place a per-circuit trusted setup is needed; the fold steps
    themselves need none. -/
class Decider (RelaxedInstance Groth16Proof : Type) where
  decide : RelaxedInstance → Groth16Proof
  verify : Groth16Proof → Bool
  -- guarantee to prove: verify (decide U) = true iff U satisfies its
  -- relaxed R1CS relation -- i.e. the decider is complete and sound with
  -- respect to whatever the fold tree actually accumulated.

/-- The composed guarantee this whole thing is actually for: reconstruction
    succeeds AND the folded proof verifies, using only threads that pass
    authentication -- explicitly not "most threads agree," which is a much
    weaker and different property (that would be closer to a BFT consensus
    guarantee, not a proof-of-execution guarantee). -/
structure FaultTolerantExecutionClaim (n t : Nat) (RelaxedInstance Groth16Proof : Type)
    [ByzantineReconstruction n t] [FoldedExecution RelaxedInstance]
    [Decider RelaxedInstance Groth16Proof] where
  claim : String := "execution is reconstructible and its tree-folded Nova instance, \
                      once decided into a Groth16 proof, verifies from any t-of-n peers, \
                      with corrupted/unauthenticated contributions rejected rather than \
                      averaged in"

```

---

## bootstrap_transport.py

```python
"""
Minimal optimal-transport bootstrap layer for the aok interface.

This is the thing that PRODUCES projectFit / registry entries in
AokInterface.lean and ZkPoPCore.lean -- those files should be regenerated
from this, not hand-maintained, once a project's declared features change
or a new project is added.

Division of labor, stated explicitly:
  - THIS script: solves the transport LP (where does each project's
    declared features minimally-cost-map onto the tier/rung lattice).
  - Lean: does NOT solve LP. It only checks the one load-bearing proof
    obligation per rung (e.g. "Ristretto255 satisfies ZkPoPGroup") and
    typechecks the per-project instance that the plan says should exist.
  - Nothing here re-verifies a project's underlying claim; source is
    intentionally withheld for zkArgument projects. This only optimizes
    over DECLARED parameters, same caveat as before.
"""
import numpy as np
from scipy.optimize import linprog
import json

# --- Step 1: declared features per project (hand-entered from prose, flagged as such) ---
PROJECTS = {
    "agda-zkpop-v1":       {"kind_hint": "zk",      "evidence": "hidden", "modulus_is_content": False, "declared_group_cost_to_ristretto": 1},
    "mojo-zkpop-v1":       {"kind_hint": "zk",      "evidence": "hidden", "modulus_is_content": False, "declared_group_cost_to_ristretto": 1},
    "nodejs-zkpop":        {"kind_hint": "zk",      "evidence": "hidden", "modulus_is_content": False, "declared_group_cost_to_ristretto": 2},
    "zk-pop-solana-lean4": {"kind_hint": "zk",      "evidence": "hidden", "modulus_is_content": False, "declared_group_cost_to_ristretto": 1},
    "mog-zk-pop-v1":       {"kind_hint": "zk",      "evidence": "hidden", "modulus_is_content": True,  "declared_group_cost_to_ristretto": 80},
    "monster":             {"kind_hint": "content", "evidence": "public", "modulus_is_content": True,  "declared_group_cost_to_ristretto": 80},
    "dasl":                {"kind_hint": "plain",   "evidence": "public", "modulus_is_content": False, "declared_group_cost_to_ristretto": None},
    "dotagents":           {"kind_hint": "none",    "evidence": None,     "modulus_is_content": False, "declared_group_cost_to_ristretto": None},
    "lean4":               {"kind_hint": "none",    "evidence": None,     "modulus_is_content": False, "declared_group_cost_to_ristretto": None},
}

# --- Step 2: tier/kind targets, each with a hard constraint on what may land there ---
KINDS = ["zkArgument", "contentArgument", "plainArgument", "publishOnly"]

def cost_to_kind(name, feat, kind):
    if kind == "publishOnly":
        # Only legitimate at zero cost if the project has NOTHING published yet.
        return 0 if feat["evidence"] is None else 40
    if kind == "plainArgument":
        return 0 if (feat["evidence"] == "public" and not feat["modulus_is_content"]) else 60
    if kind == "contentArgument":
        return 0 if feat["modulus_is_content"] else 60
    if kind == "zkArgument":
        if feat["evidence"] != "hidden":
            return 60
        return feat["declared_group_cost_to_ristretto"] or 60
    return 999

names = list(PROJECTS.keys())
n, m = len(names), len(KINDS)
cost = np.array([[cost_to_kind(nm, PROJECTS[nm], k) for k in KINDS] for nm in names], dtype=float)

A_eq = [np.eye(m).flatten() if False else None]  # placeholder removed below
A_eq, b_eq = [], []
for i in range(n):
    row = np.zeros(n*m); row[i*m:(i+1)*m] = 1
    A_eq.append(row); b_eq.append(1)

res = linprog(cost.flatten(), A_eq=A_eq, b_eq=b_eq, bounds=(0,1))
X = res.x.reshape(n, m)

plan = {}
for i, nm in enumerate(names):
    j = int(np.argmax(X[i]))
    plan[nm] = {"assigned_kind": KINDS[j], "cost": float(cost[i, j])}

print(json.dumps(plan, indent=2))
print("\ntotal bootstrap cost:", res.fun)

```

---
