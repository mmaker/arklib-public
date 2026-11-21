# Fiat-Shamir protocol interfaces and salt parameters

## Construction scope

ArkLib implements the basic random-oracle Fiat–Shamir transform and the CO25 overwrite-duplex
transform. This page describes their protocol interfaces, byte serialization, and completeness
results. The implementation correspondence for the overwrite duplex is separate from its
ideal-model security analysis.

## Application interface

`InteractiveProof/IP.lean` defines `InteractiveProver`, `InteractiveVerifier`, and
`InteractiveProtocol`. The prover initializes its state and runs the rounds. The verifier
consumes the original statement and full transcript and returns a Boolean decision.
`NonInteractiveArgument/NARG.lean` defines the honest argument's function fields:

- `prover : Statement → Witness → OracleComp oSpec NARGString`
- `verifier : Statement → NARGString → OracleComp oSpec Bool`

For applications, use `InteractiveProtocol.fiatShamir` from `Canonical/Construction.lean` or
`InteractiveProtocol.duplexSpongeFiatShamir` from `DuplexSponge/Construction.lean`. Both return a
`NonInteractiveArgument`; the `InteractiveProver` and `InteractiveVerifier` namespaces expose
the individual algorithms. These algorithms return a NARG string and acceptance decision,
without computing or returning a reduced statement or witness.

The established reduction-based constructors and security proofs remain available.
`InteractiveProver.toReductionProver` adds a dummy terminal `(true, ())` output for that proof
interface; NARG-string generation does not execute it. `InteractiveVerifier.toReductionVerifier`
embeds the Boolean computation without adding queries, retaining rejection as `some false`.
`InteractiveProtocol.toReduction` bundles these views. In the reverse direction,
`Prover.toInteractiveProver` forgets terminal output and `Verifier.toInteractiveVerifier` maps
an aborting Boolean verifier's abort to rejection.

`InteractiveProtocol.run` delegates to the established round executor, preserving query order
without executing a terminal prover output. `InteractiveProtocol.toReduction_verdict` proves
that the compatibility execution is exactly `some` applied to this Boolean computation.
The DSFS generator likewise delegates to the existing message algorithm, retaining its optimized
termination and permutation query routing.

The exact computation laws `InteractiveProver.compileFiatShamir_eq_sendMessage` and
`InteractiveVerifier.compileFiatShamir_eq_verify`, and their DSFS counterparts
`InteractiveProver.duplexSpongeFiatShamirPayload_sendMessage` and
`InteractiveVerifier.duplexSpongeFiatShamirPayload_verify`, identify the application algorithms with
the compatibility compilers. They preserve oracle effects, not just returned values. Existing
security theorems apply to the explicit compatibility views under their original hypotheses;
changing the return interface does not remove sampling, codec, round-shape, or oracle assumptions.

### Canonical byte NARG strings

`DSFSTypedNARGString pSpec U δ` is the typed NARG string: the salt paired with the
prover messages, before byte serialization. `DSFSNARGString` is its public byte representation,
`ByteArray`. Verifier messages are reconstructed and are not included in either representation.
The public `InteractiveProtocol.duplexSpongeFiatShamir`
compiler takes an explicit `Serializer (DSFSTypedNARGString pSpec U δ)` before its salt sampler.
Its prover serializes the typed NARG string; its verifier parses the whole input and rejects failure
before issuing any oracle query. The `...Payload` algorithms expose the structured internal view.
`Serializer` supplies byte serialization and parsing with correctness laws. `Codec` supplies
protocol-message encoding into sponge units and decoding of sponge output into verifier messages.
These are separate interfaces; an existing `Serde` instance without correctness laws is not
sufficient for serialization.

`NonInteractiveArgument/Serialization/Serializer.lean` formally requires and proves:

- `deserialize (serialize value) = some value` (round-trip correctness).
- Successful parsing implies `serialize value = input` (canonical acceptance).
- Encodings are prefix-free. Consequently, appending any nonempty suffix to a complete encoding
  yields `none`, even if the suffix could otherwise make an encoding of a different value.

The first two laws imply injectivity and rejection of every byte array outside the encoding's
image. All validity conditions must live in the payload type: use a subgroup type for subgroup
membership, or a subtype for a canonical range. `Serializer.subtype` checks a decidable
predicate during parsing; it does not silently assume that an arbitrary curve-point type has
subgroup membership. `vector`, `ofFixedSize`, and `ofEquiv` supply executable construction helpers.

**Implementation guidance:** lengths and counts read from bytes are untrusted.
Check them against remaining input and resource limits before indexing, allocation, iteration,
or arithmetic that could overflow. The abstract serializer laws do not prove memory/time bounds or
check ordering. Fixed-length formats can avoid transmitted counts entirely.

`NonInteractiveArgument/Serialization.lean` proves exact verifier correspondence on valid encodings, rejection
of malformed and trailing-byte inputs, and preservation of honest execution and completeness.
`NonInteractiveArgument/Serialization/Legacy.lean` transports adaptive soundness and knowledge soundness to
byte inputs, preserving query budgets, query logs, and extractor oracle permissions.
`NonInteractiveArgument/Serialization/Security.lean` exposes these transfers for decision-facing arguments;
malformed inputs reject without queries and cannot increase the failure probability. Serialization-induced ambiguity is excluded;
this does not assert general cryptographic non-malleability.

## Salt parameters

The salt-bearing transformations are `fiatShamirSalted` and `duplexSpongeFiatShamir`.
The core `Prover.fiatShamir`, `Verifier.fiatShamir`, and `Reduction.fiatShamir`
remain in `FiatShamir/Basic.lean`; their fixed-table and shared-random-oracle completeness
theorems live in `FiatShamir/Canonical/Completeness/Unsalted.lean`. The public completeness
statements for the two constructions live in `Canonical/Completeness.lean` and
`DuplexSponge/Completeness.lean`, respectively. Fork callers that previously passed a salt
length to `fiatShamir` now use `fiatShamirSalted`, with unchanged argument order and wire format.
The application-facing `InteractiveProver`, `InteractiveVerifier`, and `InteractiveProtocol`
`fiatShamir` methods take a `Serializer` and produce or consume `ByteArray`. Their
`fiatShamirTyped` counterparts retain the internal salt/message tuple. Malformed and trailing-byte
inputs reject before oracle queries. `InteractiveProtocol.fiatShamir_completeness` combines exact
random-oracle completeness with `NonInteractiveArgument.serialize_completeness_iff`;
serialization adds no error.
`fiatShamirSalted_completeness` preserves arbitrary completeness error with shared lazy uniform
round functions, an initially empty cache, stateless ambient oracles, and any ambient-only salt
sampler. The proof in `Canonical/Completeness/RandomOracle.lean` establishes equality of honest output
distributions by conditioning on the salt and reusing the core random-oracle theorem.
`fiatShamirSalted_perfectCompleteness` additionally permits arbitrary fixed-function distributions;
that stronger oracle generality applies only to zero completeness error.
`ProtocolSpec.MessagesUpTo.completeMessages` converts an early prefix containing every prover
message; upstream `MessagesUpTo.toMessages` converts the complete round prefix.

Both salt-bearing transformations take a salt-length parameter and an ambient-only salt sampler.
The sampler is invoked once per NARG string. Its result has type `Vector U saltLength` and is reused for all rounds.
Canonical FS includes it in each random-oracle key; DSFS absorbs it once before the rounds.

`FiatShamirNARGString pSpec U saltLength` packages salt metadata alongside `pSpec.Messages`.
This is transport packaging, not a change to the application statement, relation, witness, or
interactive message family. An empty salt contributes no encoded symbols. Length zero is the
same construction, obtained by parameter instantiation; it has no separate compiler or public
security theorem family. Use `pure #v[]` when the zero-length sampler should make no queries.

The canonical compatibility entry points (CO25 Construction 3.17) live in
`FiatShamir/Canonical/Construction.lean`, with namespace `CanonicalFS`.
`Canonical/Security/Soundness.lean` exposes soundness and knowledge soundness. Their proofs and
helpers live in `Canonical/Security/Proofs/`.
Its generic abstract-salt
`compileFiatShamir` is an internal encoding adapter used by the DS-to-FS security bridge.
The state-restoration API takes the original verifier, input language or relation, and a separate
salt type. An SR prover returns `((x, τ), messages)`; its moves query the existing
`srVerifierMessageOracle (StmtIn × Salt) pSpec` interface. The product here is query context, not the
IP statement space. Transcript reconstruction uses `(x, τ)`, verification receives only `x`,
and an SR extractor receives `x` and `τ` as separate arguments. The canonical FS
premises therefore use the original language and relation directly. No salted-verifier wrapper
is needed. The named SR prover types accept a private sampling interface explicitly; the standard
security predicates instantiate it with `unifSpec`. False-acceptance and extraction-failure
probabilities, query counts, and final security bounds are preserved by the FS/SR execution proofs.

The `IP` namespace in `InteractiveProof/StateRestorationSoundness.lean` specializes these games
to Boolean acceptance with no ambient IP oracles. `NonInteractiveArgument/Soundness.lean` defines
the corresponding NARG security games. `OracleReduction/Salt.lean` remains a separate
transformation that inserts salts into protocol messages; the SR game here uses one salt in
every verifier-message query.

The sampler has type `OracleComp oSpec (Vector U saltLength)` and cannot inspect the statement,
witness-bearing prover state, or public FS oracle. The ZK experiments instantiate it with fresh
uniform private coins. Merely invoking an arbitrary ambient sampler once does not establish
uniformity. Canonical perfect-completeness, soundness and knowledge-soundness entry points have
explicit salt-length parameters. DSFS preserves terminal-work omission and the forward-only
honest verifier interface.

`FiatShamir/Codec.lean` owns the message codec and salt encoding interfaces.
`DuplexSponge/Sponge.lean` owns the ideal-oracle sponge state and operations, and
`DuplexSponge/Construction.lean` owns the DSFS prover and verifier compilers.
`DuplexSponge/Completeness.lean` owns the public perfect-completeness theorem. Its proof lives in
`DuplexSponge/Completeness/Perfect.lean`.
It preserves the zero-error guarantee for a stateless ambient handler and any ambient-only salt
sampler.

The public-coin view is `Reduction.honestVerifierView impl prover stmt wit`; HVZK uses
`Reduction.honestVerifierZeroKnowledge impl prover relation error`. Verifier messages are
independent uniform samples from the protocol's finite nonempty message spaces. The OR round
runner reveals each message only at its turn, and returns the statement and full transcript.
The final verifier check is neither an argument nor executed; acceptance is not a condition
of the view. In blueprint notation use `View_IP(P, x, w)`, with the protocol and ambient-oracle
handler specified in context. This specializes CO25 Definition 7.2 to its public-coin case;
it does not model general private-state verifier strategies. DSFS uses only private uniform
coins for the IP prover. Do not add unused verifier parameters to the view or its downstream
security statements merely to reproduce the paper's general notation.

Use `oSpec` for the ambient/shared oracle interface. Standard security games provide a separate
`unifSpec` for private prover coins; custom samplers remain inside reduction helpers. See
[the private-sampling lemmas](../../ArkLib/Security/PrivateCoins.lean) for routing and transcript rules. Instantiating `oSpec`
with `unifSpec` does not make the
interface prover-only: the usual handler supplies fresh coins per call, without exposing
one party's sampled coins to the other. In the SR game, the verifier-message oracle is a
separate interface. The generic SR initialization and stateful handler do not by themselves
ensure uniform sampling or repeatable answers.

After changing this surface, run `./scripts/validate.sh --axioms`. Do not introduce new axiom or
admission debt; native-compiler trust is never allowlisted.

## Security interfaces

Adaptive soundness, knowledge soundness, their experiments, and size restrictions live in
`NonInteractiveArgument/Soundness.lean`; `NARG.lean` contains only the honest argument.
The ordinary `IP` state-restoration contracts live in
`InteractiveProof/StateRestorationSoundness.lean`.
`InteractiveProtocol.toReduction_completeness_iff` belongs to `InteractiveProof/IP.lean`.

## Quantitative duplex-sponge completeness dependency boundary

The integration branch's completeness bound `ε + spongeLoss + ∑ i, Codec.decodingBias i`
is not part of this construction branch. Its proof currently goes through the
zero-knowledge programming development. Perfect completeness remains a separate theorem:
the quantitative bound has additional nondegeneracy, uniform-coin, and uniform-salt
hypotheses and does not specialize to zero error merely by setting `ε = 0`.

The required proof boundary has three parts:

- **Honest execution:** tagged round execution and its real-handler correspondence;
  IID squeeze recording and `TaggedHybrid.evalDist_record_run`;
  `VerifierMessageSampling.evalDist_runFixed_plan`; fixed-message execution;
  and projections from eager real/hybrid executions. The final private state must be
  retained so transcript instrumentation can recover the verifier's acceptance event.
- **Decoder loss:** `discreteTVDist_decodeVerifierMessages_uniform_le_sum`, currently
  in `SimulationReduction`, is the only theorem from that file directly used by
  `CompletenessError`. Its finite-product sampling and codec-bias support belongs with
  the codec, without the subsequent simulation games.
- **Sponge loss:** `EagerProgramming.tvDist_eagerWithAux_le_bad` and
  `HybridBadProbability.prEvent_eager_bad_le`. The latter is instantiated with a
  fixed-input, zero-query adversary. Its current proof still uses monitored prefix
  tables, conditional permutation completion, capacity monitoring, salt-avoidance
  reasoning, and the zero-knowledge tagged game. Setting the prefix budget to zero
  removes the prefix term in the bound, but does not remove these proof dependencies.

At integration commit `16c839a6d`, the source import closure of `CompletenessError` and
`CompletenessExecution` adds 39 files and 12,410 lines relative to the original construction
branch: 27 zero-knowledge modules, nine staging modules, the query bounds, and the two
completeness proof modules. This is an import-closure count, not a claim that every
line is mathematically necessary. The nine staging modules provide permutation
conditioning/programming, subdistribution and relational reasoning, and supporting
sampling/measure lemmas. The two proof modules themselves total 609 lines.

A declaration-dependency traversal of their compiled statements and proof bodies finds
65 direct constants from zero-knowledge/staging owners and 870 constants in their
transitive closure (including generated helpers), spread across 27 zero-knowledge and
eight staging modules. `ProgramLogic/Relational/MeasureRelational.lean` is in the import
closure but contributes no constant to this proof closure. This distinguishes the
actual proof dependencies from incidental imports; it still leaves the adaptive
bad-event and permutation-programming development in the required closure.

A small port needs a prior refactor: expose a fixed-input honest-execution comparison
that retains arbitrary final private state, with sponge loss proved directly from an
empty permutation table. Move the tagged executor, IID challenge-plan law, codec tuple
bound, and generic permutation comparison support into shared owners; keep adaptive
adversaries and simulation games above those owners. The existing proof through the
adaptive bad-event theorem does not provide a self-contained port near 1,500 lines.
The payload and byte-level completeness theorems can then consume that boundary while
continuing to use the separate perfect-completeness transcript reconstruction lemmas.
