# Fiat–Shamir interfaces

The honest interactive interface lives in `ArkLib/InteractiveProof/IP.lean`:
`InteractiveProver`, `InteractiveVerifier`, and `InteractiveProtocol` describe the
algorithms and their execution. `InteractiveProtocol.completeness` measures honest
acceptance; `InteractiveProtocol.toReduction_completeness_iff` identifies it with
the legacy reduction predicate.

`ArkLib/NonInteractiveArgument/NARG.lean` owns `NonInteractiveArgument`, its shared-oracle
execution, and completeness. Adaptive soundness, knowledge soundness, their experiments,
and statement-size restrictions live in `NonInteractiveArgument/Soundness.lean`.
`Legacy.lean` connects those security interfaces to legacy non-interactive reductions;
`ZeroKnowledge.lean` owns adaptive simulation games.

The ordinary public-coin `IP` state-restoration games and adapters live in
`InteractiveProof/StateRestorationSoundness.lean`, alongside the general games.
These ownership boundaries keep honest algorithms separate from adversarial experiments.
