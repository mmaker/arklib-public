/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Completeness.Application
public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Completeness.FixedOracle
public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Completeness.RandomOracle

/-!
# Completeness of canonical Fiat–Shamir

A fixed verifier-message function preserves perfect completeness under a stateless ambient
handler. Shared lazy uniform random functions preserve arbitrary completeness error. Both
results allow an ambient salt sampler, including the specialization to zero-length salts.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

section FixedOracle

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type}

variable [VCVCompatible Salt]
variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- **Perfect completeness of canonical Fiat–Shamir (CO25, Construction 3.17).**
A perfectly complete interactive reduction remains perfectly complete under a stateless ambient
handler and one fixed, consistently answered verifier-message function sampled at initialization.
The function distribution and the salt sampler need not be uniform. This is a probability-one
result; arbitrary completeness error is preserved under the random-oracle assumptions of
`canonicalFiatShamir_completeness_randomOracle`. -/
theorem canonicalFiatShamir_perfectCompleteness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
    (fsInit : ProbComp (QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (h : R.perfectCompleteness init (impl.liftTarget (StateT σ ProbComp)) relIn relOut) :
    (R.compileFiatShamir sampleSalt).perfectCompleteness fsInit
      ((impl.liftTarget (StateT (QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
        ProbComp)).addLift fsChallengeQueryImpl') relIn relOut :=
  CanonicalFS.perfectCompleteness init impl fsInit R sampleSalt relIn relOut h

/-- Perfect completeness of canonical Fiat-Shamir for every configured salt length.
The private ambient sampler is invoked once per NARG string. -/
theorem fiatShamirSalted_perfectCompleteness {σ U : Type} [VCVCompatible U] (saltLength : ℕ)
    (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
    (fsInit : ProbComp
      (QueryImpl (fsVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (h : R.perfectCompleteness init (impl.liftTarget (StateT σ ProbComp)) relIn relOut) :
    (R.fiatShamirSalted saltLength sampleSalt).perfectCompleteness fsInit
      ((impl.liftTarget (StateT
        (QueryImpl (fsVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id)
        ProbComp)).addLift fsChallengeQueryImpl') relIn relOut := by
  exact canonicalFiatShamir_perfectCompleteness init impl fsInit R sampleSalt relIn relOut h

end FixedOracle

/-- Basic Fiat–Shamir preserves every completeness error under shared uniform random functions.
The salt sampler uses only the stateless ambient oracles and is called once per NARG string. -/
theorem canonicalFiatShamir_completeness_randomOracle
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut Salt : Type} [VCVCompatible Salt]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain]
    (impl : QueryImpl oSpec ProbComp)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) (ε : ℝ≥0)
    (h : R.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relIn relOut ε) :
    (R.compileFiatShamir sampleSalt).completeness
      (pure ((), (∅ : (srVerifierMessageOracle (StmtIn × Salt) pSpec).QueryCache)))
      (CanonicalFS.randomOracleImpl (pSpec := pSpec) (StmtIn := StmtIn) (Salt := Salt) impl)
      relIn relOut ε :=
  CanonicalFS.completeness_randomOracle impl R sampleSalt relIn relOut ε h

/-- Canonical basic Fiat–Shamir preserves arbitrary completeness error at every salt length. -/
theorem fiatShamirSalted_completeness
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut U : Type} [VCVCompatible U] (saltLength : ℕ)
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec).Domain]
    (impl : QueryImpl oSpec ProbComp)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) (ε : ℝ≥0)
    (h : R.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relIn relOut ε) :
    (R.fiatShamirSalted saltLength sampleSalt).completeness
      (pure ((), (∅ : (srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec).QueryCache)))
      (CanonicalFS.randomOracleImpl (pSpec := pSpec) (StmtIn := StmtIn)
        (Salt := Vector U saltLength) impl) relIn relOut ε :=
  canonicalFiatShamir_completeness_randomOracle impl R sampleSalt relIn relOut ε h

section Application

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {Statement Witness Salt U : Type}

/-- The typed basic Fiat–Shamir argument preserves arbitrary interactive completeness error. -/
theorem InteractiveProtocol.compileFiatShamir_completeness [VCVCompatible Salt]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srVerifierMessageOracle (Statement × Salt) pSpec).Domain]
    (P : InteractiveProtocol oSpec Statement Witness pSpec)
    (impl : QueryImpl oSpec ProbComp) (sampleSalt : OracleComp oSpec Salt)
    (relation : Set (Statement × Witness)) (ε : ℝ≥0)
    (h : P.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relation ε) :
    (P.compileFiatShamir sampleSalt).completeness
      (pure ((), (∅ : (srVerifierMessageOracle (Statement × Salt) pSpec).QueryCache)))
      (CanonicalFS.randomOracleImpl (pSpec := pSpec) (StmtIn := Statement) (Salt := Salt) impl)
      relation ε :=
  CanonicalFS.compileFiatShamir_application_completeness P impl sampleSalt relation ε h

/-- Canonical byte serialization adds no completeness error to basic Fiat–Shamir. -/
theorem InteractiveProtocol.fiatShamir_completeness [VCVCompatible U] (saltLength : ℕ)
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srVerifierMessageOracle (Statement × Vector U saltLength) pSpec).Domain]
    (P : InteractiveProtocol oSpec Statement Witness pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (impl : QueryImpl oSpec ProbComp) (sampleSalt : OracleComp oSpec (Vector U saltLength))
    (relation : Set (Statement × Witness)) (ε : ℝ≥0)
    (h : P.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relation ε) :
    (P.fiatShamir saltLength serializer sampleSalt).completeness
      (pure ((),
        (∅ : (srVerifierMessageOracle (Statement × Vector U saltLength) pSpec).QueryCache)))
      (CanonicalFS.randomOracleImpl (pSpec := pSpec) (StmtIn := Statement)
        (Salt := Vector U saltLength) impl) relation ε :=
  CanonicalFS.fiatShamir_byte_completeness saltLength P serializer impl sampleSalt relation ε h

end Application
