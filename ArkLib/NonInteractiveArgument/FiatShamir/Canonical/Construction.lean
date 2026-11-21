/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Michele Orrù, Quang Dao, Yuxi Zheng
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Basic
public import ArkLib.InteractiveProof.IP
public import ArkLib.NonInteractiveArgument.Serialization
public import ToMathlib.Control.OptionT

/-!
# Canonical Fiat–Shamir construction

The single-salt compiler samples its salt once using the ambient oracle, includes it in the
NARG string, and keys all verifier-message queries by the statement and salt. The application
statement, witness, and interactive messages keep their original types. The legacy and
application compilers share payload generation and transcript reconstruction.

The public `fiatShamirSalted` constructors use `Vector U saltLength`. Length zero is the same
construction with an empty salt. The abstract-salt compiler supports the encodings used in the
security reductions. Salted and unsalted provers share the round runner in
`FiatShamir/Basic.lean`.

## References

* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

open ProtocolSpec OracleComp OracleSpec OracleReduction

section Legacy

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

/--
Canonical Fiat-Shamir NARG string: pair of a public salt and the prover's messages.
-/
abbrev FSSaltedNARGString (pSpec : ProtocolSpec n) (Salt : Type) :=
  Salt × pSpec.Messages

/-- Carry the salt in the public oracle context and pass only the statement to the prover. -/
@[inline]
def CanonicalFS.contextProver {Salt : Type}
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Prover oSpec (StmtIn × Salt) WitIn StmtOut WitOut pSpec where
  toProverRound := P.toProverRound
  input := fun ctx => P.input (ctx.1.1, ctx.2)
  output := P.output

/--
Prover's per-round step for the canonical Fiat-Shamir transformation.

This is the salted analog of `Prover.processRoundFS`: each Fiat-Shamir query is keyed by the
context `(stmtIn, salt)` instead of just `stmtIn`. The inner prover state is threaded through
unchanged.
-/
@[inline, specialize]
def Prover.processRoundFSSalted {Salt : Type} [VCVCompatible Salt] (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)
      (pSpec.MessagesUpTo j.castSucc ×
        (StmtIn × Salt) × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)
        (pSpec.MessagesUpTo j.succ ×
          (StmtIn × Salt) × prover.PrvState j.succ) :=
  (CanonicalFS.contextProver (Salt := Salt) prover).processRoundFS j currentResult

/--
Run the prover up to round `i` under the canonical Fiat-Shamir transformation, given an
explicit salt `τ`.
-/
@[inline, specialize]
def Prover.runToRoundFSSalted {Salt : Type} [VCVCompatible Salt]
    (salt : Salt) (i : Fin (n + 1))
    (stmt : StmtIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (state : prover.PrvState 0) :
        OracleComp (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)
          (pSpec.MessagesUpTo i × (StmtIn × Salt) × prover.PrvState i) :=
  (CanonicalFS.contextProver prover).runToRoundFS i (stmt, salt) state

/-- Sample the salt and run the rounds once, returning the argument and final prover state. -/
@[inline, reducible]
def CanonicalFS.compilePayload {Salt : Type} [VCVCompatible Salt]
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : StmtIn) (state : P.PrvState 0) :
    OracleComp (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)
      (FSSaltedNARGString pSpec Salt × P.PrvState (Fin.last n)) := do
  let salt ← sampleSalt
  let ⟨messages, _, state⟩ ← P.runToRoundFSSalted salt (Fin.last n) stmt state
  return ⟨(salt, messages), state⟩

/-- Reconstruct the transcript using the salt carried in the argument. -/
abbrev CanonicalFS.deriveTranscript {Salt : Type}
    (stmt : StmtIn) (nargString : FSSaltedNARGString pSpec Salt) :
    OracleComp (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) pSpec.FullTranscript :=
  nargString.2.deriveTranscriptFS (oSpec := oSpec) (stmt, nargString.1)

/--
Canonical Fiat-Shamir transformation for the prover ([CO25, Construction 3.17] prover surface).

The prover samples a salt `τ ← sampleSalt` using only the ambient oracle `oSpec`, then runs the
underlying interactive prover with all FS queries keyed by the context `(stmtIn, τ)`,
and packages the salt together with the produced messages as the NARG string. The sampler
cannot inspect the statement, witness-bearing prover state, or Fiat–Shamir table.

Adapted from **[snarg-book, Construction 14.1.1]**, which salts every round; here a single salt
is sampled once and keys all rounds.
-/
def Prover.compileFiatShamir {Salt : Type} [VCVCompatible Salt]
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) :
    NonInteractiveProver (Message := FSSaltedNARGString pSpec Salt)
      (oSpec := oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)
      StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => match i with
    | 0 => StmtIn × P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := fun ctx => ⟨ctx.1, P.input ctx⟩
  sendMessage | ⟨0, _⟩ => fun ⟨stmtIn, state⟩ =>
    CanonicalFS.compilePayload P sampleSalt stmtIn state
  -- This function is never invoked so we apply the elimination principle
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => (P.output st).liftComp _

/--
Canonical Fiat-Shamir transformation for the verifier ([CO25, Construction 3.17] verifier
surface).

The verifier reads the salt `τ` and messages from the NARG string, then derives the transcript by
querying the FS oracle keyed at the context `(stmtIn, τ)`.
Adapted from **[snarg-book, Construction 14.1.1]** (single salt instead of per-round salts).
-/
def Verifier.compileFiatShamir {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (FSSaltedNARGString pSpec Salt)
      (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) StmtIn StmtOut where
  verify := fun stmtIn nargString => do
    let transcript ← CanonicalFS.deriveTranscript (oSpec := oSpec) stmtIn (nargString 0)
    Option.getM (← (V.verify stmtIn transcript).run)

/--
Canonical Fiat-Shamir transformation for an (interactive) reduction ([CO25, Construction 3.17]),
combining the salted prover and verifier surfaces.
Adapted from **[snarg-book, Construction 14.1.1]** (single salt instead of per-round salts).
-/
def Reduction.compileFiatShamir {Salt : Type} [VCVCompatible Salt]
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) :
    NonInteractiveReduction (FSSaltedNARGString pSpec Salt)
      (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.compileFiatShamir sampleSalt
  verifier := R.verifier.compileFiatShamir

/-- The single-salt FS verifier run as a NARG `verify` (CO25 `V_std^f(x,·)`): build the
single-message transcript from the FS NARG string and run `Verifier.compileFiatShamir V`. Used by
the DSFS Section 5 `Hyb₄`/basic-FS game so both games refer to the same verifier. -/
def fsSaltedVerify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    StmtIn → FSSaltedNARGString pSpec Salt →
      OptionT (OracleComp (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)) StmtOut :=
  fun stmtIn nargString =>
    (Verifier.compileFiatShamir (Salt := Salt) V).verify stmtIn
      (Fin.cons nargString (fun i => i.elim0))

/-- Canonical Fiat-Shamir NARG metadata: one fixed-length salt and the unchanged message family.
The salt is not part of the application statement, witness, relation, or interactive messages. -/
abbrev FiatShamirNARGString (pSpec : ProtocolSpec n) (U : Type) (saltLength : Nat) :=
  FSSaltedNARGString pSpec (Vector U saltLength)

/-- Canonical FS keys use separate salt context. The paired context here is a random-oracle key,
not an augmented application statement or relation. -/
abbrev ProtocolSpec.canonicalFSOracle (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (U : Type) (saltLength : Nat) :=
  fsVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec

/-- Canonical Fiat-Shamir prover. Sample one salt of the configured length using only the ambient
oracle, then reuse it in every verifier-message query. Fresh uniform private salt randomness is
required by the ZK experiment. Length zero uses the same construction with an empty salt. -/
def Prover.fiatShamirSalted {U : Type} [VCVCompatible U] (saltLength : Nat)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    NonInteractiveProver (FiatShamirNARGString pSpec U saltLength)
      (oSpec + canonicalFSOracle StmtIn pSpec U saltLength) StmtIn WitIn StmtOut WitOut :=
  P.compileFiatShamir sampleSalt

/-- Canonical Fiat-Shamir verifier, taking salt metadata separately from the original messages. -/
def Verifier.fiatShamirSalted {U : Type} [VCVCompatible U] (saltLength : Nat)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (Message := FiatShamirNARGString pSpec U saltLength)
      (oSpec + canonicalFSOracle StmtIn pSpec U saltLength) StmtIn StmtOut :=
  V.compileFiatShamir

/-- Canonical Fiat-Shamir transformation with one salt of fixed length per NARG string.
The abstract-salt compiler serves as an encoding adapter for the security reductions. -/
def Reduction.fiatShamirSalted {U : Type} [VCVCompatible U] (saltLength : Nat)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    NonInteractiveReduction (Message := FiatShamirNARGString pSpec U saltLength)
      (oSpec + canonicalFSOracle StmtIn pSpec U saltLength) StmtIn WitIn StmtOut WitOut :=
  R.compileFiatShamir sampleSalt

namespace CanonicalFS

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- `Verifier.compileFiatShamir`'s `verify` on the length-1 transcript `Fin.cons π 0` is, by
definition, the bare FS-NARG `verify` map `fsSaltedVerify V x π`.  Bridges the NIV-shaped
`adaptiveNARG*Exp init impl (Verifier.compileFiatShamir V)` experiments back to the
`fsSaltedVerify`-shaped §6.1/§6.2 game-match proofs (`simp only [fsSaltedNIV_verify]` after
unfolding the experiment restores the `fsSaltedVerify`-form goal). -/
theorem fsSaltedNIV_verify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (x : StmtIn) (π : FSSaltedNARGString pSpec Salt) :
    (Verifier.compileFiatShamir (Salt := Salt) V).verify x (Fin.cons π (fun i => i.elim0))
      = fsSaltedVerify V x π :=
  rfl

end CanonicalFS

end Legacy

/-! ## Canonical Fiat–Shamir for interactive protocols -/

section InteractiveProtocols

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {Statement Witness Salt U : Type}
  [VCVCompatible Statement] [∀ i, VCVCompatible (pSpec.Challenge i)]

/-- Generate a canonical NARG string with one ambient-only salt sample.
No terminal reduction output is executed. -/
def InteractiveProver.compileFiatShamir [VCVCompatible Salt]
    (P : InteractiveProver oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : Statement) (wit : Witness) :
    OracleComp (oSpec + fsVerifierMessageOracle (Statement × Salt) pSpec)
      (FSSaltedNARGString pSpec Salt) :=
  Prod.fst <$> CanonicalFS.compilePayload P.toReductionProver sampleSalt stmt
    (P.input (stmt, wit))

/-- Derive the interactive transcript and return its acceptance decision. -/
def InteractiveVerifier.compileFiatShamir [VCVCompatible Salt]
    (V : InteractiveVerifier oSpec Statement pSpec)
    (stmt : Statement) (nargString : FSSaltedNARGString pSpec Salt) :
    OracleComp (oSpec + fsVerifierMessageOracle (Statement × Salt) pSpec) Bool := do
  let transcript ← CanonicalFS.deriveTranscript (oSpec := oSpec) stmt nargString
  (V.verify stmt transcript).liftComp _

/-- Canonical FS with an abstract salt type, used for encoding correspondence. -/
def InteractiveProtocol.compileFiatShamir [VCVCompatible Salt]
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec Salt) :
    NonInteractiveArgument (oSpec + fsVerifierMessageOracle (Statement × Salt) pSpec)
      Statement Witness (FSSaltedNARGString pSpec Salt) where
  prover := protocol.prover.compileFiatShamir sampleSalt
  verifier := protocol.verifier.compileFiatShamir

/-- Canonical FS generates one NARG string using a salt of the configured length. -/
def InteractiveProver.fiatShamirTyped [VCVCompatible U] (saltLength : Nat)
    (P : InteractiveProver oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    Statement → Witness →
      OracleComp (oSpec + canonicalFSOracle Statement pSpec U saltLength)
        (FiatShamirNARGString pSpec U saltLength) :=
  P.compileFiatShamir sampleSalt

/-- Canonical FS verification returns a decision bit. -/
def InteractiveVerifier.fiatShamirTyped [VCVCompatible U] (saltLength : Nat)
    (V : InteractiveVerifier oSpec Statement pSpec) :
    Statement → FiatShamirNARGString pSpec U saltLength →
      OracleComp (oSpec + canonicalFSOracle Statement pSpec U saltLength) Bool :=
  V.compileFiatShamir

/-- Compile a public-coin protocol to a NARG-string generator and decision algorithm. -/
def InteractiveProtocol.fiatShamirTyped [VCVCompatible U] (saltLength : Nat)
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    NonInteractiveArgument (oSpec + canonicalFSOracle Statement pSpec U saltLength)
      Statement Witness (FiatShamirNARGString pSpec U saltLength) :=
  protocol.compileFiatShamir sampleSalt

/-- Generate the canonical byte encoding of the salt and prover messages. -/
def InteractiveProver.fiatShamir [VCVCompatible U] (saltLength : Nat)
    (P : InteractiveProver oSpec Statement Witness pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (sampleSalt : OracleComp oSpec (Vector U saltLength))
    (stmt : Statement) (wit : Witness) :
    OracleComp (oSpec + canonicalFSOracle Statement pSpec U saltLength) ByteArray :=
  serializer.serialize <$> P.fiatShamirTyped saltLength sampleSalt stmt wit

/-- Parse the entire NARG string before reconstructing and checking the transcript. -/
def InteractiveVerifier.fiatShamir [VCVCompatible U] (saltLength : Nat)
    (V : InteractiveVerifier oSpec Statement pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (stmt : Statement) (bytes : ByteArray) :
    OracleComp (oSpec + canonicalFSOracle Statement pSpec U saltLength) Bool :=
  match serializer.deserialize bytes with
  | none => pure false
  | some nargString => V.fiatShamirTyped saltLength stmt nargString

/-- Compile a public-coin protocol to a byte-valued NARG and decision algorithm. -/
def InteractiveProtocol.fiatShamir [VCVCompatible U] (saltLength : Nat)
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    NonInteractiveArgument (oSpec + canonicalFSOracle Statement pSpec U saltLength)
      Statement Witness ByteArray :=
  (protocol.fiatShamirTyped saltLength sampleSalt).serialize serializer

omit [VCVCompatible Statement] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The byte-valued compiler exposes the serialized prover algorithm. -/
@[simp] theorem InteractiveProtocol.fiatShamir_prover [VCVCompatible U] (saltLength : Nat)
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    (protocol.fiatShamir saltLength serializer sampleSalt).prover =
      protocol.prover.fiatShamir saltLength serializer sampleSalt := rfl

omit [VCVCompatible Statement] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The byte-valued compiler exposes parsing followed by typed verification. -/
@[simp] theorem InteractiveProtocol.fiatShamir_verifier [VCVCompatible U] (saltLength : Nat)
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    (protocol.fiatShamir saltLength serializer sampleSalt).verifier =
      protocol.verifier.fiatShamir saltLength serializer := by
  funext stmt bytes
  cases h : serializer.deserialize bytes <;>
    simp [InteractiveProtocol.fiatShamir, NonInteractiveArgument.serialize,
      InteractiveVerifier.fiatShamir, h, InteractiveProtocol.fiatShamirTyped,
      InteractiveProtocol.compileFiatShamir, InteractiveVerifier.fiatShamirTyped]

omit [VCVCompatible Statement] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The new generator is exactly the NARG string sent by the compatibility compiler,
including every oracle effect and excluding its terminal output. -/
theorem InteractiveProver.compileFiatShamir_eq_sendMessage [VCVCompatible Salt]
    (P : InteractiveProver oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : Statement) (wit : Witness) :
    P.compileFiatShamir sampleSalt stmt wit =
      Prod.fst <$> (P.toReductionProver.compileFiatShamir sampleSalt).sendMessage ⟨0, rfl⟩
        ((P.toReductionProver.compileFiatShamir sampleSalt).input (stmt, wit)) := rfl

omit [VCVCompatible Statement] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Verification has the same oracle computation as the established security interface.
A rejected NARG string returns `some false`; it is not confused with abort. -/
theorem InteractiveVerifier.compileFiatShamir_eq_verify [VCVCompatible Salt]
    (V : InteractiveVerifier oSpec Statement pSpec)
    (stmt : Statement) (nargString : FSSaltedNARGString pSpec Salt) :
    ((V.toReductionVerifier.compileFiatShamir).verify stmt
      (Fin.cons nargString (fun i => i.elim0))).run =
      some <$> V.compileFiatShamir stmt nargString := by
  simp only [ChallengeIdx, Challenge, Nat.reduceAdd, Fin.vcons_fin_zero,
    Verifier.compileFiatShamir, Fin.isValue, InteractiveVerifier.toReductionVerifier,
    OptionT.lift, bind_pure_comp, OptionT.run_mk, liftM_map, bind_map_left,
    Option.getM_some, bind_pure, Fin.cons_zero, OptionT.run_bind, OptionT.run_monadLift,
    monadLift_self, Option.elimM_map, Option.elim_some,
    InteractiveVerifier.compileFiatShamir, liftComp_eq_liftM, map_bind]
  congr 1
  funext transcript
  rw [← OracleComp.monadLift_liftM_OptionT]
  simp only [OptionT.run_monadLift, monadLift_self]

end InteractiveProtocols
