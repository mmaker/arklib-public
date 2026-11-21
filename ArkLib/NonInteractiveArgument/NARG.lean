/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
module

public import ArkLib.Security.Game

/-!
# Non-interactive arguments

The honest prover generates an argument string from a statement and witness. The verifier
consumes the statement and argument string directly. Both algorithms share an oracle environment.

## References

* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

open OracleComp OracleSpec
open scoped NNReal ProbabilityTheory

/-! ## Honest execution and completeness -/

section HonestArgument

/-- A non-interactive argument consists of NARG string generation and a decision algorithm.
No reduced statement or witness is computed or returned. -/
structure NonInteractiveArgument {ι : Type} (oSpec : OracleSpec ι)
    (Statement Witness NARGString : Type) where
  prover : Statement → Witness → OracleComp oSpec NARGString
  verifier : Statement → NARGString → OracleComp oSpec Bool

variable {ι : Type} {oSpec : OracleSpec ι} {Statement Witness NARGString : Type}

/-- Generate a NARG string and verify it in the same oracle world. -/
def NonInteractiveArgument.run
    (argument : NonInteractiveArgument oSpec Statement Witness NARGString)
    (stmt : Statement) (wit : Witness) : OracleComp oSpec Bool := do
  argument.verifier stmt (← argument.prover stmt wit)

/-- Completeness requires acceptance for every valid input, with the stated error bound. -/
def NonInteractiveArgument.completeness {σ : Type}
    (argument : NonInteractiveArgument oSpec Statement Witness NARGString)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relation : Set (Statement × Witness)) (error : ℝ≥0) : Prop :=
  ∀ stmt wit, (stmt, wit) ∈ relation →
    Pr{let accepted ← (simulateQ impl (argument.run stmt wit)).run' (← init)}[
      accepted = true] ≥ 1 - error

end HonestArgument
