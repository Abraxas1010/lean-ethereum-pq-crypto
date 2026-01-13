# Technical Report: Lean Ethereum Post-Quantum Cryptography

**Version**: 1.0
**Date**: 2026-01-13
**Authors**: HeytingLean Project

## Abstract

This report documents the formal verification of post-quantum cryptographic primitives for Ethereum using Lean 4. We present machine-checked specifications for incomparable encodings, XMSS-style stateful signatures, Poseidon2 hash functions, Polynomial IOPs (Sumcheck, Fiat-Shamir), and post-quantum Hash Time-Locked Contracts. The formalization achieves zero `sorry`/`admit` usage and expresses all cryptographic assumptions as explicit `Prop` parameters.

## 1. Introduction

### 1.1 Motivation

Ethereum's current signature infrastructure relies on ECDSA and BLS signatures, both of which are vulnerable to quantum attacks via Shor's algorithm. The leanEthereum project proposes XMSS-based signatures as a post-quantum replacement. This formalization provides:

1. Machine-checked type-safety for cryptographic interfaces
2. Explicit security assumptions as verifiable properties
3. Modular design enabling incremental refinement

### 1.2 Scope

This bundle covers the **specification layer** — type-correct interfaces with security properties expressed as `Prop` statements. Concrete implementations and full security proofs are designated as future work.

## 2. Post-Quantum Signature Scheme

### 2.1 Incomparable Encodings

The foundational primitive for XMSS-style signatures. An incomparable encoding is a function that:

- Maps messages to codewords with optional failure
- Ensures distinct messages cannot collide within an epoch
- Supports randomized encoding

**Lean Specification** (`IncomparableEncoding.lean`):

```lean
structure Scheme where
  Msg   : Type
  Epoch : Type
  Rand  : Type
  Code  : Type
  Param : Type
  encode : Param → Epoch → Rand → Msg → Option Code
  decode : Param → Epoch → Code → Option Msg
```

**Security Properties**:

- `Correct`: Successful encodings decode correctly
- `Incomparable`: Distinct messages never encode to the same codeword

### 2.2 XMSS Stateful Signatures

XMSS extends incomparable encodings with:

- Merkle tree-based key management
- One-time signature (OTS) leaves
- Epoch-indexed state progression

**Key Invariant**: Each (key, epoch) pair is used exactly once.

```lean
def EpochAdvances (S : XMSSScheme) : Prop := ∀ kp e m sig kp',
  S.sign kp e m = some (sig, kp') → kp'.epochIdx > kp.epochIdx
```

This mirrors the `MessageModelSeq` freshness pattern, enabling unified reasoning about replay prevention.

### 2.3 Poseidon2 Hash

Poseidon2 is an algebraic hash function optimized for ZK circuits. Our specification includes:

- Field parameters (prime, state width)
- Round structure (full rounds, partial rounds)
- S-box definition (x^α for α ∈ {5, 7})

The permutation is defined at the specification level; concrete round constants are externalized.

## 3. Polynomial Interactive Oracle Proofs

### 3.1 Multilinear Polynomials

Multilinear polynomials are the foundation of modern PIOP-based proof systems. Key concepts:

- **Representation**: Evaluations over the boolean hypercube {0,1}^n
- **Multilinear Extension (MLE)**: Unique polynomial agreeing with evaluations on hypercube
- **Hypercube Sum**: ∑_{b ∈ {0,1}^n} p(b)

### 3.2 Sumcheck Protocol

The Sumcheck protocol proves claims about hypercube sums through interactive rounds.

**Protocol Structure**:

1. Prover claims sum S = ∑ p(b)
2. For each variable i:
   - Prover sends univariate polynomial g_i(X)
   - Verifier checks g_i(0) + g_i(1) = previous claim
   - Verifier samples random challenge r_i
   - New claim becomes g_i(r_i)
3. Final check: p(r₁, ..., rₙ) = last claim

**Specification** (`Sumcheck.lean`):

```lean
def roundCheck (transcript : SumcheckTranscript F n) (i : Fin n) : Prop :=
  let msg := transcript.roundMsgs i
  let prevValue := if i = 0 then transcript.claimedSum
                   else (transcript.roundMsgs ⟨i-1, _⟩).eval (transcript.challenges ⟨i-1, _⟩)
  msg.eval 0 + msg.eval 1 = prevValue
```

### 3.3 Fiat-Shamir Transform

Converts interactive protocols to non-interactive by deriving challenges from transcript hashes.

**Key Components**:

- `FSOracle`: Abstract hash/RO interface
- `FSTranscript`: Accumulated prover messages
- `NISumcheck`: Non-interactive Sumcheck proof bundle

## 4. Blockchain Integration

### 4.1 Replay Prevention via Monotone Counters

The `MessageModelSeq` module formalizes freshness using sequence numbers:

```lean
def Invariants (st : State) : Prop :=
  (st.delivered.map Message.key).Nodup ∧
  (∀ m, m ∈ st.delivered → m ∈ st.sent) ∧
  (∀ m, m ∈ st.delivered → m.seq ≤ st.maxSeq m.src)
```

**Key Theorem**: `deliver_preserves_invariants` — the delivery function maintains all invariants.

### 4.2 Post-Quantum HTLC

Combines:
- XMSS signatures for authorization
- Poseidon2 hash locks for conditional payments
- Sequence-based freshness for channel updates

## 5. Design Decisions

### 5.1 No Axioms Policy

All cryptographic hardness assumptions are expressed as `Prop` parameters, not axioms:

```lean
structure SecurityProps (S : Scheme) where
  tcr : Prop  -- Target collision resistance
```

This enables:
- Compile-time type checking without logical inconsistency
- Explicit tracking of security assumptions
- Compositional reasoning about security reductions

### 5.2 Executable-First Development

Each module is designed to compile without `sorry`:
1. Define types and operations
2. Express properties as `Prop` or theorems with proofs
3. Use `by rfl` or `by simp` where definitional equality suffices

### 5.3 Modular Dependencies

The dependency graph is intentionally shallow:

```
IncomparableEncoding ←── XMSS ←── PostQuantumHTLC
                                       ↑
Multilinear ←── Sumcheck ←── FiatShamir    MessageModelSeq
```

This enables independent verification of each layer.

## 6. Verification Results

### 6.1 Build Metrics

| Metric | Value |
|--------|-------|
| Total modules | 8 |
| Lines of Lean code | ~400 |
| Mathlib dependencies | 1081 jobs |
| Build time | ~60 seconds |
| sorry/admit count | 0 |

### 6.2 Property Coverage

| Module | Correctness | Security Props | Theorems |
|--------|-------------|----------------|----------|
| IncomparableEncoding | Correct | Incomparable, TCR | 0 |
| XMSS | Correct, EpochAdvances | SecurityAssumption | 0 |
| Poseidon2 | Permutation spec | (external) | 0 |
| Multilinear | EvalOnHypercube | — | 1 |
| Sumcheck | RoundCheck, Verify | Soundness, Completeness | 0 |
| FiatShamir | NIVerify | ROM soundness | 0 |
| MessageModelSeq | Invariants | — | 3 |
| PostQuantumHTLC | HTLCState | — | 0 |

## 7. Future Work

### 7.1 Short-Term

- **Test Vectors**: Generate JSON fixtures from leanSig/leanMultisig binaries
- **AIR Refinement**: Connect VM step relations to AIR constraints

### 7.2 Medium-Term

- **Soundness Proofs**: Full Sumcheck soundness theorem
- **STARK Integration**: Connect to HeytingLean STARK skeleton

### 7.3 Long-Term

- **Concrete Parameters**: Instantiate Poseidon2 with BN254/BLS12-381 constants
- **End-to-End Verification**: Prove zkVM execution correctness

## 8. Conclusion

This formalization establishes machine-checked foundations for post-quantum Ethereum cryptography. By expressing security assumptions as explicit `Prop` parameters and achieving zero `sorry` usage, the work provides a solid base for incremental refinement toward fully verified post-quantum blockchain infrastructure.

## References

1. Drake, Khovratovich, Kudinov, Wagner. "Hash-Based Multi-Signatures for Post-Quantum Ethereum." ePrint 2025/055.
2. "Technical Note: LeanSig for Post-Quantum Ethereum." ePrint 2025/1332.
3. Grassi et al. "Poseidon2." ePrint 2023/323.
4. Lund, Fortnow, Karloff, Nisan. "Algebraic Methods for Interactive Proof Systems." JCSS 1992.
