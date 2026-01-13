# Module Map

This document maps the Lean modules to their mathematical concepts and upstream references.

## Post-Quantum Signatures

### `HeytingLean.Crypto.PostQuantum.IncomparableEncoding`

**Concept**: Incomparable encodings as defined in ePrint 2025/055, Section 3.

**Upstream Reference**: `leanEthereum/leanSig/src/inc_encoding.rs`

**Key Types**:
- `Scheme` — Abstract encoding interface
- `Correct` — Decode-after-encode correctness
- `Incomparable` — No cross-message collisions

---

### `HeytingLean.Crypto.PostQuantum.XMSS`

**Concept**: XMSS stateful signature scheme with Merkle tree authentication.

**Upstream Reference**: `leanEthereum/leanSig/src/signature.rs`

**Key Types**:
- `XMSSKeyPair` — Public key (Merkle root) + secret key (seed + epoch)
- `XMSSSignature` — OTS signature + auth path
- `XMSSScheme` — Full scheme interface
- `EpochAdvances` — Stateful signing constraint

---

### `HeytingLean.Crypto.PostQuantum.Poseidon2`

**Concept**: Poseidon2 algebraic hash function (ePrint 2023/323).

**Upstream Reference**: `leanEthereum/leanSig/src/symmetric/tweak_hash/poseidon.rs`

**Key Types**:
- `Poseidon2Params` — Field prime, state width, round counts
- `Poseidon2State` — State vector
- `sbox`, `fullRound`, `partialRound` — Round function components

---

## Polynomial IOPs

### `HeytingLean.Crypto.PIOP.Multilinear`

**Concept**: Multilinear polynomials over boolean hypercubes.

**Upstream Reference**: `leanEthereum/multilinear-toolkit/`

**Key Types**:
- `MultilinearPoly` — Evaluations on {0,1}^n
- `hypercubeSum` — Sum over all boolean assignments

---

### `HeytingLean.Crypto.PIOP.Sumcheck`

**Concept**: Sumcheck protocol (Lund et al., 1992).

**Upstream Reference**: `leanEthereum/multilinear-toolkit/sumcheck/`

**Key Types**:
- `SumcheckRoundMsg` — Univariate polynomial from prover
- `SumcheckTranscript` — Full protocol transcript
- `roundCheck` — Per-round verification equation
- `Soundness`, `Completeness` — Security properties

---

### `HeytingLean.Crypto.PIOP.FiatShamir`

**Concept**: Fiat-Shamir non-interactive transform.

**Upstream Reference**: `leanEthereum/fiat-shamir/`

**Key Types**:
- `FSOracle` — Abstract random oracle
- `FSTranscript` — Accumulated messages
- `NISumcheck` — Non-interactive Sumcheck bundle

---

## Blockchain Integration

### `HeytingLean.Blockchain.Bridge.MessageModelSeq`

**Concept**: Replay prevention via monotone sequence numbers.

**Upstream Pattern**: ENR freshness (EIP-778), Noise nonces.

**Key Types**:
- `Message` — Payload with source, destination, sequence number
- `State` — Sent/delivered sets + maxSeq per source
- `Invariants` — No replay, delivered ⊆ sent, seq bounds
- `deliver_preserves_invariants` — Main theorem

---

### `HeytingLean.Blockchain.PaymentChannels.PostQuantumHTLC`

**Concept**: Post-quantum Hash Time-Locked Contracts.

**Key Types**:
- `PQHashLock` — Poseidon2-based hash commitment + timeout
- `HTLCWitness` — Preimage witness
- `PQChannelPayment` — Payment with XMSS authorization

---

## Dependency Graph

```
IncomparableEncoding
        ↑
      XMSS ←────────────┐
        ↑               │
        │          Poseidon2
        │
PostQuantumHTLC
        ↑
MessageModelSeq

Multilinear
     ↑
  Sumcheck
     ↑
FiatShamir
```
