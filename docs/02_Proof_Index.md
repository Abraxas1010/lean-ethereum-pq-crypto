# Proof Index

This document catalogs all theorems and lemmas in the formalization.

## MessageModelSeq

### `not_mem_keys_of_lt_maxSeq`

**Statement**: A message with sequence number above `maxSeq` cannot have its key in the delivered set.

**Location**: `MessageModelSeq.lean:99`

**Proof Method**: Contradiction via the `maxSeq` upper bound invariant.

---

### `deliver_preserves_invariants`

**Statement**: The `deliver` function preserves all three invariants (no replay, delivered ⊆ sent, seq bounds).

**Location**: `MessageModelSeq.lean:118`

**Proof Method**: Case split on `m ∈ st.sent` and `st.maxSeq m.src < m.seq`, then verify each invariant component.

---

### `runDeliveries_preserves_invariants`

**Statement**: Iterated delivery preserves invariants.

**Location**: `MessageModelSeq.lean:173`

**Proof Method**: Induction on the message list.

---

### `replayPreventionStatement_holds`

**Statement**: Delivered message keys remain duplicate-free across any run.

**Location**: `MessageModelSeq.lean:195`

**Proof Method**: Direct corollary of `runDeliveries_preserves_invariants`.

---

## Multilinear

### `eval_on_hypercube`

**Statement**: The multilinear extension agrees with the original evaluations on boolean points.

**Location**: `Multilinear.lean` (stated, proof pending)

**Proof Method**: Lagrange interpolation uniqueness.

---

## Named Properties (Prop Statements)

The following are expressed as `Prop` types for future proof development:

| Property | Module | Description |
|----------|--------|-------------|
| `Scheme.Correct` | IncomparableEncoding | Decode recovers encoded message |
| `Scheme.Incomparable` | IncomparableEncoding | No cross-message collisions |
| `XMSSScheme.Correct` | XMSS | Valid signatures verify |
| `XMSSScheme.EpochAdvances` | XMSS | Signing increments epoch |
| `Soundness` | Sumcheck | Cheating prover caught w.h.p. |
| `Completeness` | Sumcheck | Honest prover convinces verifier |
| `Invariants` | MessageModelSeq | Three-part state invariant |
| `ReplayPreventionStatement` | MessageModelSeq | No duplicate delivered keys |

---

## Axiom Audit

**Standard Axioms Only**:

- `propext` (propositional extensionality)
- `Classical.choice` (choice principle)
- `Quot.sound` (quotient soundness)

**No Custom Axioms**: All cryptographic assumptions are `Prop` parameters, not axioms.
