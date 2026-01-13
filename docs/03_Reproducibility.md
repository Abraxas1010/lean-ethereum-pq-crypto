# Reproducibility Guide

This document provides instructions for independently verifying the formalization.

## Environment Setup

### 1. Install elan (Lean Version Manager)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile  # or restart terminal
```

### 2. Verify Installation

```bash
elan --version
# Expected: elan 3.x.x

lean --version
# Expected: Lean (version 4.x.x, ...)
```

## Verification Steps

### Quick Verification

```bash
cd RESEARCHER_BUNDLE
./scripts/verify_build.sh
```

This script:
1. Checks for `sorry`/`admit` in source files
2. Updates Lake dependencies
3. Builds with `-DwarningAsError=true`

### Manual Verification

```bash
cd RESEARCHER_BUNDLE

# Update dependencies (downloads Mathlib cache)
lake update

# Build with warnings as errors
lake build -- -DwarningAsError=true

# Check for sorry/admit (should return nothing)
grep -rn --include='*.lean' -E '\bsorry\b|\badmit\b' HeytingLean/
```

### Expected Output

```
=== Lean Ethereum Post-Quantum Crypto Verification ===

Lean version: Lean (version 4.24.0, ...)
Lake version: Lake version 4.x.x (...)

Checking for sorry/admit...
No sorry/admit found.

Updating lake dependencies...
Using cache (Azure) from origin: leanprover-community/mathlib4
...
Completed successfully!

Building with warnings as errors...
Build completed successfully (XXXX jobs).

=== VERIFICATION PASSED ===
All modules compile without sorry/admit.
```

## Dependency Versions

| Component | Version | Source |
|-----------|---------|--------|
| Lean | 4.24.0 | `lean-toolchain` |
| Mathlib | v4.24.0 | `lakefile.lean` |
| Lake | (bundled) | — |

## Troubleshooting

### "lake: command not found"

Ensure elan is in your PATH:
```bash
export PATH="$HOME/.elan/bin:$PATH"
```

### Slow build

First build downloads ~300MB of Mathlib cache. Subsequent builds are faster.

### Memory issues

Mathlib compilation can require 8GB+ RAM. Close other applications or use:
```bash
lake build -j1  # Single-threaded build
```

## Verification Checklist

- [ ] `lean --version` shows 4.24.0
- [ ] `lake update` completes without error
- [ ] `lake build -- -DwarningAsError=true` succeeds
- [ ] `grep sorry` finds no matches
- [ ] `grep admit` finds no matches
