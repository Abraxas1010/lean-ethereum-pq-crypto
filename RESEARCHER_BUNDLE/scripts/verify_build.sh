#!/usr/bin/env bash
# verify_build.sh — Verify the Lean Ethereum PQ Crypto bundle builds correctly
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BUNDLE_DIR="$(dirname "$SCRIPT_DIR")"

cd "$BUNDLE_DIR"

echo "=== Lean Ethereum Post-Quantum Crypto Verification ==="
echo ""

# Check prerequisites
if ! command -v lake &> /dev/null; then
    echo "ERROR: 'lake' not found. Please install Lean 4 / elan first."
    exit 1
fi

if ! command -v lean &> /dev/null; then
    echo "ERROR: 'lean' not found. Please install Lean 4 / elan first."
    exit 1
fi

echo "Lean version: $(lean --version)"
echo "Lake version: $(lake --version)"
echo ""

# Check for sorry/admit
echo "Checking for sorry/admit..."
if grep -rn --include='*.lean' -E '\bsorry\b|\badmit\b' HeytingLean/; then
    echo "ERROR: Found sorry/admit in codebase"
    exit 1
fi
echo "No sorry/admit found."
echo ""

# Update dependencies
echo "Updating lake dependencies..."
lake update

# Build with warnings as errors
echo ""
echo "Building with warnings as errors..."
lake build -- -DwarningAsError=true

echo ""
echo "=== VERIFICATION PASSED ==="
echo "All modules compile without sorry/admit."
