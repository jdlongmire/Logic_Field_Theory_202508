# Logic Field Theory (LFT)

**Deriving Quantum Field Theory from the Three Fundamental Laws of Logic**

[![Lean 4](https://img.shields.io/badge/Lean-4.21.0-blue)](https://github.com/leanprover/lean4)
[![License: MIT](https://img.shields.io/badge/Code-MIT-green.svg)](LICENSE)
[![License: CC BY-NC-SA 4.0](https://img.shields.io/badge/Theory-CC%20BY--NC--SA%204.0-lightgrey.svg)](LICENSE)

## Overview

This repository contains the complete formal derivation proving that quantum field theory and the Standard Model emerge necessarily from the Three Fundamental Laws of Logic (Identity, Non-Contradiction, Excluded Middle). All core proofs are formally verified in Lean 4.

## Key Results

We prove that quantum mechanics is not a choice among many possible theories, but the unique mathematical structure consistent with logical coherence:

- **Complex numbers are necessary** (not real or quaternionic)
- **U(1)×SU(2)×SU(3) gauge structure is unique** (Standard Model)
- **Exactly 3 fermion generations** (not 2 or 4)
- **Born rule P = |ψ|² is derived** (not postulated)
- **Measurement problem solved** via scale invariance

## Implementation Status

| Module | File | Status | Key Result |
|--------|------|--------|------------|
| **D01** | [Core/D01_Admissibility.lean](LFT/Core/D01_Admissibility.lean) | ✅ Complete | 𝒜 = ℒ(𝒮), O(V³) complexity |
| **D02** | [Core/D02_ComplexNecessity.lean](LFT/Core/D02_ComplexNecessity.lean) | ✅ Complete | ℂ required for QM |
| **D03** | [Core/D03_UnitaryEvolution.lean](LFT/Core/D03_UnitaryEvolution.lean) | ✅ Complete | U(1)×SU(2)×SU(3), 3 generations |
| **D04** | [Core/D04_BornRule.lean](LFT/Core/D04_BornRule.lean) | ✅ Complete | P = \|ψ\|² uniquely |
| **D05** | [Core/D05_StrainWeights.lean](LFT/Core/D05_StrainWeights.lean) | ✅ Complete | Scale invariance weights |
| **D06** | [docs/predictions/D06_predictions.md](docs/predictions/D06_predictions.md) | ✅ Complete | Experimental tests |

## The Derivation Chain

```
Three Fundamental Laws of Logic
            ↓
    Admissible Graphs [D01]
            ↓
    Complex Structure [D02]
            ↓
    Gauge Groups & Generations [D03]
            ↓
    Born Probability Rule [D04]
            ↓
    Measurement Dynamics [D05]
            ↓
    Testable Predictions [D06]
```

## Repository Structure

```
LFT_GEN_19_LEAN/
├── LFT/
│   ├── Core/                          # Lean 4 implementations
│   │   ├── D01_Admissibility.lean     # Graph admissibility algorithm
│   │   ├── D02_ComplexNecessity.lean  # Complex numbers proof
│   │   ├── D03_UnitaryEvolution.lean  # Standard Model derivation
│   │   ├── D04_BornRule.lean          # Born rule uniqueness
│   │   └── D05_StrainWeights.lean     # Scale invariance
│   └── 00-lean-build-plan.md          # Build roadmap
├── docs/
│   ├── derivations-v5/                # Mathematical proofs
│   │   ├── D00-derivations-mapping.md
│   │   ├── D01-foundations.md
│   │   ├── D02-complex-necessity.md
│   │   ├── D03-unitary-evolution.md
│   │   ├── D04-born-rule-proof.md
│   │   ├── D05-strain-weights.md
│   │   └── D06-predictions.md
│   ├── predictions/                    # Experimental protocols
│   │   └── D06_predictions.md
│   ├── position-papers/               # Historical papers
│   ├── sessions/                      # Development notes
│   │   └── LFT_GEN_19_Session_1.md
│   └── theory-v5/                     # Theory exposition
│       ├── 00-glossary.md
│       ├── 01-introduction.md
│       ├── 02-pre-quantum-foundations.md
│       ├── 03-logical-strain.md
│       ├── 04-graphs-to-vector-spaces.md
│       ├── 05-quantum-structure.md
│       ├── 06-dynamics-and-measurement.md
│       ├── 07-symmetries-and-gauge-fields.md
│       └── 08-conclusion.md
├── lean-map/                          # Lean implementation mapping
├── .lake/                             # Build artifacts
├── lakefile.toml                      # Lake configuration
├── lean-toolchain                     # Lean version specification
└── README.md                          # This file
```

## Quick Start

### Prerequisites
- [Lean 4](https://leanprover.github.io/) (v4.21.0)
- [VS Code](https://code.visualstudio.com/) with Lean 4 extension

### Building

```bash
# Clone repository
git clone https://github.com/[username]/LFT_GEN_19_LEAN.git
cd LFT_GEN_19_LEAN

# Build all modules
lake build

# Test individual modules
lean LFT/Core/D01_Admissibility.lean
lean LFT/Core/D02_ComplexNecessity.lean
lean LFT/Core/D03_UnitaryEvolution.lean
lean LFT/Core/D04_BornRule.lean
lean LFT/Core/D05_StrainWeights.lean
```

## Critical Experimental Test

**Decoherence Scaling**: The theory predicts τ_D ∝ (ξ/ℓ₀)² (positive slope) while standard QM predicts τ_D ∝ 1/size (negative slope). This opposite behavior provides a decisive experimental test.

See [D06 Predictions](docs/predictions/D06_predictions.md) for detailed experimental protocols.

## Documentation

- **[Theory Overview](docs/theory-v5/)** - Complete conceptual framework
- **[Mathematical Derivations](docs/derivations-v5/)** - Rigorous proofs
- **[Experimental Predictions](docs/predictions/D06_predictions.md)** - Testable outcomes
- **[Build Plan](LFT/00-lean-build-plan.md)** - Implementation roadmap

## Author

**James D. Longmire**  
Northrop Grumman Fellow (independent research)  
Email: longmire.jd@gmail.com  
ORCID: [0009-0009-1383-7698](https://orcid.org/0009-0009-1383-7698)

## Citation

```bibtex
@software{longmire2025lft,
  author = {Longmire, James D.},
  title = {Logic Field Theory: Quantum Mechanics from First Principles},
  year = {2025},
  url = {https://github.com/[username]/LFT_GEN_19_LEAN}
}
```

## License

- **Lean Code**: MIT License
- **Theory & Documentation**: CC BY-NC-SA 4.0

## Acknowledgments

Lean 4 formalization developed with assistance from Claude (Anthropic).

---

**Status**: ✅ Theory complete and verified | 🔬 Awaiting experimental validation