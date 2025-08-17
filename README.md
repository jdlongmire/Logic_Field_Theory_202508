# Logic Field Theory (LFT)

**Deriving Quantum Field Theory from the Three Fundamental Laws of Logic**

[![Lean 4](https://img.shields.io/badge/Lean-4.21.0-blue)](https://github.com/leanprover/lean4)
[![License: MIT](https://img.shields.io/badge/Code-MIT-green.svg)](LICENSE)
[![License: CC BY-NC-SA 4.0](https://img.shields.io/badge/Theory-CC%20BY--NC--SA%204.0-lightgrey.svg)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.16884443.svg)](https://doi.org/10.5281/zenodo.16884443)

Run in Gitpod without installing Lean 4:

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/jdlongmire/Logic_Field_Theory_202508)

---

## Overview

Logic Field Theory (LFT) is a foundational program in quantum theory. It treats the **Three Fundamental Laws of Logic** (Identity, Non-Contradiction, Excluded Middle) as primitive constraints from which physics necessarily emerges.  

Instead of taking quantum mechanics as a starting postulate, LFT derives its structure from logic itself:

- **Complex numbers** arise as the unique scalar field consistent with logical orientation.  
- **Gauge structure** U(1)×SU(2)×SU(3) follows from enhancing discrete logical symmetries.  
- **Born rule** |c|² is derived via logical path counting.  
- **Decoherence scaling** τ_D ∝ 1/ξ² emerges from constraint density in 3D.  
- **Lagrangian dynamics** appear as the minimal framework preserving logical consistency.  
---
The project combines **derivation papers**, **formal Lean 4 proofs**, and **AI-assisted theorem proving** to construct a fully verifiable framework.
---
## Derivation Flow

The seven core derivations (D01–D07) build on one another as follows:

```mermaid
graph LR
  D01["D01 • Admissible Graphs"] --> D02["D02 • Complex Necessity"]
  D01 --> D03["D03 • Gauge Structure"]
  D02 --> D03
  D03 --> D04["D04 • Born Rule"]
  D03 --> D05["D05 • Decoherence Scaling"]
  D04 --> D07["D07 • Predictions"]
  D05 --> D07
  D06["D06 • Lagrangian Formalism"] --> D07
```
---

## Progress

**Derivations (D01–D07):**
- **D01** – Defined admissible graphs and logical equivalence classes. Complexity O(n³).  
- **D02** – Proved necessity of ℂ over ℝ or ℍ using representation theory.  
- **D03** – Derived unitary evolution and gauge groups from logical symmetries.  
- **D04** – Obtained the Born rule uniquely from path counting.  
- **D05** – Connected logical strain to decoherence scaling (τ_D ∝ 1/ξ²).  
- **D06** – Showed variational principles follow from logical consistency.  
- **D07** – Outlined falsifiable predictions and experimental pathways.  

**Philosophical foundation:** Published companion paper framing logic as ontological primitive.  

**Formal verification:** Lean 4 proofs underway for D01–D04, with scaffolding for later derivations.  

**Repository structure (in progress):**

## Repository Structure

```mermaid
graph TD
  ROOT["LOGIC_FIELD_THEORY_202508"]

  subgraph DOCS [LFT_001_Documents]
    PPDF["Logic_Field_Theory_202508.pdf"]
    TEX["main.tex"]
    BIB["references.bib"]
    RMD["README.md"]
  end

  subgraph DERIV [LFT_002_Derivations_Proofs]
    D01["D01 • Admissible Graphs\n(3FLL admissibility & complexity)"]
    D02["D02 • Complex Necessity\n(ℂ as unique scalar field)"]
    D03["D03 • Gauge Structure\n(Unitary + U(1)×SU(2)×SU(3))"]
    D04["D04 • Born Rule\n(Path counting derivation)"]
    D05["D05 • Decoherence Scaling\n(τ_D ∝ 1/ξ²)"]
    D06["D06 • Lagrangian\n(Variational formalism)"]
    D07["D07 • Predictions\n(Falsifiability roadmap)"]
  end

  subgraph LEAN [LFT_003_Lean_Proofs/Core]
    L01["D01_Admissibility.lean"]
    L02["D02_ComplexNecessity.lean"]
    L03["D03_UnitaryEvolution.lean"]
    L04["D04_BornRule.lean"]
    L05["D05_StrainWeights.lean"]
  end

  ROOT --> DOCS
  ROOT --> DERIV
  ROOT --> LEAN

  DOCS --> PPDF
  DOCS --> TEX
  DOCS --> BIB
  DOCS --> RMD

  DERIV --> D01
  DERIV --> D02
  DERIV --> D03
  DERIV --> D04
  DERIV --> D05
  DERIV --> D06
  DERIV --> D07

  LEAN --> L01
  LEAN --> L02
  LEAN --> L03
  LEAN --> L04
  LEAN --> L05
```

---

## Author

**James D. Longmire**  
Northrop Grumman Fellow (independent research)  
Email: longmire.jd@gmail.com  
ORCID: [0009-0009-1383-7698](https://orcid.org/0009-0009-1383-7698)

---

## Collaboration

Seeking collaborators in:
- **Experimental physics**: testing decoherence scaling predictions  
- **Formal methods**: completing Lean verifications  
- **Quantum foundations**: extending the theoretical framework  

---

## Methodological Note

This project pioneers **AI-assisted formal theorem proving** in theoretical physics. The conceptual framework and derivations are the author’s original work. Formal Lean proofs are developed in collaboration with multiple AI systems (Claude, ChatGPT, Grok, Gemini) and verified with Lean 4.

---

## License

- **Lean Code**: MIT License  
- **Theory & Documentation**: CC BY-NC-SA 4.0
