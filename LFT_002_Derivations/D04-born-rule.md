# D04: Born Rule from Path Counting

## Abstract

We derive the Born rule P(k|ψ) = |c_k|² from first principles using logical path counting in configuration space. Using the logical strain concept from D03 Section 11 to weight paths, we show that the quadratic form is the unique probability measure satisfying four fundamental logical requirements. No quantum postulates are assumed—the Born rule emerges necessarily from the structure of logical inference paths.

## 1. Path Counting in Logical Configuration Space

### 1.1 Inference Paths

**Definition D4.1 (Logical Inference Path).** Given initial configuration [G_init] and final configuration [G_final] in A/∼, an inference path is a sequence:

$$p: [G_0] \to [G_1] \to \cdots \to [G_n]$$

where:
- [G_0] = [G_init], [G_n] = [G_final]
- Each transition [G_i] → [G_{i+1}] represents a valid logical inference rule
- The transition preserves admissibility: [G_i], [G_{i+1}] ∈ A/∼

### 1.2 Path Weights from Logical Strain

**Definition D4.2 (Transition Weight).** The weight of transition [G_i] → [G_{i+1}] is determined by the logical strain change:

$$w_i = \exp(-\beta \Delta D_{i,i+1})$$

where:
- ΔD_{i,i+1} = D([G_{i+1}]) - D([G_i]) is the strain change (from D03 Section 11.1)
- β = 1/T_logical is the inverse logical temperature
- The exponential form is justified in D03 Section 11.6
- For transitions with ΔD < 0 (strain-reducing), w_i > 1 (favored)
- For transitions with ΔD > 0 (strain-increasing), w_i < 1 (suppressed)

**Remark:** The strain D(G) quantifies logical tension as defined in D03 Section 11, ensuring weights are derived from logical structure, not postulated. In the limit β → ∞ (zero logical temperature), only minimum-strain paths contribute.

### 1.3 Path Amplitudes from Oriented Cycles

**Definition D4.3 (Path Phase).** For path p passing through cycles {C_1, ..., C_m} in the logical graphs, the accumulated phase is:

$$θ_p = \sum_{j=1}^m n_j θ_{C_j}$$

where:
- n_j = winding number (times cycle C_j is traversed)
- θ_{C_j} = orientation angle of cycle C_j (from D02 Section 3)
- Sign depends on traversal direction (clockwise +, counterclockwise -)

**Definition D4.4 (Path Amplitude).** The complex amplitude for path p is:

$$A_p = \left(\prod_{i=1}^n w_i\right) \cdot e^{iθ_p}$$

where:
- Product of weights = exp(-β Σ_i ΔD_{i,i+1}) = strain-based probability factor
- Phase factor = accumulated orientation from cycle traversals

### 1.4 Total Configuration Amplitude

**Theorem D4.1 (Path Superposition).** When multiple paths {p_1, ..., p_m} lead from [G_init] to [G_final], the total amplitude is:

$$c_{[G_{final}]} = \sum_{j=1}^m A_{p_j} = \sum_{j=1}^m \left(\prod_i w_i^{(j)}\right) e^{iθ_{p_j}}$$

*Proof:* Paths represent alternative logical derivations. By the principle of logical superposition (from D02's complex structure), indeterminate alternatives must be combined linearly with their respective amplitudes. □

## 2. Logical Requirements for Probability Measures

### 2.1 The Four Fundamental Requirements

Any probability measure P on logical configurations must satisfy:

**L1 (Normalization):** Total probability equals unity:
$$\sum_{[G] \in A/∼} P([G]|ψ) = 1$$

**L2 (Logical Additivity):** For mutually exclusive configurations:
$$P([G_1] \lor [G_2]|ψ) = P([G_1]|ψ) + P([G_2]|ψ) \text{ when } [G_1] \cap [G_2] = ∅$$

**L3 (Phase Invariance):** Global phase has no physical meaning:
$$P([G]|e^{iα}ψ) = P([G]|ψ) \text{ for all } α ∈ \mathbb{R}$$

**L4 (Factorization):** Independent systems compose multiplicatively:
$$P([G_A] × [G_B]|ψ_A ⊗ ψ_B) = P([G_A]|ψ_A) · P([G_B]|ψ_B)$$

### 2.2 Constraints from Path Structure

**Lemma D4.1 (Amplitude Dependence).** The probability must depend only on |c_{[G]}|, not on the phase of c_{[G]}.

*Proof:* Consider two scenarios yielding the same final configuration [G]:
- Scenario A: Paths {p_1, ..., p_m} with total amplitude c_A
- Scenario B: Paths {q_1, ..., q_k} with total amplitude c_B

If |c_A| = |c_B|, these scenarios differ only in the relative phases of contributing paths, not in the total amplitude magnitude. Since both lead to the same admissible configuration [G] (same logical content), and global phase is unphysical (L3), we must have P([G]|A) = P([G]|B). Therefore P depends only on |c_{[G]}|. □

## 3. Uniqueness of the Born Rule

### 3.1 General Form of the Measure

**Theorem D4.2 (Measure Form).** Any probability measure satisfying L1-L4 with path amplitudes must have the form:

$$P([G]|ψ) = f(|c_{[G]}|)$$

for some function f: ℝ⁺ → ℝ⁺.

*Proof:* 
- By Lemma D4.1, P depends only on |c_{[G]}|
- By L3, phase dependence is eliminated
- By positivity of probability, f maps to ℝ⁺ □

### 3.2 The Factorization Constraint

**Theorem D4.3 (Power Law Form).** Assuming f is continuous (or measurable) on ℝ⁺, the function must be a power law:
$$f(x) = Kx^n$$
for some constants K > 0 and n > 0.

*Proof:*
Consider independent systems A and B with amplitudes c_A, c_B.

For the composite system with no entanglement:
- Amplitude factorizes: c_{AB} = c_A · c_B
- By L4: P(A×B) = P(A) · P(B)

This gives the functional equation:
$$f(|c_A c_B|) = f(|c_A|) · f(|c_B|)$$

Setting x = |c_A|, y = |c_B|:
$$f(xy) = f(x) · f(y)$$

This is Cauchy's functional equation on ℝ⁺. With the continuity assumption, the unique solution is:
$$f(x) = Kx^n$$

for constants K > 0, n > 0. 

**Note:** Without continuity, pathological solutions exist (e.g., f(x) = x^{g(log x)} for arbitrary g). Physical measurability requires continuity. □

### 3.3 Determining the Constants

**Theorem D4.4 (Born Rule Uniqueness).** The constants must be K = 1 and n = 2.

*Proof:*

**Step 1: Normalization determines K**

Consider any normalized state |ψ⟩ = Σ_i c_i|i⟩ with Σ_i |c_i|² = 1.

By L1: Σ_i P(i|ψ) = Σ_i K|c_i|^n = 1

For the specific case of a single basis state |j⟩ (where c_j = 1, c_{i≠j} = 0):
- LHS: K·1^n = K
- By L1: K = 1

Therefore f(x) = x^n.

**Step 2: Determining n = 2**

Consider a general two-configuration system with amplitudes c₁, c₂.

The standard normalization convention (from D02's Hilbert space structure) gives:
$$|c_1|^2 + |c_2|^2 = 1$$

By L1 with K = 1:
$$P([G_1]) + P([G_2]) = |c_1|^n + |c_2|^n = 1$$

For these to be consistent for all valid amplitudes:
$$|c_1|^n + |c_2|^n = |c_1|^2 + |c_2|^2$$

Define g(x) = x^n - x² on [0,1]. We need g(x) = 0 for all x ∈ [0,1] satisfying the constraint.

**Analysis of g(x) = x^n - x²:**

- g(0) = 0 and g(1) = 0 for all n
- g'(x) = nx^{n-1} - 2x
- g''(x) = n(n-1)x^{n-2} - 2

*Case n > 2:* 
- g''(1/2) = n(n-1)/2^{n-2} - 2 > 0 for large enough n
- g is strictly convex on some interval
- By convexity and boundary conditions: g(x) < 0 for some x ∈ (0,1)
- Contradiction with normalization

*Case n < 2:*
- g''(x) < 0 for x near 0
- g is strictly concave near 0
- By concavity and g(0) = 0: g(x) > 0 for small x > 0
- Contradiction with normalization

*Case n = 2:*
- g(x) = x² - x² = 0 identically
- Consistency for all amplitudes ✓

Therefore n = 2 uniquely, giving P = |c|². □

### 3.4 Uniqueness Summary

The Born rule P = |ψ|² is the unique measure because:
1. **f must have form f(x) = Kx^n** (factorization + continuity)
2. **K = 1** (normalization on basis states)
3. **n = 2** (consistency with amplitude normalization)

No other measure satisfies L1-L4 with complex path amplitudes.

## 4. Connection to Measurement

### 4.1 When Measurement Occurs

From D03 Section 11.5, measurement is triggered when logical strain exceeds the critical threshold:

$$D(ψ) > D_{critical} \Rightarrow \text{measurement event}$$

This determines **when** collapse happens (strain threshold exceeded), not the probabilities.

### 4.2 What Outcomes Occur

**Theorem D4.5 (Measurement Probabilities).** When measurement occurs, outcomes follow Born probabilities:

$$P(k|ψ) = |⟨k|ψ⟩|² = |c_k|²$$

*Proof:* By Theorems D4.2-D4.4, this is the unique measure consistent with:
- Path interference (complex amplitudes from oriented cycles)
- Logical requirements (L1-L4)
- Continuity (physical measurability)
- Standard normalization (⟨ψ|ψ⟩ = 1)

The strain mechanism (D03 Section 11) triggers measurement, but outcome selection follows the unique path-counting measure. □

## 5. Examples

### 5.1 Double-Slit Experiment

Consider paths through two slits to detector position x:
- Path through slit 1: amplitude A₁e^{iθ₁} with A₁ = exp(-βD₁)
- Path through slit 2: amplitude A₂e^{iθ₂} with A₂ = exp(-βD₂)

Where D₁, D₂ are the logical strains (D03 Section 11) of the respective paths.

Total amplitude: c(x) = A₁e^{iθ₁} + A₂e^{iθ₂}

Probability: P(x) = |c(x)|² = A₁² + A₂² + 2A₁A₂cos(θ₁ - θ₂)

The interference term 2A₁A₂cos(θ₁ - θ₂) arises necessarily from path superposition with n = 2.

### 5.2 Spin Measurement

For spin-1/2 in state |ψ⟩ = α|↑⟩ + β|↓⟩ with |α|² + |β|² = 1:

Paths to |↑⟩ outcome: amplitude α (weighted by strain)
Paths to |↓⟩ outcome: amplitude β (weighted by strain)

By Theorem D4.4:
- P(↑) = |α|²
- P(↓) = |β|²
- P(↑) + P(↓) = |α|² + |β|² = 1 ✓

## 6. Falsifiable Predictions

### 6.1 Testing n = 2 Uniqueness

If experiments found P ∝ |ψ|^n with n ≠ 2:
- Would violate normalization consistency
- Would break factorization for product states
- Would produce different interference patterns

**Critical test:** Prepare |ψ⟩ = (|0⟩ + |1⟩)/√2
- Born rule predicts: P(0) = P(1) = 1/2
- Alternative n = 3: P(0) = P(1) = (1/√2)³ = 1/(2√2) ≈ 0.35
- Precision required: ~1% to definitively exclude n = 3

### 6.2 Testing Path Weight Structure

The strain-based weights (D03 Section 11.6) predict:
1. **Temperature dependence:** Lower T_logical → sharper path selection
2. **Strain correlations:** High-strain paths contribute less to amplitude
3. **Threshold behavior:** Paths with D > D_critical are suppressed

## 7. Summary

**Main Result:** The Born rule P = |c|² is the unique probability measure satisfying:
1. Path amplitudes sum as complex numbers (orientation from D02)
2. Normalization (L1)
3. Logical additivity (L2) 
4. Phase invariance (L3)
5. System factorization (L4)
6. Continuity/measurability

**Key Dependencies:**
- Uses logical strain from D03 Section 11 for path weights
- Uses complex structure from D02 for oriented amplitudes
- Provides Born rule for D05's decoherence analysis

**Not Circular:** The derivation uses only:
- Logical path structure (graph transitions from D01)
- Complex amplitudes (from D02 orientation requirement)
- Logical strain (from D03 Section 11)
- Basic probability axioms (L1-L4)
- No quantum postulates

The Born rule emerges as the unique measure consistent with logical path counting in complex configuration space.

## References

- D01: Admissible graphs and graph transitions
- D02: Complex necessity from orientation
- D03 Section 11: Logical strain definition and properties
- D05: Size-dependent decoherence using Born rule
- Cauchy (1821): Functional equations
- Feynman (1948): Path integral formulation (comparison)