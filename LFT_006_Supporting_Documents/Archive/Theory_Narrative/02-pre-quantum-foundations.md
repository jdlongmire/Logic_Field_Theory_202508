# 2. Pre-Quantum Foundations

This section defines the syntactic substrate of Logic Field Theory — the purely formal space from which physically admissible configurations will be selected by the logic operator $\mathbb{L}$.

## 2.1 The Syntactic Space $\mathcal{S}$

The syntactic space $\mathcal{S}$ consists of all **finite formal configurations** constructible from a countable set of atomic propositions. These configurations are represented as finite directed graphs with a negation involution.

**Definition 2.1 (Syntactic Space).**
Let the set of atomic propositions be:
$$\mathcal{P} = \{ p_1, p_2, p_3, \dots \}$$

and let the set of literals be:
$$\mathcal{L} = \mathcal{P} \cup \{ \neg p : p \in \mathcal{P} \}$$

The syntactic space is:
$$\mathcal{S} = \{\, G = (V, E, \tau) \mid V \subset \mathcal{L},\ |V| < \infty,\ E \subseteq V \times V,\ \tau : V \to V,\ \tau \circ \tau = \mathrm{id}_V \,\}$$

where:
- $V$ is a **finite** set of vertices (literals: atomic propositions or their negations)
- $E$ is a set of directed edges (implications) between vertices
- $\tau$ is a **negation involution** mapping each literal to its negation and satisfying $\tau(\tau(v)) = v$ for all $v \in V$

**Properties of $\mathcal{S}$:**

1. **Countable** – Since $\mathcal{P}$ is countable and $V$ is finite, the set of all such graphs is countable.

2. **Constructible** – Any $G \in \mathcal{S}$ can be built via:
   - Choose $n \in \mathbb{N}$ (number of proposition pairs)
   - Define $V = \{ p_1, \neg p_1, \dots, p_n, \neg p_n \}$
   - Define $\tau(p_i) = \neg p_i$ and $\tau(\neg p_i) = p_i$
   - Choose any $E \subseteq V \times V$ for implications

3. **Complete** – Contains **all** possible logical configurations:
   - Self-contradictory ($\exists$ path from $v$ to $\tau(v)$)
   - Incomplete (missing edges)
   - Over-constrained (excess implications)
   - Admissible (will survive $\mathbb{L}$ filtering)

**Example elements of $\mathcal{S}$:**
- Empty graph: $G_0 = (\emptyset, \emptyset, \emptyset)$
- Single proposition: $G_1 = (\{p, \neg p\}, \emptyset, \tau)$
- Contradiction: $G_{\bot} = (\{p, \neg p\}, \{(p,\neg p)\}, \tau)$
- Tautology: $G_{\top} = (\{p, \neg p\}, \{(p,p), (\neg p,\neg p)\}, \tau)$

**Remark 2.1.**  
We **allow** self-loops $(v,v)$ in $E$ to represent tautological entailment.  
We **do not** filter out contradiction edges $(v,\tau(v))$ here — those are removed by the logic operator $\mathbb{L}$ in Section 2.2.

**Rationale for Finiteness:**
1. Physical systems have finite information content
2. Ensures computability of admissibility checks
3. Supports explicit construction and enumeration
4. Infinite structures can emerge as limits of finite sequences

## 2.2 The Logic Operator $\mathbb{L}$

The logic operator $\mathbb{L} : \mathcal{S} \to \mathcal{S}$ filters the syntactic space to extract only logically admissible configurations by enforcing the Three Fundamental Laws of Logic.

**Definition 2.2 (Logic Operator).**
For any graph $G = (V, E, \tau) \in \mathcal{S}$, the logic operator $\mathbb{L}$ is defined by:

$$\mathbb{L}(G) = \begin{cases}
G & \text{if } G \text{ satisfies conditions (L1)-(L3)} \\
\emptyset & \text{otherwise}
\end{cases}$$

where the admissibility conditions are:

**(L1) Identity:** Every vertex has a self-loop:
$$\forall v \in V: (v,v) \in E$$

**(L2) Non-Contradiction:** No directed path exists from any vertex to its negation:
$$\forall v \in V: \nexists \text{ path } v \to^* \tau(v)$$
where $\to^*$ denotes a directed path of length $\geq 1$ through edges in $E$.

**(L3) Excluded Middle:** The vertex set respects negation pairing:
$$\forall v \in V: \tau(v) \in V$$
(If a proposition appears, so does its negation.)

**Algorithm 2.1 (Logic Filter).**
```python
def apply_logic_operator(G):
    V, E, τ = G.vertices, G.edges, G.negation
    
    # Check L1: Identity
    for v in V:
        if (v,v) not in E:
            return ∅  # Fails identity
    
    # Check L2: Non-Contradiction
    for v in V:
        if exists_path(v, τ(v), E):
            return ∅  # Contains contradiction
    
    # Check L3: Excluded Middle
    for v in V:
        if τ(v) not in V:
            return ∅  # Incomplete negation pairs
    
    return G  # Passes all checks

def exists_path(start, end, edges):
    """Check if directed path exists from start to end"""
    visited = set()
    queue = [start]
    
    while queue:
        current = queue.pop(0)
        if current == end:
            return True
        if current in visited:
            continue
        visited.add(current)
        queue.extend([v for (u,v) in edges if u == current])
    
    return False
```

**Properties of $\mathbb{L}$:**

**Theorem 2.1.** The logic operator $\mathbb{L}$ satisfies:
1. **Contractive:** $\mathbb{L}(G) \in \{G, \emptyset\} \subseteq \{G\}$
2. **Idempotent:** $\mathbb{L}(\mathbb{L}(G)) = \mathbb{L}(G)$
3. **Decidable:** Checking $\mathbb{L}(G) \neq \emptyset$ is computable in $O(|V|^3)$ time

*Proof sketch:*
1. Contractive: By definition, $\mathbb{L}$ either returns $G$ or $\emptyset$
2. Idempotent: If $\mathbb{L}(G) = G$, then $G$ satisfies (L1)-(L3), so $\mathbb{L}(G) = G$ again. If $\mathbb{L}(G) = \emptyset$, then $\mathbb{L}(\emptyset) = \emptyset$
3. Decidable: Identity check is $O(|V|)$, path existence is $O(|V|^2)$ per vertex via BFS, excluded middle is $O(|V|)$

## 2.3 The Admissible Set $\mathcal{A}$

**Definition 2.3 (Admissible Set).**
The admissible set is:
$$\mathcal{A} = \mathbb{L}(\mathcal{S}) = \{G \in \mathcal{S} : \mathbb{L}(G) = G\}$$

This is the set of all graphs that survive logical filtering.

**Remark 2.2.** The empty graph $\emptyset$ is technically admissible (vacuously satisfies all conditions) but represents "no information." The meaningful admissible configurations have $|V| \geq 2$.

**Example 2.1 (Admissibility Check).**
Consider $G = (\{p, \neg p\}, \{(p,p), (\neg p,\neg p), (p,\neg p)\}, \tau)$:
- L1 ✓: Both $p$ and $\neg p$ have self-loops
- L2 ✗: Path exists from $p$ to $\tau(p) = \neg p$
- L3 ✓: Both $p$ and $\tau(p)$ are in $V$

Result: $\mathbb{L}(G) = \emptyset$ (inadmissible due to contradiction)

**Example 2.2 (Admissible Graph).**
Consider $H = (\{p, \neg p, q, \neg q\}, \{(p,p), (\neg p,\neg p), (q,q), (\neg q,\neg q), (p,q)\}, \tau)$:
- L1 ✓: All vertices have self-loops
- L2 ✓: No paths to negations ($p \to q$ but no path to $\neg p$ or $\neg q$)
- L3 ✓: All negation pairs present

Result: $\mathbb{L}(H) = H$ (admissible)

## 2.4 Logical Equivalence Classes

Two admissible graphs may represent the same logical content despite structural differences.

**Definition 2.4 (Logical Equivalence).**
Two graphs $G, H \in \mathcal{A}$ are **logically equivalent**, denoted $G \sim H$, if they yield identical truth valuations under all consistent assignments. Formally:
$$G \sim H \iff \forall \phi: \mathcal{P} \to \{0,1\}, \quad \text{Sat}(G,\phi) = \text{Sat}(H,\phi)$$

where $\text{Sat}(G,\phi)$ indicates whether assignment $\phi$ satisfies the constraints encoded by $G$.

**Proposition 2.1.** Logical equivalence $\sim$ is an equivalence relation on $\mathcal{A}$.

*Proof:* Reflexivity, symmetry, and transitivity follow directly from the definition. □

The quotient space $\mathcal{A}/\!\sim$ forms the basis for our state space construction in Section 4. Each equivalence class $[G]$ represents a distinct logical configuration, independent of its syntactic representation.

## 2.5 Why This Foundation Matters

Before introducing any quantum machinery, we have established:
1. **A precise syntactic space** $\mathcal{S}$ (all finite formal configurations)
2. **An algorithmic filter** $\mathbb{L}$ (enforcing logical laws)
3. **A well-defined admissible set** $\mathcal{A}$ (logically coherent configurations)
4. **Equivalence classes** $\mathcal{A}/\!\sim$ (distinct logical content)

This foundation is purely logical — no physics has been introduced. The quantum structure will emerge when we ask: *"How must admissible configurations compose and transform while preserving logical coherence?"* This question drives us toward the vector space structure explored in Section 4.

## Key Results

- **Syntactic space $\mathcal{S}$** is countable and constructible
- **Logic operator $\mathbb{L}$** is algorithmic with $O(|V|^3)$ complexity
- **Admissible set $\mathcal{A}$** contains only logically coherent configurations
- **Equivalence classes** provide the basis for quantum state space

The next section introduces the logical strain functional that determines which admissible configurations are physically realized.