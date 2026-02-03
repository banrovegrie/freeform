# Taste

Papers for taste, reference and style guidance, organized by author.

Deep analysis of writing patterns, structural techniques, and actionable guidance for thesis writing.


## Scott Aaronson

**Style essence**: Makes you *feel* why a result matters before showing you the proof. Master of the philosophical hook.

### What Makes His Writing Work

Aaronson writes for intelligent outsiders. His signature move is to take a technical result and show why it matters for questions people already care about. In "Why Philosophers Should Care About Computational Complexity," he opens not with definitions but with a Turing quote about the fallacy of logical omniscience, immediately signaling that this will connect to deep questions.

**Structural patterns observed**:
1. **The philosophical hook**: Opens with a question or paradox that the reader already finds interesting
2. **The ground rules**: Explicitly states what the essay will and won't cover (see Section 1.1)
3. **The complexity 101 section**: Brief, accessible primer before diving deep
4. **The "one might think... but" construction**: Anticipates and addresses objections
5. **The concrete example**: Tornado assembling a 747, lookup tables, Borges' Library of Babel
6. **The honest admission**: "I personally see no reason to believe..." shows intellectual honesty

**Paragraph-level techniques**:
- Paragraphs often begin with a provocative claim, then unpack it
- Uses rhetorical questions to guide the reader's thinking
- Employs first person liberally ("I find it surprising that...")
- Footnotes handle technical qualifications without disrupting flow
- Italics for emphasis on key conceptual points

**Sentence-level patterns**:
- Short punchy sentences after long complex ones for rhythm
- Parenthetical asides that add personality ("the other complexity theory, which studies complex systems")
- Explicitly numbered lists when making multiple distinct points

### Actionable Pointers for Thesis

1. **Opening chapters**: Ask "What question does this answer that a physicist would already care about?"
2. **Before every definition**: Write one paragraph explaining why we need this concept
3. **The ground rules trick**: Early in introduction, explicitly list what thesis will/won't cover
4. **Vivid analogies**: For every abstract concept, find one concrete physical analogy
5. **Anticipate objections**: Include "One might worry that..." paragraphs
6. **Honest limitations**: Include explicit "Criticisms of [approach]" subsection
7. **The relevance test**: For each section, write one sentence explaining its philosophical import

### Papers

1. 1011.3245 - Aaronson, Arkhipov - The Computational Complexity of Linear Optics (2010)
2. 1108.1791 - Aaronson - Why Philosophers Should Care About Computational Complexity (2011)
3. 1612.05903 - Aaronson, Chen - Complexity-Theoretic Foundations of Quantum Supremacy Experiments (2016)


## Aram Harrow

**Style essence**: Maximum information density with perfect clarity. Every sentence earns its place.

### What Makes His Writing Work

Harrow's HHL paper is a masterclass in technical writing. The abstract alone contains: the problem, the classical baseline, the quantum improvement, and the conditions under which it applies. No wasted words. The paper follows a rigid logical structure that makes it easy to find specific information.

**Structural patterns observed**:
1. **The problem-solution abstract**: Problem statement, classical bound, quantum algorithm, improvement factor
2. **The "sketch then details" pattern**: Section II gives algorithm intuition, Appendix A gives full proofs
3. **The modular proof structure**: Each piece (algorithm, runtime, optimality) is self-contained
4. **The reduction for hardness**: Shows optimality by reducing from BQP-complete problems
5. **The "discussion" section**: Extensions, generalizations, and connections to other work
6. **The explicit error analysis**: Separate subsection devoted entirely to error bounds

**Paragraph-level techniques**:
- Topic sentences that precisely state what the paragraph will establish
- Mathematical statements interspersed naturally with prose
- Equations are part of sentences, not separate entities
- Each paragraph typically makes exactly one point

**Notation discipline**:
- Consistent use of O-tilde notation for suppressing log factors
- Explicit statement of what norms mean (spectral norm for operators)
- Runtime stated with all dependencies explicit: O(log(N) s^2 kappa^2 / epsilon)

### Actionable Pointers for Thesis

1. **State results precisely**: Every theorem should have explicit error bounds and complexity
2. **Separate intuition from proof**: Use "We sketch here the basic idea... we discuss it in more detail in the next section"
3. **Modular structure**: Algorithm description, runtime analysis, optimality proof as distinct sections
4. **Runtime with dependencies**: Always state T = O(f(n, epsilon, kappa, ...)) with all parameters
5. **The "Related work" paragraph**: Brief, precise comparison to prior results
6. **The "Discussion" section**: Extensions, limitations, open questions
7. **Hardness via reduction**: If claiming something is hard, prove it by reduction

### Papers

1. 0802.1919 - Harrow, Low - Random Quantum Circuits are Approximate 2-designs (2008)
2. 0811.3171 - Harrow, Hassidim, Lloyd - Quantum Algorithm for Linear Systems of Equations (2008)
3. 1208.0692 - Brandao, Harrow, Horodecki - Local Random Quantum Circuits are Approximate Polynomial-Designs (2012)


## Ronald de Wolf

**Style essence**: The patient teacher who never loses you. Sustains narrative across hundreds of pages.

### What Makes His Writing Work

De Wolf's PhD thesis is perhaps the best model for thesis writing. It opens with a philosophical epigraph ("Se non e vero, e ben trovato" - even if it's not true, it's a nice idea), immediately establishing a personal, reflective voice. The acknowledgments read like a story of intellectual development, not a list of names.

**Structural patterns observed**:
1. **The philosophical epigraph**: Sets tone before content begins
2. **The acknowledgments as narrative**: Thanks people for specific intellectual contributions
3. **The roadmap introduction**: Chapter 1 is itself a mini-survey of the field
4. **The motivation-definition-theorem-discussion cycle**: Each concept introduced this way
5. **The running examples**: OR, PARITY, MAJORITY appear throughout
6. **The chapter summary**: Each chapter ends with "Summary" consolidating key insights
7. **The linear algebra appendix**: Technical preliminaries in appendix, not main text

**Chapter-level architecture** (from Chapter 2):
- 2.1 Introduction: Why this chapter matters, what we'll prove
- 2.2 Boolean Functions and Polynomials: Building blocks, carefully motivated
- 2.3 Query Complexity: The models we need
- 2.4-2.7: Main results, organized by function class
- 2.8 Summary: What we learned, what's next

**The "two-pass" exposition**:
- First pass: Informal explanation in plain language
- Second pass: Formal definition/theorem/proof
- Example: "Roughly, by a 'classical' state we mean a state in which the system can be found if we observe it." Then formal definition follows.

**Transition techniques**:
- "Before continuing with the harder case, notice the resemblance..."
- "The point of these examples was to illustrate that..."
- "An important property that deserves to be mentioned is..."

### Actionable Pointers for Thesis

1. **Philosophical opening**: Begin with an epigraph or philosophical framing
2. **Acknowledgments as narrative**: Write about intellectual journey, not just names
3. **Chapter 1 as mini-survey**: Introduction should be readable as standalone overview
4. **The two-pass pattern**: Informal intuition, then formal statement
5. **Running examples**: Choose 2-3 examples (functions, Hamiltonians) and use throughout
6. **Chapter summaries**: End every chapter with "Summary" section
7. **Appendix for background**: Put linear algebra, complexity definitions in appendix
8. **Historical context**: Weave in who proved what when ("Bernstein and Vazirani also defined...")
9. **The "helpful comparison" paragraph**: "At this point, a comparison with [X] may be helpful."

### De Wolf vs Template Thesis: Detailed Comparison

| Aspect | De Wolf | Template |
|--------|---------|----------|
| Opening | Philosophical epigraph, personal voice | Jumps to notation |
| Acknowledgments | Narrative of intellectual development | Standard list format |
| Definitions | Motivated before stated | Stated then sometimes motivated |
| Examples | Running examples throughout | Examples isolated in sections |
| Transitions | Explicit signposting | Minimal transitions |
| Summaries | Every chapter has one | Sporadic |
| Reader assumed | Intelligent but not specialist | Already in the field |
| Notation | Introduced only when needed | Front-loaded |

### Works

1. dewolf_phd_thesis - de Wolf - Quantum Computing and Communication Complexity (2001)
2. 1907.09415 - de Wolf - Quantum Computing: Lecture Notes (2019)


## Shantanav Chakraborty

**Style essence**: Modern quantum algorithms paper with rigorous complexity-theoretic framing.

### What Makes His Writing Work

The AQO paper (2411.05736) is directly relevant to the thesis topic. It demonstrates how to write about adiabatic quantum computation with proper complexity-theoretic care. The structure is: problem statement, main results, technical development, hardness results, discussion.

**Structural patterns observed**:
1. **The "Contents" as roadmap**: Detailed table of contents showing logical flow
2. **The "Preliminaries" section**: Defines complexity classes, notation, key concepts
3. **The "Summary of results" subsection**: States main theorems upfront in Section 1.2
4. **The "Related Work" subsection**: Explicit comparison to prior art
5. **The main result theorem boxes**: Key results in named, numbered theorems
6. **The "Discussion" section**: Limitations, open questions, philosophical implications
7. **The appendix structure**: Technical proofs separated from main narrative

**Mathematical writing patterns**:
- Complexity-theoretic notation explained: "g(n) = O(f(n)) implies g is upper bounded by f"
- Norm conventions stated explicitly: "||A|| will denote the spectral norm"
- Named definitions: "Definition 4 (The problem Hamiltonian)"
- Lemmas support theorems: Lemma 3 (Adiabatic Theorem) enables Theorem 5

**Figure usage**:
- Figure 1: Spectrum visualization with inset for detail
- Figure 2: Schematic of proof technique
- Figure 3: Comparison of actual gap vs. lower bounds

### Domain-Specific Conventions for AQO

1. **Hamiltonian notation**: H(s) = (1-s)H_0 + sH_P with s as schedule
2. **Spectral parameters**: Gap g(s), avoided crossing position s*, window delta_s
3. **Complexity classes**: NP, #P with formal definitions
4. **Runtime statements**: T = O(2^{n/2} poly(n)) with explicit polynomial factors
5. **Error analysis**: Trace distance, fidelity, epsilon-closeness
6. **Adiabatic theorem**: Cite the standard formulation (Jansen et al., Ambainis-Regev)

### Actionable Pointers for Thesis

1. **Preliminaries section**: Define notation, complexity classes, key concepts
2. **Summary of results early**: State main theorems in introduction before proofs
3. **Named definitions**: Use "Definition X (Descriptive Name)" format
4. **Related work**: Explicit subsection comparing to prior art
5. **Figures for spectra**: Visualize eigenvalue structure with avoided crossings
6. **Hardness results**: If claiming optimality, prove hardness via reduction
7. **Discussion section**: Address limitations, open problems, implications
8. **Appendix for proofs**: Keep main text focused on results and intuition

### Papers

1. 2402.10362 - Hejazi, Shokrian Zini, Arrazola - Better Bounds for Low-Energy Product Formulas (2024)
2. 2403.08922 - Aftab, An, Trivisa - Multi-product Hamiltonian Simulation with Explicit Commutator Scaling (2024)
3. 2410.14243 - Mizuta, Ikeda, Fujii - Explicit Error Bounds with Commutator Scaling for Time-Dependent Product and Multi-Product Formulas (2024)
4. 2411.05736 - Braida, Chakraborty, Chaudhuri, Cunningham, Menavlikar, Novo, Roland - Unstructured Adiabatic Quantum Optimization: Optimality with Limitations (2024)
5. 2412.02673 - Chakraborty, Das, Ghorui, Hazra, Singh - Sample Complexity of Black Box Work Extraction (2024)
6. 2504.02385 - Chakraborty, Hazra, Li, Shao, Wang, Zhang - Quantum Singular Value Transformation without Block Encodings (2025)
7. 2504.21564 - Garg, Ahmed, Mitra, Chakraborty - Simulating Quantum Collision Models with Hamiltonian Simulations (2025)
8. 2506.17199 - David, Sinayskiy, Petruccione - Tighter Error Bounds for the qDRIFT Algorithm (2025)
9. 2507.13670 - Chakraborty, Choi, Ghosh, Giurgica-Tiron - Fast Computational Deep Thermalization (2025)
10. 2510.06851 - Wang, Zhang, Hazra, Li, Shao, Chakraborty - Randomized Quantum Singular Value Transformation (2025)


## Synthesis: Principles for Thesis Writing

### The Three Voices

From studying these authors, three distinct "voices" emerge that can be combined:

1. **The Philosopher (Aaronson)**: Why does this matter? What's at stake?
2. **The Engineer (Harrow)**: Precisely what do we achieve? With what cost?
3. **The Teacher (de Wolf)**: How do we understand this? Let me show you step by step.

A good thesis uses all three: philosophical framing in introductions, engineering precision in results, pedagogical care throughout.

### Structural Blueprint for Chapters

Based on de Wolf's thesis structure combined with modern conventions:

```
Chapter N: [Title]

N.1 Introduction
    - Why this chapter matters
    - What we will prove
    - Connection to previous chapters

N.2 Preliminaries (if needed)
    - Definitions specific to this chapter
    - Notation conventions

N.3-N.k Main Content
    - Each section: motivation -> definition -> result -> discussion
    - Running examples throughout
    - Figures for complex structures

N.(k+1) Summary
    - Key results stated informally
    - Connections to broader themes
    - Preview of next chapter
```

### The 15 Commandments of Good Technical Writing

**On Motivation**:
1. Never introduce a concept without first explaining why we need it
2. Every chapter should answer a question the reader already cares about
3. The abstract/introduction should make a physicist want to read more

**On Structure**:
4. State main results early; proofs can come later
5. Use the two-pass pattern: intuition first, formalism second
6. End every chapter with a summary that ties to larger themes

**On Precision**:
7. Every theorem should have explicit error bounds and complexity
8. Define notation when introduced, not in a front-loaded section
9. State clearly what results do and don't achieve

**On Examples**:
10. Choose 2-3 running examples and use them throughout
11. For every abstract concept, provide at least one concrete instance
12. Use figures to visualize spectra, algorithms, proof structures

**On Connection**:
13. Explicitly compare your work to prior results
14. Acknowledge intellectual debts generously and specifically
15. Include a discussion of open questions and limitations

### Writing Checklist for Each Section

Before finalizing any section, ask:

- [ ] Does the opening paragraph explain why this section matters?
- [ ] Are all definitions motivated before being stated?
- [ ] Is there at least one concrete example?
- [ ] Are all theorems stated with precise bounds?
- [ ] Is there a transition to the next section?
- [ ] Would a graduate student understand the main point on first read?
- [ ] Have I acknowledged relevant prior work?
- [ ] Does this connect to the thesis's larger narrative?

### Common Mistakes to Avoid

1. **The definition dump**: Opening with pages of notation before any motivation
2. **The orphan concept**: Introducing something that's never used again
3. **The vague claim**: "This is efficient" without stating O(f(n))
4. **The missing context**: Proving something without explaining why we care
5. **The abrupt ending**: Finishing a section without summary or transition
6. **The assumed background**: Using terms without definition or reference
7. **The citation-free claim**: Making strong statements without supporting references
8. **The emotional hedge**: "We believe that..." instead of stating precisely what's proven

### For the AQO Thesis Specifically

Based on the domain-specific analysis of Chakraborty's papers:

**Notation to use consistently**:
- H(s) for time-dependent Hamiltonian
- g(s) for spectral gap
- Delta for gap of problem Hamiltonian
- kappa for condition number
- T for total runtime
- epsilon for error parameter

**Structure suggestions**:
- Chapter 1: Introduction with philosophical framing (Aaronson style)
- Chapter 2: Preliminaries - quantum computing, complexity classes (de Wolf style)
- Chapter 3: Adiabatic quantum computation - models, adiabatic theorem (de Wolf style)
- Chapter 4-5: Main technical results (Harrow style precision)
- Chapter 6: Hardness results and limitations (Chakraborty style)
- Chapter 7: Discussion and open problems

**Key results to state precisely**:
- Runtime bounds: T = O(f(n, epsilon, kappa, ...))
- Gap bounds: g(s) >= lower bound for all s in [a,b]
- Complexity statements: "Computing X is NP-hard" with reduction proof
