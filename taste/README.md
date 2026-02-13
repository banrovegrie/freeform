# Taste

Aaronson opens with a problem or story, never a definition. His PhD thesis builds seven distinct interpretations of the collision lower bound before touching formalism, and by the time the math arrives the reader is asking for it. Each section opening creates a gap the section fills. Definitions arrive only when existing language is insufficient and are used immediately. First person marks opinions and conjectures, keeping them distinct from proved results. Background chapters are compressed tool chests; contribution chapters are arguments. Proofs end abruptly and sections end forward-looking, naming what remains open.

Penrose opens with the physical situation, never the apparatus. The core habit is geometric patience: one to three paragraphs of physical picture-building that make the equation inevitable when it arrives. Arguments end by returning to the physical prediction and stating what remains testable. Equations appear as conclusions of arguments, not starting points of explanations. For this thesis, his approach governs every motivation paragraph.

Harrow writes at maximum density without sacrificing clarity. The HHL abstract contains the problem, the classical baseline, the quantum improvement, and the conditions under which it applies. Proofs are modular: algorithm, runtime, optimality as distinct self-contained units. Runtime is always stated with all parameter dependencies explicit: $O(\log(N) s^2 \kappa^2 / \varepsilon)$, not "efficient." Equations are grammatical parts of sentences, not displayed objects floating between paragraphs.

De Wolf teaches. The signature habit is two-pass exposition: first an informal explanation in the reader's vocabulary ("roughly, by a 'classical' state we mean a state in which the system can be found if we observe it"), then the formal statement with quantifiers. Running examples (OR, PARITY, MAJORITY) thread through every chapter and accumulate meaning. Every chapter ends with a summary tying back to the arc. Background goes to appendices, keeping the main text focused on ideas.

The AQO paper (Chakraborty et al.) is the thesis's source material and notation baseline: $H(s) = (1-s)H_0 + sH_P$ with $s$ as schedule, gap $g(s)$, avoided crossing at $s^*$, runtime $T = O(2^{n/2} \text{poly}(n))$ with explicit polynomial factors. Results are stated with bounds, hardness is proved by reduction, limitations are named honestly. The thesis must exceed this paper in exposition depth on every point it covers.


## Signaling Transforms

Delete sentences that describe what you are doing rather than doing it. Five types:

Technique-signaling: "To provide intuition, consider X" becomes "Consider X."
Source-signaling: "The paper proves g_min = ..." becomes "The minimum gap is g_min = ... [cite]."
Process-signaling: "We now need to define X before stating Y" becomes: define X, state Y.
Structure-signaling: "In this chapter we discuss X, Y, Z" becomes: open with the question X answers. If a roadmap is needed, make it carry content: "This chapter establishes the baseline in three steps: the quantum formalism (Section 3.1), the query model (Section 3.2), and the Grover frontier (Section 3.3) that later chapters must match."
Register-signaling: "It is important to note that..." becomes: state the important thing.

The deletion test: remove the frame, keep the content. If nothing is lost, it was signal. Exception: section closings that name specific results ("The deliverables of this section are the adiabatic condition and the Landau-Zener formula") are consolidation, not signal.


## Warmth and Bloat

Warmth contributes to reading experience without new technical information: anticipation, reframing, rhythm, emphasis. Bloat contributes nothing to either. Two questions distinguish them: (1) Is meaning unchanged if deleted? (2) Is reading experience unchanged if deleted? Both yes means bloat. If deleting makes prose feel rushed or disorienting, the sentence was doing rhetorical work.

Warm: "A concrete example makes this vivid." "This asymmetry is not an accident of 3-SAT." "A first-year student can verify a solution."
Bloat: "It is important to understand the distinction between P and NP." "Having discussed the complexity classes, we now turn to their application."

Dryness across an entire section is as much a failure as filler across an entire section.


## Register

Formal register for theorem statements, proof steps, definitions, explicit bounds. Short sentences, mathematical precision. Warm register for section openings, motivation, interpretation after proofs, transitions, physical intuition. Longer sentences, varied rhythm, concrete images, authorial voice.

Shifts happen at structural boundaries, never announced. Monotone formality and monotone informality are both failures.


## Depth

Floor test: the thesis treatment of every central concept must match or exceed the published paper. A thesis thinner than its source paper is broken.
Teaching test: could a graduate student new to AQO reconstruct the argument and extend it after reading the section?
Guard rail: depth is explanatory power per sentence, not sentence count.


## Craft

Before writing any prose, identify the chapter's spine: the questions that determine the order of sections. Write them down. Be willing to throw them away and start over if the order feels forced.

### Openings

First sentence names the question or tension, not the topic. A narrative vignette that builds to the tension by end of the opening paragraph is equally valid. Second or third sentence gives a concrete instance: a specific Hamiltonian, function, or parameter regime. No formalism in the opening paragraph. Identify one driving example per chapter and thread it through every section.

### Definitions

Before every definition, write the paragraph that makes the reader want it. Two-pass exposition: informal in the reader's vocabulary, then formal with quantifiers. After every definition, use it immediately. No definition sits unused for more than a paragraph. Definition sequences are death: if three definitions must appear near each other, separate them with motivation or use.

### Proofs

State proof strategy in one content sentence. Not "the proof proceeds by induction" but "the bound follows from comparing two-level dynamics to the full system." End by returning to the claim. After every major proof, write an interpretation paragraph: what changed, what assumption carried the weight, what would go wrong without it. But do not force interpretation on bookkeeping lemmas. Where a result is routine, say so and move on.

### Transitions

Every transition sentence carries content. Replace "We now turn to..." with a sentence that closes one topic and opens the next. Between sections: the new question arises from the previous answer. Between chapters: the opening recalls a specific limitation from the previous chapter.

### Closings

Close with what was established and what question it opens. A closing sentence naming specific results is consolidation, not signal. One saying "We have established the necessary background" is signal. End every chapter with a summary or bridge.

### Throughout

Write about the subject, not about the paper or thesis. Attribute results to specific people, not passive citations, and when citing a source, say what it contributes at that point in the argument. Thread running examples across chapters and let them accumulate meaning. Import math from the published paper and do not invent formulas. Use figures for geometric and spectral concepts. Write out of order, introduction last.


## Baselines

The thesis aims to match de Wolf's structural discipline and exceed Zeeshan's MS thesis on every axis. De Wolf opens chapters with motivation and closes them with summaries that tie back to the arc; Zeeshan's chapters lack both. De Wolf uses two-pass exposition consistently; Zeeshan gives single-pass definitions with less buildup. De Wolf threads running examples across chapters; Zeeshan's appear locally. De Wolf writes with personal voice and weaves historical context naturally; Zeeshan writes technically and cites by number. De Wolf puts background in appendices; Zeeshan's Chapter 2 competes with main results for attention. The gap is not scope (PhD vs MS) but craft.


## Papers

### Scott Aaronson

1. aaronson_phd_thesis - Limits on Efficient Computation in the Physical World (2004)
2. aaronson_npcomplete - NP-Complete Problems and Physical Reality (2005)
3. 1011.3245 - Aaronson, Arkhipov - The Computational Complexity of Linear Optics (2010)
4. 1108.1791 - Aaronson - Why Philosophers Should Care About Computational Complexity (2011)
5. 1612.05903 - Aaronson, Chen - Complexity-Theoretic Foundations of Quantum Supremacy Experiments (2016)

### Roger Penrose

1. penrose_gravity_qsr - On Gravity's Role in Quantum State Reduction (1996)

### Aram Harrow

1. 0802.1919 - Harrow, Low - Random Quantum Circuits are Approximate 2-designs (2008)
2. 0811.3171 - Harrow, Hassidim, Lloyd - Quantum Algorithm for Linear Systems of Equations (2008)
3. 1208.0692 - Brandao, Harrow, Horodecki - Local Random Quantum Circuits are Approximate Polynomial-Designs (2012)

### Ronald de Wolf

1. dewolf_phd_thesis - Quantum Computing and Communication Complexity (2001)
2. 1907.09415 - Quantum Computing: Lecture Notes (2019)

### Shantanav Chakraborty

1. 2402.10362 - Hejazi, Shokrian Zini, Arrazola - Better Bounds for Low-Energy Product Formulas (2024)
2. 2403.08922 - Aftab, An, Trivisa - Multi-product Hamiltonian Simulation with Explicit Commutator Scaling (2024)
3. 2410.14243 - Mizuta, Ikeda, Fujii - Explicit Error Bounds with Commutator Scaling (2024)
4. 2411.05736 - Braida, Chakraborty, Chaudhuri, Cunningham, Menavlikar, Novo, Roland - Unstructured Adiabatic Quantum Optimization: Optimality with Limitations (2024)
5. 2412.02673 - Chakraborty, Das, Ghorui, Hazra, Singh - Sample Complexity of Black Box Work Extraction (2024)
6. 2504.02385 - Chakraborty, Hazra, Li, Shao, Wang, Zhang - Quantum Singular Value Transformation without Block Encodings (2025)
7. 2504.21564 - Garg, Ahmed, Mitra, Chakraborty - Simulating Quantum Collision Models with Hamiltonian Simulations (2025)
8. 2506.17199 - David, Sinayskiy, Petruccione - Tighter Error Bounds for the qDRIFT Algorithm (2025)
9. 2507.13670 - Chakraborty, Choi, Ghosh, Giurgica-Tiron - Fast Computational Deep Thermalization (2025)
10. 2510.06851 - Wang, Zhang, Hazra, Li, Shao, Chakraborty - Randomized Quantum Singular Value Transformation (2025)

### Zeeshan Ahmed

1. zeeshan_ms_thesis - MS Thesis (baseline comparison)
