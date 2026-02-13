# Unstructured Adiabatic Quantum Optimization

My master's thesis on Unstructured Adiabatic Quantum Optimization, supervised by Shantanav Chakraborty. Built on the published paper [Unstructured Adiabatic Quantum Optimization: Optimality with Limitations](https://arxiv.org/abs/2411.05736) (Braida, Chakraborty, Chaudhuri, Cunningham, Menavlikar, Novo, Roland, 2025).

## Table of Contents

This thesis aims to be a single coherent path from first principles to the main results of `paper/` (arXiv:2411.05736) and `rough/`, and to the extensions in `src/experiments/`.

- Chapter 1: Introduction
- Chapter 2: Physics and Computation
- Chapter 3: Quantum Computation
- Chapter 4: Adiabatic Quantum Computation
- Chapter 5: Adiabatic Quantum Optimization
- Chapter 6: Spectral Analysis
- Chapter 7: Optimal Schedule
- Chapter 8: Hardness of Optimality
- Chapter 9: Information Gap
- Chapter 10: Formalization
- Chapter 11: Conclusion

The chapters should be written in this order:

1. Core chapters first (**5 to 8**): These are the heart of the thesis, directly exposing the published paper's main results and any background relevant (that is not supposed to be covered in chapters 2-4). Chapter 5 sets up AQO, Chapter 6 does spectral analysis, Chapter 7 derives the optimal runtime, Chapter 8 proves hardness. Writing these first ensures the technical spine is solid before anything else.

2. Extensions and original contributions next (**9**): Chapter 9 contains original contributions building directly on Chapters 5-8 and should be written while that content is fresh.

3. Background backward (**4, 3, 2**): Background chapters are written after the core to ensure they define exactly what is needed and nothing more. Writing them backward (from AQC to QC to Physics) ensures each chapter prepares precisely for what follows. Avoids over-explaining or under-explaining.

4. Formalization (**10**): Documents the Lean proofs. Best written after all mathematical content is stable, so the formalization section accurately reflects what was proven and also expresses our formalization efforts best and their usefulness.

5. Framing last (**1, 11**): Introduction and Conclusion are written last because they must reflect actual content. The Introduction previews results that exist; the Conclusion summarizes what was achieved. Writing them early leads to promises the thesis doesn't keep. Note that they are to serve as introduction and conclusion to the entire thesis (not paper or extensions or original work but rather the whole).

## On Writing

Good writing respects the reader's time and rewards their attention. It leaves them interested, curious, amused, and pulls them forwards rather than dragging them through. In that sense it is no different from art, for it too must hold conversation with the reader(s) and nourish them with perspective.

The thesis is a single path from first principles to the frontier, and it should read as one. Not eleven chapters that happen to share a binding, but a narrative where each chapter's closing question becomes the next chapter's opening tension. The pace should vary with the material. Slow and spacious when building intuition for a new concept, brisk when assembling standard machinery, suspended before a major result lands. A graduate student new to AQO should be able to learn from it. An expert should find the perspective fresh.

What makes a thesis worth reading, as opposed to merely correct, is that the reader finishes each chapter able to do something they could not do before. Not just knowing a new fact, but seeing how it connects, what it controls, where it breaks. That is the test. After every section, ask: what can the reader now predict, construct, or critique? If the answer is nothing new, the section fails regardless of how polished the prose.

The central danger for this thesis is specific: paper-voice leaking into thesis-voice. The published paper was written under page constraints, for an audience that already knew the landscape. The thesis has room to breathe. It should use that room not to pad but to teach. Every argument the paper compresses, the thesis expands until a graduate student new to adiabatic quantum optimization can follow it unaided. If the paper gives more detail on some point than the thesis does, something has gone wrong.

The hardest skill in mathematical exposition is making the reader want each definition before it arrives. Build the tension first. What are you trying to say, and why does current language fail? Only then introduce the new concept, and use it immediately. The same pattern holds at every scale. Before a theorem, say plainly what it will mean and what it will enable. After a proof, say what you actually used, which hypotheses bore weight, which were along for the ride. Do not leave a proof and move on. A proof that is merely correct teaches less than one that reveals its own structure.

None of this means softening the mathematics. Accessibility and rigor are not in tension; a vague claim is harder to learn from than a precise one. State results with explicit bounds, named assumptions, and honest scope. Never replace a precise term with an approximate one for readability, never narrow a claim to avoid explaining a subtlety, never omit the sentence that says why a result matters. If a bound has a parameter dependence, show it. If a theorem requires a hypothesis that might surprise, say so upfront.

The prose should feel written, not produced. Not textbook-appendix voice presenting facts for reference, but the voice of someone who has lived inside this subject and wants to show you what they found. Have opinions about which results matter, which lemma does the real work, where you got stuck and why. Curious, not arrogant. Vary the rhythm, a short sentence after a long one, a direct claim after a complex argument, room to breathe after a dense proof. Let transitions carry content ("the bound breaks down when the gap closes polynomially, and understanding why requires a different decomposition") rather than navigation ("we now turn to spectral analysis"). State honestly what the thesis does not achieve. Anticipate objections rather than hoping no one notices. Own judgments in first person rather than hiding behind passive hedging.

Do not signal technique. Never write "to provide intuition," just provide it. Never write "we now make a crucial observation," just make it. Do not announce what you are doing. Do it. And do not mistake depth for length. A ten-line motivated derivation beats two lines of compressed algebra when those ten lines are where the insight lives. But a ten-line derivation that could be three is just slow.

Failures in mathematical writing tend to cluster at section boundaries and around formal statements. Openings go wrong when they start cold with formalism before the reader has any reason to care; every opening must first say why we are here and what question drives this section. Middles go wrong when proofs chain without interpretation, when "it is shown that" and "it can be verified that" pile up until the prose goes lifeless, when "clearly" is used where the claim is neither clear nor easy. Closings go wrong when they stop at the QED with nothing after. Every section should land what was established and what question it opens next. Throughout, watch for pronoun fog after displayed equations, notation introduced in bulk before any of it is needed, colons and em dashes doing work that connective thought should do, nominalizations draining every verb, "recall that" where natural re-introduction would do, and bland titles that name a topic without making a claim.

On agents: iterate hard. Try an approach, test it, throw it away if it fails, try another. The one thing to guard against is invisible hallucination in notation and mathematical robustness. Verify every step as rigorously as possible, state every assumption explicitly, cite every "it is known." Everything else rewards exploration.
