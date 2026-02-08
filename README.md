# Unstructured Adiabatic Quantum Optimization

My master's thesis on Unstructured Adiabatic Quantum Optimization, supervised by Shantanav Chakraborty. Built on the published paper [Unstructured Adiabatic Quantum Optimization: Optimality with Limitations](https://arxiv.org/abs/2411.05736) (Braida, Chakraborty, Chaudhuri, Cunningham, Menavlikar, Novo, Roland, 2025).

Make sure that the way this thesis would be written is satisfactory to Prof. Shantanav Chakraborty (check `taste/` for papers by him). We also aim to beat the baseline expectations of the theses we have with us in `taste/` (of Zeeshan Ahmed and Ronald de Wolf).

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

Detailed chapter sketches for the remaining unwritten chapters (1, 2, 3, 4, 9, 10, 11) are in [`CHAPTERS.md`](CHAPTERS.md).

## On Writing

One must imagine the writer at work. The cycle is always the same: study, think, act, reflect, begin again. There are no shortcuts. To do something new, one must know the old intimately, and then be willing to betray it.

Writing is the act that makes the rest visible. A proof in a notebook changes nothing. A proof that others can follow changes the field. Good writing is about holding a conversation with the readers and nourishing them with perspective. The conversation is the questions they actually have. The nourishment is how your answers rearrange what they see.

A thesis is not a diary of labor. It is an experience designed to end in understanding. When it works, the reader finishes able to predict what happens when parameters shift, what breaks when assumptions weaken, where the real obstacles hide. This is the only honest measure: not what the writer did, but what the reader can now do.

Every thesis needs a spine --- a few questions that determine the order of everything else. Without this, you default to chronology or taxonomy: locally readable, globally dead. The difference between a thesis and a stack of results is the spine.

Before writing anything, write one page. Name the tension: what you want to prove and what obstructs you. State what is fixed and what you control. State the main results with explicit hypotheses. Say what changes because they hold. One sentence per chapter, naming its question. If you cannot write this page, the thesis does not exist yet. Writing the page forces the decision.

Then say the rules. What you will and will not do. Where you are headed. Readers who see the destination read proofs differently --- they allocate attention, forgive necessary detours, and recognize when you are stalling.

Build a skeleton before prose. Each chapter's question. The definitions its claims require. The theorems with hypotheses. The lemmas each theorem needs. Unused background means the story wandered.

Definitions come from failure. You try to state your goal and find the language insufficient. You introduce the smallest concept that clears the obstruction. Use it immediately. A definition that sits unused for pages arrived too early.

Exposition needs two passes. First explain plainly: what the statement means, what the parameters control, what the theorem lets you do that you could not do before. Then state and prove. The plain pass cannot be vague. Readers should be able to predict the scaling before seeing algebra.

A proof is not scratchwork but a guided path. State the strategy upfront. Decompose into lemmas matching logical moves, not algebraic accidents. Mark where the key inequalities enter. After proving, say what you actually used. Readers learn structure by seeing which assumptions bear weight.

Clarity is correctness. Ambiguous prose plants false theorems in the reader's mind. Short sentences. Write for intelligence that is not inside your head. A paragraph requiring rereading is not deep; it is unfinished. Rewriting is thinking.

Revise in passes. Structure: align the order of sections with the order of dependencies. Clarity: each paragraph advances the argument. Precision: replace vague words with explicit conditions. Style: cut scaffolding. If a sentence does no work, delete it.

Write out of order. Begin where you are surest. Introduction last. Written early, it promises what later chapters may not deliver.

Sometimes the spine does not hold. The proof stays broken. The theorem you wanted is false. This is not failure of effort but discovery of terrain. Document what you learned. The thesis that honestly maps a dead end serves the field better than the thesis that pretends the path was always clear.

Agents generate fast and err without grounding. They simulate understanding without possessing it. Asking for pages and hoping they are true is the fastest way to destroy a thesis. Give them artifacts: the one-page story, a theorem skeleton, claims paired with proofs. Feed sources and demand lifted statements, not invention. Require explicit assumptions, named failure modes, forward references. Reject "it is known" without pointers. You may outsource production. You cannot outsource judgment.

The only question that matters is what the reader can do afterward that they could not do before. When you doubt a section, ask this. If the answer is nothing, delete it. What remains after the cutting is the work. The cycle begins again.

### Summary

The writing should:

- Read as though written by someone who spent months inside the problem — with opinions about which results matter, who knows where they got stuck, which lemma is the real engine and which theorem is packaging
- Make an argument, not catalog results — the chapter title is the claim, each experiment is evidence in that argument, and the reader should feel the thread connecting them
- Be specific and concrete — state exact bounds, name techniques, give scalings. A person who did the work knows the numbers
- Build intuition before formalism: the concrete example that makes the reader want the abstraction, then the abstraction as relief not overhead
- Separate the intuitive story from full technical detail when both are needed, and be explicit about which you're doing
- Slow down where the actual insight lives and compress routine verification — taste is knowing which is which
- Make definitions and proofs illuminate, not just verify — why this is the right definition, what goes wrong otherwise, what the proof teaches beyond the truth of the statement
- State what it doesn't achieve as clearly as what it does — gaps, limitations, failed approaches presented with the same care as results
- Anticipate objections head-on ("there is a catch, though") rather than hoping the reader won't notice
- Carry content in transitions: what changed, what we now know, what question that opens
- Distinguish contributions from tools — say plainly when using a known technique, slow down when doing something new with it
- Own editorial judgments in first person ("in our view," "as we see it") — the alternative is passive hedging where no one seems responsible for the claims
- Treat notation as interface design: consistent across chapters, never introduced for single use
- Say each thing once, well — not restated across introduction, body, and conclusion in three slightly different phrasings
- Vary the rhythm — short sentence after long, direct claim after complex argument, informal aside after formal passage
- Let negative results in when they sharpen understanding of why the approach that works is the right one
- Let moments of genuine surprise land — sparingly, without decoration, only when warranted

The writing should NOT have:

- Structure failures: no coherent narrative arc, premature formalism, uniform template and pacing regardless of the material, equal weight given to everything when some results are harder and some contributions more significant
- Rigor failures: hand-waving past the hard parts, appearing complete while eliding the most interesting pieces, shallow or circular motivation ("X is important because X is widely studied"), over-attribution to convention, vague claims hedged into vapor where a clean claim with stated conditions would serve
- Voice failures: signaling rather than showing, narrating its own rhetorical moves ("we now make a crucial observation"), hedging filler where insight should be ("it is worth noting"), treating a surprising result and a routine calculation at identical emotional temperature, sycophantic citation language ("the seminal work of") — just state the result and cite it, symmetric treatment of related work where every citation gets the same template
- Taste failures: throat-clearing openings that could appear in any thesis on the topic, redundant previews of what's two paragraphs away (chapter-level orientation is fine — section-level "we will now show" is not), generic transitions carrying no content, notation introduced once and never reused, rhythmic monotony — uniform sentence structure, paragraph length, and register — that reads as generated rather than written

The standard is simple: correctness, completeness, and depth that remains accessible. No hallucinated mathematics, no hedged claims standing in for real ones, no cheap prose: the kind that signals effort without containing any. The reader should finish each chapter able to do something they could not do before.

Any piece of writing (irrespective of origin or whether it is generated) can be good writing if and only if it holds a conversation with the reader and leaves them nourished with perspective, not just information.

What survives revision against that test is the thesis we intend to write.
