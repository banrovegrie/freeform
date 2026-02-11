Start fresh.

You are editing a thesis for writing quality. Your references for what good writing sounds like are Aaronson's papers and Harrow's papers in @taste/ and of course @CLAUDE.md. Your rules are in @WRITING.md. Your humanization diagnostic is @src/tests/agent-writer.md. Your taste diagnostic is @src/tests/check-taste.md. Read all of them before you touch anything. Feel free to also refer to @reading-report.md as well.

Here is how you will work. This is not a suggestion — this is the method.

Line by line. Start at line 1 of @src/chapters/chapter5.tex. Read each line. For each line, ask yourself: does this sentence earn its place? Is it doing real work? Does it sound like a person wrote it — someone with opinions about this material? Is the rhythm right in context of the sentences around it? Is there a better way to say this that a reader would actually enjoy?
If the line is good, move on. If it needs work, think about why it's bad before changing it. Say what's wrong in a sentence, then make the edit. Don't change things that are already working — every edit must have a reason, and "I can rephrase this" is not a reason. "This is compressed to the point of incoherence" is a reason. "This has no voice" is a reason. "This transition drops the reader" is a reason.

Specific things to watch for at line level:

- Delimiter abuse. Colons, semicolons, and em dashes used as load-bearing punctuation where a connective sentence should be. If the clause after the delimiter could be its own sentence with connective work, it should be.

- Motivation before formalism. Before every definition and every theorem, there must be a sentence in plain language saying what it captures and why we need it now. If it's missing, add it. If it's fake ("intuitively, X because X in different words"), rewrite it so a reader could predict a consequence.

- Theorem-proof deserts. After a proof ends, there should be interpretation: what did we learn, what does it rule out, how does it serve the chapter's argument. If the proof just ends and the next theorem starts, add connective prose.

- Voice. This thesis is written by someone who spent a year inside spectral gaps and adiabatic schedules. That person has reactions. Some results are surprising — the optimality of AQO matching Grover despite NP-hard scheduling is genuinely remarkable. Some proofs are elegant. Some open problems are frustrating. If the prose treats every result at the same temperature, it's flat. Add evaluative content where warranted: "this result is surprising because...," "the proof is more subtle than it first appears," "the real engine is Lemma X; Theorem Y is packaging." Use first person ("we find," "in our view") where it's natural. Don't fake it — but don't suppress it either.

- Intellectual history. When a concept has a history — the adiabatic theorem evolving from Kato through Jansen-Ruskai-Seiler, Roland and Cerf's schedule being a breakthrough because earlier ones were suboptimal — weave that into the exposition. Not as a timeline, but as explanation that helps the reader understand why the current formulation has the structure it does.

- Lexical tells. Kill on sight: "delve," "landscape" (non-literal), "multifaceted," "underscores" (as emphasizes), "pivotal," "cornerstone," "realm," "Moreover" as paragraph opener, "It is worth noting," "It should be noted." Also watch for: "crucial/crucially," "robust" (non-technical), "nuanced," "facilitate," "leverage" (as verb), "shed light on."

- Scaffolding phrases. "To provide intuition...," "The key insight is...," "Importantly," "Interestingly," "In other words." Delete the phrase. If the sentence still works, the phrase was scaffolding.

- Depth check. This thesis must exceed the source paper (@paper/v3-quantum.tex) in exposition. If a passage is thinner than the paper's treatment of the same point — less motivation, less interpretation, fewer intermediate steps — flag it and fix it.

After each section, stop. Reread the section you just edited from top to bottom. Ask:

- Does it open with motivation, not formalism?
- Does it close by handing off to the next section?
- Does it have a voice — would you know a person wrote this?
- Is the rhythm varied or monotonous? (Check: do five consecutive paragraphs have roughly the same number of sentences? Do all sentences fall in the 15-25 word range? If so, vary them.)
- Did I break anything? Did I accidentally flatten something that was already good?
- So-what test: What question does this section answer? How does the answer matter for the thesis? If I can't say, the section lacks purpose.

If the section doesn't hold together after your line edits, fix the section-level problems now before moving on. After each chapter, stop again. Reread the full chapter (skim the math, read all the prose). 

Ask:

- Does this chapter make one argument or is it a collection of results?
- Does the opening promise something the chapter delivers?
- Does the closing connect to the next chapter?
- Is there a passage where the author's perspective genuinely shows through? If not, that's a problem.
- Temperature check: Are there moments where the writing registers that something is surprising, elegant, or hard-won? Or is every result presented with identical affect? If the latter, identify the 2-3 places where a calibrated reaction would be most honest and add it.

After all five chapters (5–9), do two final passes:

- Continuity pass. Read the opening and closing paragraphs of each chapter in sequence (ch5 open → ch5 close → ch6 open → ch6 close → ... → ch9 close). Do the handoffs work? Does the reader feel carried or dropped?
- Voice pass. Pick five random paragraphs across the five chapters. Run the writer check from @src/tests/agent-writer.md on each. Report honestly.

What you must not do:

- Do not batch-edit. One line, one thought, one edit, then next line.
- Do not search for patterns (grep for colons, grep for semicolons). Read the prose. The patterns will show themselves.
- Do not add filler to create "warmth." Every word must carry information or forward motion.
- Do not flatten good passages. If something already has voice and rhythm, leave it alone even if you could rephrase it.
- Do not make edits you can't justify in one sentence.
- Do not narrate your own rhetorical moves ("we now make a crucial observation"). Just make the observation.

What you must do:

- Actually read. Not scan, not grep, not skim headers.
- Think before editing. The thinking matters more than the edit.
- Maintain mathematical correctness absolutely. Every equation, bound, and theorem statement is untouchable unless there is a genuine error.
- Build voice through specific moves: first person, evaluative statements, intellectual history, calibrated reactions to the material.
- Check depth against the paper. The thesis must always be the richer document.

Begin with chapter 5, line 1. Take your time.

NOTE: make sure that the idea is to make the writing richer and more engaging.

Additional NOTE: Keep the math descriptions faithful to the math. The most dangerous edits are not in equations but in the English sentences that describe equations. The $K'(s)$ inversion was a verbal error in the original, but a prose pass could just as easily introduce one. After rewriting any sentence that paraphrases a formula, re-derive the paraphrase from the formula. "Shorter" is not the same as "correct."

Do not narrow correct claims. "No prior knowledge" is stronger than "no prior spectral knowledge." When tightening prose, check whether you accidentally added a qualifier that restricts a true statement. The instinct to be precise can overshoot into being wrong.

Do not reframe the author's positioning. "Edge" vs "catch," "results" vs "claims" -- these are not style choices, they are intellectual stance. A prose agent should treat framing words (contribution, limitation, obstacle, feature, edge, catch, caveat) as load-bearing. Changing them changes what the thesis argues, not how it argues it.

Do not cut explanatory content that the thesis guidelines demand. CLAUDE.md says "exceed the paper in exposition depth." A prose pass that shortens everything uniformly will cut the exact passages that distinguish a thesis from a paper. Before deleting a sentence, ask: does this explain why something is true, not just that it is true? If yes, keep it.

Flag what you fixed. The $K'(s)$ correction was real and valuable. But it was silent. A future agent should leave a comment or note when a prose edit also fixes a substantive error, so the author can verify the fix independently rather than discovering it buried in a 200-line diff.

Preserve deliberate rhetorical structure. The Chapter 9 triple was not an accident of verbose writing. It was a constructed device. Before flattening parallel constructions, repeated phrasings, or structured enumerations, consider whether they serve a navigational purpose. Not all repetition is waste.
