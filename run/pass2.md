# Pass 2: Taste and Humanization Review

Calibration: Read de Wolf (Chapter 1-2 introductions, acknowledgments), Aaronson (introductions from taste/), and taste/README.md style notes before analysis.

## Pass 1: Impression

Chapters 5-8 read as strong technical writing by someone who knows the material. The running example (Grover, M=2) recurs across all four chapters, accumulating meaning exactly as de Wolf does with OR/PARITY/MAJORITY. The arc is coherent: framework (Ch5), proofs (Ch6), runtime (Ch7), hardness (Ch8). The prose is dense without being ornamental. Several passages land with real intellectual force -- the opening of Ch8 ("the adiabatic algorithm is fast, provided someone has already done the slow part") and Ch6's geometric explanation of why the naive resolvent line fails both feel like they came from someone who thought hard about the problem.

However, the voice is intermittent. Long stretches read as excellent exposition-by-committee rather than exposition-by-a-person. The author is visible when explaining why something works or fails, but invisible during the mechanical setup and proof machinery. A reader would sense competence throughout but personality only in bursts.

Gut reaction: human-adjacent. Better than most AI output by a wide margin. Not yet at de Wolf's level of sustained authorial presence.

## Pass 2: Voice

### First person

Zero instances of "I" or "we" (with specific referent) across all four chapters. This is the single largest voice deficit. A thesis permits and benefits from first person:
- "We prove both lemmas" (ch6:8) uses "we" but it's the generic mathematical "we," not a person speaking.
- Ch8:207 says "The results of this section are contributions of this thesis" -- the closest thing to an authorial statement, but still avoids "I" or "we."

Compare de Wolf: "Even if the theory of quantum computing never materializes to a real physical computer..." -- he takes a personal stance. Compare Aaronson: "I find it surprising that complexity theory has not influenced philosophy..." -- he names himself as the person with the reaction.

### Evaluative statements (good -- these exist)

- ch5:13 "The answer in full generality is yes, but with complications" -- person with a view
- ch5:88 "The spectral parameters are trivial in this case, which is precisely why the Roland-Cerf analysis is simple" -- judgment call
- ch6:97 "Bounding the spectral gap to the right of s* is the main technical challenge of this chapter" -- honest assessment
- ch6:127-129 "The failure has a geometric explanation" followed by the explanation -- this is excellent: the author saw something fail, understood why, and tells the reader
- ch6:271 "The bound is conservative by a factor of approximately 30 but correctly captures the linear growth. This constant is the price of a clean, uniform bound" -- honest about tradeoffs
- ch7:193 "The algorithm wastes time far from the crossing" -- direct, evaluative
- ch8:3 "the quadratic speedup becomes conditional: the adiabatic algorithm is fast, provided someone has already done the slow part" -- punchy, opinionated
- ch8:364-366 "This asymmetry raises a precise question... Does the information cost represent a fundamental limitation, or can it be circumvented?" -- genuine intellectual tension

### What's missing

- No moments of "this result surprised us" or "the connection to X took time to see"
- No stated preference for one proof technique over another beyond functional reasons
- No personal perspective on open problems (e.g., "I suspect the interpolation barrier is fundamental" vs. the neutral "The barrier does not rule out #P-hardness by other means")
- The author never reveals where their own understanding changed

Verdict: Evaluative content is present and distributed across all four chapters. But the evaluations are always about the mathematics ("this bound is conservative"), never about the author's experience with the mathematics ("this bound took us three attempts to tighten"). First person is completely absent.

## Pass 3: Rhythm

### Paragraph length variation

Good. Chapters vary naturally between 2-sentence and 8-sentence paragraphs. Ch5's opening has a 4-sentence paragraph followed by a 5-sentence one followed by a 3-sentence one. Ch6 alternates between proof blocks (long) and interpretive paragraphs (short). Ch8's opening is a particularly strong rhythm: long setup paragraph, then the compact restatement of the runtime formula, then the precise "makes this dependence explicit" paragraph.

### Sentence length variation

Adequate but somewhat uniform within paragraphs. Most sentences fall in the 20-35 word range. There are too few very short sentences (under 10 words) that would provide rhythmic contrast.

Counterexamples (good variation):
- ch6:129 "The line must start with O(g_min) separation from both eigenvalues at s*." -- short, punchy, after long explanation
- ch8:3 sentence fragment "provided someone has already done the slow part" -- effective rhythm break

But many paragraphs have 4-5 sentences all roughly the same length. For example, ch5:92-93 (lines 92-93) has four medium-length sentences in a row with similar syntactic structure (subject-verb-object, subject-verb-object).

Verdict: Inter-paragraph variation is natural. Intra-paragraph sentence variation could be stronger. Not a FAIL -- more a missed opportunity for de Wolf-style rhythm shifts.

## Pass 4: Lexicon

### High-confidence AI tells

None found. Zero instances of: delve, tapestry, multifaceted, underscores (as "emphasizes"), pivotal, cornerstone, realm, "Moreover" as paragraph opener, "It is worth noting that," "This serves as."

### Medium-confidence AI tells

- "complexity landscape" (ch8:333) -- borderline; this is standard terminology in complexity theory, not the metaphorical "landscape" the test flags
- No instances of: crucial/crucially, robust (non-technical), nuanced, facilitate, leverage (as verb), "a testament to," "shed light on"

### What the chapters use instead

Plain verbs throughout: "gives," "shows," "yields," "reduces to," "follows from," "captures." Direct constructions: "The bound is conservative" not "the bound underscores the conservative nature." "The failure has a geometric explanation" not "this sheds light on the geometric underpinnings."

Verdict: CLEAN PASS. The lexicon is free of AI tells. The vocabulary matches the taste references.

## Pass 5: Intellectual History

### Chapter 5

Strong. Roland-Cerf, Farhi et al., Znidari/Horvat, and Hen are all cited with what they proved and why it matters. The technique lineage (spatial search -> AQO) is explicitly stated at ch5:243. The opening traces the progression from single-marked-item to general Hamiltonians, placing the thesis work in context.

### Chapter 6

Adequate. The resolvent approach is placed in the Childs-Goldstone / Chakraborty lineage (ch6:116). Sherman-Morrison is cited. But the chapter doesn't explain why the variational principle was the natural first attempt, or how the community arrived at the resolvent approach for rank-one perturbations. The techniques appear somewhat fully-formed.

### Chapter 7

Good. Jansen-Ruskai-Seiler, Roland-Cerf, Boixo-Knill-Somma, Cunningham-Roland, and Elgart-Hagedorn are all cited with what they contribute and how they relate (ch7:46). The progression from constant-rate to local to adaptive is presented as an intellectual arc, not just a list of results.

### Chapter 8

Strong. Valiant's #P-completeness is placed in context (ch8:125). The connection to boson sampling and random circuit sampling hardness proofs (ch8:255) is excellent -- it shows the author recognizes the structural similarity across subfields. Le Cam's two-point method and the Heisenberg limit are both properly situated. The interpolation barrier discussion (Sec 8.3) explicitly connects proof technique limitations across quantum computing.

Verdict: History is present and functional across all chapters. It explains why techniques were chosen and how the field arrived at current formulations. Could be deeper in Ch6 (the chapter that would benefit most from explaining how the resolvent approach was discovered). Overall above the WARN threshold.

# Aggregate Results

**WARN: Voice deficit**
- ch5-ch8: Zero first-person usage across 1581 lines of thesis. A thesis should have "I" or "we" (with specific referent) where the author takes a position, makes a choice, or expresses a reaction. Currently all evaluative statements use impersonal constructions ("The bound is conservative," "The failure has a geometric explanation"). Compare de Wolf: "Even if the theory of quantum computing never materializes..." Compare Aaronson: "I find it surprising..."

**WARN: Intellectual engagement is present but externally directed**
- ch5-ch8: The author evaluates the mathematics (what's hard, what's tight, what's conservative) but never reveals their own experience. No "this took us time to see," no "the connection to spatial search was not obvious," no "I suspect the barrier is fundamental." The writing has opinions about results but not about the process of arriving at them.

**WARN: Sentence rhythm slightly uniform**
- ch5:67-99, ch7:306-370: Stretches where most sentences fall in the 20-35 word range without short punchy breaks. Not a FAIL (paragraph-level variation is good) but misses the rhythmic contrast that de Wolf achieves with one-sentence observations between multi-clause definitions.

**PASS: Lexicon**
- Zero high-confidence AI tells across all four chapters
- Zero medium-confidence AI tells
- Plain verbs, direct constructions throughout

**PASS: Intellectual history**
- Techniques attributed and placed in lineage across all chapters
- Connections to broader field (boson sampling, spatial search)
- Running example accumulates meaning across ch5-ch8

**PASS: Intellectual engagement (partial)**
- Evaluative statements distributed across all chapters
- Honest about tradeoffs (ch6:271 on the factor-30 bound)
- Genuine tension in ch8 closing
- Ch8:3 "provided someone has already done the slow part" is the single best authorial moment in these four chapters

**PASS: Running example**
- Grover (M=2) checked at every major result, serving as both calibration and teaching tool. Exactly the de Wolf pattern.

# Summary

Chapters 5-8 are technically strong, lexically clean, historically grounded, and structurally sound. The running example is used masterfully. The writing is better than most thesis prose and far better than typical AI output.

The primary deficit is voice: the author is visible as a competent expositor but not as a specific person. First person is absent. The intellectual reactions are real but always directed outward (at the mathematics) rather than inward (at the author's experience of doing the mathematics). A reader finishes these chapters knowing what the results are and why they matter, but not who proved them or what it felt like to work through the proofs.

The fix is surgical, not structural. The chapters do not need rewriting. They need:
1. A handful of first-person statements where the author takes a position (5-8 across all four chapters)
2. 2-3 moments where the author reveals their experience: what surprised them, what was harder than expected, what connection they didn't initially see
3. Occasional short (under 10 word) sentences for rhythmic contrast in the longer expository stretches
