# Humanize Check

## Purpose

Verify that writing reads as though a person wrote it: someone who spent months thinking about spectral gaps and adiabatic schedules, not a model that saw the prompt ten seconds ago.

A section can be technically correct, information-dense, well-structured, and utterly authorless. This test catches that.

This test never penalizes technical depth, precision, or rigor. De Wolf's thesis is the model: maximally technical and maximally human. The goal is not simpler writing. The goal is writing with someone behind it.

## Failure Modes

### 1. Voice Absence

The writing has no discernible author. Every paragraph could have been written by anyone or by no one. There is no sense of a person who chose these words because they thought hard about the subject and arrived at these particular judgments.

Signs:
- No first person where first person would be natural. Thesis writing permits and benefits from "I" and "we" with specific referent.
- No evaluative statements about the material: "this result is surprising," "the proof is more subtle than it first appears," "the connection to X took us some time to see."
- No moments where the author's specific perspective shows through: why they find one formulation cleaner than another, what they noticed that others seem to have missed, where their understanding changed.
- The text reads like an encyclopedia entry: informative, neutral, authorless. A textbook has no identifiable author. A thesis should.

This is the central failure mode. Everything else in this test is a special case or a symptom.

**Test:** Remove the author's name and all self-references. Could you tell one person wrote this, or could it be a composite stitched together from different sources? If the latter, voice is absent.

**What this is not:** Voice does not mean informality or reduced rigor. De Wolf writes with deep personal presence while proving tight query complexity bounds. Aaronson takes strong intellectual positions while stating theorems with full precision. The target is authority *with* personality, not personality *instead of* authority.

**Passing (Aaronson):** "I find it surprising that complexity theory has not influenced philosophy to anything like the extent computability theory has." A person with a position, stated directly, in first person.

**Passing (de Wolf):** "Even if the theory of quantum computing never materializes to a real physical computer, quantum-mechanical computers are still an extremely interesting idea which will bear fruit in other areas." An author who cares about his subject and says so, without grandstanding.

**Passing (de Wolf, acknowledgments):** He thanks Buhrman for being "a very creative and interminable source of interesting problems." The word "interminable" is a human choice: wry, affectionate, specific. A model writes "prolific."

### 2. Rhythmic Uniformity

AI-generated prose has a characteristic sameness. Paragraphs tend toward the same length. Sentences follow similar syntactic patterns. The pace never changes. The result is readable but monotonous.

Human academic writing varies naturally. De Wolf alternates between one-sentence observations and multi-clause definitions that unspool across several lines. Aaronson interrupts long technical passages with short punchy sentences. Harrow packs one paragraph densely, then gives a single-sentence breather. Within a section, some paragraphs are three sentences long and some are ten, because the material demands it.

**Test:** Select five consecutive paragraphs. Count the sentences in each. If all five are within one sentence of each other, suspect uniformity. Check sentence length variance within paragraphs: if every sentence falls in the 15-25 word range, the rhythm is flat.

**What this is not:** Not a license for sloppy paragraph breaks or artificially varying sentence length. The point is that real thinking produces natural variation. A section where every paragraph has exactly four medium-length sentences was probably not written by someone thinking through the material.

**Passing (de Wolf, Section 1.2.1):** Opens with a short orienting sentence, expands into a multi-clause definition, drops to a brief intuitive gloss ("Intuitively, a system in quantum state $|\phi\rangle$ is in all classical states at the same time!"), then gives the mathematical formalism. Four sentences, four different lengths, four different functions.

### 3. Lexical Tells

Certain words and phrases are statistically overrepresented in AI-generated text and rare in the human academic writing collected in `taste/`. Their presence, especially in clusters, signals generation.

**High-confidence tells** (rare in human academic prose, common in AI output):
- "delve" / "delving into"
- "landscape" (when not literal geography)
- "tapestry"
- "multifaceted"
- "underscores" (as verb meaning "emphasizes")
- "pivotal"
- "cornerstone"
- "realm"
- "Moreover" as paragraph opener
- "It is worth noting that" / "It should be noted that"
- "This serves as" / "This stands as"

**Medium-confidence tells** (common in AI, uncommon in the `taste/` references):
- "crucial" / "crucially" (Aaronson and de Wolf rarely use these)
- "robust" (outside its technical meaning)
- "nuanced"
- "facilitate"
- "leverage" (as verb)
- "a testament to"
- "shed light on"

**Test:** Flag all instances. A single medium-confidence tell is fine. Two or more high-confidence tells per section, or a cluster of medium-confidence tells, is WARN. Five or more high-confidence tells is FAIL.

**What the references use instead:** Aaronson writes "I find it surprising" not "it is worth noting." De Wolf writes "this explains the motto" not "this underscores." Harrow writes "we use" not "we leverage." Plain verbs, direct constructions.

### 4. Intellectual Engagement

The writing treats every result, definition, and proof with the same level of affect. Nothing is surprising. Nothing is elegant. Nothing is unsatisfying. The temperature is a constant 20 degrees from start to finish.

A researcher who spent a year on adiabatic quantum optimization has reactions to the material. Some results genuinely are surprising (the optimality of AQO matching Grover despite the NP-hardness of computing the schedule). Some proofs are elegant. Some open problems are genuinely frustrating. Some definitions required weeks to understand. A thesis that registers none of this is not written by that researcher.

This is not grandstanding or emoting. This is calibrated intellectual response from someone who knows the material deeply enough to distinguish the routine from the remarkable.

**Test:** In a 10-page stretch, are there zero sentences expressing a genuine reaction to the material? Zero moments of "this is the key tension," "this constraint is what makes the problem hard," "the elegance of this argument is that..."? If so, the writing is flat.

**Passing (de Wolf):** His introduction traces the history of quantum computing, notes "The following years saw only sparse activity," then pivots: interest "increased tremendously after Peter Shor's very surprising discovery." The word "surprising" is doing real work. He is telling you, as someone who knows the field, that Shor's result changed things in a way that was not predicted.

**Failing example:** "The adiabatic theorem provides a bound on the runtime. The bound depends on the minimum spectral gap. The spectral gap can be computed in certain cases." Three facts, no author. Compare: "The adiabatic theorem ties runtime to the minimum spectral gap, which in principle resolves the question of how long evolution must run. In practice the gap is rarely known, and computing it for general Hamiltonians is itself QMA-hard. This is the central tension of the field."

### 5. Absence of Intellectual History

Ideas are presented as if they arrived fully formed. The definition is stated, the theorem is proved, the result is applied. There is no sense that people had to discover these things, that earlier formulations were weaker, that the current statement emerged from a process of refinement.

Human mathematical writing, especially in theses, weaves history into exposition. Not as decoration or a "related work" box, but as explanation: knowing that the adiabatic theorem was first proved under stronger conditions, then generalized by Jansen, Ruskai, and Seiler, helps the reader understand why the current formulation has the structure it does. Knowing that Roland and Cerf's schedule was a breakthrough because earlier schedules were suboptimal tells the reader what to pay attention to in the proof.

**Test:** Does the text ever mention how concepts evolved, why earlier formulations were insufficient, or who contributed what insight? Not as a timeline but woven into the argument itself?

**Passing (de Wolf):** "The field started in the early 1980s with suggestions for analog quantum computers by Paul Benioff and Richard Feynman, and reached more digital ground when in 1985 David Deutsch defined the universal quantum Turing machine. The following years saw only sparse activity..." This is not a bibliography. It is a narrative: the field had a slow start, specific people changed its direction, the sociology of the field is part of the explanation.

**Passing (Aaronson):** His treatment of the Entscheidungsproblem traces from Hilbert through Godel, Church, and Turing, then reveals: Godel's 1956 letter to von Neumann "has become famous in theoretical computer science since its rediscovery in the 1980s." The aside about rediscovery is a human touch. Even the history has history.

**Failing:** A section on the adiabatic theorem that states the theorem, proves it, and moves on, with no mention of Kato's original work, the evolution through Jansen-Ruskai-Seiler, or why the current formulation supersedes earlier ones. The reader gets the result but not the understanding of where it sits.

## Positive Criteria

A section passes when:

1. A reader senses a specific person behind the writing: someone with a perspective, not a committee
2. Sentence and paragraph rhythm varies naturally with the material
3. The author is present: taking positions, expressing honest intellectual reactions, occasionally using first person
4. No clusters of AI lexical tells
5. The intellectual history of ideas shows through the exposition, woven into explanation rather than boxed off
6. Technical depth and precision are maintained throughout. Voice never comes at the expense of rigor

## Severity

**FAIL:** The section reads as obviously machine-generated.
- Five or more high-confidence lexical tells in a section
- Complete voice absence across an entire section (no evaluative content, no first person, no intellectual personality)
- Zero intellectual engagement in 10+ pages

**WARN:** Local issues that weaken authenticity.
- Rhythmic uniformity over 3+ consecutive paragraphs
- Medium-confidence lexical tells in clusters
- A section that would benefit from intellectual history but presents ideas as if they materialized from nothing

## Procedure

**Pass 1 (impression):** Read the section at normal speed. Does it feel like a person wrote it? Record the gut reaction before analyzing.

**Pass 2 (voice):** Look for first person, evaluative statements, honest intellectual reactions, moments of personality. Flag sections where the author is invisible.

**Pass 3 (rhythm):** Check sentence and paragraph length variation. Flag uniform stretches.

**Pass 4 (lexicon):** Scan for AI tells. Flag clusters.

**Pass 5 (history):** For sections introducing key concepts or results, check whether intellectual history is present. Flag sections that present ideas as fully formed with no context of discovery.

**Calibration:** Before running this test, read one page of de Wolf's thesis (any chapter introduction or summary) and one page of Aaronson (the introduction to any paper in `taste/`). These set the baseline for what human academic writing sounds like. The thesis need not match their quality, but it should be recognizably the same kind of thing: writing by a person, for persons, with full technical rigor intact.

## Output Format

```
FAIL: Machine-generated signals
  - ch3.tex:45-78: Entire subsection has no voice (no evaluative content, no first person, no intellectual personality)
  - ch4.tex:12: "delves into the multifaceted landscape" - high-confidence AI tell cluster

WARN: Authenticity weaknesses
  - ch2.tex:30-50: Five consecutive paragraphs of near-identical length (4 sentences each)
  - ch5.tex:100: "crucially" + "facilitates" + "robust" in same paragraph
  - ch3.tex:40-60: Adiabatic theorem introduced with no intellectual history

PASS: Section reads as human-written with full technical depth
```
