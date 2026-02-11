# Chapters 2-4: Physics, Quantum Computation, Adiabatic Quantum Computation

## Context

You are writing three foundational chapters of a master's thesis on
Unstructured Adiabatic Quantum Optimization (Alapan Chaudhuri, supervised
by Shantanav Chakraborty). The thesis is built on the published paper
`paper/v3-quantum.tex` (arXiv:2411.05736).

These chapters teach everything the reader needs to follow Chapters 5-9.
A reader who finishes Chapter 4 should be able to state the AQO problem
precisely, know why the spectral gap matters, understand what Roland-Cerf
achieved, and feel why generalizing it is the hard part. The reader should
want to keep reading.

Any piece of writing, irrespective of origin, can be good writing if and
only if it holds a conversation with the reader and leaves them nourished
with perspective, not just information.


## The Narrative Arc

Chapters 2-4 tell a single story in three movements.

The first movement establishes that nature computes, and some computations
are hard. Ground states of physical systems encode solutions to optimization
problems, and the distinction between easy and hard is captured by
complexity classes (P, NP, #P) that Chapter 8 will use to prove concrete
impossibility results. Classical approaches to hard optimization (simulated
annealing, local search) hit barriers that have physical explanations:
rugged energy landscapes, exponentially many local minima, the need to
cross energy barriers. The movement ends with a question that has been
building: could quantum mechanics, which allows tunneling and superposition,
do better?

The second movement answers partially. Quantum computation does give
provable speedups for certain problems. The circuit model, BQP, and
Grover's algorithm establish that unstructured search admits a quadratic
quantum speedup, and BBBV proves this is tight. Grover's algorithm has a
geometric heart: rotation in a 2D subspace by an angle proportional to
$1/\sqrt{N}$. This geometry will reappear at the avoided crossing in
Chapter 5, so the reader must see it clearly here. But the circuit model
solves search, not optimization-by-evolution. Something different is
needed.

The third movement introduces adiabatic quantum computation: encode the
problem in a Hamiltonian, start in an easy ground state, evolve slowly,
and read off the answer. The adiabatic theorem makes this rigorous, the
spectral gap controls the runtime, and Roland-Cerf proves it can match
Grover for a single marked item. But generalizing beyond a single marked
item is where the difficulty lives. The gap depends on the full spectral
structure of the problem Hamiltonian, computing it is QMA-hard, and the
optimal schedule requires exponential-precision knowledge of a parameter
($A_1$) that is NP-hard to estimate. This is the tension Chapter 5 inherits.

The arc must feel inevitable, not constructed. Each chapter should make
the next feel necessary.


## Phase 0: Read Everything

Before planning or writing, read all of the following. You need the
technical content to write correctly, the voice to write well, and the
tests to self-evaluate.

### Source material
- `paper/v3-quantum.tex` -- the published paper, source of truth for all math
- `citations/guo2025adiabatic.tex` -- paper citing ours; their treatment
  of the QAT with general scheduling, power-law scheduling, and the measure
  condition is relevant context for Chapter 4
- `references/README.md` -- index of available references for citations

### Existing chapters
- `src/chapters/chapter5.tex` through `chapter9.tex` -- read all of them.
  Chapter 5 is the voice standard. Notice how it opens, how it takes
  positions, how it weaves history, how it uses M=2 (Grover) as a running
  example checked at every result. Write in this register from the start.
  Do not write flat prose and plan to add personality later.
- `src/chapters/chapter10.tex` (first 40 lines) -- notice how it opens
  honestly about what the chapter contributes and what it does not

### Writing and style
- `CLAUDE.md`, `WRITING.md`, `README.md` -- internalize these. They
  contain the writing principles. The prompt below does not repeat them.
  The principles are not a checklist. They describe what good writing
  does. Let them inform how you think about sentences, not how you audit
  them.

### Tests
- `src/tests/check-math.md` -- canonical notation. Every symbol ch2-4
  introduces must be consistent.
- `src/tests/check-taste.md` -- prose quality failure modes
- `src/tests/check-format.md` -- formatting rules
- `src/tests/agent-writer.md` -- voice and authenticity. Read the
  failure modes and the passing examples (de Wolf, Aaronson).
- `src/tests/agent-reviewer.md` -- holistic peer review criteria

### Baselines and calibration
- `taste/zeeshan_ms_thesis.md` (first 100 lines) -- the quality floor.
  Functional but thin background, front-loaded definitions, no voice.
  We must clearly exceed this.
- `taste/README.md` -- style analysis of reference authors
- `run/pass2.md` -- review of chapters 5-8. They scored well on lexicon
  and intellectual history but were warned for voice deficit (no first
  person, evaluations only about mathematics not the author's experience,
  some rhythmic uniformity). Read this to understand what worked and what
  to watch for. Do not mechanically insert first-person phrases to fix
  this; let voice emerge from genuine engagement with the material.


## Phase 1: Plan

Use `/planning-with-files:plan`. The plan must cover:

### Spine
Name the tension for each chapter. What question drives it? What does the
reader gain? One sentence per chapter naming the claim. The suggestions
in the Narrative Arc above are a starting point, not a constraint.

### Writing order
Write backward: `chapter4.tex` first, then `chapter3.tex`, then
`chapter2.tex`. Background chapters written after the core define exactly
what is needed. Writing them backward ensures each chapter prepares
precisely for what follows.

### Notation plan
List every symbol chapters 2-4 will define. Cross-check against
`check-math.md`. Symbols defined in ch5-9 must not be redefined
differently.

### Forward-reference map
For each definition and result in ch2-4, list where it is first used in
ch5-9. If nothing downstream uses it, question whether it belongs.

### Section plan
For each chapter: the sections (3-5 per chapter, not more), what each
teaches, what definitions it introduces, what it needs, what it feeds
forward. The outline at the bottom of this file is a suggestion. Depart
from it if you find a better structure through thinking about the
material.

### Citation plan
Key references for each section from `references/`. Engage with cited
work. Do not just drop reference numbers.


## Phase 2: Write

Write all three chapters as complete LaTeX files in `src/chapters/`.
Order: `chapter4.tex`, `chapter3.tex`, `chapter2.tex`.

The writing principles live in `CLAUDE.md`, `WRITING.md`, and `README.md`.
What follows here is specific to these three chapters.

### What Chapter 5 needs

Chapter 5 opens with these assumptions:
```
% ASSUMES: Chapter 3 defines Hilbert space, qubit, Hamiltonian, eigenvalue,
%   eigenvector, spectral gap, spectral decomposition, unitary, measurement,
%   BQP, Grover's algorithm and its optimality.
% ASSUMES: Chapter 4 defines AQC, adiabatic theorem, spectral gap as
%   computational resource, avoided crossings, local/adaptive schedules,
%   Roland-Cerf construction.
```

These are hard constraints. Chapter 5 also opens with: "In the circuit
model, unstructured optimization is already understood." Chapter 4 must
arrive at exactly the tension that makes this opening land.

### Chapter 4: Adiabatic Quantum Computation

Write this first. It is the most technically constrained.

A reader finishes this chapter understanding: adiabatic quantum computation
encodes optimization problems in Hamiltonians and solves them by slow
evolution; runtime is controlled by the spectral gap; the Roland-Cerf
schedule achieves the Grover speedup for a single marked item; and
generalizing beyond this is the central challenge the thesis addresses.

The chapter needs to cover the adiabatic theorem quantitatively (the
Jansen-Ruskai-Seiler form, since Chapter 7 uses a simplified version),
avoided crossings and Landau-Zener as physical intuition for the
bottleneck, the Roland-Cerf construction as the first AQO achieving
$\sqrt{N}$, AQC universality (brief, Aharonov et al. 2007), why AQO is
more restricted than general AQC (diagonal $H_z$, projector $H_0$), and
the no-free-lunch tension.

The Guo et al. paper (`citations/guo2025adiabatic.tex`) gives a clear
treatment of the QAT with general scheduling functions and shows how
nonlinear scheduling improves gap dependence from $O(1/\Delta^2)$ to
$O(1/\Delta)$. This is relevant context. Our paper uses a local adaptive
schedule; their approach is complementary.

Key sources: Farhi et al. (2001), Roland-Cerf (2002), Jansen-Ruskai-
Seiler (2007), Aharonov et al. (2007), Born-Fock (1928), Kato (1950),
Landau-Zener, van Dam-Mosca-Vazirani (2001).

### Chapter 3: Quantum Computation

A reader finishes this chapter understanding quantum states, Hamiltonians,
measurement, time evolution, the circuit model, query complexity, BQP,
and Grover's algorithm with its optimality proof.

The geometric picture of Grover (rotation in the 2D subspace
$\text{span}\{|w\rangle, |s\rangle\}$ by angle $\theta \sim 1/\sqrt{N}$)
is critical. Chapter 5's avoided crossing works in a 2D subspace of the
symmetric space with the same geometric structure. A reader who sees
Grover's geometry clearly will recognize it when it reappears. This
connection is part of the narrative thread, not a footnote.

The spectral gap should be defined cleanly here. It is the central object
of the entire thesis.

Key sources: Nielsen-Chuang, Sakurai, Arora-Barak, Grover (1996),
BBBV/Bennett et al. (1997), BBHT (1998).

### Chapter 2: Physics and Computation

Write this last. Introductions are best written after you know what they
introduce.

A reader finishes this chapter understanding that ground states encode
optimization solutions, that complexity classes quantify hardness (and
Chapter 8 will use P, NP, and #P for concrete results), and that
adiabaticity is a computational strategy. The chapter should make quantum
computation feel like a natural next step, not a bolt-on.

Keep philosophy brief. The complexity definitions (P, NP, NP-complete,
NP-hard, #P, reductions) must be precise because they bear weight later.
Be honest about what classical methods can and cannot do.

Key sources: Arora-Barak, Sipser, Valiant (1979) for #P, Griffiths,
Barahona (1982) for Ising NP-hardness.

### On mathematical correctness

Import math directly from `paper/v3-quantum.tex` where it appears. Do
not invent notation or hallucinate formulas. Use the canonical notation
from `check-math.md`. These chapters introduce standard material, but the
specific notation choices must be consistent with what chapters 5-9
already use.

### On depth and running examples

The thesis must exceed the paper in exposition depth, motivation, and
accessibility. These are background chapters but they are not disposable.
They set the reader's trust. A definition that appears without motivation,
a theorem stated without interpretation, a section that could be deleted
without information loss -- these erode trust before the hard chapters.

Chapters 5-8 use Grover/M=2 as a running example checked at every major
result. Chapters 2-4 should plant this. Introduce unstructured search
early and return to it: as a complexity example (Ch2), as a quantum
algorithm (Ch3), and as the first AQO success (Ch4). By the time the
reader reaches Chapter 5, Grover should feel like an old friend whose
generalization they are now ready to understand.


## Phase 3: Test and revise

Run all tests against each chapter, fix issues, and re-test. Loop until
stable. This is the multi-pass core of the process.

For each of `chapter2.tex`, `chapter3.tex`, `chapter4.tex`, run:

1. `src/tests/check-format.md`
2. `src/tests/check-math.md`
3. `src/tests/check-taste.md`
4. `src/tests/agent-writer.md`

Record results in `progress.md` with specific line references.

Fix every FAIL. Fix WARNs where the fix is clear. Re-run the tests.
Repeat until no FAILs remain.

Priority: mathematical correctness first, then motivation and depth,
then prose quality, then voice and rhythm.


## Phase 4: Coherence and polish

### Cross-chapter coherence

Read chapters 2, 3, 4, and 5 together sequentially. Check:

- Does each chapter's ending set up the next chapter's opening?
- Does Chapter 4's conclusion land at the tension Chapter 5 picks up?
- Are definitions used before they are needed downstream?
- Any redundancy? (Hermitian, unitary, spectral gap: define once.)
- Does Grover appear in all three chapters and accumulate meaning?
- Is notation consistent across all four chapters?

Fix coherence issues.

### Quality check

Run `src/tests/agent-reviewer.md` against each chapter. Target: Weak
Accept (6.5+) or above on all dimensions. If anything scores below 6,
identify the specific problem, fix it, and re-run.

Compare against `taste/zeeshan_ms_thesis.md`. The writing must be clearly
superior in depth, motivation, voice, flow, and accessibility. If any
dimension is not clearly better, fix the specific sections.

### Final test

Run all tests one last time. Record final results in `progress.md`.
Standard: zero FAILs.


## What "Done" Looks Like

Three complete LaTeX chapter files in `src/chapters/`. All tests pass.
The chapters flow as a single arc into Chapter 5's existing opening.
Chapter 5's ASSUMES comments are fully satisfied. The writing is
mathematically correct, well-motivated, sufficiently deep, and reads
like it was written by someone who cared about the material. A reader
finishing Chapter 4 can state the AQO problem and wants to see what
happens next. `progress.md` documents the test results across rounds.


## Suggested Outline (starting point, not a constraint)

Depart from this if the material suggests a better structure. The right
structure is the one where each section feels necessary and the order
feels inevitable.

### Chapter 2: Physics and Computation
- Computation and Complexity
- Physics, Energy, and Optimization
- Adiabaticity and the Quantum Possibility

### Chapter 3: Quantum Computation
- Quantum Mechanics for Computation
- The Circuit Model and Query Complexity
- Grover's Algorithm and Its Optimality

### Chapter 4: Adiabatic Quantum Computation
- The Adiabatic Theorem and Its Consequences
- Schedules and the Roland-Cerf Construction
- Universality, Restrictions, and the Central Tension


## Reminders

- Writing order is 4, 3, 2.
- Chapter 5 already exists. Read its opening before writing Chapter 4's
  conclusion.
- Do not re-define terms from earlier chapters. Check `check-math.md`.
- Import math from `paper/v3-quantum.tex`. Do not invent formulas.
- The voice standard is Chapter 5. Match it from the start.
- The central danger is paper-voice: compressed, telegraphic prose that
  made sense under a page limit but has no excuse in a thesis.
- Check `src/references.bib` for existing BibTeX keys before citing.
  Add entries for any new references you introduce. Use keys from
  `references/README.md` where available.
- After writing, run `make` in `src/` to verify LaTeX compilation.
  Fix any errors before moving to the test phase.
- This is a marathon. Multiple passes. Each one should make the chapters
  better.
