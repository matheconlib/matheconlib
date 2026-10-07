# Lean 4 and `MathEconLib` — A Beginner's Manual

## Status of this document

This manual was written by Moran Koren (@morankor) as a standalone document,
and is reproduced here with editorial corrections: link paths rewritten
relative to `docs/`, stale counts refreshed and dated, a new §4.0 on the
module-system lines a reader meets at the top of the first real file, an
architecture appendix, reading list and glossary updated for the layers added
since, a pointer to `CONTRIBUTING.md` in place of a partial restatement of it,
and a few typos.

Its runnable snippets are collected in
[`MathEconLibTest/Manual/HandsOn.lean`](../MathEconLibTest/Manual/HandsOn.lean),
which `lake build` compiles, so a snippet that stops working turns the build
red rather than quietly rotting in the prose.

## Preface

### Who this manual is for

You are comfortable with mathematics (functions, sets, calculus, a little probability) and you have never written a line of Lean. You may or may not know auction theory; **this manual does not assume you do.** Where economic vocabulary appears, it is explained on the spot, and [Appendix A](#appendix-a--glossary-of-auction-theory-terms) collects the terms in one place.

You do not need prior experience with functional programming, type theory, or any other proof assistant. If you have written a little Python, that will help you read the code blocks, but nothing more is assumed.

### What you will be able to do afterwards

By the end you should be able to open a real file in the `MathEconLib` library, read it, and follow what it claims and roughly how it proves it. You will not yet be able to write substantial proofs; that takes practice, and [Part 8](#part-8--exercises) starts you on it. But the syntax will have stopped being an obstacle.

### How this manual is organised

The material is arranged so that nothing is used before it is explained.

| Part | What it covers | Skip if… |
| --- | --- | --- |
| [0](#part-0--working-with-lean-on-your-mac) | Getting Lean running on a Mac, and the editor loop | it already works for you |
| [1](#part-1--why-formalise-mathematics-at-all) | Why anyone formalises mathematics | you are already convinced |
| [2](#part-2--a-syntax-primer) | The punctuation and symbols of Lean | you have written Lean before |
| [3](#part-3--the-one-big-idea-propositions-are-types) | **The central idea.** Read this one properly | never |
| [4](#part-4--reading-a-real-file) | A guided tour of an actual `MathEconLib` file | — |
| [5](#part-5--watching-a-proof-happen) | A proof built one step at a time | — |
| [6](#part-6--traps-for-beginners) | Traps that cost beginners hours | — |
| [7](#part-7--reference-tables) | Lookup tables | it is reference material |
| [8](#part-8--exercises) | Exercises, with full solutions | — |
| [A](#appendix-a--glossary-of-auction-theory-terms) | Economics vocabulary | you are an economist |
| [B](#appendix-b--how-matheconlib-is-organised) | The library's architecture | you only want the Lean |

A practical suggestion: do Part 0 at the computer, read Parts 1–3 away from it, then return to the machine for Parts 4–5. Part 3 is the part that matters. Everything else is either preparation for it or consequence of it.

### A note on the code

Every Lean snippet here was compiled against `MathEconLib` at Lean `v4.28.0`. Where a snippet is meant to fail, it was checked that it fails, and the error quoted is the real one. If something does not typecheck for you, the likeliest cause is that the library or the Lean version has moved on. Please let us know.

### ✍️ A note on the hands-on blocks

Every section ends with a block marked ✍️. These are not decoration. Reading about a proof assistant teaches you very little; five minutes of typing teaches you a lot. Several blocks ask you to **break working code deliberately** and read the resulting error, which is where most of the learning happens.

All of them are collected, ready to run, in [`MathEconLibTest/Manual/HandsOn.lean`](../MathEconLibTest/Manual/HandsOn.lean). That file is compiled by the ordinary `lake build`, so it cannot drift away from the manual without turning the build red. Examples meant to fail sit commented out, each labelled with the error you should see on uncommenting. Copy what you want into a scratch file of your own rather than editing it in place.

---

## Part 0 — Working with Lean on your Mac

Lean is not a language you run. There is no moment where you type `./myproof` and watch it go. Instead you keep an editor open and Lean runs continuously beside you, re-checking as you type and reporting, at whatever point your cursor sits, exactly what remains to be proved. Getting that loop working is the first job, and this part is about nothing else.

### The three pieces

| Piece | What it does | How you get it |
| --- | --- | --- |
| **elan** | version manager; downloads and switches Lean versions for you | Homebrew, or the extension installs it |
| **VS Code** | the editor | download from `code.visualstudio.com` |
| **Lean 4 extension** | the actual interface: live checking, the InfoView, symbol input | VS Code's Extensions panel |

The official advice is to install VS Code first and let the Lean 4 extension handle the rest. It detects a missing Lean and offers to set it up.

### Step 1 — VS Code

Download from `code.visualstudio.com`, drag to `/Applications`, open it. macOS may warn that it was downloaded from the internet; that is expected for any app not from the App Store.

### Step 2 — The Lean 4 extension

Open the Extensions panel with **⇧⌘X**, search for `lean4`, and install the one published by **leanprover**. Reload VS Code afterwards if it asks.

To confirm it took, open any `.lean` file: an `∀` symbol appears in the top-right corner of the editor, which is the extension's menu.

### Step 3 — elan and the toolchain

```bash
brew install elan-init
```

Or let the VS Code extension install it when it notices Lean is missing.

You never pick a Lean version by hand. Each project pins its own in a file called `lean-toolchain` (this one says `leanprover/lean4:v4.28.0`), and `elan` reads that file and fetches the matching version automatically. Mathlib is pinned to a matching revision in `lake-manifest.json`.

This is why you must **open the project folder, not a lone file**: outside the folder there is no `lean-toolchain`, and elan will download whatever is newest for no reason.

### Step 4 — Open the project and build it

If you do not already have a checkout, clone it first:

```bash
git clone https://github.com/AxiomMath/auctionlib.git
cd auctionlib
```

The repository currently requires team access. Until it is public, authenticate
Git with an account that has access, or use GitHub's SSH clone URL. Use the
current repository URL shown on GitHub after the planned transfer.

**File → Open Folder**, and select the repository root (the folder containing `lakefile.toml`). Not the folder above it, not a single file inside it. VS Code will ask whether you trust the authors; say yes, or nothing will run.

Then, in a terminal (**⌃`** opens one inside VS Code, already in the right folder):

```bash
lake exe cache get   # download Mathlib already compiled. ALWAYS do this first,
                     # or Lean will build Mathlib from source, which takes hours
bash scripts/update-imports.sh  # regenerate and verify library and test imports
lake build           # build the project
```

The cache command downloads dependencies, the import helper updates the two
root import files, and `lake build` checks the library and tests, including
`MathEconLibTest/Manual/HandsOn.lean`. Run them in that order. On an unchanged
checkout, the import helper should leave no diff.

`lake build` compiles Lean source into `.olean` files, which are the compiled form Lean loads when one file imports another. MathEconLib has dozens of source files; Mathlib, which it imports, has thousands. Compiling Mathlib from source on a laptop takes hours.

To avoid this, the Mathlib project publishes prebuilt `.olean` files for every commit (about 8,000 files, which unpack to some 5 GB). `lake exe cache get` downloads the set matching your pinned version, so nothing has to be compiled from source.

So the first run takes roughly half an hour, nearly all of it network. After that, builds are fast: `lake` tracks which files changed and rebuilds only those and whatever depends on them. Editing one file in `MathEconLib/` and rebuilding is usually seconds.

Two things that will send you back to `cache get`: pulling changes that bump the Mathlib revision, and running `lake clean`. In both cases the cached oleans no longer match, and Lean will start compiling from source unless you fetch the new set first. If a build ever begins printing thousands of `Building Mathlib.…` lines, stop it and run `lake exe cache get`.

### Anatomy of the window

```
┌──────────────┬───────────────────────────┬──────────────────────────┐
│              │                           │                          │
│  EXPLORER    │   your .lean file         │   INFOVIEW               │
│  ⇧⌘E         │                           │   goals at your cursor   │
│              │   example (x : ℝ) :       │                          │
│  MathEconLib/ │       0 ≤ x^2 := by       │   x : ℝ                  │
│    Bidder…/  │     positivity  ←cursor   │   ⊢ 0 ≤ x^2              │
│              │                           │                          │
├──────────────┴───────────────────────────┴──────────────────────────┤
│  TERMINAL  ⌃`            lake build, git, etc.                      │
└─────────────────────────────────────────────────────────────────────┘
```

**The InfoView on the right is the entire point**, and it is the single most important piece of workflow advice in this manual. It shows, for wherever your cursor is: the hypotheses you may use, then a `⊢`, then the goal remaining. Move the cursor one line down inside a proof and it updates.

If it is not visible, open the Command Palette with **⇧⌘P** and run `Lean 4: Infoview: Toggle`.

> **Read the InfoView, not the proof text.** The text is a transcript of moves someone already made; the InfoView is the live position. [Part 5](#part-5--watching-a-proof-happen) is built entirely around this.

### Mac keyboard shortcuts

| Keys | Does |
| --- | --- |
| **⇧⌘P** | Command Palette — shows every Lean command, prefixed `Lean 4:` |
| **⌘P** | jump to a file by name |
| **⇧⌘X** | Extensions panel |
| **⌃`** | show/hide the built-in terminal (control, not command) |
| **⌘S** | save |
| **⌘click** | jump to the definition of whatever is under the pointer |
| **⌥click** | (in the InfoView) expand a term to see its full form |

Two important Command Palette entries:

- `Lean 4: Restart Server`. Use when Lean gets wedged or stops responding.
- `Shell Command: Install 'code' command in PATH`. Lets you type `code .` in Terminal to open the current folder in VS Code. Worth doing once.

### Typing mathematical symbols

When you type a backslash, an abbreviation, then **space** or **tab**, the sequence turns into the symbol.

| Type this | Get this | | Type this | Get this |
| --- | --- | --- | --- | --- |
| `\R` | `ℝ` | | `\in` | `∈` |
| `\N` | `ℕ` | | `\le` | `≤` |
| `\to` | `→` | | `\ge` | `≥` |
| `\forall` | `∀` | | `\ne` | `≠` |
| `\exists` | `∃` | | `\o` | `∘` |
| `\and` | `∧` | | `\<` `\>` | `⟨` `⟩` |
| `\or` | `∨` | | `\alpha` | `α` |

If you cannot remember an abbreviation, **hover the mouse over the symbol** anywhere it already appears and VS Code tells you how to type it. If a symbol refuses to appear, you probably pressed space twice or moved the cursor mid-sequence. Delete back to the backslash and try again.

**Do not use the macOS Character Viewer (⌃⌘Space) for this.** It inserts characters that look right but are not the ones Lean expects, and the resulting error tells you an identifier is unknown without hinting that the character is wrong.

### When something goes wrong

| Symptom | Cause and fix |
| --- | --- |
| No InfoView, no goals | Extension not installed (Step 2), or you opened a file rather than the folder |
| Orange or yellow bar down the file | Lean is still working. Wait; normal on first open |
| Red squiggle | A real error. Hover it, or read the InfoView |
| `unknown identifier` on a Mathlib name | Your file is outside the project, so Mathlib is not in scope |
| Everything suddenly unknown | `Lean 4: Restart Server` from the Command Palette |
| First build running for many minutes | Expected. You are downloading Mathlib. Roughly half an hour, once |



### ✍️ Hands-on 0 — your first file, and the loop

Inside the project, create `MathEconLib/Playground/Scratch.lean`. The `Playground` folder is excluded from version control, so nothing you write there can break anything.

Type this. Actually type it, using `\R` for `ℝ` rather than pasting:

```lean
import Mathlib

#eval 2 + 2

#check (2 : ℝ)

example : (2:ℝ) + 2 = 4 := by norm_num
```

Check these in order:

1. `#eval 2 + 2` shows `4` in the InfoView when your cursor is on that line.

2. `#check (2 : ℝ)` shows `2 : ℝ`. Lean is reporting a *type*, not a value. That difference is the subject of Part 3.

3. Put your cursor immediately after `by` on the last line. The InfoView shows `⊢ 2 + 2 = 4`.

   A **goal** is whatever Lean still needs from you at that point in the proof. It is printed after the `⊢` symbol, with any facts you are allowed to use listed above it. The goal is **open** while it remains unproved. Sitting just after `by`, you have announced that a proof is coming but have not yet supplied any of it, so the whole statement is still owed. Closing a goal means producing something that discharges it; a proof is finished when no goals are left.

4. Move the cursor to the end of `norm_num`. The InfoView now reads "No goals." The tactic supplied what was owed.

That transition, from a goal present to a goal discharged, is the loop you will live in.

Now break it on purpose. Change `4` to `5` and watch the red squiggle appear. Hover it. Change it back.

Finally, confirm you can reach the library itself:

```lean
import MathEconLib.BidderProblem.Basic

open MathEconLib

#check BidderProblem
#check BidderProblem.payoff
```

Both should report types rather than errors. If you get `unknown identifier`, your file is outside the project folder.

---

## Part 1 — Why formalise mathematics at all?

A proof in a journal is a piece of persuasive writing. It is addressed to a human referee, who reads it, believes it or does not, and eventually signs off. This system works remarkably well, but it has known failure modes: referees are busy, "it is easy to see that" sometimes is not, and a gap can sit undetected in the literature for years.

A **proof assistant** such as Lean offers a different arrangement. You write the proof in a formal language, and a small program called the **kernel** checks every single inference against the axioms. The kernel does not get tired, does not skim, and will not extend you the courtesy of assuming you meant something sensible. If it accepts your proof, then modulo bugs in a few thousand lines of well-scrutinised kernel code, the theorem follows from the axioms.

Two important things about Lean:

**It scales to real mathematics.** The Flyspeck project formally verified Thomas Hales's proof of the Kepler conjecture, a proof whose original referees famously declined to certify with complete confidence. More recently, Peter Scholze proposed the Liquid Tensor Experiment to check a result he himself was uneasy about, and the Lean community verified it.

**There is a library.** Lean's mathematical library, **Mathlib**, contains a substantial fraction of an undergraduate and graduate curriculum (analysis, algebra, topology, measure theory, probability) already formalised. You are not starting from the axioms of set theory every morning. `MathEconLib` builds on Mathlib the way an applied paper builds on standard results.

The cost is real: formalising is slower than writing prose, and the language takes some weeks to become comfortable. The benefit is that a formalised result is one nobody has to check again.

> **A note on names.** Mathlib is maintained by the Lean community, not by any one company. MathEconLib is a library for mathematical economics that *uses* Mathlib's general foundations. When this manual says "look it up in Mathlib," it means the general mathematical library; MathEconLib contains the economics-specific definitions and theorems.

### ✍️ Hands-on 1 — meet the kernel

The claim above is that a machine checks every inference and cannot be talked round. Test it.

```lean
example : (2:ℝ) + 2 = 4 := by norm_num
example : (2:ℝ) + 2 = 5 := by norm_num
```

The first is accepted silently. The second reports:

```
error: unsolved goals
⊢ False
```

Take that error apart, because every piece of it will recur.

Start with the part you wrote. `norm_num` is a **tactic**: a command that tries to finish a proof on your behalf. This particular one does arithmetic. On the first line it worked out that `2 + 2` really is `4`, found nothing left to do, and Lean accepted the line without comment.

On the second line it did the same arithmetic, got `4`, and compared it with the `5` you claimed. Those differ, so it could not finish. What it printed is the part of the job still outstanding.

That leftover is what the `⊢` marks, and it is the same **goal** you met in Hands-on 0: whatever Lean still needs and has not been given. Here the goal it hands back is `False`.

`False` is a particular statement that Lean supplies, and its whole purpose is to be unprovable. There is no command, no rule, and no assumption anywhere in Lean that establishes `False`. `False` is the designated dead end.

So `⊢ False` is Lean telling you: *the piece you still owe me is the one piece that can never be supplied.*

That is the right answer, since `2 + 2 = 5` is not true. But notice what the machine did **not** do. It did not look your claim up in a list of true statements, and it did not form an opinion about you. It followed your claim as far as arithmetic goes and showed you the dead end at the bottom of it. When `⊢ False` turns up after a tactic, the usual reading is that the tactic worked correctly and the thing you asked it to prove is false.

**Now check how little the machine takes on faith.** Both examples above were accepted or rejected by the kernel, but on what basis? Every result rests on some set of axioms, and you can ask any result which ones it used:

```lean
#print axioms Nat.add_comm      -- 'Nat.add_comm' does not depend on any axioms
#print axioms Real.sqrt_nonneg  -- depends on axioms: [propext, Classical.choice, Quot.sound]
```

The first answer surprises people, so it is worth explaining.

`ℕ` in Lean is defined inductively: a natural number is either `zero` or the successor of another natural number, and nothing else. Addition is defined by recursion on that structure. Commutativity is then proved by induction, and every step of that induction is a computation the kernel can carry out by unfolding definitions. Nothing is ever assumed along the way. There is no point in the argument where you must reach for a principle that cannot be justified from the definitions, which is what "does not depend on any axioms" records.

`ℝ` is a different kind of object. Lean builds it as equivalence classes of Cauchy sequences of rationals, and that construction needs machinery: `Quot.sound` to identify sequences converging to the same limit, `propext` to treat equivalent propositions as equal, and `Classical.choice` to get facts like trichotomy that no algorithm can decide. Any theorem about reals inherits those three.

The difference is not that one result is shakier. Both are proved. It is that `ℕ` is a computational object and `ℝ` is a classical one, and that distinction has consequences you will meet repeatedly, most visibly in [Trap 4](#trap-4--noncomputable-is-not-a-complaint-about-your-mathematics).

Three axioms plus a few thousand lines of kernel is the whole trusted base. Everything else in Mathlib was checked against it.

---

## Part 2 — A syntax primer

Before the punctuation, we provide a map of the Lean building blocks. Lean has fewer kinds of thing in it than most programming languages, and knowing the whole list early makes the syntax much easier to read.

### 2.0 What a Lean file is made of

Everything in Lean is a **term**: an expression that denotes something. Every term has a **type**, and you find out which with `#check`. That is the entire ontology. What follows are the varieties you will meet.

**Types.** A type is a classification of terms. `ℝ` is the type of real numbers, so `3.7 : ℝ`.  `ℝ → ℝ` is the type of functions from reals to reals. Types are themselves terms with types of their own: `ℝ : Type`.  This is what lets Lean compute with types (§3.4) and ultimately what lets it express mathematics at all (§3.8).

**Functions.** A function turns terms into terms. `fun x => x + 1` adds one;  applied to `5`, it gives `6`. Functions of several arguments are written by taking one argument at a time, so a two-argument function has type `ℝ → ℝ → ℝ`. Nothing here is unusual except the notation, which §2.2 covers.

**Definitions.** A definition gives a name to a term so you can use it later. `def double (x : ℝ) : ℝ := 2 * x` names a function. Definitions are how a library accumulates vocabulary.

**Propositions.** A proposition is a mathematical statement: `2 + 2 = 4`, or `∀ x : ℝ, x ≤ x`. In Lean a proposition is *itself a type*, whose type is `Prop`. We explain this strange idea in Part 3.  For now: a statement is a kind of type.

**Proofs.** A proof is a term whose type is a proposition. Proving `2 + 2 = 4` means constructing a term of type `2 + 2 = 4`. Proofs are ordinary terms, so they can be named, stored in records, and passed to functions like any other value.

**Tactics.** Writing proof terms by hand is painful, so Lean provides tactics: commands that build the term for you. `by norm_num` runs a tactic that handles arithmetic. Anything you can do with tactics you could in principle do by writing the term directly; tactics are a convenience, not a separate mechanism. §2.5 introduces them.

**Structures.** A structure bundles several terms under one name, like a record in any other language. `BidderProblem` bundles five functions and numbers together with one proof. Because proofs are terms, a structure can carry them alongside its data, which is the subject of §3.5.

**Type classes.** A class is a structure that Lean can find for you automatically, used for assumptions that travel with a type rather than being passed by hand. §4.6 covers them; you can ignore them until then.

Two more pieces, neither of them mathematical objects:

**Commands** begin with `#` and ask Lean a question without changing anything. `#check` reports a type, `#eval` computes a value, `#print` shows a definition. They are your main instrument for exploring.

**Attributes** are written `@[...]` and tag a declaration with metadata. The one you will meet most is `@[simp]`, which enrols a lemma in the automatic simplifier (§4.5).

That is the whole inventory:

```
term ─── has a ──→ TYPE
 │
 ├─ if its type is Prop ......... the term is a PROOF, the type a PROPOSITION
 ├─ if its type is A → B ........ the term is a FUNCTION
 ├─ if it is a named term ....... a DEFINITION  (def / theorem / lemma)
 ├─ if it bundles several ....... a STRUCTURE   (or a CLASS, if auto-found)
 └─ built by a script ........... via TACTICS   (by …)
```



### 2.1 The two most important punctuation marks

Almost every line of Lean contains one or both of these, and confusing them is the most common beginner stumble.

| Symbol | Read it as | Example |
| --- | --- | --- |
| `:` | "**has type**" / "is a" | `x : ℝ` — *x is a real number* |
| `:=` | "**is defined to be**" | `x := 3` — *x is defined to be 3* |

A typical definition uses both, in a fixed order: first announce the type, then give the value.

```lean
def double (x : ℝ) : ℝ := 2 * x
    ─┬───  ────┬───   ─┬─  ──┬──
     │         │       │     └── the definition:  what it IS
     │         │       └──────── the output type: a real number
     │         └──────────────── the input:       a real number called x
     └────────────────────────── the name
```

Spelled out in words, that line says: *we are defining a function called `double`; it takes one argument, named `x`, which must be a real number; it returns a real number; and the value it returns is `x` multiplied by two.*

Walk across the line piece by piece.

`def` announces that a new name is being introduced. `double` is that name, and you choose it. `(x : ℝ)` declares the input: the parentheses group one argument, `x` is the name the body will use to refer to it, and `: ℝ` says that argument must be a real number. Lean will reject `double true`, because `true` is a `Bool` and the slot demands an `ℝ`.

The second `: ℝ`, the one after the closing parenthesis, is a different claim. It gives the type of the *result*. Reading the two together: `double` is a function from `ℝ` to `ℝ`.

Then `:=` closes the announcement and opens the answer. Everything after it is the body, the actual recipe. Here the recipe is `2 * x`, using the name `x` that was introduced on the left.

You can ask Lean to confirm all of this:

```lean
#check double     -- double (x : ℝ) : ℝ
```

To emphasise: **`:` announces a type, `:=` supplies a value.**

### ✍️ Hands-on 2.1 — define, then interrogate

```lean
def double (x : ℝ) : ℝ := 2 * x
#check double            -- double (x : ℝ) : ℝ

def doubleN (n : ℕ) : ℕ := 2 * n
#eval doubleN 5          -- 10
```

`#check` reports a type; `#eval` computes a value.

Now try the real-valued one:

```lean
#eval double 5
```

You get something like this, rather than `10`:

```
Real.ofCauchy (sorry /- 10, 10, 10, 10, ... -/)
```

Three things are going on, and each is worth naming.

`Real.ofCauchy` is a constructor. A real number in Mathlib is not a decimal or a floating-point value; it is built from a Cauchy sequence of rationals, and `Real.ofCauchy` is the function that wraps such a sequence up as a real. So what you are looking at is the real number ten in the form Lean actually stores it.

The comment `/- 10, 10, 10, 10, ... -/` shows that sequence: the constant sequence every term of which is ten. That does converge to ten, which is the point, but it is a very different object from the numeral `10` you typed.

The `sorry` is the interesting part. A Cauchy sequence is not just a sequence; it is a sequence *paired with a proof* that it converges. `#eval` cannot print a proof, so it prints `sorry` in that slot as a placeholder. Nothing is broken and nothing was left unproved. It is a display limitation.

Contrast `#eval doubleN 5`, which printed `10` and nothing else. A natural number is stored as a natural number; there is nothing else in the box.

The lesson generalises well beyond this example. `ℝ` in Mathlib is not a numeric type in the programming sense. It is a classical construction that supports proof but not computation, and asking it to compute shows you the scaffolding. [Trap 4](#trap-4--noncomputable-is-not-a-complaint-about-your-mathematics) returns to the practical consequences, of which the main one is the `noncomputable` keyword you will shortly be required to write.

Now confuse the two punctuation marks on purpose, since that is the error you are most likely to make this week:

```lean
def bad (x : ℝ) : ℝ : 2 * x
```

Read the error. Then fix it, and try dropping the output type entirely:

```lean
def alsoFine (x : ℝ) := 2 * x
#check alsoFine
```

That one works: Lean *infers* the return type. Writing it out is a courtesy to the reader, not a requirement, which is why you will see both styles in the library.

### 2.2 Functions

Lean is a functional language, and three conventions differ from ordinary mathematical notation.

**Function types use `→`.** The type of functions from reals to reals is written `ℝ → ℝ`.

**Anonymous functions use `fun`.** Where a mathematician writes $x \mapsto x + 1$, Lean writes:

```lean
fun (x : ℝ) => x + 1
```

`fun` introduces the variable, `=>` separates it from the body. (You will also see `↦` used for `=>`; they are interchangeable, and this project's settings display the arrow form.) Checking it:

```lean
#check fun (x : ℝ) => x + 1     -- fun x ↦ x + 1 : ℝ → ℝ
```

**An underscore `_` means "I do not care about this argument."** So `fun _ => 1 / 2` is the constant function returning one-half, ignoring its input. You will see this constantly.

**Parentheses are not needed for application.** Where a mathematician writes $f(x)$, Lean writes `f x`. A space is the application operator.

This is the convention most likely to bite you, so it is worth being precise about what the parentheses are doing when they do appear.

In ordinary mathematical notation, the parentheses in $f(x)$ are part of how you say "apply". In Lean they are not. Lean applies a function to whatever term comes next, and parentheses serve one purpose only: to mark where a term begins and ends. So:

| You write | Lean reads it as | Meaning |
| --- | --- | --- |
| `f x` | apply `f` to `x` | $f(x)$ |
| `f x y` | apply `f` to `x`, then that to `y` | $f(x, y)$ |
| `f (x + 1)` | apply `f` to the term `x + 1` | $f(x+1)$ |
| `f x + 1` | apply `f` to `x`, then add 1 | $f(x) + 1$ |

The last two rows are the trap. They differ by one pair of parentheses and mean entirely different things, because **application binds more tightly than any arithmetic operator**. `f x + 1` cannot mean $f(x+1)$; the `f x` is grabbed first and the `+ 1` applies to the result.

Multi-argument application follows the same rule and explains a piece of notation you will meet in Part 3. `f x y` is really `(f x) y`: apply `f` to `x`, get back another function, apply that to `y`. This is why the type of a two-argument function is written `ℝ → ℝ → ℝ` rather than something involving a pair. Each arrow consumes one argument.

When in doubt, add parentheses. They are free, and Lean will not object to `f (x)`.

### ✍️ Hands-on 2.2 — application binds tightest

These examples produce wrong answers rather than errors, which is the worst kind of mistake.

```lean
def f (n : ℕ) : ℕ := n * 10

#eval f 2 + 1        -- 21   ← (f 2) + 1
#eval f (2 + 1)      -- 30   ← f 3
```

Both compile. Both are silent. They differ by nine.

Now the anonymous functions. Take these one line at a time rather than as a block.

**A function, unapplied.** Ask Lean what `fun (x : ℝ) => x + 1` is:

```lean
#check fun (x : ℝ) => x + 1
```

Lean answers `fun x ↦ x + 1 : ℝ → ℝ`. Note the arrow came back as `↦` even though you typed `=>`; the box below explains why. Everything before the colon is the term you wrote, echoed back; everything after it is the type. So Lean is telling you this is a function from reals to reals. You have described a function without applying it to anything.

**The same function, applied.** Now give it an argument. The extra parentheses are needed because the function is anonymous: without them, Lean would read `n + 1 5` and fail.

```lean
#eval (fun (n : ℕ) => n + 1) 5
```

Lean answers `6`. This is `#eval` rather than `#check` because we want the value, not the type.

**A function that ignores its input.** The underscore takes the place of a name you never use:

```lean
#check fun (_ : ℝ) => (1:ℝ) / 2
```

Lean answers `fun x ↦ 1 / 2 : ℝ → ℝ`. Two things to notice. The type is still `ℝ → ℝ`, because this is still a function that accepts a real; it simply pays no attention to what it is given. And Lean has printed a name, `x`, where you wrote `_`, since it needs something to display.

That last pattern is exactly how `winProb := fun _ => 1 / 2` works in Part 3: a bidder whose chance of winning is one half no matter what they bid.

> **`=>` or `↦`?** Both are accepted and mean the same thing. `MathEconLib` uses both, with `=>` the more common: as of this writing, 414 `fun` arrows written `=>` against 268 written `↦`. The split runs by file rather than by rule, with `GameTheory/Basic.lean` almost entirely `↦` and `Statistics/OrderStatistics.lean` almost entirely `=>`. No linter enforces either, so match whichever the file you are editing already uses. One wrinkle: the project sets `pp.unicode.fun = true` in `lakefile.toml`, so Lean *prints* `↦` in the InfoView whatever you typed. Do not be thrown when your `=>` comes back as `↦`.

### 2.3 Symbols you will meet

You do not need to memorise this table. Refer back to it as symbols appear.

| Symbol | Meaning | Typed as |
| --- | --- | --- |
| `ℝ` `ℕ` `ℤ` `ℚ` | reals, naturals, integers, rationals | `\R` `\N` `\Z` `\Q` |
| `→` | function type; also "implies" | `\to` |
| `∀` | for all | `\forall` |
| `∃` | there exists | `\exists` |
| `∈` | is a member of | `\in` |
| `∧` `∨` `¬` | and, or, not | `\and` `\or` `\not` |
| `↔` | if and only if | `\iff` |
| `≤` `≥` `≠` | at most, at least, not equal | `\le` `\ge` `\ne` |
| `∘` | function composition: `(f ∘ g) x = f (g x)` | `\o` |
| `⟨ ⟩` | bundles things together (see §4.2) | `\<` `\>` |
| `⊢` | separates assumptions from the goal | (Lean prints it) |
| `α` `β` | stand-ins for arbitrary types | `\a` `\b` |

In VS Code, type the backslash abbreviation and press space. Hovering over any symbol shows you how to type it.

### ✍️ Hands-on 2.3 — type the symbols

The stated purpose is muscle memory.  Each of the three examples below is also a small complete proof, and none of them is doing what a newcomer expects. Type each one, then read what it actually says.

**Example one: a proof that is a function.** Type this using `\R`, `\to`, `\forall`, `\le`:

```lean
example : ∀ x : ℝ, x ≤ x := fun x => le_refl x
```

The claim, everything between the first `:` and the `:=`, reads "for every real number `x`, `x` is at most itself." True, and dull. The interesting half is the proof on the right.

`le_refl` is a lemma that already exists in Mathlib. Ask what it says:

```lean
#check @le_refl     -- ∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
```

Ignore the material in braces and brackets for now; §4.6 explains it. The readable part is `(a : α), a ≤ a`: hand `le_refl` any object and it hands back the fact that that object is at most itself. So `le_refl x` is not a general principle, it is the one specific fact `x ≤ x`.

Now look at what wraps it. The proof is `fun x => le_refl x`, and `fun` is the function keyword from §2.2. **The proof of this statement is a function.** Given any real `x`, it produces the fact for that particular `x`.

Set the claim and its proof side by side:

```
claim:  ∀ x : ℝ,      x ≤ x
proof:  fun x =>      le_refl x
```

The `∀` and the `fun` line up. That is not a coincidence or a cute analogy, we explain this in  §3.6. For now, just notice the shape.

**Example two: a proof that is already sitting there.** This one uses `\in` and `\and`:

```lean
example (x : ℝ) (h : x ∈ Set.Icc (0:ℝ) 1) : 0 ≤ x ∧ x ≤ 1 := h
```

New syntax first. The two bracketed groups before the colon are **hypotheses**: things you are given rather than things you must show. `(x : ℝ)` supplies a real number, and `(h : x ∈ Set.Icc (0:ℝ) 1)` supplies an assumption, named `h`, that this number lies in the interval $[0,1]$. Naming assumptions is how you refer to them later, and `h` is the conventional name.

So the line reads: *given a real `x` known to lie in $[0,1]$, show that `0 ≤ x` and `x ≤ 1`.*

The proof is `h`. Not a tactic, not a calculation, just the assumption handed straight back.

That works because of how `Set.Icc` is defined. To Lean, "`x` lies in the interval $[0,1]$" and "`0 ≤ x` and `x ≤ 1`" are not two facts connected by a lemma; they are **the same statement written two ways**. No conversion step exists because none is needed. This is called definitional equality, and it explains a great deal of Lean code that otherwise looks like it skipped a step.

Since `h` is a conjunction, you can also take it apart:

```lean
example (x : ℝ) (h : x ∈ Set.Icc (0:ℝ) 1) : 0 ≤ x := h.1
```

`.1` takes the left half of an "and", `.2` the right. You will use these constantly.

**Example three: building an "and" rather than taking one apart.** Here are the angle brackets, `\<` and `\>`:

```lean
example : (0:ℝ) ≤ 1 ∧ (1:ℝ) ≤ 2 := ⟨by norm_num, by norm_num⟩
```

The claim is a conjunction, so proving it means supplying both halves. `⟨ ⟩` is Lean's general bundling notation: whatever goes inside, separated by commas, gets packaged into the single thing being asked for. Here the two `by norm_num` calls prove `0 ≤ 1` and `1 ≤ 2` respectively, and the brackets combine them into a proof of the conjunction.

Compare the two directions and the symmetry is clear. Line two took an "and" apart with `.1`; line three puts one together with `⟨ , ⟩`.

The same brackets build records, pairs, and existence statements, which is why §4.2 can use them to construct a `BidderProblem` out of five numbers and a proof.

If a symbol will not appear as you type, you probably pressed space twice or clicked elsewhere mid-sequence. Delete back to the backslash and retype.

### 2.4 Four ways to declare something

| Keyword | What it makes | Typical use |
| --- | --- | --- |
| `def` | a definition | `def double (x : ℝ) : ℝ := 2 * x` |
| `theorem` / `lemma` | a proved statement | `theorem my_two_pos : (0:ℝ) < 2 := by norm_num` |
| `example` | a statement proved but *not named* | scratch work; nothing is added to the library |
| `structure` | a record with several fields | see §4.2 |

An `example` is exactly a `theorem` that you have not bothered to name, which makes it ideal for experimenting. Most snippets in this manual are `example`s for that reason.

### ✍️ Hands-on 2.4 — named versus anonymous

```lean
theorem my_two_pos : (0:ℝ) < 2 := by norm_num
example            : (0:ℝ) < 2 := by norm_num

#check my_two_pos     -- my_two_pos : 0 < 2
```

Identical statements, identical proofs. The only difference is that the first has a name and can be used later, while the second vanishes the moment it is checked.

Confirm that by asking for the `example`. There is nothing to ask for. It has no name.

Now a lesson in why names matter. Try:

```lean
theorem two_pos : (0:ℝ) < 2 := by norm_num
```

It fails: `` `two_pos` has already been declared``. Mathlib got there first. Name collisions are a routine nuisance, which is why this manual prefixes its throwaway names with `my_`, and why Mathlib's own naming conventions ([Part 7](#how-mathlib-names-things)) are as rigid as they are.

### 2.5 `by`, and what a tactic is

There are two ways to supply a proof.

You can write the proof **term** directly after `:=`, which is what you do when the proof is short. Or you can write `by` followed by a **tactic script**, a list of instructions for building the proof:

```lean
example : (2:ℝ) + 2 = 4 := by norm_num
                             ─┬─ ────┬───
                              │      └── a tactic: "normalise the numbers"
                              └───────── "what follows is a set of instructions"
```

A **tactic** is a command that transforms the thing you are trying to prove. `norm_num` handles arithmetic; `intro` introduces a variable; `rw` rewrites using an equation. [Part 5](#part-5--watching-a-proof-happen) shows a tactic script running step by step, and [Part 7](#part-7--reference-tables) lists the common ones.

The mental picture: `by` opens a little workshop where you manipulate the goal until it is discharged; when the workshop closes, out comes a proof term. Both routes produce the same kind of object. In Part 3 we explain what that object is.

### ✍️ Hands-on 2.5 — a first taste of tactics

Each of these is a different tactic doing a different job. Type them, then put your cursor before and after the tactic and watch the InfoView.

```lean
example (x : ℝ) : 0 ≤ x ^ 2 := by positivity
example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
example (x : ℝ) (h : 0 ≤ x) : 0 ≤ 2 * x := by linarith
example : ∀ x : ℝ, x + 0 = x := by intro x; ring
```

Roughly: `positivity` proves things are non-negative, `ring` proves algebraic identities, `linarith` draws linear conclusions from linear hypotheses, and `intro` handles a `∀`.

The fourth line is the interesting one, because it shows two tactics in sequence separated by `;`. Put the cursor between `intro x` and `ring`. The goal has changed from `∀ x : ℝ, x + 0 = x` to `x + 0 = x`, with `x : ℝ` now listed above the `⊢`. That is `∀`-introduction, precisely what a mathematician means by "fix an arbitrary `x`."

Now try the wrong tool for the job:

```lean
example (x : ℝ) (h : 0 ≤ x) : 0 ≤ x ^ 2 := by linarith
```

It fails, and the error repays reading in full:

```
error: linarith failed to find a contradiction
x : ℝ
h : 0 ≤ x
a✝ : x ^ 2 < 0
⊢ False
```

Notice the strategy this exposes. `linarith` did not attack the goal directly. It *assumed the opposite* (`a✝ : x ^ 2 < 0`) and hunted for a contradiction, in the manner of a proof by contradiction. It failed because `x ^ 2` is nonlinear and therefore invisible to it. Swap in `positivity` or `nlinarith` and it goes through.

Tactics are specialists, not a single button labelled "prove it". Learning which to reach for is a large part of learning Lean.

---

## Part 3 — The one big idea: propositions are types

Lean may seem strange at first due to a single design decision we introduce next. Once you are used to it, all that remains is vocabulary.

### 3.1 The colon means exactly one thing

From §2.1: `x : T` says "`x` is a value of type `T`." Lean applies this uniformly, including in places where you might expect something else to be happening.

Here are two adjacent lines from a real `MathEconLib` declaration. It describes one bidder's situation in an auction: `winProb b` is the probability of winning when you bid `b`.

```lean
winProb       : ℝ → ℝ                      -- a function from bids to probabilities
winProb_range : ∀ x, winProb x ∈ Icc 0 1   -- ??? 
```

(`Icc 0 1` is Mathlib's notation for the closed interval $[0,1]$; the naming scheme is in §4.3. So the second line says: for every `x`, the number `winProb x` lies between 0 and 1, which is exactly what you would demand of a probability.)

Now read both lines using only the rule from §2.1. The first says `winProb` is a value whose type is `ℝ → ℝ`. The second says `winProb_range` is a value whose type is `∀ x, winProb x ∈ Icc 0 1`.

Identical grammar. Same declaration form. The second line declares a value, exactly as the first line does. It is **not** a comment, a docstring, or a runtime check bolted on beside the data. It is a field holding a value, in precisely the way the first line is.

So there is only one question left: what sort of thing is a value whose type is `∀ x, winProb x ∈ Icc 0 1`?

**Lean's answer: a proof of it.**

```
        DATA                                   PROOF
  ┌──────────────────────┐         ┌────────────────────────────┐
  │ winProb : ℝ → ℝ      │         │ winProb_range :            │
  │                      │         │    ∀ x, winProb x ∈ [0,1]  │
  └──────────────────────┘         └────────────────────────────┘
      the colon says                     the colon says
      "has type ℝ → ℝ"                   "has type <this statement>"
      values of that type                values of that type
      are FUNCTIONS                      are PROOFS
```

This identification of propositions with types, and of proofs with the values inhabiting them, is called the **Curry–Howard correspondence**. It is why *"the field's type is a proposition, so any value of that field is a proof"* is not an extra rule you have to memorise: it follows from the colon meaning one thing everywhere.

The correspondence is worth a paragraph of its own, because it is older and stranger than it first looks.

In the 1930s Haskell Curry noticed a coincidence, and in the 1960s William Howard made it precise. Two subjects that had grown up separately turned out to be the same subject in different notation. On one side, logic: statements, and proofs of them. On the other, computation: types, and the values belonging to them. Line them up and every concept on the left has a twin on the right.

| Logic | Computation |
| --- | --- |
| proposition `P` | type `P` |
| a proof of `P` | a value of type `P` |
| `P` implies `Q` | function type `P → Q` |
| modus ponens (from `P → Q` and `P`, get `Q`) | applying a function to an argument |
| `P` and `Q` | a pair holding a `P` and a `Q` |
| `P` or `Q` | a value that is either a `P` or a `Q` |
| for all `x`, `P x` | a function taking `x` to a value of type `P x` |
| a false statement | a type with no values |

Read the third and fourth rows together. "If `P` then `Q`" and "a function from `P` to `Q`" are the same thing, and *using* an implication is the same operation as *calling* a function. That is not an analogy offered for intuition. In Lean it is literally the same mechanism, which is why §3.6 can prove a lemma by writing `B.winProb_range (B.strategy v)`, an application and nothing more.

The last row is the one you already met. In Hands-on 1, `2 + 2 = 5` failed and left `⊢ False`. On the logic side that reads "the statement is false"; on the computation side it reads "the type has no values, so no value can be produced." Same fact, two vocabularies.

What Curry–Howard buys Lean is that it needs only one engine. There is no separate proof-checker bolted onto a programming language. The machinery that decides whether `2 * x` is a legitimate `ℝ` is the same machinery that decides whether your argument is a legitimate proof. Everything in the rest of Part 3 is a consequence of building the system that way.

### ✍️ Hands-on 3.1 — `#check` everything

One of the most useful commands in Lean is `#check` . It is used to interrogate Lean about types, and the most useful command while learning. Run each and read the answer:

```lean
#check (3 : ℝ)                 -- 3 : ℝ
#check fun (x : ℝ) => x ^ 2    -- fun x ↦ x ^ 2 : ℝ → ℝ
#check ℕ                       -- ℕ : Type          ← a type is itself a value
#check (2 + 2 = 4)             -- 2 + 2 = 4 : Prop  ← a statement is a type
#check Set.Icc (0:ℝ) 1         -- Icc 0 1 : Set ℝ
```

Let's understand what we see. `ℕ` has a type, namely `Type`. Types are things Lean manipulates like anything else. And `2 + 2 = 4` has type `Prop`, meaning the *statement* is a type. 

Now for the line that makes the section's point. Ask for the type of a theorem:

```lean
#check @Nat.add_comm    -- ∀ (n m : ℕ), n + m = m + n
```

Lean reports its type as *the statement it proves*. A theorem is a value; its type is what it says. If that seems confusing at first. We explain it in  the next few sections.

### 3.2 `Prop` is not `Bool`

This is the misconception worth clearing up early, because others grow from it.

**`Bool` is ordinary data.** It has two values, `true` and `false`. You can compute with it, branch on it, store it in a list. In Lean, `2 + 2 == 4` is a `Bool`, and it *evaluates* to `true`.

**`Prop` is a collection of types.** `2 + 2 = 4` is a `Prop`, which is to say it is a *type*. It does not evaluate to anything. Asking what `2 + 2 = 4` evaluates to is a category error, rather like asking what the set $\{1,2,3\}$ evaluates to.

```lean
#check (true : Bool)              -- Bool
#eval  (2 + 2 == 4 : Bool)        -- true      ← computed, gives an answer
#check (2 + 2 = 4  : Prop)        -- Prop      ← a type
#check (2 + 2 = 5  : Prop)        -- Prop      ← also a perfectly legal type!
```

Look at the last line. `2 + 2 = 5` is a well-formed type. Lean is happy to discuss it, quantify over it, assume it. It is not an error to write it down. It is simply a type that happens to have **no values**.

> **Notation.** A single `=` builds a `Prop`. A double `==` builds a `Bool`. You almost always want `=`.

### ✍️ Hands-on 3.2 — the two worlds side by side

```lean
#check (1 < 2)              -- 1 < 2 : Prop      ← Lean's default reading
#eval  (1 < 2 : Bool)       -- true              ← forced into the Bool world
#eval  decide ((1:ℕ) < 2)   -- true              ← what that coercion does
```

The last line works because `1 < 2` on naturals is **decidable**: there is an algorithm that settles it, and `decide` runs it.

Now the case that seems to contradict the whole section:

```lean
#eval (2 + 2 = 4)           -- true
```

A proposition evaluating to `true`? The resolution matters, because this is where beginners conclude the distinction was fake. `2 + 2 = 4` is still a `Prop`. But equality of naturals is decidable, and when `#eval` is handed a `Prop`, Lean quietly inserts `decide` to run the algorithm.

So the bridge exists, but in one direction only and not always. Most interesting propositions are not decidable: no algorithm settles `∀ x : ℝ, f x ≤ 1`, and `#eval` on it fails. The `Prop`/`Bool` distinction is real; decidability is a special case that spans it.

Finally, confirm falsehood is perfectly expressible:

```lean
#check (2 + 2 = 5)          -- 2 + 2 = 5 : Prop
```

No error. Lean hands you the type. It simply contains nothing.

### 3.3 Propositions as boxes

Here is the picture that makes this concrete:

> **A proposition is a box that can only be filled by evidence.**

- `2 + 2 = 4` is a box with something in it.
- `2 + 2 = 5` is a box that is empty. Perfectly well-made, permanently unfillable.
- **Proving `P` and producing a value of type `P` are the same activity.**

That last line is the whole idea. When you write

```lean
example : (2:ℝ) + 2 = 4 := by norm_num
```

you are not asserting `2 + 2 = 4` and asking Lean to adjudicate. You are *constructing a value* whose type is `2 + 2 = 4`. The `by norm_num` part is a small program whose job is to build that value. When it succeeds, a term exists, and the kernel verifies that the term really does have the claimed type.

This reframing has an immediate payoff: it explains why proofs can be stored in records, passed to functions, and returned from functions. They are values, and values go wherever values go. 

### ✍️ Hands-on 3.3 — fill some boxes, then try an empty one

Each of these asks you to construct a value of a proposition. Watch the InfoView go from a goal to "No goals."

```lean
example : (2:ℝ) + 2 = 4 := by norm_num
example : (3:ℝ) * 3 = 9 := by norm_num
example (x : ℝ) : x ^ 2 - x ^ 2 = 0 := by ring
```

Now the empty box:

```lean
example : (2:ℝ) + 2 = 5 := by norm_num
```

`unsolved goals ⊢ False`. There is nothing to put in it, and no tactic will invent one.

Finally, see that a proof really is a value you can name and reuse:

```lean
theorem my_fact : (2:ℝ) + 2 = 4 := by norm_num

example : (2:ℝ) + 2 = 4 := my_fact          -- reuse it by name
example : (4:ℝ) = 2 + 2 := my_fact.symm     -- and manipulate it like data
```

That second line deserves unpacking, because it is doing something no informal proof ever does.

`my_fact` is a proof of `2 + 2 = 4`. Writing `my_fact.symm` produces a proof of `4 = 2 + 2`. Nothing was re-proved; you took an object you already had and transformed it into a different object.

The tool doing the work is `Eq.symm`, Mathlib's statement that equality runs both ways: from a proof of `a = b` it manufactures a proof of `b = a`. The dot notation is the lookup rule from §2.3 and §4.4 — `my_fact` has an equation for its type, so `my_fact.symm` means `Eq.symm my_fact`.

Now notice the shape of that. `Eq.symm` takes a proof and returns a proof, which makes it **a function whose inputs and outputs are proofs**. Try it directly:

```lean
#check @Eq.symm     -- ∀ {α : Sort u_1} {a b : α}, a = b → b = a
```

The arrow in `a = b → b = a` is the ordinary function arrow from §2.2. Feed the left, receive the right.

This is what "computing with proofs" means, and it is the practical payoff of §3.3. Because a proof is a value, the whole apparatus you would use on data becomes available: you can name proofs, pass them to functions, get them back, store them in records, and build large ones by combining small ones. `h.symm`, `h.trans h'`, and `h.1` are all just that.

Compare the informal situation. On paper, "and by symmetry" is an instruction to the reader, who re-runs the argument in their head. Here it is an operation applied to an object, and the object it returns is checked like any other.

### 3.4 Types that depend on values

One more ingredient is needed, and it is what separates Lean from ordinary programming languages.

In most languages, types are fixed shapes: "integer," "list of strings," "function from reals to reals." In Lean, **a type may mention a value.** The standard small example is `Fin n`, the type of natural numbers less than `n`:

```lean
#check (Fin 3)          -- Fin 3 : Type
#check fun n => (Fin n) -- fun n ↦ Fin n : ℕ → Type
```

Read that second line carefully: `fun n => Fin n` is a **function from numbers to types**. Feed it `3` and you get the type `Fin 3` (which has three elements); feed it `5` and you get a different type. Types are values that can be computed.

This is exactly what is happening in §3.1. The type of `winProb_range`, namely `∀ x, winProb x ∈ Icc 0 1`, *mentions the `winProb` field*. Change `winProb` and you change what `winProb_range` is required to prove. Such **dependent types** are what let a type system express not just shapes but properties, and hence arbitrary mathematics.

### ✍️ Hands-on 3.4 — watch a type get computed

```lean
#check Fin 3                     -- Fin 3 : Type
#check fun n => Fin n            -- fun n ↦ Fin n : ℕ → Type
#check fun (n : ℕ) => (Fin n → ℝ)
```

Read the second line closely: `ℕ → Type`. A **function from numbers to types**. Feed it `3` and you get a type with three elements; feed it `5` and you get a different type altogether. Types are computed here, not fixed in advance.

The third line goes further: `fun n => (Fin n → ℝ)` sends a number to *the type of `n`-dimensional real vectors*. That is how Mathlib talks about vectors of varying length without needing a separate type for each.

This capability is what ordinary programming languages lack, and it is what makes `winProb_range` expressible in the next section: its type mentions the `winProb` *value*, so changing the function changes what must be proved.

### 3.5 What this buys: illegal states become unconstructible

Now the payoff. `BidderProblem` is a record with six fields, describing one bidder's situation. To build one, you must supply all six:

```lean
noncomputable def coinFlip : BidderProblem where
  lowestType    := 0                     -- the lowest possible valuation
  highestType   := 1                     -- the highest possible valuation
  winProb       := fun _ => 1 / 2        -- wins half the time, whatever the bid
  winProb_range := by intro x; norm_num [Set.mem_Icc]    -- ← the certificate
  cost          := fun b => b            -- pays their bid
  strategy      := id                    -- bids their true valuation
```

Five fields take data. One takes a proof. It is not optional, not defaulted, not skippable.

Two pieces of that block are unexplained, and neither has anything to do with the point of this section.

**`noncomputable`.** The definition sets `winProb := fun _ => 1 / 2`, and `1 / 2` is a division of real numbers. As Hands-on 2.1 showed, `ℝ` in Mathlib is a classical construction rather than a numeric type, so real division has no executable procedure behind it. Lean can reason about `1 / 2` perfectly well; it just cannot *run* it. The keyword is you acknowledging that, and nothing about the mathematics changes. Leave it off and Lean tells you exactly what to add. [Trap 4](#trap-4--noncomputable-is-not-a-complaint-about-your-mathematics) has the full story, including why `theorem`s never need it.

**`id`.** The identity function: it returns its argument untouched, so `id 5` is `5`. Writing `strategy := id` therefore says this bidder bids exactly their own valuation, with no shading up or down. In auction-theory terms they are bidding truthfully. Mathlib supplies `id` so you never have to write `fun v => v`, though the two mean the same thing and you may use either.

Both are incidental scaffolding. The point of the section is the `winProb_range` line, which is the one field that takes a proof rather than data.

Now try to cheat. Replace `winProb` with `fun _ => 2`, a "probability" of 2. The other five fields are still perfectly fine; `2` is a real number and the record's shape is unchanged. But the `winProb_range` slot now demands a value of type `∀ x, (2 : ℝ) ∈ Icc 0 1`, and by §3.3 that box is empty. No tactic can fill it, because nothing inhabits it.

Lean rejects the definition, with this error at the proof field:

```
error: unsolved goals
x : ℝ
⊢ False
```

Read that as: *after simplifying, I need you to prove `False`, and I cannot.* Which is correct. You asked for something untrue.

Stated sharply:

> A `BidderProblem` with an out-of-range win probability is not a *bad value*. It is an *unconstructible* one. The illegal state does not exist.

Compare the alternatives you might reach for elsewhere:

| Approach | Checked when? | On which inputs? |
| --- | --- | --- |
| A runtime check, e.g. Python's `assert 0 <= q <= 1` | when the program runs | only the ones you actually ran |
| A sentence in a paper: "where `Q(b) ∈ [0,1]`" | when a referee reads it | whatever they happen to notice |
| Lean's `winProb_range` field | once, at construction | all of them, permanently |

And having paid that cost once, every later theorem gets the property for free. It rides along inside the record.

### ✍️ Hands-on 3.5 — build one, then try to cheat two ways

Build a bidder who always wins:

```lean
noncomputable def alwaysWins : BidderProblem where
  lowestType    := 0
  highestType   := 10
  winProb       := fun _ => 1
  winProb_range := by intro x; norm_num [Set.mem_Icc]
  cost          := fun b => b
  strategy      := id

#check alwaysWins.winProb_range
-- alwaysWins.winProb_range : ∀ (x : ℝ), alwaysWins.winProb x ∈ Icc 0 1
```

That `#check` is what the section has been building to. The certificate is a real field you can pull out and inspect, exactly like `alwaysWins.cost`.

Now cheat, in two different ways, and compare the failures.

**Cheat 1, an impossible probability.** Change `winProb` to `fun _ => 2`. The error lands *on the proof field*: `unsolved goals ⊢ False`. The data was fine; the certificate could not be produced.

**Cheat 2, declining to certify.** Restore `winProb` to `fun _ => 1`, then delete the `winProb_range` line entirely. Now the error moves to the definition as a whole:

```
error: Fields missing: `winProb_range`
```



### 3.6 Proofs are functions

Because proofs are values, and because `∀` is Lean's way of writing a function type, **specialising a "for all" statement is literally function application.**

Here is the first proof in `BidderProblem/Basic.lean`, one line long:

```lean
lemma q_range (v : ℝ) : B.q v ∈ Icc 0 1 := B.winProb_range (B.strategy v)
```

Three names appear there without introduction. Take them in turn, because each comes from a different place, and knowing which is which is most of what it takes to read Lean fluently.

**Where `B` comes from.** It is nowhere in the lemma, yet every line uses it. Twelve lines earlier the file says:

```lean
namespace BidderProblem

variable (B : BidderProblem)
```

`variable` declares something shared by every declaration that follows, so any lemma below which mentions `B` silently receives it as an argument. It is the formal counterpart of a paper writing "fix a bidder problem $B$ throughout this section." Lean adds the parameter only where it is actually used. §4.4 covers this properly; for now, `B` is simply *some* bidder problem, fixed once at the top of the file.

**Where `B.strategy` comes from.** It is one of the six fields of the structure itself, declared in §3.5 as `strategy : ℝ → ℝ` and documented in the source as the equilibrium bidding rule: hand it a valuation, get back the bid that bidder makes. `B.strategy` is the dot notation of §2.3, reaching into the record and pulling that field out. `B.winProb_range` in the same line is another field, the certificate.

**Where `B.q` comes from.** This one is neither a field nor a variable but a definition made a few lines above:

```lean
def q : ℝ → ℝ := B.winProb ∘ B.strategy
```

`∘` is function composition, so `B.q v` means `B.winProb (B.strategy v)`: first work out what this bidder bids at valuation `v`, then ask how likely that bid is to win. The distinction is worth being careful about. `winProb` is a function of your **bid**; `q` is a function of your **valuation**. They differ by one application of the strategy, and auction theory cares about the difference constantly.

So the lemma says: the chance of winning, viewed as a function of valuation, also lies in $[0,1]$. Obvious once stated, and it still has to be recorded, because Lean will not grant it unasked.

To summarise the three sources:

| Name | Kind | Introduced |
| --- | --- | --- |
| `B` | section variable | `variable (B : BidderProblem)`, at the top of the namespace |
| `B.strategy` | structure field | in the `structure BidderProblem` block (§3.5) |
| `B.q` | derived definition | `def q := B.winProb ∘ B.strategy`, above the lemma |

If you ever lose track of which is which in a real file, put the cursor on the name and read the InfoView, or **⌘click** to jump straight to where it was declared.

Read the right-hand side as a function call:

```
B.winProb_range                 : ∀ x, B.winProb x ∈ Icc 0 1
B.winProb_range (B.strategy v)  :      B.winProb (B.strategy v) ∈ Icc 0 1
                                       └────────── this is B.q v ─────────┘
```

We reached into the record, took out the stored certificate, and applied it at the point `B.strategy v`. No tactics, no re-proving. Because `B.q` is *defined* as that composition, the result is already the goal.

The general pattern is that implication is a function type and modus ponens is application:

```
   h : P → Q        hp : P
   ─────────────────────────
         h hp : Q
```

If you have a proof `h` that `P` implies `Q`, and a proof `hp` of `P`, then `h hp`, literally applying one to the other, is a proof of `Q`. This is why Lean users say "apply the lemma." They mean it literally.

### ✍️ Hands-on 3.6 — apply proofs like functions

No tactics in any of these. Every proof is a single application:

```lean
-- specialising a ∀ is function application
example (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ f 3 := hf 3

-- modus ponens is function application
example (P Q : Prop) (h : P → Q) (hp : P) : Q := h hp

-- the pattern from the file itself
example (B : BidderProblem) : B.q 5 ∈ Set.Icc 0 1 := B.winProb_range (B.strategy 5)
```

Then mis-apply one deliberately:

```lean
example (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ f 3 := hf
```

The error shows both types side by side:

```
error: Type mismatch
  hf
has type
  ∀ (x : ℝ), 0 ≤ f x
but is expected to have type
  0 ≤ f 3
```

Supplying the argument is not a formality. It is the step that turns the general statement into the specific one, and forgetting it is a type error in exactly the way forgetting a function's argument is.

### 3.7 Proof irrelevance

A reasonable worry: if proofs are values stored inside records, do two `BidderProblem`s that used *different* proofs of the same range condition count as different objects? That would be a disaster: you could never prove two constructions equal.

Lean's answer is **proof irrelevance**: any two values of the same `Prop` are regarded as equal, automatically. So this holds, with the one-word proof `rfl` ("by definition"):

```lean
example (h₁ h₂ : ∀ x, coinFlip.winProb x ∈ Icc 0 1) : h₁ = h₂ := rfl
```

Whereas for data it of course fails, as it must:

```lean
example (a b : ℝ) : a = b := rfl
-- error: Type mismatch: rfl has type ?m = ?m but is expected to have type a = b
```

So although `winProb_range` occupies a slot in the structure, it contributes nothing to the *identity* of the value. Two `BidderProblem`s with the same numbers and functions are the same `BidderProblem`, however elegantly or clumsily each discharged the range condition.

A slogan to keep:

> **Data fields carry information. Proof fields carry only permission.**

### ✍️ Hands-on 3.7 — proofs interchangeable, data not

```lean
-- any two proofs of the same proposition are equal, by definition
example (p : Prop) (h₁ h₂ : p) : h₁ = h₂ := rfl

-- concretely, for an inequality
example (x : ℝ) (h₁ h₂ : 0 ≤ x) : h₁ = h₂ := rfl

-- but data is data
example (a b : ℝ) : a = b := rfl
```

The first two succeed with the one-word proof `rfl`; the third fails with a type mismatch.

Note how little you had to know in the first example. It works for *any* proposition `p`, because the principle has nothing to do with what is being proved, only with the fact that it is a `Prop`.

The practical consequence: you never have to worry about having produced the "wrong" proof of a side condition. There is no such thing.

### 3.8 Why this is not merely a stricter type-checker

A tempting misreading is: "so it is like a very strict programming language." The difference is one of kind, not degree.

An ordinary type system expresses **shapes**: this is a function from reals to reals, that is a list of integers. It cannot express **properties**: that this function's values lie in $[0,1]$, that this list is sorted, that this strategy is an equilibrium.

Because Lean's types can depend on values (§3.4), the type system becomes expressive enough to state arbitrary mathematics. "This mechanism is incentive compatible" is a *type*. A proof of it is a *value* of that type. And the program that checks your definitions is the same kernel that checks your theorems. There is only one mechanism, doing both jobs.

That is why formalisation is possible at all.

### ✍️ Hands-on 3.8 — state a property no ordinary type system can

Ordinary types express shapes. Write down some *properties* and confirm Lean takes each as a perfectly ordinary type:

```lean
#check ∀ (l : List ℕ), l.Pairwise (· ≤ ·)            -- "sorted" is a type
#check ∀ (f : ℝ → ℝ), Monotone f                     -- "monotone" is a type
#check ∀ (f : ℝ → ℝ), ∀ x, f x ∈ Set.Icc (0:ℝ) 1     -- "lands in [0,1]" is a type
```

(If you reach for `l.Sorted` instead, Lean accepts it but warns that it is deprecated in favour of `Pairwise`. Deprecation warnings are common in a library this active, and are worth heeding rather than silencing.)

None of these is a statement Lean is evaluating; each is a *type*, and a proof would be a value inhabiting it. Try naming one and see:

```lean
def BoundedFn : Type := { f : ℝ → ℝ // ∀ x, f x ∈ Set.Icc (0:ℝ) 1 }
#check BoundedFn
```

That `{ x // P x }` notation is a **subtype**: the type of things satisfying `P`, packaged as data plus certificate. It is a small version of the `BidderProblem` pattern, and it has no counterpart in a conventional type system.

---

## Part 4 — Reading a real file

Open [`MathEconLib/BidderProblem/Basic.lean`](../MathEconLib/BidderProblem/Basic.lean) beside this section. It is about a hundred lines.

### 4.0 The three lines before the mathematics

The file does not open with mathematics. It opens with this:

```lean
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import MathEconLib.SingleParameter.Basic

@[expose] public section
```

None of that is about auctions, and none of it has appeared so far in this manual. It is bookkeeping about **visibility**: which parts of this file other files are allowed to see. Taking the lines in turn:

| Line | What it does |
| --- | --- |
| `module` | opts this file into Lean's module system. Every file in `MathEconLib` starts this way |
| `public import X` | imports `X` **and passes it on**: files that import this file get `X` too |
| `import X` (no `public`) | imports `X` for use here only; importers do not inherit it |
| `@[expose] public section` | what follows is visible to importers — `public` exposes the statements, `@[expose]` also exposes the definitions |

The matching `end` at the bottom of the file closes that section.

The distinction between the two kinds of import is worth a moment, because it is a real design choice rather than a formality. Look at [`GameTheory/NashExistence.lean`](../MathEconLib/GameTheory/NashExistence.lean), which uses both:

```lean
public import MathEconLib.GameTheory.Basic
public import Mathlib.Analysis.Convex.Quasiconvex

import MathEconLib.ForMathlib.Kakutani
import Mathlib.MeasureTheory.Measure.Prokhorov
```

The first two are public because the file's *statements* mention them: you cannot read its theorems without knowing what a game or a quasiconvex function is. The rest are private because they are needed only inside the *proofs*. A file downstream that wants the Nash existence theorem should not have Prokhorov's theorem forced into scope along with it.

> **`public` is about what your readers inherit, not about what you may use.**

Two practical notes. First, none of this applies to the scratch files you have been writing: a file outside the library needs only `import MathEconLib.BidderProblem.Basic`, and everything in that exposed section is available. You will meet these keywords when you *add* a file to the library, not before. Second, §4.5 explains a separate reason a definition can still be opaque when you are proving things.

### ✍️ Hands-on 4.0 — see the two kinds of import

Open [`GameTheory/NashExistence.lean`](../MathEconLib/GameTheory/NashExistence.lean) and read the header. Predict, before scrolling: which of those imports are mentioned in the *statements* of its theorems, and which are used only inside proofs? Then check.

Now scroll to the bottom of [`BidderProblem/Basic.lean`](../MathEconLib/BidderProblem/Basic.lean). The bare `end` closes the `@[expose] public section`; `end MathEconLib` closes the project namespace. Everything in the public section is available to importers under `MathEconLib`.

Finally, confirm the reassurance above in your own scratch file:

```lean
import MathEconLib.BidderProblem.Basic

open MathEconLib

#check BidderProblem.winProb
```

No `module`, no `public`, and it works.

### 4.1 What the file is for

An auction has many bidders, each uncertain about the others. That is a complicated object. The standard simplification, and the one this file encodes, is to fix attention on **one** bidder and average over everything the others might do. What remains is a single-agent problem described by three functions:

| Field | Meaning |
| --- | --- |
| `winProb b` | the probability of winning if you bid `b` |
| `cost b` | the expected payment if you bid `b` |
| `strategy v` | the bid you make when your valuation is `v` |

Together with the lowest and highest possible valuations, that is the whole model. A bidder with valuation `v` who bids `b` gets, on average, `v * winProb b - cost b`: the value of the object times the chance of getting it, less what they pay. This quantity is called the **payoff**.

If none of that is familiar, [Appendix A](#appendix-a--glossary-of-auction-theory-terms) says more. For reading the Lean, the table above is enough.

Here is the whole file in outline:

```
BidderProblem  (a record: the model's ingredients)
├── lowestType, highestType : ℝ            ← data: range of possible valuations
├── winProb : ℝ → ℝ                        ← data: chance of winning, given a bid
├── winProb_range : ∀ x, winProb x ∈ [0,1] ← a PROOF, stored as a field
├── cost : ℝ → ℝ                           ← data: expected payment, given a bid
└── strategy : ℝ → ℝ                       ← data: what you bid, given a valuation

        │  derived definitions
        ▼
payoff v b = v * winProb b − cost b        what you get, bidding b with valuation v
q          = winProb ∘ strategy            chance of winning, as a function of valuation
U v        = payoff v (strategy v)          what you get by following the strategy

        │  optional extra assumptions, bundled together
        ▼
IsRegular
├── winProb is monotone           ├── strategy is non-negative
└── strategy is monotone on the   └── cost is continuous
    valuation range
```

### ✍️ Hands-on 4.1 — open the real thing

Enough scratch files. Open [`MathEconLib/BidderProblem/Basic.lean`](../MathEconLib/BidderProblem/Basic.lean) in the editor and orient yourself in it.

1. **⌘click** on `Icc` in the `winProb_range` line. VS Code jumps you into Mathlib's own source, where `Set.Icc` is defined. Come back with **⌃-** (control-minus).
2. Hover over `Monotone` further down. A tooltip gives its definition and docstring, without your leaving the file.
3. Put your cursor on the `q_range` lemma and look at the InfoView.

Then, in your own scratch file, confirm the vocabulary from the table above is really there:

```lean
import MathEconLib.BidderProblem.Basic

open MathEconLib

#check BidderProblem.winProb
#check BidderProblem.cost
#check BidderProblem.strategy
#check BidderProblem.payoff
```

Each reports a function taking a `BidderProblem` and returning that field:

```
BidderProblem.winProb (self : BidderProblem) : ℝ → ℝ
BidderProblem.payoff  (B : BidderProblem) (v bid : ℝ) : ℝ
```

These are the projection functions, and dot notation ([§4.4](#44-namespace-variable-and-dot-notation)) is sugar over exactly them. Note the small difference in the argument's name: the fields Lean generated for you call it `self`, while `payoff`, which the author wrote by hand under `variable (B : BidderProblem)`, kept the name `B`. Cosmetic, but it tells you at a glance which declarations were generated and which were written.

### 4.2 `structure` — making a record

```lean
structure BidderProblem where
  lowestType : ℝ
  highestType : ℝ
  winProb : ℝ → ℝ
  winProb_range : ∀ x, winProb x ∈ Icc 0 1
  cost : ℝ → ℝ
  strategy : ℝ → ℝ
```

A `structure` is a record type: several values bundled under one name. Declaring it gives you, for free:

- a way to **build** one, using the `where` syntax you saw in §3.5;
- a way to **read** each field back out, written `B.winProb` for a bidder problem `B`;
- the **anonymous constructor** `⟨0, 1, f, hf, c, s⟩`, which supplies the six fields positionally. Those angle brackets are the `⟨ ⟩` from §2.3, and they show up everywhere in Mathlib as shorthand for "bundle these together."

### ✍️ Hands-on 4.2 — your own record with a proof field

Build the miniature version of `BidderProblem`: a real number carrying a proof it lies in $[0,1]$.

```lean
structure UnitReal where
  val : ℝ
  property : val ∈ Set.Icc (0:ℝ) 1

noncomputable def half : UnitReal where
  val      := 1 / 2
  property := by norm_num [Set.mem_Icc]

#check half.val         -- half.val : ℝ
#check half.property    -- half.property : half.val ∈ Icc 0 1
```

Read that last line closely. The *type* of `property` mentions `half.val`, so the proof is about this particular number rather than about `UnitReal`s in general. Dependency ([§3.4](#34-types-that-depend-on-values)) is doing real work here.

Three things to try:

1. Change `val` to `2` and watch the failure move to `property`.
2. Build the same thing with the anonymous constructor: `⟨1/2, by norm_num [Set.mem_Icc]⟩`. The `⟨ ⟩` supply fields in order.
3. Ask for `#check UnitReal.mk` and read the constructor type Lean generated:
   `UnitReal.mk (val : ℝ) (property : val ∈ Set.Icc 0 1) : UnitReal`.

That constructor is the whole idea in one line: to make one, hand over a number *and* a reason.

### 4.3 Intervals, and why functions are defined everywhere

**`Icc 0 1` means the closed interval $[0,1]$.** The naming is systematic: `I` for interval, then one letter per endpoint, `c` for closed and `o` for open:

| Notation | Interval |
| --- | --- |
| `Icc a b` | $[a,b]$ |
| `Ico a b` | $[a,b)$ |
| `Ioc a b` | $(a,b]$ |
| `Ioo a b` | $(a,b)$ |
| `Ici a` / `Ioi a` | $[a,\infty)$ / $(a,\infty)$ |
| `Iic b` / `Iio b` | $(-\infty,b]$ / $(-\infty,b)$ |

**A second convention is stranger.** `winProb : ℝ → ℝ` is a function defined on *all* real numbers, including negative bids, which make no sense. Mathlib does this deliberately and systematically: it avoids functions with restricted domains, because carrying a domain around infects every statement about the function with side conditions.

Instead, functions are defined everywhere, given arbitrary ("junk") values where they are meaningless, and the real content is placed in *hypotheses*. That is precisely what `winProb_range` does. It is also why, in §4.7, you will find monotonicity asserted only on the valuation range rather than on all of ℝ.

This feels wrong at first. It turns out to be much less painful than the alternative. [Trap 5](#trap-5--junk-values-are-deliberate) revisits it.

### ✍️ Hands-on 4.3 — intervals, and the junk values

First the interval notation, which you will read constantly:

```lean
#check Set.Icc (0:ℝ) 1
example : (0.5 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num [Set.mem_Icc]
example (x : ℝ) (h : x ∈ Set.Icc (0:ℝ) 1) : x ≤ 1 := h.2
```

That last line is the important idiom: membership in `Icc` *is* a conjunction, so `.1` gives the lower bound and `.2` the upper. No unfolding needed.

Now confirm that Mathlib really means what this section says about total functions:

```lean
example : (1:ℝ) / 0 = 0 := by simp
example : Real.log 0 = 0 := by simp
```

Both are true. Division by zero is not an error, not undefined, not a special value. It is zero, chosen so that no statement about division has to carry a side condition.

This looks like vandalism and is in fact bookkeeping. The mathematical content moves into hypotheses: a theorem that genuinely needs `x ≠ 0` says so, and the ones that do not are spared the clutter. [Trap 5](#trap-5--junk-values-are-deliberate) returns to it.

### 4.4 `namespace`, `variable`, and dot notation

```lean
namespace BidderProblem

variable (B : BidderProblem)
```

The file is already inside `namespace MathEconLib`. Its nested `namespace BidderProblem` puts another prefix on what follows, so the full name of `payoff` is `MathEconLib.BidderProblem.payoff`. That is what makes **dot notation** work: for `B : MathEconLib.BidderProblem`, writing `B.payoff v b` invokes that declaration. `open MathEconLib` lets examples use the shorter `BidderProblem.payoff` spelling.

Dot notation is everywhere in Mathlib, and always means the same thing: `h.1`, `h.symm`, `h.trans h'` are all this mechanism.

`variable (B : BidderProblem)` says that every declaration below which mentions `B` should quietly take it as an argument. It is the formal counterpart of a paper saying "fix a bidder problem $B$ for the rest of this section."

### ✍️ Hands-on 4.4 — dot notation is just a lookup rule

```lean
-- these two say exactly the same thing
example (B : BidderProblem) (v : ℝ) : 0 ≤ B.q v := (B.q_range v).1
example (B : BidderProblem) (v : ℝ) : 0 ≤ B.q v := (BidderProblem.q_range B v).1

-- the same mechanism, elsewhere in Mathlib
example (a b : ℝ) (h : a = b) : b = a := h.symm
example (a b c : ℝ) (h : a = b) (h' : b = c) : a = c := h.trans h'
example (P Q : Prop) (h : P ∧ Q) : Q := h.2
```

The rule: for `x : Foo`, writing `x.bar` means `Foo.bar x`. Lean looks at the type of `x`, goes to that type's namespace, and finds `bar`. Nothing more.

This explains a construction that otherwise looks like magic. In `h.symm`, `h` is a *proof*, its type is an equation, and `Eq.symm` is the lemma that equations reverse. Proofs get dot notation because proofs are values with types, like everything else. That is [§3.6](#36-proofs-are-functions) showing up in the syntax.

### 4.5 Definitions, and the `@[simp]` habit

```lean
def payoff (v bid : ℝ) : ℝ := v * B.winProb bid - B.cost bid

@[simp] lemma payoff_eq (v bid : ℝ) :
    B.payoff v bid = v * B.winProb bid - B.cost bid := rfl
```

At first sight the lemma is pointless: it states exactly the definition, and its proof is `rfl` ("true by definition"). Why bother?

Because **definitions are opaque during proofs.** Lean's automation will not spontaneously unfold `payoff` into its body. If it unfolded everything eagerly, goals would balloon into unreadable expressions and proof search would grind. So the definition is sealed, and you publish a controlled interface instead.

The `@[simp]` marker registers the lemma with the `simp` tactic ("simplify"). From then on, any proof that says `simp` will automatically rewrite `B.payoff v bid` into its expanded form. The convention across Mathlib:

> **The definition is private. The `simp` lemmas are its public interface.**

When you define something, immediately ask what equation a later user will need, state it, prove it with `rfl`, and tag it. This file does exactly that three times: for `payoff`, `q`, and `U`.

### ✍️ Hands-on 4.5 — feel why the `simp` lemma is needed

Define something and give it the standard two-line treatment:

```lean
def myPayoff (v b : ℝ) : ℝ := v * b - b

@[simp] lemma myPayoff_eq (v b : ℝ) : myPayoff v b = v * b - b := rfl

example (v : ℝ) : myPayoff v 0 = 0 := by simp
example (v : ℝ) : myPayoff v 1 = v - 1 := by simp
```

Now delete the `@[simp]`, just the attribute, leaving the lemma itself, and re-run. The examples fail with:

```
error: `simp` made no progress
```

Read that literally. `simp` did not fail to find a proof; it found *nothing to do at all*. The definition is sealed, the one lemma that could open it is no longer in the simp set, so `simp` looked at the goal and had no applicable rewrite.

Get them working again without restoring the attribute, in either of two ways:

```lean
example (v : ℝ) : myPayoff v 0 = 0 := by simp [myPayoff_eq]    -- name it explicitly
example (v : ℝ) : myPayoff v 0 = 0 := by unfold myPayoff; ring -- or open it up
```

That is the whole argument for the convention: the definition is deliberately opaque, and `@[simp]` hands out the key once so no later proof has to.

One diagnostic to adopt now: replace `simp` with `simp?` and Lean reports exactly which lemmas it used. When a `simp` call mysteriously succeeds or fails, that is how you find out why.

### 4.6 `class` — bundling optional assumptions

```lean
class IsRegular (B : BidderProblem) : Prop where
  winProb_mono : Monotone B.winProb
  strategy_mono : MonotoneOn B.strategy B.typeInterval
  strategy_nonneg : ∀ v ∈ B.typeInterval, 0 ≤ B.strategy v
  cost_continuous : Continuous B.cost
```

A `class` is a structure that Lean can locate **automatically**. Mathematically, this bundles four extra assumptions under one name: the chance of winning rises with your bid, the bidding strategy rises with your valuation, bids are non-negative, and costs vary continuously.

Later theorems that need these assumptions are written:

```lean
theorem foo (B : BidderProblem) [IsRegular B] : ...
```

The **square brackets** mean "Lean, find this argument yourself." You never pass it by hand; Lean searches for a registered `instance`. This is how the library arranges its hierarchy of assumptions so that establishing a strong hypothesis silently unlocks every theorem stated under weaker ones. [Appendix B](#appendix-b--how-matheconlib-is-organised) describes the mechanism.

Three kinds of brackets appear in Lean, and the difference matters:

| Written | Called | Do you supply it? |
| --- | --- | --- |
| `(x : T)` | explicit | yes, in order |
| `{x : T}` | implicit | no — Lean infers it from the other arguments |
| `[C x]` | instance | no — Lean searches for it |

### ✍️ Hands-on 4.6 — assumptions that arrive by themselves

Write a theorem that demands regularity, and pull the pieces back out:

```lean
example (B : BidderProblem) [h : B.IsRegular] : Monotone B.winProb := h.winProb_mono
example (B : BidderProblem) [h : B.IsRegular] : Continuous B.cost := h.cost_continuous
```

Naming the instance `h` is optional; it is there so you can reach inside. Most of the time you write `[B.IsRegular]` with no name and simply use lemmas that require it; Lean locates the instance without being told.

Now delete `[h : B.IsRegular]` from the first line. You get `unknown identifier 'h'`. More characteristically, when a *lemma* needs an instance you have not supplied, the error reads `failed to synthesize`.

That phrase always means one thing, **Lean went looking for an instance and could not find one**, and the fix is always the same: add the missing `[...]` to your hypotheses. Learn to recognise it on sight, because it looks alarming and is almost always trivial.

### 4.7 `Monotone` versus `MonotoneOn`

Look closely at the first two fields of `IsRegular`:

```lean
winProb_mono  : Monotone B.winProb
strategy_mono : MonotoneOn B.strategy B.typeInterval
```

These are *different predicates*, and the difference is not stylistic. `Monotone f` says `f` is increasing everywhere. `MonotoneOn f s` says it is increasing only on the set `s`.

`winProb` gets the everywhere version: bidding more should never reduce your chance of winning, at any bid. `strategy` gets the restricted version, because a bidding strategy is only meaningful for valuations in the actual range. Outside it the function is junk (§4.3), and demanding monotonicity there would be both unnecessary and false.

This distinction gets its own entry in Part 6, because it is the most common source of beginner frustration in the whole library.

### ✍️ Hands-on 4.7 — the two monotonicities

```lean
-- "everywhere" gives you "on a set", for free
example (f : ℝ → ℝ) (hf : Monotone f) : MonotoneOn f (Set.Icc 0 1) := hf.monotoneOn _

-- and "everywhere" applies directly at any two points
example (f : ℝ → ℝ) (hf : Monotone f) (a b : ℝ) (hab : a ≤ b) : f a ≤ f b := hf hab
```

The first is the conversion you will reach for constantly. Memorise the shape `hf.monotoneOn _`.

Now attempt the converse:

```lean
example (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc 0 1)) : Monotone f := hf
```

It fails, and of course it should: knowing `f` increases on $[0,1]$ says nothing about its behaviour at $x = 7$. The type error is Lean declining to let you claim more than you established.

Note also the difference in *use*. `Monotone f` applied to `hab : a ≤ b` gives the conclusion at once, as above. `MonotoneOn f s` first wants proofs that `a ∈ s` and `b ∈ s`, and only then `a ≤ b`. That extra bookkeeping is exactly what makes the restricted form more work, and why the library uses the global form wherever it honestly can.

---

## Part 5 — Watching a proof happen

Reading finished proofs teaches you less than watching one being built. This part shows a complete tactic proof with the machine's actual output at every step.

**The claim.** If a bidder's valuation is non-negative, and following their strategy happens to cost them nothing, then the payoff from following that strategy is non-negative. Obvious mathematically, since you get something for free, but let us watch Lean do it.

```lean
example (B : BidderProblem) (v : ℝ) (hv : 0 ≤ v)
    (hcost : B.cost (B.strategy v) = 0) : 0 ≤ B.U v := by
  rw [BidderProblem.U_eq]
  rw [hcost, sub_zero]
  apply mul_nonneg hv
  exact (B.winProb_range _).1
```

Four lines. Here is what Lean shows at each stage. Everything above the `⊢` is what you may assume; the line after `⊢` is what remains to be shown.

**At the start.** The assumptions are named (`hv` for the non-negativity, `hcost` for the zero cost), and the goal is the statement itself:

```
B : BidderProblem
v : ℝ
hv : 0 ≤ v
hcost : B.cost (B.strategy v) = 0
⊢ 0 ≤ B.U v
```

**After `rw [BidderProblem.U_eq]`.** The `rw` tactic ("rewrite") replaces something using an equation, here the `simp` lemma from §4.5 that unfolds `U`. Note that only the goal changed:

```
⊢ 0 ≤ v * B.winProb (B.strategy v) - B.cost (B.strategy v)
```

**After `rw [hcost, sub_zero]`.** Two rewrites in one step. First `hcost` replaces the cost term with `0`; then `sub_zero` (a Mathlib lemma saying `a - 0 = a`) tidies up. Notice we rewrote using a *hypothesis*. Hypotheses that are equations can be used exactly like lemmas:

```
⊢ 0 ≤ v * B.winProb (B.strategy v)
```

**After `apply mul_nonneg hv`.** `mul_nonneg` is the Mathlib lemma "if `0 ≤ a` and `0 ≤ b` then `0 ≤ a * b`." Applying it with `hv` supplying the first condition leaves the second as a new goal. This is the `apply` pattern: work backwards from the goal, and whatever the lemma still needs becomes what you must prove:

```
⊢ 0 ≤ B.winProb (B.strategy v)
```

**Finally, `exact (B.winProb_range _).1`.** No tactic magic left; we supply the term directly, and it is the certificate from §3.5. `B.winProb_range _` gives us `B.winProb (B.strategy v) ∈ Icc 0 1`; membership in an interval is a pair of inequalities, and `.1` takes the first. The underscore lets Lean work out the point for itself.

No goals remain, and the proof is complete.

**What to take from this.** A tactic proof is a *conversation*: you make a move, the machine tells you what is left, you make another. The goal shrinks until it is something you can hand over directly. This is why [Part 0](#part-0--working-with-lean-on-your-mac) insists on the InfoView panel. Without it you are working blind. With it, the proof almost writes itself.

### ✍️ Hands-on 5 — take the proof apart

Type the four-line proof into your scratch file and get it compiling:

```lean
example (B : BidderProblem) (v : ℝ) (hv : 0 ≤ v)
    (hcost : B.cost (B.strategy v) = 0) : 0 ≤ B.U v := by
  rw [BidderProblem.U_eq]
  rw [hcost, sub_zero]
  apply mul_nonneg hv
  exact (B.winProb_range _).1
```

Then work through it as an experiment rather than a text.

1. **Step through it.** Put the cursor at the start of each line in turn and check the InfoView against the goal states printed above. If they differ, the library has changed and this manual needs updating.

2. **Comment out the last line.** The error becomes `unsolved goals`, showing you exactly what was left. Uncomment.

3. **Reorder two steps.** Move `apply mul_nonneg hv` above the `rw` lines. It fails, because `apply` needs the goal already in the shape `0 ≤ _ * _`, and before rewriting it is still `0 ≤ B.U v`. Tactic order is not cosmetic.

4. **Collapse it.** Try replacing the two `rw` lines with a single `simp [BidderProblem.U_eq, hcost]`. It works, and the proof becomes two lines:

   ```lean
   example (B : BidderProblem) (v : ℝ) (hv : 0 ≤ v)
       (hcost : B.cost (B.strategy v) = 0) : 0 ≤ B.U v := by
     simp [BidderProblem.U_eq, hcost]
     exact mul_nonneg hv (B.winProb_range _).1
   ```

   Shorter is not always better. The four-line version shows its reasoning; the two-line version hides it inside `simp`. Library authors trade these off constantly, and `simp?` will tell you what the short version actually did.

5. **Weaken a hypothesis.** Delete `hv : 0 ≤ v` and watch which step breaks. It is `apply mul_nonneg hv`. The proof tells you precisely where non-negativity of the valuation was needed, which is a kind of feedback informal proofs rarely give.

---

## Part 6 — Traps for beginners

### Trap 1 — "Everywhere" versus "on a set"

Mathlib keeps parallel versions of nearly every analytic property:

| Everywhere | On a set `s` |
| --- | --- |
| `Monotone f` | `MonotoneOn f s` |
| `Continuous f` | `ContinuousOn f s` |
| `Differentiable ℝ f` | `DifferentiableOn ℝ f s` |
| `Integrable f μ` | `IntegrableOn f s μ` |
| `StrictMono f` | `StrictMonoOn f s` |

Lemmas about one do **not** automatically apply to the other. An everywhere-property restricts to any subset (`Monotone.monotoneOn` does this), but the converse needs the set to be everything.

**Diagnostic habit.** When a proof will not close and the goal *looks* right, first ask whether you are mixing an everywhere-property with an on-a-set one, or using the wrong set.

### Trap 2 — `=` versus `==` versus `↔`

- `=` for equality of two things. A `Prop`. This is nearly always what you want.
- `==` for boolean equality. A `Bool`. Computes; used in programs, rarely in mathematics.
- `↔` for "if and only if", between two *propositions*.

Use `↔` when both sides are statements, `=` when both sides are objects.

### Trap 3 — `rfl` failing when things "obviously" match

`rfl` proves goals that are true *by definition*, by unfolding and computing. It does not reason arithmetically, does not consult your hypotheses, and will not always see through an opaque definition (§4.5). When `rfl` fails, escalate to `simp`, `norm_num`, `ring`, or `omega`.

### Trap 4 — `noncomputable` is not a complaint about your mathematics

Write the `coinFlip` definition from §3.5 without the keyword and Lean says:

```
failed to compile definition, consider marking it as 'noncomputable'
because it depends on 'Real.instDivInvMonoid', which is 'noncomputable'
```

Nothing is wrong. Real numbers in Mathlib are built classically, as limits of sequences using the axiom of choice, so real division has no executable procedure behind it. You can *prove* whatever you like about the definition; Lean simply cannot *run* it.

Rule of thumb: a definition that produces a real number via division, inversion, square roots, limits, or integrals will need `noncomputable`. Add the keyword and move on.

Note the asymmetry: `theorem`s never need it. Proofs are erased when compiling, proof irrelevance again (§3.7), so there is nothing to run. Only *data* can be noncomputable.

### Trap 5 — Junk values are deliberate

In Mathlib, `(1 : ℝ) / 0 = 0`. Also `Real.log 0 = 0` and `Real.sqrt (-1) = 0`. This is not sloppiness; it is the total-functions convention from §4.3. Keeping functions defined everywhere avoids threading domain conditions through every statement, and the real content moves into theorem hypotheses instead (`hx : x ≠ 0`).

Do not try to fix it. Do remember that a theorem about a function may need a hypothesis ruling out the junk region.

### Trap 6 — Editing a definition invalidates its `simp` lemmas

If you change a `def` whose companion lemma was proved by `rfl`, either the lemma still holds (fine) or the file stops compiling (also fine; that is the machine catching you). What cannot happen is a silent mismatch between a definition and its stated interface. Trust the failure.

### Trap 7 — Typing the symbols

Type a backslash and the abbreviation, then space: `\R` gives `ℝ`, `\to` gives `→`, `\forall` gives `∀`, `\in` gives `∈`, `\le` gives `≤`, `\o` gives `∘`, `\<` and `\>` give `⟨` and `⟩`. Hovering over any symbol in VS Code tells you its abbreviation. The full list is in §2.3.

### ✍️ Hands-on 6 — spring each trap deliberately

Better to meet these now, on purpose, than mid-proof at a bad moment.

**`rfl` and the reals (Trap 3).** This looks like it must work:

```lean
example : (2:ℝ) + 2 = 4 := rfl
```

It fails with a type mismatch. Then note the contrast with naturals, where computation *is* available:

```lean
example : (2:ℕ) + 2 = 4 := rfl      -- this one works
```

Same statement, different number system, opposite outcome. Reals do not reduce, so `rfl` has nothing to unfold. Use `by norm_num`.

**`noncomputable` (Trap 4).** Write a definition producing a real by division, without the keyword:

```lean
def aHalf : ℝ := 1 / 2
```

Read the error, add `noncomputable`, watch it compile. Nothing about the mathematics changed. Note also that `theorem`s never need this, because proofs are erased.

**Junk values (Trap 5).** Confirm Mathlib means it:

```lean
example : (1:ℝ) / 0 = 0 := by simp
example : Real.log 0 = 0 := by simp
```

**Global versus restricted (Trap 1).** Return to Hands-on 4.7 and try the same conversion for continuity, turning `ContinuousOn` into `Continuous`. The failure has the identical shape, because the issue was never about monotonicity; it is about the difference between a claim on a set and a claim everywhere.

**`=` versus `↔` (Trap 2).** Both of these are fine, and knowing which to reach for is the skill:

```lean
example (P : Prop) : P ↔ P := Iff.rfl     -- statements
example (a : ℝ) : a = a := rfl            -- objects
```

---

## Part 7 — Reference tables

### Declarations

| Keyword | Purpose |
| --- | --- |
| `def` | a definition; body opaque during proofs |
| `noncomputable def` | a definition Lean cannot execute — usually anything producing a real (Trap 4) |
| `abbrev` | a definition Lean unfolds freely; for notation-like shorthands |
| `theorem` / `lemma` | a proved statement |
| `example` | a statement proved but not named — ideal for scratch work |
| `structure` | a record type |
| `class` | a structure Lean can find automatically |
| `instance` | registers something for `class` search to find |
| `variable` | declares parameters shared by the declarations below |
| `namespace` … `end` | prefixes names; enables dot notation |

### Commands for asking Lean questions

| Command | Purpose |
| --- | --- |
| `#check e` | show the type of `e` |
| `#print f` | show the definition of `f` |
| `#eval e` | evaluate a computable expression |
| `exact?` | **search Mathlib for a proof of the current goal** |
| `apply?` | search for lemmas that could apply to the goal |
| `simp?` | show which lemmas `simp` actually used |

`exact?` is the one to learn first. With a goal on screen it will often locate precisely the Mathlib lemma you need, and it is the fastest way to discover the library. Know its limit, though: it searches for *library lemmas*, and will not think to combine or take apart the hypotheses you already have (Exercise 4 shows a goal it fails on for exactly this reason). The other reliable method of discovery is searching the Mathlib source directly, which lives in `.lake/packages/mathlib/` inside the project.

### Everyday tactics

| Tactic | Use |
| --- | --- |
| `rfl` | the goal is true by definition |
| `exact h` | supply the proof `h` directly |
| `apply f` | work backwards: use `f`, leaving its hypotheses as new goals |
| `intro x` | introduce a `∀`-variable, or assume the left side of an implication |
| `rw [h]` | rewrite using equation `h` |
| `simp [lemmas]` | simplify using the `simp` set plus anything extra you name |
| `norm_num` | arithmetic with concrete numbers |
| `ring` | identities in commutative rings |
| `linarith` | goals that follow by linear arithmetic from the hypotheses |
| `omega` | linear arithmetic over integers and naturals |
| `constructor` | split an "and" into two goals, or build a structure |
| `obtain ⟨a, b⟩ := h` | take apart an "and" or a "there exists" |
| `calc` | chained equalities or inequalities, written out in steps |

### How Mathlib names things

Names describe the statement, read left to right, in `snake_case`:

- `q_range`: about `q`, gives a range
- `payoff_eq`: about `payoff`, an equation
- `mul_nonneg`: about multiplication, concludes non-negativity
- `add_comm`: addition is commutative
- `Set.mem_Icc`: membership in `Icc`

Hypotheses are conventionally named starting with `h`: `hv`, `hcost`, `hmono`.

Once this clicks you can often *guess* a lemma's name correctly, which is faster than any search.

### ✍️ Hands-on 7 — make the tools find things for you

**`exact?` searches the library.** Put the cursor on the goal and let it work:

```lean
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by exact?
```

It answers with something of the form `Try this: exact mul_nonneg ha hb`. Click the suggestion and it rewrites the tactic for you. Do not be surprised if the name offered is `Left.mul_nonneg` or another variant. Which one surfaces depends on your imports, and several equivalent lemmas exist. That is itself a useful early lesson: Mathlib usually has more than one route to the same fact.

**Know its limit.** Now try:

```lean
example (x : ℝ) (h : x ∈ Set.Icc (0:ℝ) 1) : x ≤ 1 := by exact?
```

It *cannot* close this, reporting `exact? could not close the goal`, even though `exact h.2` works, and even if you first run `rw [Set.mem_Icc] at h`. The reason matters: `exact?` hunts for *library lemmas*, and does not think to take your own hypotheses apart with `.1` and `.2`. It answers "which lemma is this?", never "combine what I already have."

**Guess a name.** Mathlib names are compositional, so predict before you look. What would "addition is commutative" be called? "A product of non-negatives is non-negative"? Check yourself:

```lean
#check @add_comm
#check @mul_nonneg
```

**Read the source.** In the terminal:

```bash
grep -rn "theorem le_min" .lake/packages/mathlib/Mathlib/Order/ | head -5
```

Between `exact?`, name-guessing, and grep, you can find almost anything in Mathlib without leaving the project.

---

## Part 8 — Exercises

Work in your own scratch file under `MathEconLib/Playground/`, which is excluded from version control, so nothing you do there can disturb the library. Worked versions of the Part 3 material live in [`MathEconLibTest/Manual/HandsOn.lean`](../MathEconLibTest/Manual/HandsOn.lean) if you want to compare.

Solutions follow the exercises. All of them have been compiled.

**Exercise 1. Build a `BidderProblem`.** Make one whose `winProb` is `fun b => min 1 (max 0 b)`: the bid itself, clipped into $[0,1]$. Use `cost := fun b => b / 2` and `strategy := id`. The work is in `winProb_range`.

**Exercise 2. Break it deliberately.** In your answer to Exercise 1, change `winProb` to `fun _ => 2` and read the error carefully. Error messages are how you learn what Lean wanted.

**Exercise 3. A one-line proof.** Prove `B.q v ≤ 1` for any bidder problem `B` and valuation `v`. (`q_range` from §3.6 already gives you both halves; you need the second.)

**Exercise 4. Let Lean find the lemma.** Write this and see what `exact?` suggests:

```lean
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by exact?
```

Then try the same trick on `example (x : ℝ) (h : x ∈ Icc (0:ℝ) 1) : x ≤ 1 := by exact?` and observe that it *fails*, even though the goal follows immediately from `h`. Why? See the solution.

**Exercise 5. Watch the goal move.** Take the proof from Part 5, put your cursor at the start of each line in turn, and check the InfoView against the goal states printed there.

<details>
<summary><strong>Solutions</strong></summary>

**1.** The key steps are `rw [Set.mem_Icc]` to turn interval membership into a conjunction, then `constructor` to split it. Watch the argument order in the last line: because `1` sits on the *left* of the `min`, the lemma is `min_le_left`, not `min_le_right`.

```lean
noncomputable def clamped : BidderProblem where
  lowestType    := 0
  highestType   := 1
  winProb       := fun b => min 1 (max 0 b)
  winProb_range := by
    intro x
    rw [Set.mem_Icc]
    constructor
    · exact le_min zero_le_one (le_max_left 0 x)
    · exact min_le_left 1 _
  cost          := fun b => b / 2
  strategy      := id
```

**2.** You should see `⊢ False` at the `winProb_range` field. Lean simplified `(2 : ℝ) ∈ Icc 0 1` down to an impossibility.

**3.** `example (B : BidderProblem) (v : ℝ) : B.q v ≤ 1 := (B.q_range v).2`

**4.** On the first goal `exact?` answers `Try this: exact mul_nonneg ha hb`, the very lemma used in Part 5.

The second goal it cannot close, reporting ``exact? could not close the goal``. This marks a real boundary of the tool. The goal *is* immediate: `x ∈ Icc 0 1` is by definition the pair of facts `0 ≤ x` and `x ≤ 1`, so `h.2` proves it, and writing `exact h.2` by hand works. But `exact?` searches the library for *lemmas*; it does not think to take your hypotheses apart with `.1` and `.2`. (Adding `rw [Set.mem_Icc] at h` first does not rescue it either.)

The lesson: `exact?` is excellent at "which library lemma is this," and no help at all with "combine what I already have." For the latter, look at your hypotheses yourself.

**5.** No written answer. But if the InfoView shows something different from Part 5, the library has changed and this manual needs updating.

</details>

### Where to go next in the library

1. **`SingleParameter/Basic.lean`**: mostly definitions, and the gentlest entry point. It is also the deterministic core the rest of the library is built on.
2. **`Mechanism/Core/Mechanism.lean`**: the rules of a mechanism: which outcome is chosen and how money moves, as functions of everyone's actions. Also mostly definitions.
3. **`BidderProblem/Basic.lean`**: the file dissected above, and the bridge from that core into the auction setting.
4. **`BidderProblem/EnvelopeIC.lean`**: the first file with substantial mathematics, and where you will see Mathlib's measure theory doing real work.
5. **`BidderProblem/TypeDeviationIC.lean`**: payment identities and Myerson's lemma.
6. **`Auction/RevenueEquivalence.lean`**: a landmark result of auction theory, and a good test of whether you can now read Lean.

Posted pricing is a second branch rather than a further rung on this ladder. If selling at a fixed price interests you more than auctions do, read `SingleParameter/PostedPrice.lean` for the deterministic version and `ValueDistribution/PostedPrice.lean` once a distribution of buyer values is in play.

### Learning Lean beyond this manual

- **Mathematics in Lean.** The standard tutorial, working through real mathematics rather than toy problems. The recommended next step, and it comes with exercises.
- **Theorem Proving in Lean 4.** The language reference; heavier on type theory, and the right place to go for the questions Part 3 raised.
- **The Mathlib documentation.** Searchable, and pairs well with `exact?`.
- **The Lean Zulip chat** (`leanprover.zulipchat.com`). Unusually welcoming, with a `#new members` stream that exists precisely for the questions you are about to have.

### Contributing to `MathEconLib`

The `ForMathlib/` folder holds general mathematical results needed by MathEconLib that may be suitable for upstream contribution to Mathlib. Small, well-scoped additions can be suitable first contributions, but the folder also contains substantial results. Upstream contributions are voluntary, with no promised submission or deadline; see the [ForMathlib policy](../CONTRIBUTING.md#formathlib-and-upstream-contributions).

Before opening a pull request, stage any new Lean files with `git add` so that
the import generator can see them. From the repository root, run:

```bash
bash scripts/update-imports.sh  # regenerate and verify both library and test imports
lake build
```

Commit any changes to `MathEconLib.lean` and `MathEconLibTest.lean` with your work.
Use `bash scripts/update-imports.sh --check` to verify without changing files.
See the [verification and review requirements](../CONTRIBUTING.md#verification-bar)
before requesting review. Core changes need maintainer review and the applicable
CI checks must pass on the latest PR revision.

**House rules.** Names follow the Mathlib conventions in [Part 7](#how-mathlib-names-things), and the tactic `native_decide` is not permitted anywhere in the library. [`CONTRIBUTING.md`](../CONTRIBUTING.md) has the rest — no `sorry` or `admit`, `#print axioms` on new results showing only the three axioms from [Part 1](#part-1--why-formalise-mathematics-at-all), the API stability pins, and the design-first rule for changes to the core layers.

The second rule repays understanding rather than mere obedience. `native_decide` settles a goal by compiling it to machine code and running it, then asking you to believe the answer. It is fast, and for some finite checks it is the only practical option. But it moves the compiler and the runtime inside the trusted base, alongside the kernel. A proof using it is no longer checked by the small, heavily scrutinised program described in [Part 1](#part-1--why-formalise-mathematics-at-all); it is underwritten by the whole Lean compiler. Since the trusted base is the entire argument for formalising in the first place, the project declines to enlarge it.

---

## Appendix A — Glossary of auction-theory terms

Enough to read the library. Not a substitute for a course.

**Valuation** (in the code, *type*). What the object is worth to a bidder. Private information, known only to them. The code writes `lowestType` and `highestType` for the range of possible valuations.

**Bid.** What the bidder announces. The **strategy** is the rule turning a valuation into a bid.

**Interim.** Describes a quantity computed after a bidder learns their own valuation but before learning anyone else's, so it is an average over the others. `winProb` and `cost` are both interim quantities: they have already averaged out what the opponents do.

**Payoff.** `v * winProb b - cost b`. What you expect to gain by bidding `b` when the object is worth `v` to you: value times the chance of getting it, less the expected payment. The form (value times probability, minus money) is called **quasi-linear**.

**Mechanism.** The rules of the auction: who gets the object and who pays what, as a function of all the bids. Independent of any beliefs about bidders.

**Posted price.** Selling at a single take-it-or-leave-it price rather than by auction. The buyer's only choice is whether to buy, which makes it the simplest mechanism in the library and a good place to see the general machinery working on something small. In `SingleParameter/PostedPrice.lean`.

**Single-parameter problem.** The generalisation the library proves its main results at. One agent has a real-valued type `v`, chooses an action `a`, and gets `v · x(a) - t(a)`: the type enters utility only through the scalar allocation `x(a)`. A bid, a report, or a decision to buy are all such actions, so the envelope and payment theorems are proved once here and reused everywhere. In `SingleParameter/Basic.lean`.

**Incentive compatible (IC).** A mechanism is incentive compatible if no bidder can do better by misreporting their valuation. Truthfulness is optimal. The library has a hierarchy of increasingly strong versions of this condition.

**Envelope theorem.** A result letting you recover a bidder's equilibrium payoff by integrating their winning probability over valuations. A workhorse of the field, and the mathematical core of `BidderProblem/EnvelopeIC.lean`.

**Myerson's lemma.** Roughly: once the allocation rule is fixed and the mechanism is incentive compatible, the payments are pinned down up to a constant. Formalised in `BidderProblem/TypeDeviationIC.lean`.

**Revenue equivalence.** The striking consequence that broad classes of auction which look quite different, first-price and second-price among them, nevertheless yield the seller the same expected revenue. In `Auction/RevenueEquivalence.lean`.

**Value distribution.** How buyers' valuations are spread out, as a probability distribution over the reals. The seller does not know any individual's valuation but is assumed to know this distribution. In `ValueDistribution/`.

**Virtual value.** A transformed valuation that accounts for the information rent a buyer earns from private information. Expected seller profit can be rewritten as expected *virtual* surplus, which is what turns choosing a price into an ordinary maximisation. In `ValueDistribution/VirtualValue.lean`.

**Regular.** As used by `IsRegular`, a package of technical smoothness and monotonicity assumptions that rule out pathological cases.

---

## Appendix B — How `MathEconLib` is organised

Three layers, separating the rules of an auction from its probabilistic setting from the single-bidder problem that results. The arrows run in the direction of increasing specialisation:

```
Mechanism      the rules: who gets the object, who pays what,
    │          as a function of everyone's bids
    ▼
Auction        those rules PLUS the probabilistic setting:
    │          how valuations are distributed
    ▼          (toBidderProblem)
BidderProblem  one bidder's view, with everyone else averaged out:
               winProb, cost, strategy
```

The final step is where the mathematics becomes tractable: a game among many bidders becomes a single-agent optimisation problem, which the envelope theorem then solves.

Sitting on top of `BidderProblem` is a chain of incentive-compatibility conditions, each stronger than the next:

```
HasUniversalIC  ⟹  HasTypeDeviationIC  ⟹  HasEnvelopeIC
       │                    │                    │
       │                    │                    └─→ envelope theorem,
       │                    │                        Lipschitz utility,
       │                    │                        integral representation
       │                    └─→ payment identity, Myerson's lemma,
       │                        revenue equivalence
       └─→ (the strongest assumption; implies both of the others)
```

Each `⟹` is registered with Lean as an `instance` (§4.6). The practical effect is that if you prove the strongest condition holds, every theorem stated under the weaker ones becomes available automatically, with no further work. It is the machine-checked counterpart of a paper remarking that "Assumption 1 implies Assumption 2, so the results of Section 5 apply."

The three layers above are the auction spine, but they now sit on a more general
deterministic core. `SingleParameterProblem` models an affine-in-type
quasilinear choice problem over an arbitrary action type, and
`BidderProblem.toSingleParameterProblem` bridges into it losslessly, so the
envelope and payment results are proved once at that level and reused here. A
separate layer supplies value distributions.

The rest of the library:

| Folder | Contents |
| --- | --- |
| `SingleParameter/` | the deterministic core: affine-in-type quasilinear problems, the IC hierarchy, envelope and payment results |
| `ValueDistribution/` | real-valued value distributions, posted-price demand, expected payment, seller profit |
| `Mechanism/` | allocation and payment rules |
| `Auction/` | auctions with a probabilistic environment; revenue equivalence, symmetric private values, affiliation, all-purchase auctions |
| `BidderProblem/` | the single-bidder view and the IC hierarchy |
| `GameTheory/` | existence of Nash equilibria for continuous games |
| `ForMathlib/` | general mathematics and potential Mathlib contributions — Kakutani and Schauder fixed points, measure-theoretic lemmas |
| `Statistics/` | order statistics |
