# NominalFrames.jl


## What is this for?
This is a codebase for computational "logical expressivism", as described in [Reasons for Logic, Logic for Reasons (2025)]((https://philpapers.org/archive/HLOPOR.pdf)) (R4LL4R). This is a 
framework which *begins* with a consequence relation, e.g. 

```
Bird(x) ⊢ Flies(x)   Penguin(x),Bird(x) ⊬ Flies(x)   Bird(x) ⊢ Flies(x),Swims(x)
```

> [!Note] 
> **How to read the ⊢ notation:** 
> The turnstile ⊢ denotes a notion of _consequence_, which could be formal (e.g. the consequence relation of intuitionistic logic) or informal (e.g. some model of what sentences follow from others... or, in the other direction, which are good reasons for others). Once you are comfortable with that, the next hurdle to overcome is the fact _multiple_ sentences can appear on either side of the turnstile! One trick is to think of the commas on the left (between premises) as "and" and the commas to the right (between conclusions) as "or". So, if you are used to thinking of truth conditions rather than taking this notion of inference as primary, then an inference is good if all of the premises being true means at least one of the conclusions is true. One last way to think about this without an appeal to 'truth': the inference is good if it's bad to simultaneously assert all the premises and deny all the conclusions.

The data of one of these consequence relations is called an _implication frame_. You have access to at least one of these in virtue of being a fluent speaker of some natural language, but you could also come up with many more.[^1] This codebase allows a user to declare their own implication frames by specifying a signature (a set of predicates with arities, e.g. `Bird(-), Flies(-),IsBiggerThan(-,=),MoonIsMadeOfCheese()`) and then stating precisely which implications are the good ones, according to the frame.

[^1]: Consider how notions of consequence over the same sentences can vary over groups, places and time periods. Consider any formal language's notion of consequence.  Consider anthropologically gathering this data from observing the social practices of an uncontacted tribe. Consider how many books (such as [Roberts Rules of Order](https://en.wikipedia.org/wiki/Robert%27s_Rules_of_Order)) codify certain inferences in a very restricted vocabulary.

Traditionally, logicians describe _meaning_ via semantic machinery, which includes things like [domains of discourse](https://en.wikipedia.org/wiki/Domain_of_discourse), possible worlds, interpretation functions, semantic consequence relations.
However, a frame seems to have no explicit appeals to these kinds of semantic gadgets; it just has the consequence relation. Logical expressivism _derives_ a space of semantic values, an interpretation function for predicates in our signature + logical complexes thereof, and a semantic consequence relation.

Therefore we can, having started with a _pre-logical_ notion of consequence, run logically-articulated queries on the implication frame. There are other aspirations for what to do with this construction, but at the moment running queries (in the so-called "implication space" of the frame, using semantic values and semantic consequence) is the primary feature of this codebase. 

>[!Warning] 
> **A limitation:** Nominal sets do not have a notion of duplication of variables (equivalently, they do not have a notion of substitution with arbitrary variables: only substitution of a variable with a free variable). This means if one's signature has `Loves(-,=)` as a predicate, that one is capable of declaring good inferences such as `Loves(a,b)⊢Loves(b,a)` but _not_ inferences such as `⊢Loves(a,a)`. In some sense this is a limitation, but in another it is not. One might imagine that `⊢Loves(a,a)` is simply syntactic sugar for `⊢Loves²(a)`, and one could automatically generate predicates associated with each possible identification of the argument positions. Regardless, nominal sets would treat these as different predicates for all practical purposes.  


## Why do logic this way?

One reason to work in this "backwards" direction from traditional semantics is that there are many notions of consequence that are inexpressible from the semantic viewpoint.[^2] It is taken as a criterion of adequacy that one's formal semantics has a consequence relation which satisfies _reflexivity_, _transitivity_, and _monotonicity_ (among the three it is most common to reject this last demand). This means, when trying to pick a logic to describe / represent / navigate some subject matter, one is _forced_ to assume that the consequence relation of that domain satisfies these structural principles. This is far too prescriptive for a modeling tool which is meant to be descriptive. Although ordinary mathematics and scientific reasoning often satisfies these structures, we hope the logical expressivist approach allows one to retain all of the useful tools of formal semantics without having to compromise on faithfully representing the our domains which truly matter to us, even if their ordinary/pre-logical consequence relations fail to have the structure expected of purely logical consequence relations


[^2]: This critique does not apply to some sufficiently rich approaches to formal semantics (in particular, some [hyperintentional](https://plato.stanford.edu/entries/hyperintensionality/) ones, see Chapter 4 of [R4LL4R](https://www.routledge.com/Reasons-for-Logic-Logic-for-Reasons-Pragmatics-Semantics-and-Conceptual-Roles/Hlobil-Brandom/p/book/9781032360775)).

Note this is a distinct approach from traditional "nonmonotonic logic". It is classically meta-reasoning about non-monotonic consequence relations.

## How to use

See the `demos/` folder. Both demos are written for readers of _R4LL4R_ and assume contraction and containment throughout:

- `demos/demo.jl` — birds, penguins and flying: declaring a nonmonotonic implication frame, then asking it logically complex questions (¬, ∧, ∨, ⇒, ∀, ∃).
- `demos/courtroom.jl` — accusers, alibis and guilt: a two-place predicate, several individuals, quantifiers, and a court in which Beck–Chevalley fails (the content of "anyone" depends on who is in scope).

Run one with `julia --project=. demos/demo.jl`, or both with `julia --project=. demos/rundemos.jl`.

## Road map

- Morphisms between frames
  - Declaration and automatic search
  - (Co)limits of frames to glue/multiply them together
- Scorekeeping dynamics
  - Also 'argument crux' identification

>[!Caution]
> This repo is a sequel to [ROLE.jl](https://github.com/kris-brown/ROLE/), which is informed by this [category-theoretic reconstruction](https://arxiv.org/abs/2605.24796) of Chapter 5 of [R4LL4L](https://www.routledge.com/Reasons-for-Logic-Logic-for-Reasons-Pragmatics-Semantics-and-Conceptual-Roles/Hlobil-Brandom/p/book/9781032360775). The present extension to use nominal sets to represent predication lies ahead of any work which has been published, so it should be considered extremely experimental.
> Because this library is currently under active development, it is not yet at a point where a constant API/behavior can be assumed. That being said, if this project looks interesting/relevant please contact me at `kris@topos.institute`!

