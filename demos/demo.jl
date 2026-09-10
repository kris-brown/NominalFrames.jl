# # Birds, penguins, and flying
#
# A first demonstration, for readers of *Reasons for Logic, Logic for Reasons*.
# Run it with `julia --project=. demos/demo.jl`.
#
# R4LL4R's starting point is a relation of material consequence among
# claimables, given *before* any logical vocabulary: some implications are
# good, others are not, and the good ones need not be monotonic or transitive.
# Logical vocabulary is then introduced to make explicit what is already
# implicit in that relation.
#
# This file does exactly that with a computer. We
#
#   1. write down a vocabulary of claimables,
#   2. list which implications among them are good (an implication frame),
#   3. ask the frame about implications we did not list, and
#   4. introduce ¬, ∧, ∨, ⇒, ∀, ∃ and ask logically complex questions, whose
#      answers are *derived* from the frame in step 2.
#
# Throughout, premises and conclusions are sets (asserting something twice is
# asserting it once) and containment holds (`A ⊢ A` is good, whatever else is
# said). The two standing assumptions are made in `prelude.jl`.

module Tweety

include("prelude.jl")

# ## 1. The vocabulary
#
# Three predicates, each with one argument place.

banner("1. The vocabulary")

Bird    = Predicate(:Bird, 1)      # "x is a bird"
Penguin = Predicate(:Penguin, 1)   # "x is a penguin"
Flies   = Predicate(:Flies, 1)     # "x flies"
Σ = Signature([Bird, Penguin, Flies])

say("Claimables are built by filling the argument place with an individual:")
say("    Bird(tweety), Penguin(opus), Flies(tweety), ...")

# ## 2. The good implications
#
# An implication frame is a list of good implications. Two kinds are listed,
# because they differ in their range of subjunctive robustness:
#
# - *defeasible* implications, written with `κ`: good exactly as stated (and,
#   by containment, when the same claim is added to both sides), but the frame
#   makes no commitment about what happens when further premises are added;
#
# - *robust* implications, written with `𝒲`: good as stated and good however
#   many further premises or conclusions are added.
#
# Nothing else is good. In particular a defeasible implication is *not*
# automatically good with an extra premise: nonmonotonicity is the default,
# and whatever robustness an implication has must be declared.
#
# Notation: on either side of `⊢`, claims are joined with `+`; an empty side is
# written `0`. Lowercase `x` stands for any individual, so one line of the
# list covers Tweety, Opus, and everyone else.

banner("2. The good implications")

defeasible = [:(Bird(x) ⊢ Flies(x))]                 # birds fly (defeasibly)
robust     = [:(Penguin(x) ⊢ Bird(x)),               # penguins are birds, come what may
              :(Penguin(x) + Flies(x) ⊢ 0)]          # being a penguin and flying are incompatible

F = Frame(Σ, κ(defeasible) ∪ 𝒲(robust) ∪ containment(Σ))

declare("Defeasible (good as stated):", defeasible)
declare("Robust (good however weakened):", robust,
        "A ⊢ A                for every claimable A (containment)")

# ## 3. Asking the frame
#
# The list is finite, but it determines a verdict on every implication. Each
# line below asks whether an implication is good; nothing has been assumed
# beyond the list above.

banner("3. Which implications are good?")

check(F, :(Bird(tweety) ⊢ Flies(tweety)), expect=true)
check(F, :(Penguin(opus) ⊢ Bird(opus)), expect=true)
check(F, :(Bird(tweety) ⊢ Flies(opus)), expect=false,
      why="Tweety being a bird says nothing about Opus")
check(F, :(Penguin(opus) + Flies(opus) ⊢ 0), expect=true,
      why="incompatible: this position is out of bounds")

note("Monotonicity fails: adding a premise can defeat a good implication.")
check(F, :(Bird(opus) ⊢ Flies(opus)), expect=true)
check(F, :(Bird(opus) + Penguin(opus) ⊢ Flies(opus)), expect=false,
      why="defeated by the second premise")

note("Transitivity fails: two good implications need not chain.")
check(F, :(Penguin(opus) ⊢ Bird(opus)), expect=true)
check(F, :(Bird(opus) ⊢ Flies(opus)), expect=true)
check(F, :(Penguin(opus) ⊢ Flies(opus)), expect=false,
      why="not listed, so not good")

note("A robust implication survives any addition; a defeasible one survives only " *
     "what containment guarantees.")
check(F, :(Penguin(opus) + Flies(tweety) + Bird(tweety) ⊢ Bird(opus)), expect=true,
      why="robust: extra premises do no harm")
check(F, :(Bird(tweety) + Bird(opus) ⊢ Flies(tweety)), expect=false,
      why="not listed: robustness under a second bird was never declared")
check(F, :(Bird(tweety) + Penguin(opus) ⊢ Flies(tweety) + Penguin(opus)), expect=true,
      why="containment: Penguin(opus) is on both sides")

# ## 4. Logical vocabulary
#
# From the frame, the semantics assigns every claimable a conceptual role (its
# role as a premise and its role as a conclusion) and extends the consequence
# relation to logically complex claimables. We write the resulting relation
# `⊨` and, in code, `⊩`; `[A, B] ⊩ [C]` reads `A, B ⊨ C`, and `[] ⊩ C` asks
# whether `C` holds outright. `A ⊩ B` is shorthand for one premise and one conclusion.
#
# First, nothing is lost: on the original vocabulary, `⊨` agrees with `⊢`.

banner("4. Logical vocabulary")

Bt, Pt, Ft = RolePair(F, :(Bird(tweety))), RolePair(F, :(Penguin(tweety))), RolePair(F, :(Flies(tweety)))
Bo, Po, Fo = RolePair(F, :(Bird(opus))),   RolePair(F, :(Penguin(opus))),   RolePair(F, :(Flies(opus)))

say("The semantics agrees with the frame on the original vocabulary:")
ask("Bird(tweety) ⊨ Flies(tweety)", Bt ⊩ Ft, expect=true)
ask("Bird(opus), Penguin(opus) ⊨ Flies(opus)", [Bo, Po] ⊩ [Fo], expect=false)
ask("Penguin(opus) ⊨ Flies(opus)", Po ⊩ Fo, expect=false)

note("Negation makes incompatibility explicit.")
ask("Penguin(opus) ⊨ ¬Flies(opus)", Po ⊩ ¬Fo, expect=true)
ask("Flies(opus) ⊨ ¬Penguin(opus)", Fo ⊩ ¬Po, expect=true)
ask("⊨ ¬(Penguin(opus) ∧ Flies(opus))", [] ⊩ ¬(Po ∧ Fo), expect=true)
ask("¬Flies(tweety) ⊨ ¬Bird(tweety)", ¬Ft ⊩ ¬Bt, expect=true,
    why="contraposition of Bird ⊢ Flies")

note("The conditional makes implication explicit: ⊨ A ⇒ B exactly when A ⊨ B.")
ask("⊨ Bird(tweety) ⇒ Flies(tweety)", [] ⊩ (Bt ⇒ Ft), expect=true)
ask("⊨ Penguin(opus) ⇒ Flies(opus)", [] ⊩ (Po ⇒ Fo), expect=false)
ask("⊨ (Bird(opus) ∧ Penguin(opus)) ⇒ Flies(opus)", [] ⊩ ((Bo ∧ Po) ⇒ Fo), expect=false,
    why="the frame's nonmonotonicity is visible in the logic")
ask("⊨ Penguin(opus) ⇒ ¬Flies(opus)", [] ⊩ (Po ⇒ ¬Fo), expect=true)

note("Conjunction and disjunction.")
ask("Penguin(opus) ⊨ Bird(opus) ∧ ¬Flies(opus)", Po ⊩ (Bo ∧ ¬Fo), expect=true,
    why="a penguin is a bird that does not fly")
ask("Bird(tweety) ∨ Penguin(tweety) ⊨ Bird(tweety)", (Bt ∨ Pt) ⊩ Bt, expect=true,
    why="both disjuncts imply it")
ask("Bird(tweety) ∨ Penguin(tweety) ⊨ Flies(tweety)", (Bt ∨ Pt) ⊩ Ft, expect=false,
    why="the second disjunct does not")

note("Conditionals as premises: detachment holds, and conditionals chain, even " *
     "where the material implications themselves do not.")
ask("Bird(tweety), Bird(tweety) ⇒ Flies(tweety) ⊨ Flies(tweety)", [Bt, Bt ⇒ Ft] ⊩ [Ft], expect=true)
ask("Penguin(opus), Penguin(opus) ⇒ Flies(opus) ⊨ Flies(opus)", [Po, Po ⇒ Fo] ⊩ [Fo], expect=true,
    why="the conditional is not a theorem, but as a premise it detaches")
ask("Penguin(opus) ⇒ Bird(opus), Bird(opus) ⇒ Flies(opus) ⊨ Penguin(opus) ⇒ Flies(opus)",
    [Po ⇒ Bo, Bo ⇒ Fo] ⊩ [Po ⇒ Fo], expect=true,
    why="compare: Penguin(opus) ⊭ Flies(opus)")

note("Incompatible premises imply anything.")
ask("Penguin(opus), Flies(opus) ⊨ Bird(tweety)", [Po, Fo] ⊩ [Bt], expect=true)

# ## 5. Quantifiers
#
# `∀(:x, A)` binds `x` in `A`; `x` ranges over every individual. The
# informative quantified claims are conditionals, and their verdicts come
# straight from the list in section 2.

banner("5. Quantifiers")

Bx, Px, Fx = RolePair(F, :(Bird(x))), RolePair(F, :(Penguin(x))), RolePair(F, :(Flies(x)))

ask("⊨ ∀x. Bird(x) ⇒ Flies(x)", [] ⊩ ∀(:x,Bx ⇒ Fx), expect=true, why="birds fly")
ask("⊨ ∀x. Penguin(x) ⇒ Bird(x)", [] ⊩ ∀(:x,Px ⇒ Bx), expect=true)
ask("⊨ ∀x. Penguin(x) ⇒ Flies(x)", [] ⊩ ∀(:x,Px ⇒ Fx), expect=false)
ask("⊨ ∀x. Penguin(x) ⇒ ¬Flies(x)", [] ⊩ ∀(:x,Px ⇒ ¬Fx), expect=true)
ask("⊨ ∀x. (Bird(x) ∧ Penguin(x)) ⇒ Flies(x)", [] ⊩ ∀(:x,(Bx ∧ Px) ⇒ Fx), expect=false,
    why="nonmonotonicity survives quantification")

note("An existential premise does not fix an individual, and a claim about one " *
     "individual does not reach all of them.")
ask("∃x. Penguin(x) ⊨ Flies(tweety)", ∃(:x,Px) ⊩ Ft, expect=false,
    why="some penguin somewhere says nothing about Tweety")
ask("∃x. Penguin(x) ∧ Flies(x) ⊨ Flies(tweety)", ∃(:x,Px ∧ Fx) ⊩ Ft, expect=true,
    why="an incompatible premise, whoever it is about")
ask("Bird(tweety) ⊨ ∀x. Flies(x)", Bt ⊩ ∀(:x,Fx), expect=false)

note("One feature of quantifying over an unlimited stock of individuals: no finite " *
     "position can deny that *something* is a bird, so ∃x. Bird(x) holds outright, and " *
     "dually ∀x. Bird(x) as a premise is absurd. The following are *robustly* true.")
ask("⊨ ∃x. Bird(x)", [] ⊩ ∃(:x,Bx), expect=true)
ask("∀x. Bird(x) ⊨ Flies(tweety)", ∀(:x,Bx) ⊩ Ft, expect=true)

println()

end # module
