# # The courtroom: several individuals, a relation between them, and quantifiers
#
# Run it with `julia --project=. demos/courtroom.jl`. It assumes the reader has
# seen `demo.jl`.
#
# The first demo had one argument place per predicate and one individual at a
# time. Here claimables relate individuals to one another, and the interesting
# questions quantify over who did what. As before, premises and conclusions
# are sets and containment holds.
#
# The setting: a court in which two accusers convict (unless there is an
# alibi), an alibi is incompatible with guilt, and nothing else is settled.

module Courtroom

include("prelude.jl")

# ## 1. The vocabulary

banner("1. The vocabulary")

Accuses = Predicate(:Accuses, 2)   # "x testifies that y did it"
Guilty  = Predicate(:Guilty, 1)    # "y is guilty"
Alibi   = Predicate(:Alibi, 1)     # "y has an alibi"
Σ = Signature([Accuses, Guilty, Alibi])

say("Two-place claimables relate distinct individuals: Accuses(ann, carl) is")
say("a different claim from Accuses(carl, ann), and nobody accuses themselves.")

# ## 2. The good implications
#
# `x`, `y`, `z` stand for any three *distinct* individuals. So the defeasible
# rule really does require two accusers: one person testifying twice is not
# covered by it (and, since premises are sets, testifying twice is testifying
# once anyway).
#
# Conclusions are as sensitive to additions as premises are, so the weaker
# claim "two accusers: guilty, or else there is an alibi" is listed separately.
# It does not follow from the first line.

banner("2. The good implications")

defeasible = [:(Accuses(x, y) + Accuses(z, y) ⊢ Guilty(y)),             # two accusers convict
              :(Accuses(x, y) + Accuses(z, y) ⊢ Guilty(y) + Alibi(y))]  # ... or there is an alibi
robust     = [:(Alibi(y) + Guilty(y) ⊢ 0)]                    # an alibi is incompatible with guilt

F = Frame(Σ, κ(defeasible) ∪ 𝒲(robust) ∪ containment(Σ))

declare("Defeasible (good as stated):", defeasible)
declare("Robust (good however weakened):", robust,
        "A ⊢ A                for every claimable A (containment)")

# ## 3. Asking the frame
#
# Ann and Bob are witnesses; Carl is the accused.

banner("3. Which implications are good?")

check(F, :(Accuses(ann, carl) + Accuses(bob, carl) ⊢ Guilty(carl)), expect=true)
check(F, :(Accuses(ann, carl) ⊢ Guilty(carl)), expect=false, why="one accuser is not enough")
check(F, :(Accuses(ann, carl) + Accuses(bob, carl) ⊢ Guilty(ann)), expect=false,
      why="the accused is Carl")
check(F, :(Accuses(ann, carl) + Accuses(carl, ann) ⊢ Guilty(carl)), expect=false,
      why="mutual accusation: one accuser each")

note("The alibi defeats the rule, and settles the matter the other way.")
check(F, :(Accuses(ann, carl) + Accuses(bob, carl) + Alibi(carl) ⊢ Guilty(carl)), expect=false,
      why="defeated")
check(F, :(Accuses(ann, carl) + Accuses(bob, carl) + Alibi(carl) + Guilty(carl) ⊢ 0), expect=true,
      why="asserting guilt as well is incompatible")
check(F, :(Accuses(ann, carl) + Accuses(bob, carl) + Alibi(ann) ⊢ Guilty(carl)), expect=false,
      why="not listed: Ann's alibi was never declared harmless")
check(F, :(Accuses(ann, carl) + Accuses(bob, carl) ⊢ Guilty(carl) + Alibi(carl)), expect=true)
check(F, :(Accuses(ann, carl) + Accuses(bob, carl) ⊢ Guilty(carl) + Alibi(ann)), expect=false,
      why="not listed: an extra conclusion is as much an addition as an extra premise")

# ## 4. Logical vocabulary
#
# The claimables, as conceptual roles. Names are chosen to read like the claims.

banner("4. Logical vocabulary")

AnnC, BobC, CarlA = RolePair(F, :(Accuses(ann, carl))), RolePair(F, :(Accuses(bob, carl))),
                    RolePair(F, :(Accuses(carl, ann)))
GuiltyC, AlibiC = RolePair(F, :(Guilty(carl))), RolePair(F, :(Alibi(carl)))

ask("Accuses(ann,carl), Accuses(bob,carl) ⊨ Guilty(carl)", [AnnC, BobC] ⊩ [GuiltyC], expect=true)
ask("Accuses(ann,carl) ⊨ Guilty(carl)", AnnC ⊩ GuiltyC, expect=false)
ask("Accuses(ann,carl), Accuses(ann,carl) ⊨ Guilty(carl)", [AnnC, AnnC] ⊩ [GuiltyC], expect=false,
    why="the same accuser twice is one accuser")
ask("Accuses(ann,carl) ∧ Accuses(bob,carl) ⊨ Guilty(carl)", (AnnC ∧ BobC) ⊩ GuiltyC, expect=true,
    why="conjunction makes the two-premise implication explicit")

note("Negation and the alibi.")
ask("Alibi(carl) ⊨ ¬Guilty(carl)", AlibiC ⊩ ¬GuiltyC, expect=true)
ask("Guilty(carl) ⊨ ¬Alibi(carl)", GuiltyC ⊩ ¬AlibiC, expect=true)
ask("Accuses(ann,carl), Accuses(bob,carl), Alibi(carl) ⊨ Guilty(carl)",
    [AnnC, BobC, AlibiC] ⊩ [GuiltyC], expect=false, why="defeated")
ask("Accuses(ann,carl), Accuses(bob,carl), Alibi(carl) ⊨ ¬Guilty(carl)",
    [AnnC, BobC, AlibiC] ⊩ [¬GuiltyC], expect=true, why="the alibi wins")
ask("Accuses(ann,carl), Accuses(bob,carl) ⊨ Guilty(carl) ∨ Alibi(carl)",
    [AnnC, BobC] ⊩ [GuiltyC ∨ AlibiC], expect=true,
    why="disjunction makes the two-conclusion implication explicit")
ask("Accuses(ann,carl), Accuses(bob,carl), ¬Alibi(carl) ⊨ Guilty(carl)",
    [AnnC, BobC, ¬AlibiC] ⊩ [GuiltyC], expect=true,
    why="negation moves the alibi across the turnstile")
ask("Accuses(ann,carl), Accuses(bob,carl) ⊨ Guilty(carl) ∨ Alibi(ann)",
    [AnnC, BobC] ⊩ [GuiltyC ∨ RolePair(F, :(Alibi(ann)))], expect=false,
    why="not listed")

note("Conditionals.")
ask("⊨ (Accuses(ann,carl) ∧ Accuses(bob,carl)) ⇒ Guilty(carl)", [] ⊩ ((AnnC ∧ BobC) ⇒ GuiltyC), expect=true)
ask("⊨ Accuses(ann,carl) ⇒ Guilty(carl)", [] ⊩ (AnnC ⇒ GuiltyC), expect=false)
ask("⊨ Alibi(carl) ⇒ ¬Guilty(carl)", [] ⊩ (AlibiC ⇒ ¬GuiltyC), expect=true)
ask("Accuses(ann,carl) ⊨ Accuses(bob,carl) ⇒ Guilty(carl)", AnnC ⊩ (BobC ⇒ GuiltyC), expect=true,
    why="with Ann's testimony in hand, Bob's would convict")
ask("Accuses(ann,carl) ⊨ Accuses(carl,ann) ⇒ Guilty(carl)", AnnC ⊩ (CarlA ⇒ GuiltyC), expect=false)

# ## 5. Quantifiers
#
# `∀([:x, :z], A)` binds `x` and `z` in `A`, and they range over distinct
# individuals, both different from anyone already mentioned in `A`.

banner("5. Quantifiers")

Axy, Azy = RolePair(F, :(Accuses(x, y))), RolePair(F, :(Accuses(z, y)))
Gy, Ay = RolePair(F, :(Guilty(y))), RolePair(F, :(Alibi(y)))

ask("⊨ ∀x∀y∀z. (Accuses(x,y) ∧ Accuses(z,y)) ⇒ Guilty(y)",
    [] ⊩ ∀([:x, :y, :z], (Axy ∧ Azy) ⇒ Gy), expect=true, why="the rule, as a law")
ask("⊨ ∀x∀y. Accuses(x,y) ⇒ Guilty(y)", [] ⊩ ∀([:x, :y], Axy ⇒ Gy), expect=false)
ask("⊨ ∀y. Alibi(y) ⇒ ¬Guilty(y)", [] ⊩ ∀(:y, Ay ⇒ ¬Gy), expect=true)
ask("⊨ ∀x∀y∀z. (Accuses(x,y) ∧ Accuses(z,y) ∧ Alibi(y)) ⇒ Guilty(y)",
    [] ⊩ ∀([:x, :y, :z], (Axy ∧ Azy ∧ Ay) ⇒ Gy), expect=false, why="defeated under the quantifier too")

note("Existential premises: it takes two accusers, whoever they are.")
Axc, Azc = RolePair(F, :(Accuses(x, carl))), RolePair(F, :(Accuses(z, carl)))
ask("∃x∃z. Accuses(x,carl) ∧ Accuses(z,carl) ⊨ Guilty(carl)", ∃([:x, :z], Axc ∧ Azc) ⊩ GuiltyC, expect=true)
ask("∃x. Accuses(x,carl) ⊨ Guilty(carl)", ∃(:x, Axc) ⊩ GuiltyC, expect=false)
ask("∃x. Accuses(x,carl), Alibi(carl) ⊨ ¬Guilty(carl)", [∃(:x, Axc), AlibiC] ⊩ [¬GuiltyC], expect=true)
ask("Alibi(carl) ⊨ ¬∃x∃z. Accuses(x,carl) ∧ Accuses(z,carl)", AlibiC ⊩ ¬∃([:x, :z], Axc ∧ Azc), expect=false,
    why="an alibi does not mean nobody accuses you")

# ## 6. Does "anyone" depend on who is in the room? (Beck–Chevalley)
#
# Ann has testified. Would one more accuser convict Carl? Consider the claim
#
#     ∀z. Accuses(z, carl) ⇒ Guilty(carl)
#
# A bound variable ranges over individuals distinct from everyone *in scope*.
# So the claim can be evaluated in two settings: with only Carl in scope, so
# that `z` may be anyone at all, Ann included; or with Ann in scope too, so
# that `z` is someone else. `in_context(A, names)` puts individuals in scope
# before a quantifier is applied.
#
# Beck–Chevalley is the principle that the two settings agree: that a
# quantified claim has the same content whichever further individuals happen
# to be in scope when it is evaluated. Put differently, first quantifying and
# then bringing a new individual into the conversation comes to the same thing
# as first bringing them in and then quantifying.
#
# In this court it fails, and the court itself says why. Identifying the two
# accusers in the rule gives `Accuses(x, y), Accuses(x, y) ⊢ Guilty(y)`, which
# is `Accuses(x, y) ⊢ Guilty(y)`: one accuser convicts, which the court
# rejects. A frame whose good implications are closed under identifying
# individuals in this way satisfies Beck–Chevalley; this one is not, and does
# not. The two readings of the claim are then genuinely different claims, not
# merely different answers to one question.

banner("6. Does \"anyone\" depend on who is in the room? (Beck–Chevalley)")

anyone  = ∀(:z, Azc ⇒ GuiltyC)                                   # only Carl in scope: z may be anyone, Ann included
another = ∀(:z, in_context(Azc ⇒ GuiltyC, [:ann, :z, :carl]))   # Ann in scope too: z is someone else

ask("Accuses(ann,carl) ⊨ ∀z. Accuses(z,carl) ⇒ Guilty(carl)   [z: anyone at all]", AnnC ⊩ anyone, expect=false,
    why="z might be Ann again, and her second testimony adds nothing")
ask("Accuses(ann,carl) ⊨ ∀z. Accuses(z,carl) ⇒ Guilty(carl)   [z: anyone else]", AnnC ⊩ another, expect=true)
ask("the two readings are the same claim", in_context(anyone, [:ann, :carl]) == another, expect=false,
    why="Beck–Chevalley fails in this court")

note("Compare a court in which one accuser already convicts (or else there is an alibi). " *
     "Its good implications are closed under identifying individuals, and the two readings coincide.")

one_accuser = [:(Accuses(x, y) ⊢ Guilty(y)), :(Accuses(x, y) ⊢ Guilty(y) + Alibi(y))]
F₁ = Frame(Σ, κ([defeasible; one_accuser]) ∪ 𝒲(robust) ∪ containment(Σ))
AnnC₁, Azc₁, GuiltyC₁ = RolePair(F₁, :(Accuses(ann, carl))), RolePair(F₁, :(Accuses(z, carl))),
                        RolePair(F₁, :(Guilty(carl)))
anyone₁  = ∀(:z, Azc₁ ⇒ GuiltyC₁)
another₁ = ∀(:z, in_context(Azc₁ ⇒ GuiltyC₁, [:ann, :z, :carl]))

ask("Accuses(ann,carl) ⊨ ∀z. Accuses(z,carl) ⇒ Guilty(carl)   [z: anyone at all]", AnnC₁ ⊩ anyone₁, expect=true)
ask("Accuses(ann,carl) ⊨ ∀z. Accuses(z,carl) ⇒ Guilty(carl)   [z: anyone else]", AnnC₁ ⊩ another₁, expect=true)
ask("the two readings are the same claim", in_context(anyone₁, [:ann, :carl]) == another₁, expect=true,
    why="Beck–Chevalley holds in this court")

println()

end # module
