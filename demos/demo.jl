using Test, NominalFrames

banner(s) = println("\n", "═"^78, "\n ", s, "\n", "═"^78)
say(args...) = println("  ", args...)

S(x) = Sequent(x)
S(x::Sequent) = x
C(κ, μ, λ, ctx) = Constructible(Set{Sequent}(S.(κ)), Set{Sequent}(S.(μ)),
                                Set{Sequent}(S.(λ)), Set{Int}(ctx))

∅, Γ1, Γ12 = Set{Int}(), Set([1]), Set([1, 2])

# ## 1. The frame
#
# Three predicates: `φ` ("the moon is made of cheese", nullary), `P(x)` ("x is
# prime minister") and `J(x)` ("x has a unique job"). The good implications are
# the reflexive ones `t ⊢ t`, weakened arbitrarily, together with the *defeasible*
# `P(x) ⊢ J(x)`: defeasible because `P(x), P(y) ⊢ J(x)` is not good — were `y`
# also prime minister, the job would not be unique.

banner("1. Declaring the frame")

φ = Predicate(:φ, 0)
P = Predicate(:P, 1)
J = Predicate(:J, 1)
Σ = Signature([φ, P, J])

refl = refl_sequents(Σ)                       # φ⁺φ⁻, P⁺₁P⁻₁, J⁺₁J⁻₁
I = κ([:(P(1) ⊢ J(1))]) ∪ 𝒲(refl)           # the defeasible implication, and reflexivity weakened freely
say("I = ", I)

# A generator like `P⁺₁J⁻₁` stands for its whole orbit: `P⁺ₐJ⁻ₐ` for every
# name `a`. Membership is decidable for concrete sequents.

@test S(:(P(7) ⊢ J(7))) ∈ I
@test S(:(P(1) ⊢ J(2))) ∉ I
@test S(:(P(1) + P(2) ⊢ J(1))) ∉ I          # two prime ministers: defeated
@test S(:(P(1) + φ ⊢ J(1) + φ)) ∈ I         # ... but padding by φ⁺φ⁻ is fine
say("P⁺₇J⁻₇ ∈ I, P⁺₁J⁻₂ ∉ I, P⁺₁P⁺₂J⁻₁ ∉ I, P⁺₁φ⁺J⁻₁φ⁻ ∈ I")

# ## 2. Normal form
#
# The same set has many presentations. The *normal form*  puts
# as much as possible into `𝒲`, then into `ℛ`, and lists the rest in `κ`. Here it
# moves `P⁺J⁻` from `κ` to `ℛ`: because `𝒲(refl) ⊆ I`, adding any nonzero
# reflexive `Z ⊢ Z` to `P⁺J⁻` lands in `𝒲(z ⊢ z)`, so all of `ℛ(P⁺J⁻)` is in `I`.
# A `Frame` stores its incompatibility set in this form.

banner("2. Normal form of I")

I_nf = normal_form(I, Σ)
say("normal form: ", I_nf)
@test I_nf == ℛ([:(P(1) ⊢ J(1))]) ∪ 𝒲(refl)
@test normal_form(I_nf, Σ) == I_nf                    # idempotent
@test contained(I, I_nf, Σ) && contained(I_nf, I, Σ)  # same subobject
F = Frame(Σ, I)
@test F.sequents == I_nf

A ≃ B = normal_form(A, Σ) == normal_form(B, Σ)   # equality of the presented roles

# ## 3. Residuation and the Girard quantale
#
# For a role `S` (a set of sequents at some context Γ), `S^⊥ = S ⊸ I` is the set
# of `t` with `s + t ∈ I` for all `s ∈ S`; `S →ₒ I` computes it, given `I` in
# normal form. The closed roles `S = S^⊥⊥` form the Girard quantale `𝒢`.

banner("3. The Girard quantale 𝒢 and its constants")

# Four distinguished closed roles at the empty context. `0 = ⊤^⊥` is the least
# closed role, `1 = I^⊥` the unit of `⊠`, `⊥ = I` the point, `⊤ = M` everything.
# Here `0 = 𝒲(refl)`: the sequents that stay good however they are weakened.

z0 = zero_role(F, ∅)
say("0 = ⊤^⊥ = ", z0)
say("1 = I^⊥ = ", unit_role(F, ∅))
@test z0 ≃ 𝒲(refl)
@test z0 ≃ (top(∅) →ₒ F.sequents)
# The defeasible `P⁺J⁻` is what keeps `1` away from `⊤`: `t ∈ 1` iff `t + I ⊆ I`,
# and `t + P⁺ₐJ⁻ₐ` must be good for every `a`, which only `t = 0` and `t ∈ 0` achieve.
@test unit_role(F, ∅) ≃ κ([:(0 ⊢ 0)]) ∪ 𝒲(refl)

# ## 4. Interpreting atoms
#
# The conservative interpretation `η` sends an atom `x` to the pair
# `⟨{x⁺}^⊥⊥, {x⁻}^⊥⊥⟩` at context `supp(x)`: the closures of "x as a premise"
# and "x as a conclusion". A `Role` stands for such a closure without computing
# it; `Constructible(role)` computes the closed presentation when it is wanted.

banner("4. Atoms as pairs of roles")

Pa = RolePair(F, :(P(1)))          # ⟦P(a)⟧ at context {a}
Ja = RolePair(F, :(J(1)))          # ⟦J(a)⟧
Pb = RolePair(F, :(P(2)))          # ⟦P(b)⟧ at context {b}
φ₀ = RolePair(F, :φ)               # ⟦φ⟧ at context ∅
say("⟦P(a)⟧ = ", Constructible(Pa.prem), "  ,  ", Constructible(Pa.conc))
say("⟦φ⟧    = ", Constructible(φ₀.prem), "  ,  ", Constructible(φ₀.conc))

# `φ` takes part in no implication beyond reflexivity, so its roles are the
# generic ones `𝒲(φ⁺) ∪ 0` and `𝒲(φ⁻) ∪ 0`. `P(a)` as a premise picks up the
# defeasible `P⁺ₐJ⁻ₐ`: its role is `{P⁺ₐ} ∪ 𝒲(P⁺ₐJ⁺ₐ) ∪ 0` — note `P⁺ₐ` alone is
# strict, since `P⁺ₐP⁺ₑ` is *not* in the role (two prime ministers).
z1 = zero_role(F, Γ1)
@test Constructible(φ₀.prem) ≃ 𝒲([:(φ ⊢ 0)]) ∪ z0
@test Constructible(Pa.prem) ≃ C([:(P(1) ⊢ 0)], [], [:(P(1) + J(1) ⊢ 0)], Γ1) ∪ z1
@test Constructible(Pa.conc) ≃ 𝒲([:(0 ⊢ P(1))], Γ1) ∪ z1

# Conservativity: the frame's own judgments survive interpretation.
say("P(a) ⊨ J(a):        ", Pa ⊩ Ja)
say("J(a) ⊨ P(a):        ", Ja ⊩ Pa)
say("P(a), P(b) ⊨ J(a):  ", [Pa, Pb] ⊩ [Ja], "   (defeated by a second prime minister)")
say("P(a) ⊨ P(a):        ", Pa ⊩ Pa)
@test Pa ⊩ Ja && Ja ⊮ Pa && [Pa, Pb] ⊮ [Ja] && Pa ⊩ Pa
@test φ₀ ⊮ Pa && Pa ⊮ φ₀                            # φ is inferentially isolated

# ## 5. Connectives
#
# `tab:connectives`: `¬` swaps the pair; `⊗` tensors premises and pars
# conclusions; `⊕` joins premises and meets conclusions; `&` and `⅋` are the De
# Morgan duals; `lolli(A, B) = ¬A ⅋ B`. Classical `∧`, `∨`, `⇒` are also there.

banner("5. Connectives")

say("⟦P(a) ⊗ P(b)⟧ = ", Pa ⊗ Pb)

# Multiplicative conjunction of premises behaves like listing them:
@test Pa ⊗ Pb ⊮ Ja && [Pa, Pb] ⊮ [Ja]

# How defeasible is `P(x) ⊢ J(x)`? Completely: a `κ` generator admits no side
# premises at all, so even the irrelevant `φ` defeats it — `P⁺₁φ⁺J⁻₁` is in
# neither `ℛ(P⁺J⁻)` nor `𝒲(refl)`. The only padding tolerated is reflexive,
# which is what the normal form's `ℛ` records: carry `φ` along to the conclusion
# side and the inference is good again.
say("P(a), φ ⊨ J(a):     ", [Pa, φ₀] ⊩ [Ja], "   (any side premise defeats a κ generator)")
say("P(a), φ ⊨ J(a) ⅋ φ: ", [Pa, φ₀] ⊩ [Ja ⅋ φ₀])
@test Pa ⊗ φ₀ ⊮ Ja && [Pa, φ₀] ⊮ [Ja]
@test [Pa, φ₀] ⊩ [Ja ⅋ φ₀]

# Additive disjunction on the left is a case split: both disjuncts must entail.
say("P(a) ⊕ J(a) ⊨ J(a): ", Pa ⊕ Ja ⊩ Ja)
say("P(a) ⊕ φ ⊨ J(a):    ", Pa ⊕ φ₀ ⊩ Ja)
@test Pa ⊕ Ja ⊩ Ja && Pa ⊕ φ₀ ⊮ Ja

# Contraposition holds by construction of `¬` as the swap.
say("¬J(a) ⊨ ¬P(a):      ", ¬Ja ⊩ ¬Pa)
@test ¬Ja ⊩ ¬Pa && ¬¬Pa == Pa

# Theoremhood is `⊨ A`, i.e. the conclusory role lies in `I`. Linear implication
# internalizes consequence: `⊨ A ⊸ B` iff `A ⊨ B`.
say("⊨ P(a) ⊸ J(a):      ", [] ⊩ lolli(Pa, Ja))
say("⊨ J(a) ⊸ P(a):      ", [] ⊩ lolli(Ja, Pa))
@test [] ⊩ lolli(Pa, Ja) && [] ⊮ lolli(Ja, Pa)
@test [] ⊮ lolli(Pa ⊗ Pb, Ja)

# The classical conjunction differs from `⊗` only in its conclusory role.
@test (Pa ∧ Pb).prem == (Pa ⊗ Pb).prem
@test Pa ∧ Pb ⊮ Ja
@test [] ⊩ (Pa ⇒ Ja)                                  # classical implication too

# ## 6. Quantifiers
#
# `⟦∀x. A⟧ = ⟨∀ₓ(a₊), ∃ₓ(a₋)⟩`, where on roles `∀ₓ S = ⋂ over renamings of x`
# and `∃ₓ S = (⋃ over renamings)^⊥⊥`; `∃x. A := ¬∀x. ¬A`. `∀(Γ1, a)` binds
# the name `1`, moving from context `{1}` to `∅`.

banner("6. Quantifiers")

allP = ∀(Γ1, Pa)                       # ⟦∀x. P(x)⟧ at context ∅
someP = ∃(Γ1, Pa)                      # ⟦∃x. P(x)⟧
say("⟦∀x. P(x)⟧ = ", allP)
say("⟦∃x. P(x)⟧ = ", someP)
@test context(allP) == ∅ == context(someP)

# Both collapse in one component: no finite sequent contains `P⁺_c` for *every*
# `c`, so the premisory role of `∀x. P(x)` is just `0`, the frame's absurdity as a
# premise; dually the conclusory role of `∃x. P(x)` is `0`, a free conclusion.
@test Constructible(allP.prem) ≃ z0
@test Constructible(someP.conc) ≃ z0
# The other components go all the way to `⊤ = 0^⊥`: `∀x. P(x)` is interpreted as
# the absurd value `⟨0, ⊤⟩` and `∃x. P(x)` as the trivial value `⟨⊤, 0⟩`.
@test Constructible(allP.conc) ≃ top(∅) && Constructible(someP.prem) ≃ top(∅)

# Consequences: ex falso from `∀x. P(x)`, and anything proves `∃x. P(x)`, cheese
# notwithstanding — structural facts about quantifying over an infinite supply of
# names, not about φ.
say("∀x P(x) ⊨ φ:        ", allP ⊩ φ₀)
say("φ ⊨ ∃x P(x):        ", φ₀ ⊩ someP)
say("⊨ ∃x P(x):          ", [] ⊩ someP)
@test allP ⊩ φ₀ && φ₀ ⊩ someP && [] ⊩ someP

# The informative quantified theorems are the conditionals, where the roles
# interact *before* the collapse: `∀x. P(x) ⊸ J(x)` holds, its two-variable
# strengthening does not. And `∃x. P(x)` does not entail `J(a)` for a particular `a`.
say("⊨ ∀x. P(x) ⊸ J(x):            ", [] ⊩ ∀(Γ1, lolli(Pa, Ja)))
say("⊨ ∀x∀y. P(x) ⊗ P(y) ⊸ J(x):   ", [] ⊩ ∀(Γ12, lolli(Pa ⊗ Pb, Ja)))
say("∃x P(x) ⊨ J(a):               ", someP ⊩ Ja)
@test [] ⊩ ∀(Γ1, lolli(Pa, Ja))
@test [] ⊮ ∀(Γ12, lolli(Pa ⊗ Pb, Ja))
@test someP ⊮ Ja

# The `∀R` rule: from `A ⊨ B(x)` with `x` not free in `A`,
# conclude `A ⊨ ∀x. B(x)`. Here `φ ⊨ J(a)` fails, and so does `φ ⊨ ∀x. J(x)`;
# while `∀x. P(x)` (absurd) entails `∀x. J(x)`.
@test φ₀ ⊮ ∀(Γ1, Ja) && allP ⊩ ∀(Γ1, Ja)

# ## 7. Beyond the frame's own vocabulary: the semantic space is a Girard quantale
#
# Roles can be manipulated directly. `S ⊸ T = (S ⊗ T^⊥)^⊥` on roles; `0` is
# absorbing; closure is idempotent. Equality of roles is semantic.

banner("7. Roles as elements of 𝒢")

R₊, R₋ = Pa.prem, Ja.conc
say("S = ⟦P(a)⟧₊ = ", Constructible(R₊))
say("S^⊥         = ", Constructible(perp(R₊)))
@test perp(perp(R₊)) == R₊                                    # closed roles are fixed by ⊥⊥
@test Constructible(perp(R₊)) ≃ (Constructible(R₊) →ₒ F.sequents)  # ¬S = S ⊸ I
@test tensor(R₊, Role(F, z1)) == Role(F, z1)                  # 0 absorbs
@test Constructible(lolli(R₊, R₋)) ≃
      (minkowski(Constructible(R₊), Constructible(perp(R₋))) →ₒ F.sequents)

# ## 8. Three frames, and a query in a generic context
#
# Our running signature `{ψ, P(-), Q(-,=)}` and its overlap (𝒪), weakening (𝒲)
# and defeasible (𝒟) frames, all built from `s₀ = P⁺ₐQ⁻ₐb`. The query
# `⊨_{b} ∀a. P(a) ⊸ Q(a, b)` holds in 𝒲 and 𝒟 but not in 𝒪, and
# the earlier check `P(a) ⊨ Q(a,b)` agrees, as conservativity demands.

banner("8. 𝒪, 𝒲, 𝒟 and ⊨_{b} ∀a. P(a) ⊸ Q(a, b)")

ψ, Q = Predicate(:ψ, 0), Predicate(:Q, 2)
Σ₂ = Signature([ψ, P, Q])
refl₂ = refl_sequents(Σ₂)
s₀ = S(:(P(1) ⊢ Q(1,2)))
frames = Dict("𝒪" => 𝒲(refl₂),
              "𝒲" => 𝒲([refl₂; s₀]),
              "𝒟" => κ([s₀]) ∪ 𝒲(refl₂))
for name in ["𝒪", "𝒲", "𝒟"]
  Fᵢ = Frame(Σ₂, frames[name])
  p, q = RolePair(Fᵢ, :(P(1))), RolePair(Fᵢ, :(Q(1,2)))
  query = ∀(Γ1, lolli(p, q))                  # at context {b} = {2}
  say(name, ":  P(a) ⊨ Q(a,b) is ", p ⊩ q,
      ";  ⊨_{b} ∀a. P(a) ⊸ Q(a,b) is ", [] ⊩ query,
      ";  s₀ ∈ I is ", s₀ ∈ frames[name])
  @test (p ⊩ q) == ([] ⊩ query) == (s₀ ∈ frames[name])
  @test context(query) == Set([2])
end

# In 𝒟 the implication is defeasible: adding an unrelated premise breaks it,
# whereas in 𝒲 it survives weakening.
for (name, expected) in [("𝒲", true), ("𝒟", false)]
  Fᵢ = Frame(Σ₂, frames[name])
  p, q, r = RolePair(Fᵢ, :(P(1))), RolePair(Fᵢ, :(Q(1,2))), RolePair(Fᵢ, :ψ)
  say(name, ":  P(a), ψ ⊨ Q(a,b) is ", [p, r] ⊩ [q])
  @test ([p, r] ⊩ [q]) == expected
end

println()
