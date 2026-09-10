module TestResidual

using Test, NominalFrames
using NominalFrames: in_strict, in_weak, in_refl, refine, top, bottom

ψ′,P′,Q′ = ps = Predicate.([:ψ,:P,:Q], [0,1,2])
Σ = Signature(ps)

S(x) = Sequent(x)
C(κ, μ, λ, ctx) = Constructible(Set{Sequent}(S.(κ)), Set{Sequent}(S.(μ)),
                                Set{Sequent}(S.(λ)), Set{Int}(ctx))

refl = refl_sequents(Σ)
s₀ = S(:(P(1) ⊢ Q(1,2)))
I𝒪 = 𝒲(refl)
Iℛ = ℛ(refl)
I𝒲 = 𝒲([refl; s₀])
I𝒟 = κ([s₀]) ∪ I𝒪
frames = [I𝒪, Iℛ, I𝒲, I𝒟]


∅, Γ1 = Set{Int}(), Set([1])
⊤, ⊥ = top(∅), bottom(∅)

ts = small_sequents(Σ, [1, 2, 3], 2)

D = κ([Sequent(:(Q(2, 3) ⊢ 0))], Γ1)


# Orbit subsets
#--------------

# I𝒟 is equivariant and contains s₀, so the whole orbit of s₀ lies in it.
@test orbit_subset(s₀, I𝒟, ∅)
# D = {Q(a,b) | a,b ≠ 1} is the G_{1}-orbit of Q(2,3), so that orbit is inside D
@test orbit_subset(Sequent(:(Q(2, 3) ⊢ 0)), D, Γ1)
# the G_∅-orbit is not, since applying σ₂₁ gives Q(1,3) ∉ D.
@test !orbit_subset(Sequent(:(Q(2, 3) ⊢ 0)), D, ∅)


# Orbit intersection 
#-------------------

# The residual of a whole orbit is the orbit intersection of the singleton
# residual: (G • P⁺₁) ⊸ I𝒪 = ⋂_π π({P⁺₁} ⊸ I𝒪).
# Here {P⁺₁} ⊸ I𝒪 is I𝒪 with the name 1 fixed plus one extra generator P⁻₁
# The intersection drops P⁻₁ again: P⁻₁ + P⁺₂ ∉ I𝒪. 
# What is left is I𝒪 itself, i.e. if P(a) + t ∈ I𝒪 for *every*
# name a then t ∈ I𝒪 (take a fresh for t: the reflexive pair below P(a) + t
# cannot involve P(a), so it lies below t).
@test orbit_intersection((S(:(P(1) ⊢ 0)) →ₒ I𝒪), ∅) == I𝒪


P⁺₁P⁻₁ = :(P(1) ⊢ P(1))

# Over {1}: 𝒲(P(2)) presents P(b) for b ≠ 1; the orbit of P(1) itself is not inside
E = 𝒲([P⁺₁P⁻₁, :(P(2) ⊢ P(2))], Γ1)
@test orbit_intersection(E, ∅) == C([], [], [P⁺₁P⁻₁], [])
@test orbit_intersection(𝒲([P⁺₁P⁻₁], Γ1), ∅) == ⊥
@test orbit_intersection(ℛ([P⁺₁P⁻₁], Γ1), ∅) == ⊥
@test orbit_intersection(κ([P⁺₁P⁻₁], Γ1), ∅) == ⊥

# Joins are needed: no single P or Q stays in F under every renaming, but
# P(a)+Q(a,b) does (renaming a ↦ 1 leaves Q(1,b), renaming b ↦ 1 leaves P(a)
# with a ≠ 1), as does P(a)+P(b).
F = 𝒲([:(P(2) ⊢ 0), :(Q(1,3) ⊢ 0)], Γ1)
@test orbit_intersection(F,∅) == 𝒲([:(P(1) + Q(1,2) ⊢ 0), :(P(1) + P(2) ⊢ 0)])
@test orbit_intersection(F, Γ1) === F

# Oracle: t ∈ ⋂_π πC iff G_Γ • t ⊆ C
Cs = [enlarge_context(I, Γ1) for I in frames]
push!(Cs, E, F, D, C([], [P⁺₁P⁻₁], [], Γ1),
      C([:(Q(1,2) ⊢ 0)], [:(P(2) ⊢ ψ)], [:(Q(2,1) ⊢ 0)], Γ1),
      C([], [:(P(1) ⊢ 0), :(P(2) ⊢ 0)], [:(ψ ⊢ ψ)], Γ1),
      C([:(P(1) ⊢ 0), :(P(2) ⊢ 0)], [], [], Γ1),
      C([], [:(Q(1,2) ⊢ 0), :(Q(2,1) ⊢ 0), :(Q(2, 3) ⊢ 0)], [], Γ1))
for Cᵢ in Cs
  R = orbit_intersection(Cᵢ, ∅)
  @test R.context == ∅
  for t in ts
    @test (t ∈ R) == orbit_subset(t, Cᵢ, ∅)
  end
end
# Two names in Δ that renamings can hit
for Cᵢ in [enlarge_context(I, Set([1, 2])) for I in frames]
  R = orbit_intersection(Cᵢ, ∅)
  for t in ts
    @test (t ∈ R) == orbit_subset(t, Cᵢ, ∅)
  end
end

# Mixed 𝒲/ℛ dependence: the renamings of one element may land in 𝒲(λ) for some
# π and in ℛ(μ) for others. `P(a)+Q(a,b) ⊢ P(a)` is in the intersection — under
# the identity via P(c)⊢P(c) with c ≠ 1, under a ↦ 1 via Q(1,b) with reflexive
# remainder P(1)⊢P(1) — but it is not a 𝒲 generator: adding a fresh Q(e,f) puts
# the a ↦ 1 renaming outside C. It is ≤_ℛ-above Q(a,b), the sole ℛ generator.
# (The oracle above only sees sequents of size ≤ 2, so it cannot catch this.)
H = C([], [:(Q(1,2) ⊢ 0), :(Q(2,1) ⊢ 0), :(Q(2, 3) ⊢ 0)], [:(P(3) ⊢ P(3))], Γ1)
H∅ = orbit_intersection(H, ∅)
@test H∅ == ℛ([:(Q(1,2) ⊢ 0)]) ∪ 𝒲([:(P(1) + P(2) ⊢ P(1) + P(2))])
t₁, t₂ = S(:(P(1) + Q(1,2) ⊢ P(1))), S(:(P(1) + Q(1,2) + Q(3,4) ⊢ P(1)))
@test orbit_subset(t₁, H, ∅) && t₁ ∈ H∅
@test !orbit_subset(t₂, H, ∅) && t₂ ∉ H∅

# The general residual 
#---------------------

"""
Direct decision of `t ∈ A ⊸ C`, independent of currying: for each generator `g`
of `A` and each representative `g′` of `G_Γ • g` relative to the names of `t`
(`refine`), `g′ + t ∈ C`, resp. `𝒲(g′ + t) ⊆ C`, resp. `ℛ(g′ + t) ⊆ C`, the last
two by the covering tests of `lemma:covertest`.
"""
function in_residual(t::Sequent, A::Constructible, C::Constructible)::Bool
  Γ = A.context
  reps(g) = refine(g, Γ, setdiff(t.supp, Γ))
  all(g′ + t ∈ C for g in A.strict for g′ in reps(g)) &&
  all(covers(((g′ + t) →ₒ C), Σ) for g in A.weak for g′ in reps(g)) &&
  all(covers(((g′ + t) →ₒ C), Σ; reflexive=true) for g in A.refl for g′ in reps(g))
end

# `residual(A, C)` wants `C` in normal form; three frames are, I𝒟 is not (its
# s₀ absorbs R, see test/NormalForm.jl)
I𝒟nf = normal_form(I𝒟, Σ)
@test I𝒟nf == ℛ([s₀]) ∪ I𝒪
nfs = [I𝒪, Iℛ, I𝒲, I𝒟nf]

# Hand checks
@test (⊥ →ₒ I𝒟nf) == ⊤
@test (⊤ →ₒ I𝒟nf) == I𝒪                # ⊤ ⊸ C = 𝒲(λ_C)
@test (𝒲([:(0 ⊢ 0)]) →ₒ I𝒟nf) == I𝒪
@test (ℛ([:(0 ⊢ 0)]) →ₒ I𝒟nf) == I𝒟nf    # R ⊸ I𝒟 = I𝒟
@test (ℛ([:(0 ⊢ 0)]) →ₒ Iℛ) == Iℛ        # R ⊸ ℛ(refl) = ℛ(refl)
# (G•P⁺ₐ) ⊸ I𝒟: P⁺ₐ + t ∈ I𝒟 for all a
@test (κ([:(P(1) ⊢ 0)]) →ₒ I𝒟nf) == I𝒪
# Over Γ = {1}, P⁺₁ is a fixed point and the residual is the singleton one
@test (κ([:(P(1) ⊢ 0)], Γ1) →ₒ I𝒟nf) ==
      C([], [:(0 ⊢ Q(1,2))], [:(ψ ⊢ ψ), :(0 ⊢ P(1)), :(P(2) ⊢ P(2)),
                               :(Q(1,2) ⊢ Q(1,2)), :(Q(2,1) ⊢ Q(2,1)),
                               :(Q(2,3) ⊢ Q(2,3))], Γ1)

# Oracle
As = [κ([:(P(1) ⊢ 0)]), 𝒲([:(P(1) ⊢ 0)]),
      ℛ([:(P(1) ⊢ 0)]), κ([:(0 ⊢ Q(1,2))]),
      C([:(P(1) ⊢ 0)], [:(ψ ⊢ 0)], [], []), 𝒲([:(ψ ⊢ 0), :(P(1) ⊢ P(2))]),
      κ([:(P(1) ⊢ 0)], Γ1), κ([:(Q(1,2) ⊢ 0)], Γ1),
      ℛ([:(Q(2,1) ⊢ 0)], Γ1), κ([:(P(2) ⊢ 0)], Γ1) ∪ 𝒲([:(Q(1,2) ⊢ 0)], Γ1)]
for A in As, I in nfs
  R = A →ₒ I
  @test R.context == A.context
  for t in ts
    @test (t ∈ R) == in_residual(t, A, I)
  end
end

# ⊥⊥ closure on a few roles (the paper's table of (-)^⊥ computations)
for I in nfs, A in As[1:3]
  A⊥ = A →ₒ I
  A⊥⊥ = A⊥ →ₒ I
  for t in ts
    @test (t ∈ A) ≤ (t ∈ A⊥⊥)                     # A ⊆ A⊥⊥
    @test (t ∈ A⊥) == (t ∈ (A⊥⊥ →ₒ I))            # A⊥ = A⊥⊥⊥
  end
end

end # module
