module TestNormalForm

using Test, NominalFrames

ψ′, P′, Q′ = ps = Predicate.([:ψ,:P,:Q], [0,1,2])
Σ = Signature(ps)
Σψ = Signature([ψ′])

S(x) = Sequent(x)
S(x::Sequent) = x
C(κ, μ, λ, ctx) = Constructible(Set{Sequent}(S.(κ)), Set{Sequent}(S.(μ)),
                                Set{Sequent}(S.(λ)), Set{Int}(ctx))

refl = refl_sequents(Σ)
s₀ = S(:(P(1) ⊢ Q(1,2)))
I𝒪 = 𝒲(refl)
Iℛ = ℛ(refl)
I𝒲 = 𝒲([refl; s₀])
I𝒟 = κ([s₀]) ∪ I𝒪
frames = [I𝒪, Iℛ, I𝒲, I𝒟]
∅ = Set{Int}()

⊥, ⊤ = bottom(∅), top(∅)

ts = small_sequents(Σ, [1, 2, 3], 2)
tsψ = small_sequents(Σψ, Int[], 5)
same(A, B, ts) = all((t ∈ A) == (t ∈ B) for t in ts)


# Covering tests 
#---------------

@test covers(⊤, Σ)
@test !covers(⊥, Σ)
@test !covers(I𝒪, Σ) && !covers(Iℛ, Σ) && !covers(I𝒟, Σ)
@test covers(C([:(0 ⊢ 0)], [], [:(ψ ⊢ 0), :(0 ⊢ ψ)], []), Σψ)       # M = {0} ∪ 𝒲(ψ⁺) ∪ 𝒲(ψ⁻)
@test !covers(C([:(0 ⊢ 0)], [], [:(ψ ⊢ 0), :(0 ⊢ ψ)], []), Σ)       # ... but not with P around
@test covers(C([], [:(0 ⊢ 0)], [:(ψ ⊢ 0), :(0 ⊢ ψ)], []), Σψ)       # R ∪ 𝒲(ψ⁺) ∪ 𝒲(ψ⁻)
@test !covers(ℛ([:(0 ⊢ 0), :(ψ ⊢ 0), :(0 ⊢ ψ)]), Σψ)    # 2ψ⁺ escapes
@test covers(C([], [:(0 ⊢ 0), :(ψ ⊢ 0), :(0 ⊢ ψ)], [:(2ψ ⊢ 0), :(0 ⊢ 2ψ)], []), Σψ)
# 𝒲(z) ⊆ C iff M = {z} ⊸ C: the footnote's 𝒲(ψ⁺) = {ψ⁺} ∪ 𝒲({2ψ⁺, ψ⁺ψ⁻}) with only ψ
Foot = C([:(ψ ⊢ 0)], [], [:(2ψ ⊢ 0), :(ψ ⊢ ψ)], [])
@test covers((S(:(ψ ⊢ 0)) →ₒ Foot), Σψ)
@test !covers((S(:(ψ ⊢ 0)) →ₒ Foot), Σ)

# R ⊆ E
@test covers(⊤, Σ; reflexive=true)
@test covers(ℛ([:(0 ⊢ 0)]), Σ; reflexive=true)          # R ⊆ ℛ(0) = R
@test !covers(Iℛ, Σ; reflexive=true)                                # 0 ∈ R ∖ ℛ(refl)
@test covers(C([:(0 ⊢ 0)], refl, [], []), Σ; reflexive=true)
# ℛ(z) ⊆ C iff R ⊆ {z} ⊸ C
@test covers((S(:(P(1) ⊢ P(1))) →ₒ Iℛ), Σ; reflexive=true)
@test covers((S(:(P(1) ⊢ P(1))) →ₒ I𝒟), Σ)                    # 𝒲(P⊢P) ⊆ I𝒟
# ℛ(s₀) ⊆ I𝒟 — s₀ + Z⊢Z dominates a reflexive generator as soon as Z ≠ 0 — but 𝒲(s₀) ⊄ I𝒟
@test covers((s₀ →ₒ I𝒟), Σ; reflexive=true)
@test !covers((s₀ →ₒ I𝒟), Σ)
@test !covers((s₀ →ₒ κ([s₀])), Σ; reflexive=true)

# ⊤ ⊸ S
#------

@test top_residual(I𝒪, Σ) == I𝒪
@test top_residual(Iℛ, Σ) == ⊥
@test top_residual(I𝒲, Σ) == I𝒲
@test top_residual(I𝒟, Σ) == I𝒪
@test top_residual(⊤, Σ) == ⊤
@test same(top_residual(Foot, Σψ), 𝒲([:(ψ ⊢ 0)]), tsψ)
@test same(top_residual(Foot, Σ), 𝒲([:(2ψ ⊢ 0), :(ψ ⊢ ψ)]), [ts; tsψ])
# ℛ(ψ⁺) ∪ 𝒲(3ψ⁺) ∪ 𝒲(ψ⁺2ψ⁻) absorbs ⊤ above 2ψ⁺ψ⁻, a non-generator
Ex = C([], [:(ψ ⊢ 0)], [:(3ψ ⊢ 0), :(ψ ⊢ 2ψ)], [])
A = top_residual(Ex, Σψ)
@test same(A, 𝒲([:(3ψ ⊢ 0), :(ψ ⊢ 2ψ), :(2ψ ⊢ ψ)]), tsψ)
# Oracle on the ψ-fragment: t ∈ ⊤ ⊸ S iff t + u ∈ S for all small u (sizes exhaust here)
for Sᵢ in [Foot, Ex, ℛ([:(ψ⊢0), :(0⊢ψ)]), κ([:(0⊢0), :(ψ⊢0)])∪𝒲([:(2ψ⊢0)])]
  A = top_residual(Sᵢ, Σψ)
  for t in tsψ
    @test (t ∈ A) == all(t + u ∈ Sᵢ for u in tsψ)
  end
end

# The result is an up-set inside S
for Sᵢ in frames
  A = top_residual(Sᵢ, Σ)
  for t in ts
    t ∈ A && @test t ∈ Sᵢ
    t ∈ A && @test all(t + x ∈ A for x in atoms(Σ, t.supp))
  end
end

# Normal form 
#------------

# Three of the paper's frames are their own normal forms. Not I𝒟: since
# 𝒲(refl) ⊆ I𝒟, s₀ + Z⊢Z dominates a reflexive generator whenever Z ≠ 0, so
# ℛ(s₀) ⊆ I𝒟 and s₀ belongs in the ℛ part, not the strict one.
for I in [I𝒪, Iℛ, I𝒲]
  @test normal_form(I, Σ) == I
end
I𝒟nf = ℛ([s₀]) ∪ I𝒪 
@test normal_form(I𝒟, Σ) == I𝒟nf
# The footnote: two presentations of 𝒲(ψ⁺) (with only ψ) have one normal form
@test normal_form(Foot, Σψ) == 𝒲([:(ψ ⊢ 0)])
@test normal_form(𝒲([:(ψ ⊢ 0)]), Σψ) == 𝒲([:(ψ ⊢ 0)])
# ... but with P in the signature, Foot is already normal
@test normal_form(Foot, Σ) == Foot
# An ℛ-element strictly above its generator ends up in λ_nf
@test normal_form(Ex, Σψ) == C([], [:(ψ ⊢ 0)], [:(3ψ ⊢ 0), :(ψ ⊢ 2ψ), :(2ψ ⊢ ψ)], [])
# Redundant presentations of I𝒟 normalize to the same thing
@test normal_form(C([:(P(1) ⊢ Q(1,2)), :(P(1) + ψ ⊢ Q(1,2) + ψ), :(ψ ⊢ ψ)],
                    [:(P(1) ⊢ P(1))], [refl; :(2ψ ⊢ 2ψ)], []), Σ) == I𝒟nf
@test normal_form(C([:(P(1) ⊢ Q(1,2))], [:(P(3) ⊢ Q(3,2))], refl, []), Σ) == I𝒟nf
# κ generators whose ℛ-closure is inside S move to μ
@test normal_form(C([:(ψ ⊢ 0), :(P(1) ⊢ 0)], [:(ψ ⊢ 0)], [], []), Σ) ==
      C([:(P(1) ⊢ 0)], [:(ψ ⊢ 0)], [], [])

# Semantics preserved, idempotent
Ss = [frames; Foot; Ex; 
      C([:(P(1) ⊢ 0), :(Q(1,2) ⊢ Q(2,1))], [:(ψ ⊢ 0)], [:(P(1) ⊢ P(2))], []);
      C([:(ψ ⊢ ψ)], [:(P(1) ⊢ Q(1,2))], [:(Q(1,2) ⊢ 0)], []);
      C([:(Q(1,2) ⊢ 0)], [:(P(2) ⊢ ψ)], [:(Q(2,1) ⊢ 0)], [1])]
for Sᵢ in Ss
  N = normal_form(Sᵢ, Σ)
  @test N.context == Sᵢ.context
  @test same(N, Sᵢ, ts)
  @test normal_form(N, Σ) == N
  @test same(top_residual(N, Σ), 𝒲(N), ts)
  for g in N.refl # R⊸N=𝒲(λ)∪ℛ(μ): each μ gen absorbs R, not absorbed by 𝒲(λ)
    @test covers((g →ₒ N), Σ; reflexive=true) && !covers((g →ₒ N), Σ)
  end
end

# The general residual with the right argument normalized on the way
A₁ = κ([:(P(1) ⊢ 0)],)
for I in [I𝒪, Iℛ, I𝒲]
  @test residual(A₁, I, Σ) == (A₁ →ₒ I)
end
# Where normalization matters: ℛ(s₀) ⊸ I𝒟 = {s₀} ⊸ (R ⊸ I𝒟) contains 0, since
# ℛ(s₀) ⊆ I𝒟; the currying through the non-normal presentation misses it.
A₂ = ℛ([s₀], [1, 2])
@test zero(Sequent) ∈ residual(A₂, I𝒟, Σ)
@test zero(Sequent) ∉ (A₂ →ₒ I𝒟)
@test Frame(Σ, I𝒟).sequents == I𝒟nf

end # module
