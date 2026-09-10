module TestContraction

# Sequents with `𝔹` coefficients: sides are sets, `+` is union, and contraction
# holds. Checked against (i) the `ℕ` theory where the two must agree, (ii)
# hand computations where they must differ, (iii) brute force on frames with a
# nullary signature, where `𝔹[X]²` is finite, and (iv) the courtroom, where a
# frame with weakening may be computed with either coefficients.

using Test, NominalFrames
using NominalFrames: in_strict, in_weak, in_refl, refine, top, bottom, refl_leq,
                    refl_above, refl_meet, residual_strict, residual_refl,
                    refl_predecessors

ψ′, P′, Q′ = ps = Predicate.([:ψ,:P,:Q], [0,1,2])
Σ = Signature(ps)
Σψ = Signature([ψ′])

S(x) = Sequent{𝔹}(x)
S(x::Sequent{𝔹}) = x
C(κ, μ, λ, ctx) = Constructible{𝔹}(S.(κ), S.(μ), S.(λ), ctx)
Sℕ(x) = Sequent{ℕ}(x)

∅, Γ1, Γ12 = Set{Int}(), Set([1]), Set([1, 2])
⊤, ⊥ = top(𝔹, ∅), bottom(𝔹, ∅)

# Sequents
#---------

# Contraction at the level of positions
@test S(:(2P(1) ⊢ 0)) == S(:(P(1) ⊢ 0))
@test S(:(P(1) ⊢ 0)) + S(:(P(1) ⊢ 0)) == S(:(P(1) ⊢ 0))
@test Sℕ(:(P(1) ⊢ 0)) + Sℕ(:(P(1) ⊢ 0)) == Sℕ(:(2P(1) ⊢ 0))
@test length(S(:(P(1) + P(1) ⊢ ψ))) == 2
@test_throws ErrorException Sequent{𝔹}(MultiSet([Term(ψ′), Term(ψ′)]), MultiSet(Term[]))
# ℕ and 𝔹 sequents never mix
@test_throws MethodError S(:(P(1) ⊢ 0)) + Sℕ(:(P(1) ⊢ 0))

# q and ι
@test Sequent{𝔹}(Sℕ(:(2P(1) + ψ ⊢ 3ψ))) == S(:(P(1) + ψ ⊢ ψ))
@test Sequent{ℕ}(S(:(P(1) + ψ ⊢ ψ))) == Sℕ(:(P(1) + ψ ⊢ ψ))
for s in [S(:(P(1) + ψ ⊢ ψ)), S(:(0 ⊢ 0)), S(:(Q(1,2) ⊢ Q(2,1)))]
  @test Sequent{𝔹}(Sequent{ℕ}(s)) == s
end
# q is a monoid map, ι is not
x, y = Sℕ(:(P(1) ⊢ ψ)), Sℕ(:(P(1) + Q(1,2) ⊢ 0))
@test Sequent{𝔹}(x + y) == Sequent{𝔹}(x) + Sequent{𝔹}(y)
@test Sequent{ℕ}(S(:(P(1) ⊢ 0)) + S(:(P(1) ⊢ 0))) != Sequent{ℕ}(S(:(P(1) ⊢ 0))) + Sequent{ℕ}(S(:(P(1) ⊢ 0)))

# Subtraction: least solution, not unique
t, s = S(:(P(1) + ψ ⊢ Q(1,2))), S(:(P(1) ⊢ Q(1,2)))
@test t - s == S(:(ψ ⊢ 0))
@test all(s + u == t for u in [S(:(ψ ⊢ 0)), S(:(ψ + P(1) ⊢ 0)), S(:(ψ ⊢ Q(1,2))), t])
@test (t ∸ S(:(P(1) + P(2) ⊢ 0))) == S(:(ψ ⊢ Q(1,2)))
@test S(:(P(1) + ψ ⊢ 0)) ∧ S(:(ψ ⊢ P(1))) == S(:(ψ ⊢ 0))

# The order ≤_ℛ
#--------------

# `a⁺ + a⁺a⁻ = a⁺a⁻`, so `a⁺ ≤_ℛ a⁺a⁻` with 𝔹 coefficients and not with ℕ
@test refl_leq(S(:(ψ ⊢ 0)), S(:(ψ ⊢ ψ)))
@test !refl_leq(Sℕ(:(ψ ⊢ 0)), Sℕ(:(ψ ⊢ ψ)))
@test refl_leq(S(:(ψ ⊢ 0)), S(:(ψ + P(1) ⊢ P(1))))
@test !refl_leq(S(:(ψ ⊢ 0)), S(:(ψ + P(1) ⊢ 0)))
@test !refl_leq(S(:(ψ ⊢ 0)), S(:(0 ⊢ ψ)))
# Brute force: `t ∈ ℛ(m)` iff `t = m + (Z ⊢ Z)` for some `Z` of terms of `t`
function refl_leq_bf(m::Sequent{𝔹}, t::Sequent{𝔹})
  Z = collect(NominalFrames.terms(t))
  any(t == m + Sequent{𝔹}(collect(z), collect(z)) for z in NominalFrames.powerset(Z))
end
all𝔹 = small_sequents(𝔹, Σ, [1, 2], 3)
for m in small_sequents(𝔹, Σ, [1, 2], 2), t in all𝔹
  @test refl_leq(m, t) == refl_leq_bf(m, t)
end

# Least element of ℛ(m) above w, and ℛ(m₁) ∩ ℛ(m₂)
@test refl_above(S(:(ψ ⊢ 0)), S(:(0 ⊢ P(1)))) == S(:(ψ + P(1) ⊢ P(1)))
@test refl_meet(S(:(ψ ⊢ 0)), S(:(P(1) ⊢ 0))) == S(:(ψ + P(1) ⊢ ψ + P(1)))  # never empty
@test isnothing(refl_meet(Sℕ(:(ψ ⊢ 0)), Sℕ(:(P(1) ⊢ 0))))
for m₁ in small_sequents(𝔹, Σψ, Int[], 2), m₂ in small_sequents(𝔹, Σψ, Int[], 2),
    t in small_sequents(𝔹, Σψ, Int[], 2)
  @test refl_leq(refl_meet(m₁, m₂), t) == (refl_leq(m₁, t) && refl_leq(m₂, t))
end
for m in small_sequents(𝔹, Σ, [1, 2], 2), w in small_sequents(𝔹, Σ, [1, 2], 2)
  u = refl_above(m, w)
  @test refl_leq(m, u) && w ≼ u
  @test all(!(refl_leq(m, t) && w ≼ t) || u ≼ t for t in all𝔹)
end

# One ≤_ℛ-step down: either or both halves of a balanced pair
@test Set(refl_predecessors(S(:(ψ + P(1) ⊢ ψ)))) ==
      Set(S.([:(P(1) ⊢ ψ), :(ψ + P(1) ⊢ 0), :(P(1) ⊢ 0)]))
@test refl_predecessors(Sℕ(:(ψ + P(1) ⊢ ψ))) == [Sℕ(:(P(1) ⊢ 0))]

# Singleton residuals, generator by generator
#--------------------------------------------

# `{s} ⊸ {k}` is an interval
@test Set(residual_strict(S(:(ψ ⊢ 0)), S(:(ψ + P(1) ⊢ 0)))) == Set(S.([:(P(1) ⊢ 0), :(ψ + P(1) ⊢ 0)]))
@test residual_strict(Sℕ(:(ψ ⊢ 0)), Sℕ(:(ψ + P(1) ⊢ 0))) == [Sℕ(:(P(1) ⊢ 0))]
@test isempty(residual_strict(S(:(ψ ⊢ 0)), S(:(P(1) ⊢ 0))))
# `{a⁺} ⊸ ℛ(a⁺b⁻) = ℛ(b⁻) ∪ ℛ(a⁺b⁻) ∪ ℛ(a⁻b⁻)`
@test Set(residual_refl(S(:(ψ ⊢ 0)), S(:(ψ ⊢ P(1))))) ==
      Set(S.([:(0 ⊢ P(1)), :(ψ ⊢ P(1)), :(0 ⊢ ψ + P(1))]))
@test residual_refl(Sℕ(:(ψ ⊢ 0)), Sℕ(:(ψ ⊢ P(1)))) == [Sℕ(:(0 ⊢ P(1)))]

# Membership and the oracles of the ℕ tests, now with 𝔹 coefficients
#--------------------------------------------------------------------

"""
Membership `t ∈ κ ∪ 𝒲(λ) ∪ ℛ(μ)` by exhaustive search: a witness below `t` can
only use names of `t` and of the context.
"""
function member(t::Sequent{𝔹}, C::Constructible{𝔹})::Bool
  Δ = C.context
  pool = t.supp ∪ Δ
  any(same_orbit(t, k, Δ) for k in C.strict) ||
    any(l′ ≼ t for l in C.weak for l′ in orbit(l, Δ, pool)) ||
    any(refl_leq_bf(m′, t) for m in C.refl for m′ in orbit(m, Δ, pool))
end

refl = refl_sequents(𝔹, Σ)
s₀ = S(:(P(1) ⊢ Q(1,2)))
I𝒪 = 𝒲(refl)
Iℛ = ℛ(refl)
I𝒲 = 𝒲([refl; s₀])
I𝒟 = κ([s₀]) ∪ I𝒪
frames = [I𝒪, Iℛ, I𝒲, I𝒟]
@test all(F isa Constructible{𝔹} for F in frames)

ts = small_sequents(𝔹, Σ, [1, 2, 3], 2)
@test length(ts) == 1 + 20 + binomial(20, 2)   # no `2x` sequents

@test S(:(P(1) + ψ ⊢ ψ + P(1))) ∈ Iℛ
@test S(:(P(1) + ψ ⊢ ψ)) ∉ Iℛ
@test S(:(P(1) + ψ ⊢ 0)) ∉ Iℛ
@test S(:(ψ ⊢ ψ)) ∈ ℛ([S(:(ψ ⊢ 0))])             # ψ⁺ + ψ⁺ψ⁻ = ψ⁺ψ⁻, so ψ⁺ ≤_ℛ ψ⁺ψ⁻ ...
@test Sℕ(:(ψ ⊢ ψ)) ∉ ℛ([Sℕ(:(ψ ⊢ 0))])           # ... but not with multiplicities

for I in frames, t in ts
  @test (t ∈ I) == member(t, I)
end
for I in frames, Δ in [Γ1, Γ12], t in ts
  @test member(t, I) == member(t, enlarge_context(I, Δ))
end

# Singleton residual: `t ∈ {s} ⊸ C  iff  s + t ∈ C`
ss = S.([:(P(1) ⊢ 0), :(0 ⊢ P(1)), :(ψ ⊢ 0), :(P(1) ⊢ P(1)), :(0 ⊢ Q(1,2)),
         :(P(2) ⊢ Q(2,1)), :(P(1) ⊢ ψ), :(P(1) + P(2) ⊢ 0)])
for I in [frames; C([:(P(1) ⊢ 0)], [:(ψ ⊢ 0)], [:(Q(1,2) ⊢ 0)], []);
          C([:(ψ ⊢ P(1))], [:(ψ ⊢ P(1))], [], [])], s in ss
  R = s →ₒ I
  @test R.context == I.context ∪ s.supp
  for t in ts
    @test member(t, R) == member(s + t, I)
  end
end

# Binary intersection
As = [I𝒪, I𝒲, Iℛ, I𝒟, ⊤, ⊥,
      C([:(P(1) ⊢ 0)], [:(ψ ⊢ 0)], [:(Q(1,2) ⊢ 0)], []),
      C([], [:(P(1) ⊢ 0)], [:(P(1) ⊢ ψ)], []),
      C([], [:(P(1) ⊢ 0), :(ψ ⊢ 0)], [], []),
      𝒲([S(:(P(1) ⊢ 0))], [1])]
for A in As, B in As, t in ts
  @test (t ∈ A ∩ B) == (t ∈ A && t ∈ B)
end
# ℛ(ψ⁺) ∩ ℛ(P⁺ₐ) = ℛ(ψ⁺P⁺ₐψ⁻P⁻ₐ), nonempty unlike its ℕ counterpart
@test only((ℛ([S(:(ψ ⊢ 0))]) ∩ ℛ([S(:(P(1) ⊢ 0))])).refl) == S(:(ψ + P(1) ⊢ ψ + P(1)))
@test ℛ([Sℕ(:(ψ ⊢ 0))]) ∩ ℛ([Sℕ(:(P(1) ⊢ 0))]) == bottom(∅)

# Orbit intersection: `t ∈ ⋂_π πC` iff `G_Γ • t ⊆ C`
Cs = [enlarge_context(I, Γ1) for I in frames]
push!(Cs, 𝒲([S(:(P(1) ⊢ P(1))), S(:(P(2) ⊢ P(2)))], Γ1),
      𝒲([S(:(P(2) ⊢ 0)), S(:(Q(1,3) ⊢ 0))], Γ1),
      C([], [:(P(1) ⊢ P(1))], [], Γ1),
      C([:(Q(1,2) ⊢ 0)], [:(P(2) ⊢ ψ)], [:(Q(2,1) ⊢ 0)], Γ1),
      C([], [:(P(1) ⊢ 0), :(P(2) ⊢ 0)], [:(ψ ⊢ ψ)], Γ1),
      C([], [:(Q(1,2) ⊢ 0), :(Q(2,1) ⊢ 0), :(Q(2, 3) ⊢ 0)], [:(P(3) ⊢ P(3))], Γ1),
      C([], [:(P(2) ⊢ 0)], [:(ψ ⊢ P(1))], Γ1))
for Cᵢ in Cs
  R = orbit_intersection(Cᵢ, ∅)
  @test R.context == ∅
  for t in ts
    @test (t ∈ R) == orbit_subset(t, Cᵢ, ∅)
  end
end
for Cᵢ in [enlarge_context(I, Γ12) for I in frames]
  R = orbit_intersection(Cᵢ, ∅)
  for t in ts
    @test (t ∈ R) == orbit_subset(t, Cᵢ, ∅)
  end
end

# Covering tests
#---------------

@test covers(⊤, Σ) && !covers(⊥, Σ)
@test covers(C([:(0 ⊢ 0)], [], [:(ψ ⊢ 0), :(0 ⊢ ψ)], []), Σψ)
@test !covers(C([:(0 ⊢ 0)], [], [:(ψ ⊢ 0), :(0 ⊢ ψ)], []), Σ)
# With ℕ coefficients `2ψ⁺` escapes `R ∪ ℛ(ψ⁺) ∪ ℛ(ψ⁻)`; with 𝔹 there is no `2ψ⁺`
@test covers(ℛ(S.([:(0 ⊢ 0), :(ψ ⊢ 0), :(0 ⊢ ψ)])), Σψ)
@test !covers(ℛ(Sℕ.([:(0 ⊢ 0), :(ψ ⊢ 0), :(0 ⊢ ψ)])), Σψ)
@test !covers(ℛ(S.([:(0 ⊢ 0), :(ψ ⊢ 0), :(0 ⊢ ψ)])), Σ)   # P⁺ escapes
@test covers(ℛ(S.([:(0 ⊢ 0)])), Σ; reflexive=true)
@test !covers(Iℛ, Σ; reflexive=true)

# The general residual, against direct decision
#----------------------------------------------

function in_residual(t::Sequent{𝔹}, A::Constructible{𝔹}, C::Constructible{𝔹})::Bool
  Γ = A.context
  reps(g) = refine(g, Γ, setdiff(t.supp, Γ))
  all(g′ + t ∈ C for g in A.strict for g′ in reps(g)) &&
  all(covers(((g′ + t) →ₒ C), Σ) for g in A.weak for g′ in reps(g)) &&
  all(covers(((g′ + t) →ₒ C), Σ; reflexive=true) for g in A.refl for g′ in reps(g))
end

nfs = [normal_form(I, Σ) for I in frames]
@test nfs[4] == ℛ([s₀]) ∪ I𝒪
As = [κ([S(:(P(1) ⊢ 0))]), 𝒲([S(:(P(1) ⊢ 0))]), ℛ([S(:(P(1) ⊢ 0))]), κ([S(:(0 ⊢ Q(1,2)))]),
      C([:(P(1) ⊢ 0)], [:(ψ ⊢ 0)], [], []), 𝒲(S.([:(ψ ⊢ 0), :(P(1) ⊢ P(2))])),
      κ([S(:(P(1) ⊢ 0))], Γ1), ℛ([S(:(Q(2,1) ⊢ 0))], Γ1),
      κ([S(:(P(2) ⊢ 0))], Γ1) ∪ 𝒲([S(:(Q(1,2) ⊢ 0))], Γ1)]
for A in As, I in nfs
  R = A →ₒ I
  @test R.context == A.context
  for t in ts
    @test (t ∈ R) == in_residual(t, A, I)
  end
end
for I in nfs, A in As[1:3]
  A⊥ = A →ₒ I
  A⊥⊥ = A⊥ →ₒ I
  for t in ts
    @test (t ∈ A) ≤ (t ∈ A⊥⊥)
    @test (t ∈ A⊥) == (t ∈ (A⊥⊥ →ₒ I))
  end
end

# Normal form
#------------

same(A, B, ts) = all((t ∈ A) == (t ∈ B) for t in ts)
tsψ = small_sequents(𝔹, Σψ, Int[], 2)  # all four positions of 𝔹[{ψ}]²
Ss = [frames; C([:(P(1) ⊢ 0), :(Q(1,2) ⊢ Q(2,1))], [:(ψ ⊢ 0)], [:(P(1) ⊢ P(2))], []);
      C([:(ψ ⊢ ψ)], [:(P(1) ⊢ Q(1,2))], [:(Q(1,2) ⊢ 0)], []);
      C([:(Q(1,2) ⊢ 0)], [:(P(2) ⊢ ψ)], [:(Q(2,1) ⊢ 0)], [1]);
      C([:(ψ ⊢ 0), :(ψ ⊢ ψ), :(0 ⊢ 0)], [], [], [])]
for Sᵢ in Ss
  N = normal_form(Sᵢ, Σ)
  @test N.context == Sᵢ.context
  @test same(N, Sᵢ, ts)
  @test normal_form(N, Σ) == N
  @test same(top_residual(N, Σ), 𝒲(N), ts)
  for g in N.refl
    @test covers((g →ₒ N), Σ; reflexive=true) && !covers((g →ₒ N), Σ)
  end
end
# ⊤ ⊸ S on the finite ψ-fragment, exhaustively
for Sᵢ in [C([:(ψ ⊢ 0)], [], [:(ψ ⊢ ψ)], []), ℛ(S.([:(ψ ⊢ 0), :(0 ⊢ ψ)])),
           κ(S.([:(0 ⊢ 0), :(ψ ⊢ 0), :(ψ ⊢ ψ)])), κ(S.([:(0 ⊢ 0), :(ψ ⊢ 0), :(0 ⊢ ψ), :(ψ ⊢ ψ)]))]
  A = top_residual(Sᵢ, Σψ)
  for t in tsψ
    @test (t ∈ A) == all(t + u ∈ Sᵢ for u in tsψ)
  end
end
# One subobject, several presentations, one normal form: with only ψ around,
# `{ψ⁺, ψ⁺ψ⁻} = 𝒲(ψ⁺)`, and `𝒫[{ψ}]² = 𝒲(0)`
@test normal_form(κ(S.([:(ψ ⊢ 0), :(ψ ⊢ ψ)])), Σψ) == 𝒲([S(:(ψ ⊢ 0))])
@test normal_form(κ(tsψ), Σψ) == top(𝔹, ∅)
# ... whereas `{ψ⁺, ψ⁺ψ⁻}` is `ℛ(ψ⁺)` when `P` is around: `ψ⁺P⁺P⁻ ∉`, but `ψ⁺ + Z⁺Z⁻ ∈` for `Z ⊆ {ψ}`
@test normal_form(κ(S.([:(ψ ⊢ 0), :(ψ ⊢ ψ)])), Σψ) == 𝒲([S(:(ψ ⊢ 0))])
@test normal_form(κ(S.([:(ψ ⊢ 0), :(ψ ⊢ ψ)])), Σ) == κ(S.([:(ψ ⊢ 0), :(ψ ⊢ ψ)]))

# Brute force on a nullary signature, where `𝔹[X]²` is finite
#------------------------------------------------------------

a′, b′ = Predicate(:a, 0), Predicate(:b, 0)
Σab = Signature([a′, b′])
positions = Set(small_sequents(𝔹, Σab, Int[], 4))
@test length(positions) == 16

elements(C::Constructible{𝔹}) = Set(t for t in positions if t ∈ C)
bf_perp(I, A) = Set(t for t in positions if all(a + t ∈ I for a in A))
bf_closure(I, A) = bf_perp(I, bf_perp(I, A))
bf_tensor(A, B) = Set(a + b for a in A for b in B)

# The paper's idempotent frame `⊥_𝔹` on `X = {a, b}` (`sec:exidem`)
I_B = Set(S.([:(0 ⊢ 0), :(0 ⊢ a), :(0 ⊢ a + b), :(a ⊢ a), :(a ⊢ a + b), :(b ⊢ b),
              :(b ⊢ a + b), :(a + b ⊢ 0), :(a + b ⊢ a), :(a + b ⊢ b), :(a + b ⊢ a + b)]))
F_B = Frame(Σab, κ(collect(I_B)))
@test elements(F_B.sequents) == I_B
# `(a⁺)^⊥ = ⊤ ∖ 𝒫[{a⁺, b⁻}]` and `(a⁻)^⊥ = ⊤ ∖ {b⁺, b⁺a⁻}`
@test elements(perp(F_B, κ([S(:(a ⊢ 0))]))) == setdiff(positions, S.([:(0 ⊢ 0), :(a ⊢ 0), :(0 ⊢ b), :(a ⊢ b)]))
@test elements(perp(F_B, κ([S(:(0 ⊢ a))]))) == setdiff(positions, S.([:(b ⊢ 0), :(b ⊢ a)]))
# Not monotone (`a ⊢ a, b` holds but `a, b ⊢ a, b`... does; `⊢ a` holds, `b ⊢ a` does not)
@test S(:(0 ⊢ a)) ∈ F_B.sequents && S(:(b ⊢ a)) ∉ F_B.sequents

# Brute-force implication-space semantics: pairs of closed subsets of positions
struct BF; prem::Set{Sequent{𝔹}}; conc::Set{Sequent{𝔹}}; end
function bf_semantics(I)
  cl(A) = bf_closure(I, A)
  pp(A) = bf_perp(I, A)
  atom(x) = BF(cl(Set([S(:($x ⊢ 0))])), cl(Set([S(:(0 ⊢ $x))])))
  tensor(A, B) = cl(bf_tensor(A, B))
  par(A, B) = pp(bf_tensor(pp(A), pp(B)))
  ops = Dict{Symbol,Function}(
    :¬ => (p) -> BF(p.conc, p.prem),
    :⊗ => (p, q) -> BF(tensor(p.prem, q.prem), par(p.conc, q.conc)),
    :⊕ => (p, q) -> BF(cl(p.prem ∪ q.prem), p.conc ∩ q.conc),
    :& => (p, q) -> BF(p.prem ∩ q.prem, cl(p.conc ∪ q.conc)),
    :⅋ => (p, q) -> BF(par(p.prem, q.prem), tensor(p.conc, q.conc)),
    :lolli => (p, q) -> BF(par(p.conc, q.prem), tensor(p.prem, q.conc)),
    :∧ => (p, q) -> BF(tensor(p.prem, q.prem), p.conc ∩ q.conc ∩ tensor(p.conc, q.conc)),
    :∨ => (p, q) -> BF(p.prem ∩ q.prem ∩ tensor(p.prem, q.prem), tensor(p.conc, q.conc)))
  entails(ps, qs) = reduce(bf_tensor, [[p.prem for p in ps]; [q.conc for q in qs]];
                           init=Set([S(:(0 ⊢ 0))])) ⊆ I
  (atom=atom, ops=ops, entails=entails)
end

lib_ops = Dict{Symbol,Function}(:¬ => ¬, :⊗ => ⊗, :⊕ => ⊕, :& => &, :⅋ => ⅋,
                                :lolli => lolli, :∧ => ∧, :∨ => ∨)
binary = [:⊗, :⊕, :&, :⅋, :lolli, :∧, :∨]
# Formulas: atoms, negated atoms, and one binary connective between two of those
leaves = [(:a,), (:b,), (:¬, :a), (:¬, :b)]
formulas = [[(o, l, r) for o in binary for l in leaves for r in leaves]; leaves]
function eval_formula(φ, atom, ops)
  length(φ) == 1 && return atom(φ[1])
  φ[1] == :¬ && return ops[:¬](atom(φ[2]))
  ops[φ[1]](eval_formula(φ[2], atom, ops), eval_formula(φ[3], atom, ops))
end

# Six more frames, arbitrary subsets of the positions given by bit patterns
sorted_positions = sort(collect(positions))
frame(bits) = Set(sorted_positions[i] for i in 1:16 if (bits >> (i - 1)) & 1 == 1)
more_frames = frame.([0x5A3C, 0x0F0F, 0x9999, 0x1E2D, 0x7331, 0xC4B2])
for I in [I_B; more_frames]
  F = Frame(Σab, κ(collect(I)))
  @test elements(F.sequents) == I
  bf = bf_semantics(I)
  lib_atom(x) = RolePair(F, x)
  for φ in formulas
    p = eval_formula(φ, bf.atom, bf.ops)
    q = eval_formula(φ, lib_atom, lib_ops)
    @test elements(Constructible(q.prem)) == p.prem
    @test elements(Constructible(q.conc)) == p.conc
  end
  # Consequence among a few formulas
  fs = [formulas[i] for i in [1, 8, 20, 33, 60, 100, 113, 114]]
  for φ in fs, χ in fs
    p, q = eval_formula(φ, bf.atom, bf.ops), eval_formula(χ, bf.atom, bf.ops)
    p′, q′ = eval_formula(φ, lib_atom, lib_ops), eval_formula(χ, lib_atom, lib_ops)
    @test (p′ ⊩ q′) == bf.entails([p], [q])
    @test ([] ⊩ q′) == bf.entails(BF[], [q])
    @test ([p′, p′] ⊩ [q′]) == bf.entails([p, p], [q])
  end
end

# A frame with weakening can be computed with either coefficients
#-----------------------------------------------------------------
#
# For `I′ = 𝒲(λ′)`, `q⁻¹(I′) = 𝒲(ι λ′)` is a constructible triple with ℕ
# coefficients presenting a frame with the same Girard quantale, and `q` of the
# ℕ presentation of `S^⊥` presents the 𝔹 residual (`Semiring.jl`). The
# courtroom's affine and contractive courts are such frames; its linear court is
# not, and there the two theories give different answers.

W, Cv, R = Predicate(:W, 1), Predicate(:C, 0), Predicate(:R, 0)
Σc = Signature([W, Cv, R])
rule, twice = Sℕ(:(W(1) + W(2) ⊢ C)), Sℕ(:(2W(1) ⊢ C))
reflℕ = refl_sequents(Σc)
I_lin = ℛ([rule]) ∪ 𝒲(reflℕ)
I_aff = 𝒲([rule; reflℕ])
I_con = 𝒲([rule; twice; reflℕ])
courtsℕ = Frame.(Ref(Σc), [I_lin, I_aff, I_con])
courts𝔹 = [Frame(Σc, Constructible{𝔹}(I)) for I in [I_lin, I_aff, I_con]]
# With sets, "the same witness twice" is one witness: the court `q(I_con)` says a
# single witness convicts. `I_con` itself is not contractive in the paper's sense
# (`W⁺ₐC⁻ ∉ I_con` while `2W⁺ₐC⁻ ∈ I_con`), so it is not `q⁻¹` of anything; the ℕ
# frame with the quantale of `q(I_con)` is `q⁻¹(q(I_con)) = 𝒲(W⁺ₐC⁻, refl)`.
@test courts𝔹[3].sequents == 𝒲([S(:(W(1) ⊢ C)); refl_sequents(𝔹, Σc)])
courtsℕ′ = [Frame(Σc, Constructible{ℕ}(F.sequents)) for F in courts𝔹[2:3]]
@test courtsℕ′[1].sequents == courtsℕ[2].sequents            # I_aff = q⁻¹(q(I_aff))
@test courtsℕ′[2].sequents == 𝒲([Sℕ(:(W(1) ⊢ C)); reflℕ])   # I_con ≠ q⁻¹(q(I_con))

# Residuals: `q(perp_ℕ(ι S′)) = perp_𝔹(S′)` for the frames with weakening
roles = [κ([S(:(W(1) ⊢ 0))], Γ1), κ([S(:(0 ⊢ C))]), ℛ([S(:(W(1) ⊢ C))], Γ1),
         𝒲([S(:(W(1) + W(2) ⊢ 0))], Γ12), C([:(W(1) ⊢ 0)], [:(R ⊢ 0)], [:(W(2) ⊢ C)], Γ12)]
for (Fℕ, F𝔹) in zip(courtsℕ′, courts𝔹[2:3]), A in roles
  viaℕ = Constructible{𝔹}(perp(Fℕ, Constructible{ℕ}(A)))
  @test roles_equal(F𝔹, viaℕ, perp(F𝔹, A))
  @test roles_equal(F𝔹, Constructible{𝔹}(closure(Fℕ, Constructible{ℕ}(A))), closure(F𝔹, A))
end

# The courtroom's queries, in both theories
atoms_of(F) = (Wa=RolePair(F, :(W(1))), Wb=RolePair(F, :(W(2))), Wc=RolePair(F, :(W(3))),
               Cv=RolePair(F, :C), Rn=RolePair(F, :R))
queries = [
  F -> (A = atoms_of(F); [A.Wa, A.Wb] ⊩ [A.Cv]),
  F -> (A = atoms_of(F); A.Wa ⊩ A.Cv),
  F -> (A = atoms_of(F); [A.Wa, A.Wa] ⊩ [A.Cv]),
  F -> (A = atoms_of(F); A.Wa ⊗ A.Wa ⊩ A.Cv),
  F -> (A = atoms_of(F); [A.Wa, A.Wb, A.Wc] ⊩ [A.Cv]),
  F -> (A = atoms_of(F); [A.Wa, A.Wb, A.Rn] ⊩ [A.Cv]),
  F -> (A = atoms_of(F); [A.Wa, A.Wb, A.Rn] ⊩ [A.Cv ⅋ A.Rn]),
  F -> (A = atoms_of(F); [A.Wa, A.Wb] ⊩ [A.Cv ⅋ A.Rn]),
  F -> (A = atoms_of(F); [A.Wa, A.Wb ⊕ A.Wc] ⊩ [A.Cv]),
  F -> (A = atoms_of(F); [A.Wa, A.Wb ⊕ A.Rn] ⊩ [A.Cv]),
  F -> (A = atoms_of(F); [A.Wa, A.Wb & A.Rn] ⊩ [A.Cv]),
  F -> (A = atoms_of(F); [] ⊩ ∀(Γ12, lolli(A.Wa ⊗ A.Wb, A.Cv))),
  F -> (A = atoms_of(F); [] ⊩ ∀(Γ1, lolli(A.Wa ⊗ A.Wa, A.Cv))),
  F -> (A = atoms_of(F); [] ⊩ ∀(Γ1, lolli(A.Wa, A.Cv))),
  F -> (A = atoms_of(F); A.Wa ⊩ ∀(Set([2]), lolli(A.Wb, A.Cv))),
  F -> (A = atoms_of(F); A.Wa ⊩ ∀(Set([2]), in_context(lolli(A.Wb, A.Cv), Γ12))),
  F -> (A = atoms_of(F); ∃(Γ1, A.Wa) ⊩ ∀(Set([2]), lolli(A.Wb, A.Cv))),
  F -> (A = atoms_of(F); ∃(Γ12, A.Wa ⊗ A.Wb) ⊩ A.Cv),
  F -> (A = atoms_of(F); ∀(Γ1, A.Wa) ⊩ A.Cv),
  F -> (A = atoms_of(F); [A.Wa, A.Wb] ⊩ [A.Cv ⅋ A.Cv]),
]
answers(F) = [q(F) for q in queries]
for (Fℕ, F𝔹) in zip(courtsℕ′, courts𝔹[2:3])
  @test answers(Fℕ) == answers(F𝔹)
end
@test answers(courtsℕ[2]) == answers(courts𝔹[2])
@test answers(courtsℕ[3]) != answers(courts𝔹[3])    # e.g. `W(a) ⊨ C` only with sets
@test !queries[2](courtsℕ[3]) && queries[2](courts𝔹[3])
# The linear court has no ℕ counterpart. Against the ℕ linear court it agrees
# except where contraction bites: two witnesses convict twice over,
# `W(a), W(b) ⊨ C ⅋ C`, since `W⁺ₐW⁺ᵦC⁻C⁻ = W⁺ₐW⁺ᵦC⁻`.
linℕ, lin𝔹 = answers(courtsℕ[1]), answers(courts𝔹[1])
@test linℕ[1:19] == lin𝔹[1:19]
@test !linℕ[20] && lin𝔹[20]

end # module
