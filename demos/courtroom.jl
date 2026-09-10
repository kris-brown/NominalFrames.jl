# # The courtroom: a substructural frame that is not in the paper
#
# Run with `julia --project=. test/unchecked/courtroom.jl`.
#
# Three claimables: `W(x)` — "x testifies to the crime"; `C` — "the accused is
# convicted"; and `R` — "it rained", which takes part in no inference and is
# there to be carried around. The rule of the court is that two *distinct*
# witnesses convict:
#
#     W(x), W(y) ⊢ C
#
# What makes this substructural is what the rule does *not* say, and the
# choices give three courts on one signature:
#
# - the *linear* court `I_lin = ℛ(W⁺ₓW⁺ᵧC⁻) ∪ 𝒲(refl)`: no contraction (one
#   witness testifying twice is not two witnesses) and no weakening — the rule
#   may only be padded *reflexively*, `W(x), W(y), Z ⊢ C, Z`, so side
#   commitments are carried across rather than dropped;
# - the *affine* court `I_aff = 𝒲(W⁺ₓW⁺ᵧC⁻) ∪ 𝒲(refl)`: still no contraction,
#   but anything may be added anywhere;
# - the *contractive* court `I_con = I_aff ∪ 𝒲(2W⁺ₓC⁻)`: the same witness
#   twice does convict.
#
# All contain the reflexive `t ⊢ t` with arbitrary weakening, so `0 = 𝒲(refl)`
# as in the paper's frames.
#
# The quantified queries turn on a feature of the nominal semantics: names in a
# context are pairwise distinct, and a bound variable ranges over names *outside*
# the context at which the formula is interpreted. The first two courts are not
# substitution-equivariant (def:substeq) — identifying the two witnesses in the
# rule gives `2W(x) ⊢ C`, which they reject — so Beck–Chevalley fails for them
# (prop:hyper), and the value of `∀y. (W(y) ⊸ C)` depends on whether `a` is in
# scope when `y` is bound. The contractive court is substitution-equivariant and
# the dependence disappears.

module Courtroom

using Test, NominalFrames

banner(s) = println("\n", "═"^78, "\n ", s, "\n", "═"^78)
say(args...) = println("  ", args...)

S(x) = Sequent(x)
S(x::Sequent) = x

Γ1, Γ2, Γ12, Γ123 = Set([1]), Set([2]), Set([1, 2]), Set([1, 2, 3])

W = Predicate(:W, 1)
C = Predicate(:C, 0)
R = Predicate(:R, 0)
Σ = Signature([W, C, R])
refl = refl_sequents(Σ)
rule = S(:(W(1) + W(2) ⊢ C))
twice = S(:(2W(1) ⊢ C))

I_lin = ℛ([rule]) ∪ 𝒲(refl)
I_aff = 𝒲([rule; refl])
I_con = 𝒲([rule; twice; refl])
courts = ["linear" => Frame(Σ, I_lin),
          "affine" => Frame(Σ, I_aff),
          "contractive" => Frame(Σ, I_con)]

banner("The three courts")
for (name, F) in courts
  say(rpad(name, 12), "I = ", F.sequents)
end
# All three presentations are already normal (the paper's `I𝒟` was not: demo.jl).
@test [F.sequents for (_, F) in courts] == [I_lin, I_aff, I_con]
@test twice ∉ I_lin && twice ∉ I_aff && twice ∈ I_con

# A table-driven runner: each query is a label, a function of the court, and
# the expected answers in the linear, affine and contractive courts.
function run(queries, courts)
  for (label, q, expected) in queries
    answers = [q(F) for (_, F) in courts]
    say(rpad(label, 46), join(lpad.(string.(answers), 12), " "))
    @test answers == collect(expected)
  end
end
header() = say(rpad("", 46), join(lpad.(first.(courts), 12), " "))

# Atoms at context `{a, b, c}` = `{1, 2, 3}`, and the nullary `Cv`, `Rn`.
atoms(F) = (Wa=RolePair(F, :(W(1))), Wb=RolePair(F, :(W(2))), Wc=RolePair(F, :(W(3))),
            Cv=RolePair(F, :C), Rn=RolePair(F, :R))

# ## Propositional queries

banner("Propositional queries")
header()
run([
  # The rule itself, and contraction.
  ("W(a), W(b) ⊨ C",            F -> (A = atoms(F); [A.Wa, A.Wb] ⊩ [A.Cv]),              (true, true, true)),
  ("W(a) ⊨ C",                  F -> (A = atoms(F); A.Wa ⊩ A.Cv),                        (false, false, false)),
  ("W(a), W(a) ⊨ C",            F -> (A = atoms(F); [A.Wa, A.Wa] ⊩ [A.Cv]),              (false, false, true)),
  ("W(a) ⊗ W(a) ⊨ C",           F -> (A = atoms(F); A.Wa ⊗ A.Wa ⊩ A.Cv),                 (false, false, true)),
  # Weakening: a third witness, or the weather, is harmless where there is
  # weakening and fatal in the linear court, where every commitment counts.
  ("W(a), W(b), W(c) ⊨ C",      F -> (A = atoms(F); [A.Wa, A.Wb, A.Wc] ⊩ [A.Cv]),        (false, true, true)),
  ("W(a), W(b), R ⊨ C",         F -> (A = atoms(F); [A.Wa, A.Wb, A.Rn] ⊩ [A.Cv]),        (false, true, true)),
  # ... unless it is carried along to the conclusion side, which is exactly
  # what reflexive weakening permits.
  ("W(a), W(b), R ⊨ C ⅋ R",     F -> (A = atoms(F); [A.Wa, A.Wb, A.Rn] ⊩ [A.Cv ⅋ A.Rn]), (true, true, true)),
  ("W(a), W(b), R ⊨ C ⊗ R",     F -> (A = atoms(F); [A.Wa, A.Wb, A.Rn] ⊩ [A.Cv ⊗ A.Rn]), (true, true, true)),
  # A conclusion may not be dropped either, in the linear court.
  ("W(a), W(b) ⊨ C ⅋ R",        F -> (A = atoms(F); [A.Wa, A.Wb] ⊩ [A.Cv ⅋ A.Rn]),       (false, true, true)),
  # Additives: a case split on who the second witness is.
  ("W(a), W(b) ⊕ W(c) ⊨ C",     F -> (A = atoms(F); [A.Wa, A.Wb ⊕ A.Wc] ⊩ [A.Cv]),       (true, true, true)),
  ("W(a), W(b) ⊕ R ⊨ C",        F -> (A = atoms(F); [A.Wa, A.Wb ⊕ A.Rn] ⊩ [A.Cv]),       (false, false, false)),
  ("W(a), W(b) & R ⊨ C",        F -> (A = atoms(F); [A.Wa, A.Wb & A.Rn] ⊩ [A.Cv]),       (true, true, true)),
], courts)

# ## Quantified queries
#
# `∀(Δ, φ)` binds the names `Δ` at the smallest context; `in_context(φ, Γ)`
# first views `φ` at the larger context `Γ`, so that a subsequent binder ranges
# over names outside `Γ`.

banner("Quantified queries")
header()
run([
  # The rule as a closed theorem. `∀x∀y` ranges over *distinct* x, y, so this
  # says nothing about one witness testifying twice — which is asked next.
  ("⊨ ∀x∀y. W(x) ⊗ W(y) ⊸ C",
     F -> (A = atoms(F); [] ⊩ ∀(Γ12, lolli(A.Wa ⊗ A.Wb, A.Cv))),                   (true, true, true)),
  ("⊨ ∀x. W(x) ⊗ W(x) ⊸ C",
     F -> (A = atoms(F); [] ⊩ ∀(Γ1, lolli(A.Wa ⊗ A.Wa, A.Cv))),                    (false, false, true)),
  ("⊨ ∀x. W(x) ⊸ C",
     F -> (A = atoms(F); [] ⊩ ∀(Γ1, lolli(A.Wa, A.Cv))),                           (false, false, false)),
  # Three witnesses under the quantifier: weakening again separates the courts.
  ("⊨ ∀x∀y∀z. W(x) ⊗ W(y) ⊗ W(z) ⊸ C",
     F -> (A = atoms(F); [] ⊩ ∀(Γ123, lolli(A.Wa ⊗ A.Wb ⊗ A.Wc, A.Cv))),           (false, true, true)),
  # A witness in hand, and "any further witness convicts". Interpreted at the
  # empty context, `y` ranges over every name — including a's — and without
  # contraction the inference fails ...
  ("W(a) ⊨ ∀y. (W(y) ⊸ C)   at context ∅",
     F -> (A = atoms(F); A.Wa ⊩ ∀(Γ2, lolli(A.Wb, A.Cv))),                          (false, false, true)),
  # ... whereas interpreted at context {a}, `y` means every name *other than*
  # a, and any further witness does suffice. Beck–Chevalley fails in the first
  # two courts; in the contractive court the two readings agree.
  ("W(a) ⊨ ∀y. (W(y) ⊸ C)   at context {a}",
     F -> (A = atoms(F); A.Wa ⊩ ∀(Γ2, in_context(lolli(A.Wb, A.Cv), Γ12))),         (true, true, true)),
  ("W(a) ⊨ W(a) ⊸ C",
     F -> (A = atoms(F); A.Wa ⊩ lolli(A.Wa, A.Cv)),                                 (false, false, true)),
  # Forget who the witness was: an existential premise no longer fixes a name,
  # so the `y` of the conclusion might be the very same person.
  ("∃x. W(x) ⊨ ∀y. (W(y) ⊸ C)",
     F -> (A = atoms(F); ∃(Γ1, A.Wa) ⊩ ∀(Γ2, lolli(A.Wb, A.Cv))),                   (false, false, true)),
  # Two existential witnesses do convict: `∃x∃y` keeps them distinct.
  ("∃x∃y. W(x) ⊗ W(y) ⊨ C",
     F -> (A = atoms(F); ∃(Γ12, A.Wa ⊗ A.Wb) ⊩ A.Cv),                               (true, true, true)),
  ("∃x. W(x) ⊗ W(x) ⊨ C",
     F -> (A = atoms(F); ∃(Γ1, A.Wa ⊗ A.Wa) ⊩ A.Cv),                                (false, false, true)),
  # And the structural collapse of the paper's example: "everyone testifies"
  # has the absurd premisory role `0`, so it convicts anyone of anything.
  ("∀x. W(x) ⊨ C",
     F -> (A = atoms(F); ∀(Γ1, A.Wa) ⊩ A.Cv),                                       (true, true, true)),
], courts)

# ## The failure of Beck–Chevalley, in roles
#
# In the linear court, the conclusory role of `∀y. (W(y) ⊸ C)` interpreted at
# `∅` contains `W⁺_cC⁻` for *every* name `c`, while interpreted at `{a}` it
# contains them only for `c ≠ a`. Against the premisory role of `W(a)`, which
# contains `W⁺ₐ`, the first produces `2W⁺ₐC⁻`, which the court rejects.

banner("Beck–Chevalley, in roles (linear court)")
F = courts[1].second
A = atoms(F)
at∅ = ∀(Γ2, lolli(A.Wb, A.Cv))
at_a = ∀(Γ2, in_context(lolli(A.Wb, A.Cv), Γ12))
say("⟦∀y. (W(y) ⊸ C)⟧₋ at ∅   = ", Constructible(at∅.conc))
say("⟦∀y. (W(y) ⊸ C)⟧₋ at {a} = ", Constructible(at_a.conc))
@test context(at∅) == Set{Int}() && context(at_a) == Γ1
@test S(:(W(1) ⊢ C)) ∈ at∅.conc
@test S(:(W(1) ⊢ C)) ∉ at_a.conc && S(:(W(2) ⊢ C)) ∈ at_a.conc
@test S(:(2W(1) ⊢ C)) ∈ minkowski(Constructible(A.Wa.prem), Constructible(at∅.conc))
@test S(:(2W(1) ⊢ C)) ∉ F.sequents
# The two values differ as roles at {a}: BC fails.
@test enlarge_context(at∅.conc, Γ1) != at_a.conc
# ... and agree in the contractive court, where the frame is substitution-equivariant.
Fc = courts[3].second
Ac = atoms(Fc)
c∅ = ∀(Γ2, lolli(Ac.Wb, Ac.Cv))
c_a = ∀(Γ2, in_context(lolli(Ac.Wb, Ac.Cv), Γ12))
@test enlarge_context(c∅.conc, Γ1) == c_a.conc
@test enlarge_context(c∅.prem, Γ1) == c_a.prem

println()

end # module
