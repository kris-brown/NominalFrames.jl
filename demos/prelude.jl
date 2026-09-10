# Shared setup for the demos. Nothing here is specific to any one example; it
# only fixes two standing assumptions and provides a few display helpers so the
# demos read as a sequence of questions and answers.

using Test, NominalFrames

# Standing assumption 1: premises and conclusions are *sets*. Asserting a claim
# twice is no different from asserting it once (contraction).
default_multiplicity!(𝔹)

# Standing assumption 2 (containment) is imposed per frame, by including
# `containment(Σ)` among the good implications: for every claimable A, `A ⊢ A`
# is good, and so is anything obtained from it by adding further premises or
# conclusions. A position that both asserts and denies A is already out of
# bounds, so nothing added to it can make a difference.
containment(Σ::Signature) = 𝒲(refl_sequents(Σ))

# Display
#--------

banner(s) = println("\n", "═"^78, "\n ", s, "\n", "═"^78)
say(args...) = println("  ", args...)
note(args...) = println("\n  ", args..., "\n")

const WIDTH = 58

"""
Render a sequent expression in turnstile notation, keeping the order in which
the claims were written: `:(Bird(x) + Penguin(x) ⊢ Flies(x))` becomes
`Bird(x), Penguin(x) ⊢ Flies(x)`; an empty side (`0`) is left blank.
"""
function turnstile(e::Expr)
  claims(x) = x == 0 ? String[] :
              x isa Expr && x.head == :call && x.args[1] == :+ ?
                reduce(vcat, claims.(x.args[2:end])) : [string(x)]
  prem, conc = e.head == :call && e.args[1] == :⊢ ? (e.args[2], e.args[3]) : (0, e)
  l, r = join(claims(prem), ", "), join(claims(conc), ", ")
  string(l, isempty(l) ? "" : " ", "⊢", isempty(r) ? "" : " ", r)
end

""" A verdict, a label, and (optionally) a remark explaining the verdict """
function verdict(v::String, label::String, why::String)
  say(rpad(v, 10), isempty(why) ? label : string(rpad(label, WIDTH), "  (", why, ")"))
end

"""
Ask the frame whether an implication is good, print the answer, and record the
answer we expected (so that the demos double as tests).
"""
function check(F::Frame, e::Expr; expect::Bool, why::String="")
  answer = Sequent(e) ∈ F.sequents
  verdict(answer ? "good" : "not good", turnstile(e), why)
  @test answer == expect
  answer
end

"""
Ask a question of the semantics (an entailment `⊨`, already computed as
`answer`), print the verdict next to its label, and record what we expected.
"""
function ask(label::String, answer::Bool; expect::Bool, why::String="")
  verdict(answer ? "holds" : "fails", label, why)
  @test answer == expect
  answer
end

""" Print the implications a frame is declared with, in turnstile notation """
function declare(title::String, implications::Vector{Expr}, extra::String="")
  say(title)
  for e in implications
    say("    ", turnstile(e))
  end
  isempty(extra) || say("    ", extra)
end
