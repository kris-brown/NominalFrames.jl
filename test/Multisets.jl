module TestMultisets 

using NominalFrames, Test

s1, s2 = MultiSet([:a,:b,:b]), MultiSet([:c,:b])

@test s1+s2 ==  MultiSet([:c,:b,:a,:b,:b])

@test s1 ≼ s1+s2
@test !(≼(s1, s2))

@test sorted(s1) == [:a=>1, :b=>2]

@test (s1+s2)∸s1 == s2
@test s2∸s1 == MultiSet([:c])
@test s1∸s2 == MultiSet([:a,:b])

@test s1 ∧ s2 == MultiSet([:b])

@test s1 ∨ s2 == MultiSet([:a,:b,:b,:c])

@test (s1+s2) - s1 == s2.counts
@test s1 - s2 == Dict(:a=>1,:b=>1,:c=>-1)

end # module