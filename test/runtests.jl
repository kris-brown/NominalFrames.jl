using Test

@testset "Multisets.jl" begin
  include("Multisets.jl")
end

@testset "Syntax" begin
  include("Syntax.jl")
end

@testset "Orbits" begin
  include("Orbits.jl")
end

@testset "PowerElems" begin
  include("PowerElems.jl")
end


@testset "SingletonResidual" begin
  include("SingletonResidual.jl")
end

@testset "Residual" begin
  include("Residual.jl")
end

@testset "NormalForm" begin
  include("NormalForm.jl")
end

@testset "Semantics" begin
  include("Semantics.jl")
end

@testset "Contraction" begin
  include("Contraction.jl")
end

# @testset "Frames" begin
#   include("Frames.jl")
# end

# @testset "Demo" begin
#   include("demo.jl")
# end

# @testset "Courtroom" begin
#   include("courtroom.jl")
# end
