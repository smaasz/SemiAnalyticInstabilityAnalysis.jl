module SemiAnalyticInstabilityAnalysis

using Symbolics
import Base: getindex
# using RuntimeGeneratedFunctions
# RuntimeGeneratedFunctions.init(@__MODULE__)
include("grids.jl")
export ∑, CV, EV, EC, VC, VE, CE, ∇cv, ∇ᵀvc, rtrig, ∇̂cv, ∇̂ᵀvc

end
