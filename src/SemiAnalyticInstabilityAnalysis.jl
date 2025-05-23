module SemiAnalyticInstabilityAnalysis

using Symbolics
import Base: getindex
# using RuntimeGeneratedFunctions
# RuntimeGeneratedFunctions.init(@__MODULE__)
include("grids.jl")
export ∑, CV, EV, EC, VC, VE, CE, ∇cv, rtrig, ∇̂cv, ∇̂ᵀvc

end
