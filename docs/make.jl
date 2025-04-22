using SemiAnalyticInstabilityAnalysis
using Documenter

DocMeta.setdocmeta!(SemiAnalyticInstabilityAnalysis, :DocTestSetup, :(using SemiAnalyticInstabilityAnalysis); recursive=true)

makedocs(;
    modules=[SemiAnalyticInstabilityAnalysis],
    authors="Steffen Maass <steffen.maass@awi.de> and contributors",
    sitename="SemiAnalyticInstabilityAnalysis.jl",
    format=Documenter.HTML(;
        canonical="https://smaasz.github.io/SemiAnalyticInstabilityAnalysis.jl",
        edit_link="main",
        assets=String[],
    ),
    pages=[
        "Home" => "index.md",
    ],
)

deploydocs(;
    repo="github.com/smaasz/SemiAnalyticInstabilityAnalysis.jl",
    devbranch="main",
)
