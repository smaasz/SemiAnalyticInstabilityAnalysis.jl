function getindex(A::AbstractArray, ii::Int, jj::Symbolics.Symbolic{<:Symbolics.Integer}, kk::Symbolics.Symbolic{<:Symbolics.Integer})
    Symbolics.Term{Symbolics.symeltype(A)}(Symbolics.getindex, [A, ii, jj, kk])
end

function getindex(A::AbstractArray, ii::Int, jj::Symbolics.Symbolic{<:Symbolics.Integer}, kk::Symbolics.Symbolic{<:Symbolics.Integer}, ll::Symbolics.Symbolic{<:Symbolics.Integer})
    Symbolics.Term{Symbolics.symeltype(A)}(Symbolics.getindex, [A, ii, jj, kk, ll])
end

function cross(a, b)
    a[1] * b[2] - a[2] * b[1]
end

const sqrt3 = Symbolics.variable(:sqrt3, T=Real)

function ∑(e, E::Vector{<:Tuple}, exp)
    @assert length(e) == length(E[1])
    sum([substitute(exp, merge([Dict(e[i] .=> e_[i]) for i in 1:length(e)]...)) for e_ in E])
end

function ∑(e, E::SymbolicUtils.BasicSymbolic{Vector{T}}, exp) where T <: Tuple
    if istree(E)
        @assert operation(E) == ifelse
        return ifelse(E.arguments[1], ∑(e, Symbolics.unwrap(E.arguments[2]), exp), ∑(e, Symbolics.unwrap(E.arguments[3]), exp)) # unwrap necessary because of a bug
    else
        throw(DomainError(E))
    end
end

function CV(v)
    return [
        (v[1], v[2], 1), (v[1], v[2]+1, 1), (v[1]-1, v[2]+1, 1),
        (v[1], v[2], 2), (v[1], v[2]+1, 2), (v[1]+1, v[2], 2)
    ]
end

function EV(v)
    return [
        ((v[1], v[2], 1), (1//2, -sqrt3//2)), ((v[1]+1, v[2], 1)  , (-1//2, sqrt3//2)),
        ((v[1], v[2], 2), (1//2, sqrt3//2)) , ((v[1]-1, v[2]+1, 2), (-1//2, -sqrt3//2)),
        ((v[1], v[2], 3), (1//1, 0))        , ((v[1], v[2]+1, 3)  , (-1//1, 0))
    ]
end

const _nev = let
    _nev = zeros(Num, 2, 3, 3, 3)
    _nev[:,2,2,1] = [ 1//2; -sqrt3//2]
    _nev[:,3,2,1] = [-1//2;  sqrt3//2]
    _nev[:,2,2,2] = [ 1//2;  sqrt3//2]
    _nev[:,1,3,2] = [-1//2; -sqrt3//2]
    _nev[:,2,2,3] = [ 1//1;         0]
    _nev[:,2,3,3] = [-1//1;         0]
    _nev
end
    

function EC(c)
    ifelse(c[3] == 1,
           [((c[1]+1, c[2]-1, 1), [sqrt3//2, 1//2]), ((c[1], c[2], 2), [-sqrt3//2, 1//2]), ((c[1], c[2], 3), Num[0, -1//1])],
           [((c[1], c[2], 1), [-sqrt3//2, -1//2]), ((c[1]-1, c[2], 2), [sqrt3//2, -1//2]), ((c[1], c[2], 3), Num[0, 1//1])]
           )
end

function VC(c)
    return ifelse(c[3] == 1, [(c[1], c[2]), (c[1]+1, c[2]-1), (c[1], c[2]-1)], [(c[1], c[2]), (c[1]-1, c[2]), (c[1], c[2]-1)])
end

function CC(c)
    return ifelse(c[3] == 1, [(c[1], c[2], 2), (c[1]+1, c[2], 2), (c[1]+1, c[2]-1, 2)], [(c[1], c[2], 1), (c[1]-1, c[2], 1), (c[1]-1, c[2]+1, 1)])
end

function VE(e)
    return ifelse(e[3] == 1, [(e[1], e[2]), (e[1]-1, e[2])], ifelse(e[3] == 2, [(e[1], e[2]), (e[1]+1, e[2]-1)], [(e[1], e[2]), (e[1], e[2]-1)]))
end

function CE(e, n⃗ec)
    ifelse(e[3] == 1,
           ifelse(cross(l⃗e[1], n⃗ec) > 0, [((e[1], e[2], 2), 1.), ((e[1]-1, e[2]+1, 1), -1.)], [((e[1], e[2], 2), -1.), ((e[1]-1, e[2]+1, 1), 1.)]),
           ifelse(e[3] == 2,
                  ifelse(cross(l⃗e[2], n⃗ec) > 0, [((e[1], e[2], 1), -1.), ((e[1]+1, e[2], 2), 1.)], [((e[1], e[2], 1), 1.), ((e[1]+1, e[2], 2), -1.)]),
                  ifelse(cross(l⃗e[3], n⃗ec) > 0, [((e[1], e[2], 1), 1.), ((e[1], e[2], 2), -1.)], [((e[1], e[2], 1), -1.), ((e[1], e[2], 2), 1.)])
                  )
           )
end

function CE(e)
    return ifelse(e[3] == 1, [(e[1]-1, e[2]+1, 1), (e[1], e[2], 2)], ifelse(e[3] == 2, [(e[1], e[2], 1), (e[1]+1, e[2], 2)], [(e[1], e[2], 1), (e[1], e[2], 2)]))
end

const l⃗e = [[0.5, -√3/2], [0.5, √3/2], [1., 0.]]

const Pi = Symbolics.variable(:Pi; T=Int)

const e = @syms e₁::Int e₂::Int e₃::Int
const c = @syms c₁::Int c₂::Int c₃::Int
const c̃ = @syms c̃₁::Int c̃₂::Int c̃₃::Int
const v = @syms v₁::Int v₂::Int

const ne = Symbolics.variables(:ne, 1:2, 1:3, 1:2; T=Real)
const nev = Symbolics.variables(:ne, 1:2, 1:3, 1:3, 1:3; T=Real) #const n⃗ev = Symbolics.variables(:nev, 1:2)
const n⃗ec = Symbolics.variables(:nec, 1:2; T=Real)
const d  = Symbolics.variable(:d; T=Real)
const le = Symbolics.variable(:le; T=Real)
const Ac = Symbolics.variable(:Ac; T=Real)
const Av = Symbolics.variable(:Av; T=Real)

const bb = le * [-1//2 -1; sqrt3//2 0]

function _Ac(_le)
    1//2 * _le * sqrt3//2 * _le
end
_Av(_le) = 2 * _Ac(_le)

const _ne = [sqrt3//2; 1//2;; -sqrt3//2; 1//2;; 0; -1;;; -sqrt3//2; -1//2;; sqrt3//2; -1//2;; 0; 1]

# gradient operators

function ∇cv(p)
    ve = ∑(v, VE(e), p[v[1], v[2]] // 2)
    Symbolics.scalarize([ 1//Ac * ∑((e, nec), EC(c), ve * le * n⃗ec[iTH] ) for iTH = 1:2])
end

function ∇cc(F)
    dF = [ ∑((c, d), CE(e, n⃗ec), d * F[jTH, c[1], c[2], c[3]]) for jTH=1:2 ]
    [∑((e, n⃗ec), EC(c), n⃗ec[iTH] * dF[jTH]) for iTH=1:2, jTH=1:2]
end

# divergence operators

function ∇ᵀvc(F)
    fe = ∑(c, CE(e), le//sqrt3 * sum([F[iTH, c[1], c[2], c[3]] * n⃗ev[iTH] for iTH=1:2]))
    1//Av * ∑((e, n⃗ev), EV(v), fe)
end

const k = Symbolics.variable(:k; T=Real)
const l = Symbolics.variable(:l; T=Real)
const nS = 2
const ϕ = exp.(im * [k * x + l * y for x = -nS:nS, y = -nS:nS])
const ϕcv = [exp(im * (k * 1//3 + l * (-2//3))), exp(im * (k * -1//3 + l * -1//3))]
const ϕvc = [exp(im * (k * -1//3 + l * 2//3)), exp(im * (k * 1//3 + l * 1//3))]

const p̂ = Symbolics.variable(:p̂)
const F̂ = Symbolics.variables(:F̂, 1:2, 1:2)

const sub_cov = Dict([k => bb[1,1] * k + bb[2,1] * l, l => bb[1,2] * k + bb[2,2] * l])
const sub_ane = Dict([Ac => _Ac(le); Av => _Av(le); reduce(vcat, nev .=> _nev); reduce(vcat, ne .=> _ne); sqrt3 => √3])

function _∇̂cv()
    t = ∇cv(ϕ .* p̂)
    t = [simplify(substitute(ϕcv[iHc] * t[iTH], Dict(c .=> (nS+1,nS+1,iHc)))) for iTH=1:2, iHc=1:2]
    simplify(substitute.(t, Ref(merge(sub_cov, sub_ane))))
end

function ∇̂cv(_k,_l,_p̂, _le) # this is slow if used more often better use runtimegeneratedfunction
    g = _∇̂cv() # this is not optimal, maybe generate function instead at precompilation time!
    substitute.(g, Ref(Dict([k => _k, l => _l, p̂ => _p̂, le => _le, sqrt3 => √3])))
end

function _∇̂ᵀvc()
    t = ∇ᵀvc([ϕ[x,y] * ϕvc[jHc] * F̂[jTH, jHc] for jTH=1:2, x=1:size(ϕ,1), y=1:size(ϕ,2), jHc=1:2])
    t = simplify(substitute(t, Dict(v .=> (nS+1, nS+1))))
    simplify(substitute(t, merge(sub_cov, sub_ane)))
end

function ∇̂ᵀvc(_k,_l,_F̂,_le)
    d = _∇̂ᵀvc()
    substitute(d, Dict([k => _k; l => _l; reduce(vcat, F̂ .=> _F̂); le => _le; sqrt3 => √3]))
end


const rcos = let
    x = Symbolics.variable(:x)
    @rule cos(~x) => substitute(taylor(cos(x), x, 0, 0:3), Dict([x => ~x]))
end

const rsin = let
    x = Symbolics.variable(:x)
    @rule sin(~x) => substitute(taylor(sin(x), x, 0, 0:3), Dict([x => ~x]))
end

rtrig = SymbolicUtils.Postwalk(SymbolicUtils.PassThrough(SymbolicUtils.RestartedChain([rcos, rsin])))



subs = Dict([Ac => 1//2 * le * sqrt3//2 * le])
