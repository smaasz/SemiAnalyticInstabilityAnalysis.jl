function getindex(A::AbstractArray, ii::Int, jj::Symbolics.Symbolic{<:Symbolics.Integer}, kk::Symbolics.Symbolic{<:Symbolics.Integer})
    Symbolics.Term{Symbolics.symeltype(A)}(Symbolics.getindex, [A, ii, jj, kk])
end

function getindex(A::AbstractArray, ii::Int, jj::Symbolics.Symbolic{<:Symbolics.Integer}, kk::Symbolics.Symbolic{<:Symbolics.Integer}, ll::Symbolics.Symbolic{<:Symbolics.Integer})
    Symbolics.Term{Symbolics.symeltype(A)}(Symbolics.getindex, [A, ii, jj, kk, ll])
end

const sqrt3 = Symbolics.variable(:sqrt3, T=Real)

function ∑(e, E, exp)
    sum(Symbolics.scalarize.([substitute(exp, Dict(e .=> e_)) for e_ in E]))
end

function ∑(e, E::SymbolicUtils.BasicSymbolic, exp)
    if operation(E) == ifelse
        return ifelse(E.arguments[1], ∑(e, E.arguments[2], exp), ∑(e, E.arguments[3], exp))
    else
       throw(DomainError(E, "is not a ifelse operation")) 
    end
end

function CV(v)
    return [
        [v[1], v[2], 1], [v[1], v[2]+1, 1], [v[1]-1, v[2]+1, 1],
        [v[1], v[2], 2], [v[1], v[2]+1, 2], [v[1]+1, v[2], 2]
    ]
end

function EV(v)
    return [
        [v[1], v[2], 1], [v[1]+1, v[2], 1],
        [v[1], v[2], 2], [v[1]-1, v[2]+1, 2],
        [v[1], v[2], 3], [v[1], v[2]+1, 3]
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
    return ifelse(c[3] == 1, [[c[1]+1, c[2]-1, 1], [c[1], c[2], 2], [c[1], c[2], 3]], [[c[1], c[2], 1], [c[1]-1, c[2], 2], [c[1], c[2], 3]])
end

function VC(c)
    return ifelse(c[3] == 1, [[c[1], c[2]], [c[1]+1, c[2]-1], [c[1], c[2]-1]], [[c[1], c[2]], [c[1]-1, c[2]], [c[1], c[2]-1]])
end

function CC(c)
    return ifelse(c[3] == 1, [[c[1], c[2], 2], [c[1]+1, c[2], 2], [c[1]+1, c[2]-1, 2]], [[c[1], c[2], 1], [c[1]-1, c[2], 1], [c[1]-1, c[2]+1, 1]])
end

function VE(e)
    return ifelse(e[3] == 1, [[e[1], e[2]], [e[1]-1, e[2]]], ifelse(e[3] == 2, [[e[1], e[2]], [e[1]+1, e[2]-1]], [[e[1], e[2]], [e[1], e[2]-1]]))
end

function CE(e)
    return ifelse(e[3] == 1, [[e[1]-1, e[2]+1, 1], [e[1], e[2], 2]], ifelse(e[3] == 2, [[e[1], e[2], 1], [e[1]+1, e[2], 2]], [[e[1], e[2], 1], [e[1], e[2], 2]]))
end


const Pi = Symbolics.variable(:Pi; T=Int)

const e = @syms e₁::Int e₂::Int e₃::Int
const c = @syms c₁::Int c₂::Int c₃::Int
const c̃ = @syms c̃₁::Int c̃₂::Int c̃₃::Int
const v = @syms v₁::Int v₂::Int

const ne = Symbolics.variables(:ne, 1:2, 1:3, 1:2; T=Real)
const nev = Symbolics.variables(:ne, 1:2, 1:3, 1:3, 1:3; T=Real)
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
    [ 1//Ac * ∑(e, EC(c), ve * le * ne[iTH,e[3],c[3]] ) for iTH = 1:2]
end

function ∇cc(F)
    #[∑(c̃, CC(c
end

# divergence operators

function ∇ᵀvc(F)
    fe = ∑(c, CE(e), le//sqrt3 * sum([F[iTH, c[1], c[2], c[3]] * nev[iTH, e[1]-v[1]+2, e[2]-v[2]+2, e[3]] for iTH=1:2]))
    1//Av * ∑(e, EV(v), fe)
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
    t = ∇cv(ϕ * p̂)
    t = [simplify(substitute(ϕcv[iHc] * t[iTH], Dict(c .=> (nS+1,nS+1,iHc)))) for iTH=1:2, iHc=1:2]
    simplify(substitute.(t, Ref(merge(sub_cov, sub_ane))))
end

function ∇̂cv(_k,_l,_p̂, _le) # this is slow if used more often better use runtimegeneratedfunction
    g = _∇̂cv() # this is not optimal, maybe generate function instead at precompilation time!
    substitute(g, Ref(Dict([k => _k, l => _l, p̂ => _p̂, le => _le, sqrt3 => √3])))
end

function _∇̂ᵀvc()
    t = ∇ᵀvc([ϕ[x,y] * ϕvc[jHc] * F̂[jTH, jHc] for jTH=1:2, x=1:size(ϕ,1), y=1:size(ϕ,2), jHc=1:2])
    t = simplify(substitute(t, Dict(v .=> (nS+1, nS+1))))
    simplify(substitute(t, merge(sub_cov, sub_ane)))
end

function ∇̂ᵀvc(_k,_l,_F̂,_le)
    g = _∇̂ᵀvc()
    substitute(g, Dict([k => _k; l => _l; reduce(vcat, F̂ .=> _F̂); le => _le; sqrt3 => √3]))
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
