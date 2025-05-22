function ∑(e, E, exp)
    sum(Symbolics.scalarize.([substitute(exp, Dict(e .=> e_)) for e_ in E]))
end

function ∑(e, E::SymbolicUtils.BasicSymbolic, exp)
    if operation(E) == ifelse
        return ifelse(E.arguments[1], ∑(e, E.arguments[2], exp), ∑(e, E.arguments[3], exp))
    else
        @show E
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

function EC(c)
    return ifelse(c[3] == 1, [[c[1]+1, c[2]-1, 1], [c[1], c[2], 2], [c[1], c[2], 3]], [[c[1], c[2], 1], [c[1]-1, c[2], 2], [c[1], c[2], 3]])
end

function VC(c)
    return ifelse(c[3] == 1, [[c[1], c[2]], [c[1]+1, c[2]-1], [c[1], c[2]-1]], [[c[1], c[2]], [c[1]-1, c[2]], [c[1], c[2]-1]])
end

function VE(e)
    return ifelse(e[3] == 1, [[e[1], e[2]], [e[1]-1, e[2]]], ifelse(e[3] == 2, [[e[1], e[2]], [e[1]+1, e[2]-1]], [[e[1], e[2]], [e[1], e[2]-1]]))
end

function CE(e)
    return ifelse(e[3] == 1, [[e[1]-1, e[2]+1, 1], [e[1], e[2], 2]], ifelse(e[3] == 2, [[e[1], e[2], 1], [e[1]+1, e[2], 2]], [[e[1], e[2], 1], [e[1], e[2], 2]]))
end


const Pi = Symbolics.variable(:Pi)

const e = @syms e₁::Int e₂::Int e₃::Int
const c = @syms c₁::Int c₂::Int c₃::Int
const v = @syms v₁::Int v₂::Int

const ne = Symbolics.variables(:ne, 1:2, 1:3, T=Real)
const le = Symbolics.variable(:le, T=Real)
const Ac = Symbolics.variable(:Ac, T=Real)

const sqrt3 = Symbolics.variable(:sqrt3, T=Real)

const ne_ = [sqrt3//2 -sqrt3//2 0; 1//2 1//2 -1]

function ∇cv(p)
    ve = ∑(v, VE(e), p[v[1], v[2]] // 2)
    [∑(e, EC((3,3,1)), ve * le * ne[iTH,e[3]]) for iTH = 1:2]
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
