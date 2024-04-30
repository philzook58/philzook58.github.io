using SymbolicUtils
using MathLink
using MacroTools
cd("julia/rubistuff/Rubi/Rubi/IntegrationRules")
#cd("1 Algebraic functions")
cd(readdir()[1])
cd(readdir()[1])
cd(readdir()[1])
pwd()
f = open(readdir()[1]) do file
    read(file,String)
end
f
e = eval( :( @W_cmd( $f )) )

keymap = Dict(
  W"Power" => :^,
  W"Times" => :*)

# convert mathlink Expr to regular Expr
# puts ~ in front of pattern variables 
exprify(e::MathLink.WSymbol) = Symbol(e.name)
function exprify(e::MathLink.WExpr) 
    if e.head == W"Pattern"
        varname = Symbol(e.args[1])
        return :(~$varname)
    elseif haskey(keymap, e.head)
            Expr(:call, keymap[e.head], exprify.(e.args)...)
    else
    # maybe lookup a table here.
    Expr(:call, Symbol(lowercase(e.head.name)), exprify.(e.args)...)
        end
end
exprify(e::Int64) = e 
exprify(e)

@syms int

getpats(x::Int64) = ()
getpats(x::MathLink.WSymbol) = ()
function getpats(x::MathLink.WExpr) 
    if x.head == W"Pattern"
        [x.args[1]] 
    else 
        Iterators.flatten([getpats(i) for i in x.args ])
    end
end


pattify( x, pats) = x
pattify( x::Symbol, pats) = x ∈ pats  ? :(~ $x) : x
pattify( x::Expr, pats) = Expr(x.head, x.args[1], [pattify(e,pats) for e in x.args[2:end]]...)


function unpack(e)
   @assert e.head == W"SetDelayed"
   lhs = e.args[1]
   if e.args[2].head == W"Condition"
       rhscond = e.args[2]
       cond = rhscond.args[2]
       rhs = exprify(rhcond.args[1])
    else
       rhs = exprify(e.args[1])
       cond = []
    end
   lhs.head == W"Int"
   pats = Set(exprify.(getpats(lhs)))
   grand = exprify(lhs.args[1])
   var = exprify(lhs.args[2])
   rhs = pattify(rhs,pats)
   :(@rule int($grand, $var) => $rhs)
end

eval(unpack(e))