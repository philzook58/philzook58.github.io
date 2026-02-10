---
title: SMTLIB as a Compiler IR I
date : 2026-02-09
---

I like SMT solvers. Compilers are cool. What kind of babies can they make?

A design trick that has lead me to interesting places is to abuse the z3py AST more thoroughly than any sane person would do. Z3 already has very reasonable AST for describiing logic, bitvector operations, functions, reals, and integers. But, if you do it right, in addition to just an AST, you also get semantics and a magic solver.

Compilers are nice because they are a pretty well specified problem that is actually useful. Reasoning principles and technology can be applied to make code faster. Bad reasoning can make output code buggy even when the input wasn't.

There are at least two ways to approach what a compiler IR is:

1. It is basically pure expressions that we start bolting stateful stuff onto
2. It is basically imperative code / slightly abstracted assembly that we sometimes find pure subpieces of to help do optimization

I tend to be 1 and that is the approach I'll be taking today.

# SSA is Functional Programming

One of my favorite papers is SSA is Functional Programming <https://www.cs.princeton.edu/~appel/papers/ssafun.pdf> . From this perspective, the core of SSA is a bunch of mutually defined recursive definitions.

Single Static Assignment (SSA) <https://en.wikipedia.org/wiki/Static_single-assignment_form> is a compiler IR that people have noticed makes some compilation subproblems more straightforward. Variables can be only assigned once. You can kind of do this by making any subsequent assignments go to a fresh variable and replace later reads by reading from that fresh variables.

We can take the example program from the paper and write it in python

```python
%%file /tmp/myfun.py
def myfun():
    i = 1
    j = 1
    k = 0
    while k < 100:
        if j < 20:
            j = i
            k = k+1
        else:
            j = k
            k = k + 2
    return j

print(myfun())
```

    Overwriting /tmp/myfun.py

```python
! python /tmp/myfun.py
```

    1

For fun, I'll build a cfg of this function using a package

```python
from py2cfg import CFGBuilder

cfg = CFGBuilder().build_from_file('myfun', '/tmp/myfun.py')
cfg.build_visual('exampleCFG', 'svg')
```

![](/assets/smtexampleCFG.svg)

We can break this up into one function per block. Since python doesn't have tail call optimization, this is a ludicrous thing to do from python's perspective, but it does put the thing into a normal form.

You can see that each one of these functions corresponds to a block above. These programs compute the same thing.

```python
def myfun():
    return loop(1,1,0)

def loop(i,j,k): # orange block
    return if_head(i,j,k) if k < 100 else done(i,j,k)

def if_head(i,j,k): # red block
    return then(i,j,k) if j < 20 else else_(i,j,k)

def then(i,j,k):
    return loop(i, i, k + 1)

def else_(i,j,k):
    return loop(i, k, k + 2)

def done(i,j,k): # green block
    return j

myfun()
```

    1

# Turning it Into SMT

One of the important features of my system [knuckledragger](www.kdrag.com) is that it supports [definitions](https://github.com/philzook58/knuckledragger/blob/6e4f4e6a7a563f0c3f809278a650a78b784c5250/src/kdrag/kernel.py#L264). These definitions are registered and unfolded via the z3 function `substitute_funs`

We can replicate exactly this structure above and now we have a CFG-like thing in our logic thing. Neat!

```python
from kdrag.all import *
Z = smt.IntSort()

# predeclare all our blocks so that we can recursively call them
myfun = smt.Function("myfun", Z)
loop = smt.Function("loop", Z,Z,Z, Z)
if_head = smt.Function("if_head", Z,Z,Z, Z)
then = smt.Function("then", Z,Z,Z, Z)
else_ = smt.Function("else_", Z,Z,Z, Z)
done = smt.Function("done", Z,Z,Z, Z)
i,j,k = smt.Ints("i j k")

myfun = kd.define("myfun", [], loop(1,1,0))
loop = kd.define("loop", [i,j,k], smt.If(k < 100, if_head(i,j,k), done(i,j,k)))
if_head = kd.define("if_head", [i,j,k], smt.If(j < 20, then(i,j,k), else_(i,j,k)))
then = kd.define("then", [i,j,k], loop(i, i, k + 1))
else_ = kd.define("else_", [i,j,k], loop(i, k, k + 2))
done = kd.define("done", [i,j,k], j)



```

`define` makes a definitional theorem for each of these. Here is `if_head`'s for example

```python
if_head.defn
```

&#x22A8;ForAll([i, j, k],
       if_head(i, j, k) ==
       If(j < 20, then(i, j, k), else_(i, j, k)))

The [`full_simp`](https://github.com/philzook58/knuckledragger/blob/6e4f4e6a7a563f0c3f809278a650a78b784c5250/src/kdrag/rewrite.py#L113) function interleaves `z3.substitute_funs` and `z3.simplify` until the expression stops changing. We can use it to run the program or any other concrete definitions.

```python
kd.full_simp(kd.full_simp(myfun))
```

1

# Making it more IR-y

However, is this a compiler IR? Doesn't super look like one?

Well, this is to some degree of matter of printing. If you use the right sigils and formatting, things look more like a compiler IR.

Compiler IRs typically have a sequence of simple operations. Operations are simple flat things things like  `add %x, %y`  but not compound things like `(add (add (add x y) z) (add x y))`.

SMTLIB is a pure logic. There isn't really a notion of sequencing or assignment as one might have in an imperative language or compiler IR. However, we can expand our expressions into such a sequence basically by [traversing them in order and storing the subexpressions in a list](https://github.com/philzook58/knuckledragger/blob/91cceb88a5cbbc9937fa7f0d28e33a93a42e1e6e/src/kdrag/contrib/ir/__init__.py#L54).

It is common (to my understanding) that the "names" in the textual form of SSA rarely actually appear in the data structure of SSA. The variable is represented often by a pointer to the operation that produced it. They are basically the same thing or can be conflated/coerced to be the same thing.

In my [printer](https://github.com/philzook58/knuckledragger/blob/91cceb88a5cbbc9937fa7f0d28e33a93a42e1e6e/src/kdrag/contrib/ir/__init__.py#L106) I do the same thing. I print subexpression using their id, which is a unique number z3 supplies via hash consing.

```python
import kdrag.contrib.ir as ir

blk = ir.Block([Z,Z,Z], kd.kernel.defns[loop]._subst_fun_body)
ir.Block.of_defined_fun(loop)


```

    ^(Int,Int,Int):
     %0 = < %var2, 100
     %1 = if_head %var0, %var1, %var2
     %2 = done %var0, %var1, %var2
     %3 = if %0, %1, %2

I can also print a function consisting of mutually defined blocks. Really this isn't doing anything much to the expressions. It's a printing choice.

```python
ir.Function.of_defined_funs([myfun.decl(), loop, if_head, then, else_, done])
```

```
fn myfun {
@myfun:
^():
    %0 = loop 1, 1, 0
@loop:
^(Int,Int,Int):
    %0 = < %var2, 100
    %1 = if_head %var0, %var1, %var2
    %2 = done %var0, %var1, %var2
    %3 = if %0, %1, %2
@if_head:
^(Int,Int,Int):
    %0 = < %var1, 20
    %1 = then %var0, %var1, %var2
    %2 = else_ %var0, %var1, %var2
    %3 = if %0, %1, %2
@then:
^(Int,Int,Int):
    %0 = + %var2, 1
    %1 = loop %var0, %var0, %0
@else_:
^(Int,Int,Int):
    %0 = + %var2, 2
    %1 = loop %var0, %var2, %0
@done:
^(Int,Int,Int):
}
```

# Bits and Bobbles

Next time, maybe I'll talk about taking textual [QBE](https://c9x.me/compile/doc/il.html) and converting it to SMT by

1. Turning phi nodes into block args. Kind of push them up to the blocks they came from.
2. explicitizing memory (use the smt theory of arrays)
3. CSE

I think I like QBE.

Max has some great posts on IRs and SSA
<https://bernsteinbear.com/blog/ssa/>
<https://bernsteinbear.com/blog/irs/>

Michel was pointing out to me that in the SSA is FP paper it mentions that the dominator structure can be reflected in nested let bindings. That's pretty cool. I don't really have let is knuckledragger sadly / z3py doesn't offer it. I kind of wish it did.

Modelling a CFG as a constrained horn clause is an alternative. It is the logic programming version of SSA is functional programming. It's more predicaty than equational.
<https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/nbjorner-yurifest.pdf>
<https://www.philipzucker.com/bap-chc/>

SMTLIb dialect of MLIR <https://mlir.llvm.org/docs/Dialects/SMT/> <https://github.com/opencompl/xdsl-smt>

MimIR <https://www.arxiv.org/pdf/2411.07443> . Really neat. Trying to make a new MLIR like thing based around the SSA is functional programming style

Whitequark and wanda projunnamed <https://mastodon.social/@whitequark/113970437064821618> <https://github.com/prjunnamed/prjunnamed>

One curious thing that I'm not sure what to do with is that in a more typical IR, the tail calls would be part of the `if` operation at the end. Instead I have them early which looks weird from an imperative perspective. But I tried changing my `Block` structure to look more like this and I didn't like it.

What's intriguing about using SMT as my IR is how maybe I can use to to verify optimizations or synthesize optimizations.

Writing a new AST is a lot of bulk laborious work. It leads to decision fatigue and for blogging purposes it is too much bulk stuff. Designing an ast is it's own blog post easily. Especially in python, where the language does not make it succinct to define new node types. Dataclasses help but it isn't great to keep having to write `class` over and over again.

Having said that, I do feel the pain in my project Knuckledragger. "If only I could change just this little thing about z3 or add this little feature." But it also keeps me honest.

"The method of 'postulating' what we want has many advantages ; they are the same as the advantages of theft over honest toil.” - Russell

Ironically, the same crowd of people that may abhor cheating with axioms sometimes loves the idea of cheating by changing the nature of their logic to make this or that slicker or more automatic. This is from a certain perspective an even deeper version of postulating what you want to be true to be true by fiat. And having a logical system who I can't recognize the relation to a more conventional logic is even more suspect and uneasy making than some funky axiom.

# parsing block args qbe

Been tinkering on a variation of qbe that takes block args and explicit memory passing. Kind of neat.

```python
import lark
from kdrag.all import *
from kdrag.contrib.ir import *
grammar = r"""
start : NL* funcdef NL*
funcdef: "function" GLOBAL NL? "{" NL block+ "}"
block: LABEL "(" [param_list] ")" NL instrs jump NL
instrs : instr*
instr: TEMP "=" BASETY OP operand ("," operand)* NL

?jump: call | ite | ret

ite : "ite" operand "," call "," call
// jmp: "jmp" call
//jnz: ("jnz" | "ite") val "," call "," call
ret: "ret" [operand] // make a call?

call : LABEL "(" [call_param_list] ")"

operand: SIGNED_INT | TEMP | GLOBAL
OP: /[A-Za-z][A-Za-z0-9]+/

param_list: param ("," param)*
param : BASETY TEMP

call_param_list : operand ("," operand)*

GLOBAL: /\$[A-Za-z_.][A-Za-z0-9_.]*/
LABEL: /@[A-Za-z_.][A-Za-z0-9_.]*/
TEMP: /%[A-Za-z_.][A-Za-z0-9_.]*/
BASETY: "w" | "l" | "s" | "d" | "m" | "b" // add m for memory

%import common.WS_INLINE
%import common.NEWLINE
%import common.ESCAPED_STRING
%import common.SIGNED_INT
%ignore WS_INLINE
%ignore /#[^\n]*/
NL: NEWLINE+
"""
PARSER = lark.Lark(grammar, start="start", parser="lalr")

example = r"""
function $foo{ #(m %mem){
@entry(w %x, w %y, m %mem)
    %t =w bvadd %x, %y 
    %t2 =w bvadd %t, 42 
    ret %mem
@loop(m %mem, w %x)
    %t3 =w bvneg %x
    @entry(%t3)
}
"""
PARSER.parse(example)

basety = {
    "b" : smt.BoolSort(),
    "w" : smt.BitVecSort(32),
    "l" : smt.BitVecSort(64),
    "m" : smt.ArraySort(smt.BitVecSort(64), smt.BitVecSort(8)),
}

@lark.v_args(inline=True)
class FunctionTransformer(lark.Transformer):
    def __init__(self):
        self.labels : dict[str, smt.FuncDeclRef] = {}
        self.temps : dict[str, smt.ExprRef] = {}
        self.funcs : dict[str, smt.FuncDeclRef] = {}
    def get_temp(self, name : str):
        if name not in self.temps:
            raise Exception(f"Unknown temp {name}")
        return self.temps[name]
    def start(self, nl1, *funcs):
        return funcs[:-1] # nl
    def funcdef(self, name, _params, nl1, *blocks):
        #print("funcdef", blocks)
        return Function("entry",  {k : v for k,v in blocks})
    def block(self, label, params, nl1, insns, jmp, nl2):
        #print("block", label, "params", params, "insn", insns, "jm", jmp)
        return (label.value[1:], Block(params, insns + [jmp]))
    def BASETY(self, ty):
        return basety[ty.value]
    def param(self, ty, name):
        #print(name, name[1:])
        self.temps[name[1:]] = smt.Const(name[1:], ty)
        return smt.Const(name[1:], ty)
    def param_list(self, *params):
        return list(params)
    def operand(self, op):
        #print("operand", op)
        if isinstance(op, lark.Token):
            if op.type == "SIGNED_INT":
                return smt.BitVecVal(int(op.value), 32)
            elif op.type == "TEMP":
                #print(self.temps, op.value)
                return self.temps[op.value[1:]]
            elif op.type == "GLOBAL":
                return smt.Const(op.value[1:], smt.BitVecSort(64))
        else:
            raise Exception("Unknown operand type")
    def instrs(self, *instrs):
        return list(instrs)
    def instr(self, dest, ty, op, *operands):
        #print(operands)
        c = smt.Const(dest.value[1:], ty)
        #print(c)
        if op == "bvadd":
            expr = operands[0] + operands[1]
        elif op == "bvneg":
            expr = -operands[0]
        elif op == "bvsub":
            expr = operands[0] - operands[1]
        elif op == "bveq":
            return operands[0] == operands[1]
        else:
            raise Exception(f"Unknown op {op}")
        dname = dest.value[1:]
        if dname in self.temps:
            raise Exception(f"Reassignment to {dname}")
        self.temps[dname] = expr
        return expr
    def call_param_list(self, *params):
        return list(params)
    def call(self, label, params):
        #print("call", label, params, self.temps)
        f = smt.Function(label.value[1:], *[p.sort() for p in params], Bottom)
        return f(*params)
    def ret(self, v):
        return smt.Function("ret", v.sort(), Bottom)(self.temps[v.decl().name()])
    def ite(self, cond, call_true, call_false):
        return smt.If(cond, call_true, call_false)
    def NL(self, token):
        return None
    #def TEMP(self, name):
    #    #print(name)
    #    #return self.temps[name]


def parse(s : str):
    tree = PARSER.parse(s)
    builder = FunctionTransformer()
    return builder.transform(tree)


parse(example)[0]

sumn = r"""
function $sumn {
@entry(w %n)
    @loop(%n, 0)
@loop (w %i, w %acc)
    %acc1 =w bvadd %acc, %i
    %i1   =w bvsub %i, 1
    %c =b  bveq %i1, 0
    ite %c, @loop(%i1, %acc1), @done(%acc1)
@done(w %res)
    ret %res
}
"""
parse(sumn)[0].blocks["loop"]
```

# Correspondence

loop(e1,e2,e3) and loop expects e1

Do I need to use th

```python
%%file /tmp/myfun.s

.global myfun
.equ i, %rdi
.equ j, %rsi
.equ k, %rdx

loop:
    ret # todo
myfun:
    mov 1, i
    mov 1, j
    mov 0, k
    jmp loop
    nop



```

    Overwriting /tmp/myfun.s

```python
! gcc -c -o /tmp/myfun /tmp/myfun.s
```

```python
! objdump -d /tmp/myfun
```

    /tmp/myfun:     file format elf64-x86-64
    
    
    Disassembly of section .text:
    
    0000000000000000 <loop>:
       0: c3                    ret
    
    0000000000000001 <myfun>:
       1: 48 8b 3c 25 01 00 00  mov    0x1,%rdi
       8: 00 
       9: 48 8b 34 25 01 00 00  mov    0x1,%rsi
      10: 00 
      11: 48 8b 14 25 00 00 00  mov    0x0,%rdx
      18: 00 
      19: eb e5                 jmp    0 <loop>
      1b: 90                    nop

```python
import kdrag.contrib.pcode as pcode
ctx = pcode.BinaryContext("/tmp/myfun")

memstate0 = pcode.MemState.Const("memstate0")
memstate1 = ctx.execute_block(memstate0, ctx.loader.find_symbol("myfun").rebased_addr)

```

    Unexpected SP conflict





    [SimState(memstate=MemState((let ((a!1 (store64le (store64le (register memstate0)
                                      &RDI
                                      (select64le (ram memstate0) #x0000000000000001))
                           &RIP
                           #x0000000000400000)))
     (let ((a!2 (store64le (store64le a!1
                                      &RSI
                                      (select64le (ram memstate0) #x0000000000000001))
                           &RDX
                           (select64le (ram memstate0) #x0000000000000000))))
       (and (= CUR_RAM (ram memstate0)) (= CUR_REGFILE a!2))))), pc=(4194304, 0), path_cond=[])]

```python
class Contract():
    decl : smt.FuncDeclRef
    cut : Callable[list[smt.ExprRef],MemState], smt.BoolRef]
    #requires :  
    #asserts : 

loop_contract = lambda args, memstate: smt.And(args[0] == mem.state.register("rax"), args[1] == mem.state.register("rsi"), args[2] == mem.state.register("rdx"))

loop(i,j,k) == loop(memstate.register("rax"), memstate.register("rsi"), memstate.register("rdx"))

smt.Implies(smt.ForAll([i,j,j,mem], i == mem.register(loop_high(i,j,k) == loop_low(mem), myfun_low() == myfun_high())

my_fun_high = smt.If(,  loop_low(mem), )


def merge_states(states :  list[SimState]):
    for state in states:
        jmp = smt.Function("addr_" + str(state.addr), MemState, MemState)
        acc = smt.If(state.path_cond, jmp(state.mem), acc)
    return acc


```

```python
# predeclare all our blocks
myfun2 = smt.Function("myfun2", Z)
loop2 = smt.Function("loop2", Z,Z,Z, Z)
if_head2 = smt.Function("if_head2", Z,Z,Z, Z)
then2= smt.Function("then2", Z,Z,Z, Z)
else2_ = smt.Function("else_2", Z,Z,Z, Z)
done2 = smt.Function("done2", Z,Z,Z, Z)
i,j,k = smt.Ints("i j k")

myfun = kd.define("myfun2", [], loop(1,0))
loop = kd.define("loop2", [i,j,k], smt.If(k < 100, if_head(i,k), done(i,k)))
if_head = kd.define("if_head2", [i,j,k], then2(i,k))
then = kd.define("then2", [i,j,k], loop(i, k + 1))
done = kd.define("done2", [i,k], 1)
```

Reflection appears borken and unreliable. Maybe I should revisit.

```python
# Oh yead. This is all gonna be mutually recursive. Hmm

from kdrag.all import *
from kdrag.reflect import reflect

Z = smt.IntSort()
#myfun = smt.Function("myfun", Z)
loop = smt.Function("loop", Z,Z,Z, Z)
if_head = smt.Function("if_head", Z,Z,Z, Z)
then = smt.Function("then", Z,Z,Z, Z)
else_ = smt.Function("else_", Z,Z,Z, Z)
done = smt.Function("done", Z,Z,Z, Z)

@reflect
def myfun() -> int:
    return loop(1,1,0)

def loop(i : int,j : int,k : int) -> int: # orange block
    return if_head(i,j,k) if k < 100 else done(i,j,k)

def if_head(i,j,k): # red block
    return then(i,j,k) if j < 20 else else_(i,j,k)

def then(i,j,k):
    return loop(i, i, k + 1)

def else_(i,j,k):
    return loop(i, k, k + 2)

def done(i,j,k): # green block
    return j
```

```python
"""
SSA is Functional Programming by Andrew Appel
https://www.cs.princeton.edu/~appel/papers/ssafun.pdf

Functional programming and SSA can be put into close correspondence.
It is to some degree a matter of pretty printing.

The recipe is to define one function per block that takes in all the currently live variables as arguments.
These are also called "block arguments" and are a structural alternative to phi nodes.

SSA variables are then just references given to previous expressions.
A maximal `let` bound form can be written. https://en.wikipedia.org/wiki/A-normal_form

Jumps are calls to the other function blocks

"""

from dataclasses import dataclass, field
import kdrag as kd
import kdrag.smt as smt
from collections import defaultdict


def pp_sort(s: smt.SortRef) -> str:
    if isinstance(s, smt.BitVecSortRef):
        return f"bv{s.size()}"
    else:
        return str(s)


@dataclass
class Block:
    sig: list[smt.SortRef]
    insns: list[smt.ExprRef]

    @classmethod
    def of_defined_fun(cls, f: smt.FuncDeclRef) -> "Block":
        """
        >>> x, y = smt.Ints("x y")
        >>> f = kd.define("f809", [x,y], x + x + y)
        >>> Block.of_defined_fun(f)
        ^(Int,Int):
        %0 = + %var0, %var0
        %1 = + %0, %var1
        """
        defn = kd.kernel.defns.get(f)
        if defn is None:
            raise ValueError(f"Function {f} is not defined to knuckledragger")
        else:
            body = defn._subst_fun_body
            return cls.of_expr(body, sig=[f.domain(i) for i in range(f.arity())])

    @classmethod
    def of_expr(cls, e: smt.ExprRef, sig=[]) -> "Block":
        """
        >>> x,y = smt.BitVecs("x y", 64)
        >>> x,y = smt.Var(1, smt.BitVecSort(64)), smt.Var(0, smt.BitVecSort(64))
        >>> z = smt.BitVec("z", 64)
        >>> Block.of_expr(smt.If(True, (x + y)*42, x - y + z), [smt.BitVecSort(64), smt.BitVecSort(64)])
        ^(bv64,bv64):
        %0 = bvadd %var1, %var0
        %1 = bvmul %0, 42
        %2 = bvsub %var1, %var0
        %3 = bvadd %2, z
        %4 = if True, %1, %3
        """
        if not smt.is_if(e):
            insns = []
            seen = set()
            todo = [e]
        else:
            insns = [e]
            seen = set(e.children())
            todo = list(e.children())
        while todo:
            e = todo.pop()
            # if smt.is_const(e) and not kd.utils.is_value(e):
            #    args.append(e)
            if smt.is_var(e):
                pass
            elif smt.is_const(e):
                continue
            else:
                insns.append(e)
                for arg in e.children():
                    if arg not in seen:
                        seen.add(arg)
                        todo.append(arg)
        insns.reverse()
        return cls(sig=sig, insns=insns)

    def vname(self, e: smt.ExprRef) -> str:
        # if any(e.eq(v) for v in self.args):
        #    return str(e)
        if smt.is_var(e):
            return f"%var{smt.get_var_index(e)}"
        elif smt.is_const(e):
            return str(e)
        else:
            for i, insn in enumerate(self.insns):
                if e.eq(insn):
                    return f"%{i}"
            else:
                raise ValueError(f"Value {e} not found in block")

    def __repr__(self) -> str:
        # res = [f"^({",".join(str(arg) for arg in self.args)})"]
        res = [f"^({','.join(pp_sort(s) for s in self.sig)}):"]
        for i, insn in enumerate(self.insns):
            if isinstance(insn, smt.BitVecRef) and smt.is_bv_value(insn):
                rhs = str(insn) + f":{insn.size()}"
            elif kd.utils.is_value(insn):
                rhs = str(insn)
            else:
                rhs = f"{insn.decl().name()} {", ".join(self.vname(arg) for arg in insn.children())}"
            res.append(f"\t%{i} = {rhs}")
        return "\n".join(res)

    def succ_calls(self) -> list[smt.ExprRef]:
        jmp = self.insns[-1]
        if smt.is_if(jmp):
            return jmp.children()
        else:
            return [jmp]


type Label = str


@dataclass
class Function:
    """ """

    entry: Label  # smt.FuncDeclRef?
    blocks: dict[Label, Block]  # 0th block is entry. Or "entry" is entry? Naw. 0th.

    @classmethod
    def of_defined_funs(cls, funs: list[smt.FuncDeclRef]):
        blocks = {f.name(): Block.of_defined_fun(f) for f in funs}
        entry = funs[0].name()
        return cls(entry=entry, blocks=blocks)

    def calls_of(self) -> dict[str, list[tuple[Label, smt.ExprRef]]]:
        """
        Returns a mapping from labels to a list of calls to that label
        """
        p = defaultdict(list)
        for label, blk in self.blocks.items():
            for call in blk.succ_calls():
                p[call.decl().name()].append((label, call))
        return p

    def phis(self):
        """
        Return the analog a mapping from labels to phi nodes in that block
        """

        preds = self.calls_of()
        phis = {}
        for label, blk in self.blocks.items():
            phis[label] = zip(*[call.children() for _, call in preds[label]])
        return phis

    def __repr__(self) -> str:
        res = [f"fn {self.entry} {{"]
        for label, blk in self.blocks.items():
            res.append(f"@{label}:")
            res.append(str(blk))
        res.append("}")
        return "\n".join(res)


@dataclass
class Spec:
    pre: dict[str, smt.BoolRef] = field(default_factory=dict)
    post: dict[str, smt.BoolRef] = field(default_factory=dict)
    cut: dict[str, smt.BoolRef] = field(default_factory=dict)


# def sym_exec():

Bottom = smt.DeclareSort("Bottom")
ret64 = smt.Function("ret64", smt.BitVecSort(64), Bottom)

```
