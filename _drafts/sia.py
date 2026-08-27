from ikdrag import *

Type = Decl("type", 0)()


def Sort(name):
    decl = Decl(name, 0)
    S = decl()
    contracts[decl] = axiom(Type(S))  # Foo Type judgement kind of
    return S


Real = Sort("real")
Set = Sort("set")
Arr = Decl("arr", 2)  # Function("arr", Type, Type, Type)

x, y, z = Vars("X Y Z", Real)
A, B, C = Vars("A B C", Set)

zero, one = Consts("d0 d1", Real)

a, b, c = Vars("A B C", Real)
_a, _b, _c = Vars("A B C")

add_zero = axiom(ForAll([a], zero + a == a))
add_neg = axiom(ForAll([a], a + (Neg(a)) == zero))
add_comm = axiom(ForAll([_a, _b], _a + _b == _b + _a))  # unguarded comm worth it?
add_assoc = axiom(ForAll([_a, _b, _c], (_a + _b) + _c == _a + (_b + _c)))

add_real = axiom(ForAll([a, b], Real(a + b)))
contracts[Add] = add_real

inv = Function("inv", Real, Real)
inv_real = axiom(ForAll([a], Real(inv(a))))
contracts[inv] = inv_real

mul_zero = axiom(ForAll([a], zero * a == zero))
mul_one = axiom(ForAll([a], one * a == a))
mul_comm = axiom(ForAll([_a, _b], _a * _b == _b * _a))
mul_assoc = axiom(ForAll([_a, _b, _c], (_a * _b) * _c == _a * (_b * _c)))
mul_add = axiom(ForAll([a, b, c], a * (b + c) == (a * b) + (a * c)))
mul_inv = axiom(ForAll([a], a != zero, a * inv(a) == one))
mul_inv

mul_real = axiom(ForAll([a, b], Real(a * b)))
contracts[Mul] = mul_real

# pg 19
lt_trans = axiom(ForAll([a, b, c], a < b, b < c, a < c))
lt_irrefl = axiom(ForAll([a], Not(a < a)))
add_lt_mono = axiom(ForAll([a, b, c], a < b, a + c < b + c))
mul_lt_mono = axiom(ForAll([a, b, c], a < b, zero < c, a * c < b * c))
lt_dich = axiom(
    ForAll([a], Or(zero < a, a < one))
)  # yea I dunno what to call this principle.
distinct_lt = axiom(ForAll([a, b], a != b, Or(a < b, b < a)))


le_defn = axiom(ForAll([a, b], Iff(LE(a, b), Not(b < a))))
sub_defn = axiom(ForAll([a, b], a - b == a + Neg(b)))


a, b, c = Vars("A B C", Real)
add_lt_mono_left = prove(
    ForAll([a, b, c], a < b, c + a < c + b), by=[add_lt_mono, add_comm]
)
mul_lt_mono_left = prove(
    ForAll([a, b, c], a < b, zero < c, c * a < c * b), by=[mul_lt_mono, mul_comm]
)

add_zero_right = prove(ForAll([a], a + zero == a), by=[add_zero, add_comm])

# lt_zero_one = prove(ForAll([a], zero < one), by=[l])
neq_zero_one = prove(zero != one, by=[lt_dich, lt_irrefl])
lt_zero_one = prove(
    zero < one,
    by=[
        lt_dich,
        lt_irrefl,
        zero.decl.contract,
    ],
)
lt_one_two = prove(
    one < one + one, by=[lt_zero_one, add_lt_mono, zero.decl.contract, add_zero]
)

lt_one_two = (
    Theorem(one < one + one)
    .have(zero < one, by=[lt_zero_one])
    .have(zero + one < one + one, by=[add_lt_mono])
    .have(one < one + one, by=[add_zero])
    .qed(solver="nanocopi")
)

lt_zero_two = prove(zero < one + one, by=[lt_zero_one, lt_one_two, lt_trans])


def inf(x):
    return x * x == zero


z1 = Var("Z")
inf = Decl("inf", 1)
inf_defn = axiom(ForAll([z1], Iff(inf(z1), And(Real(z1), z1 * z1 == zero))))
# inf = define("inf", [z1], And(Real(z1), z1 * z1 == zero))
contracts[inf] = inf_defn  # immediate unfolding

lt_ne = prove(ForAll([a, b], a < b, a != b), by=[lt_irrefl])

eps = Vars("Eps", inf)[0]


inf_lt = (
    Theorem(ForAll([eps], Not(zero < eps)))
    .fixes(eps)
    .assumes(zero < eps)
    .have(eps * eps == zero)
    .have(zero * eps < eps * eps, by=[mul_lt_mono])
    .have(zero < eps * eps, by=[mul_zero])
    .have(zero != eps * eps, by=[lt_ne])
    .qed()
)


real_neg = axiom(ForAll([a], Real(a), Real(-a)))
contracts[Neg] = real_neg


lt_neg = (
    Theorem(ForAll([a, b], a < b, -b < -a))
    .fixes(a, b)
    .assumes(a < b)
    .have(a + (-a) < b + (-a), by=[add_lt_mono])
    .have(zero < b + (-a), by=[add_neg])
    .have(zero + (-b) < b + (-a) + (-b), by=[add_lt_mono])
    .have(-b < (b + (-a)) + (-b), by=[add_zero])
    .have(-b < zero + -a, by=[add_neg, add_assoc, add_neg, add_comm])
    .have(-b < -a, by=[add_zero])
    .qed()
)
lt_neg


# mul_lt_mono_neg = prove(
#    ForAll([a, b, c], a < b, c < zero, c * b < c * a), by=[mul_lt_mono, mul_comm, lt_irrefl]
# )


def search(env, decl=None):
    return {
        k: v
        for k, v in env.items()
        if isinstance(v, Proof) and (decl is None or decl in v.thm.decls())
    }


from pprint import pprint

mul_zero_right = prove(ForAll([a], a * zero == zero), by=[mul_zero, mul_comm])
mul_add_distrib_right = prove(
    ForAll([a, b, c], (a + b) * c == a * c + b * c), by=[mul_add, mul_comm]
)

mul_neg_left = (
    Theorem(ForAll([a, b], (-a) * b == -(a * b)))
    .fixes(a, b)
    .have(zero == (a + (-a)) * b, by=[add_neg, add_zero, mul_zero])
    .have(zero == a * b + (-a) * b, by=[mul_add_distrib_right])
    .have(zero + -(a * b) == a * b + (-a) * b + -(a * b), by=[add_neg, add_assoc])
    .have(-(a * b) == a * b + (-a) * b + -(a * b), by=[add_zero])
    .have(-(a * b) == (-a) * b + (a * b + -(a * b)), by=[add_assoc, add_comm])
    .have(-(a * b) == (-a) * b + zero, by=[add_neg, add_zero])
    .have((-(a * b)) == (-a) * b, by=[add_zero_right])
    .qed()
)
# add_zero
# str(zero + -(a * b) == -(a * b))
# pprint(search(locals(), Add))


# .have(a * (Neg(b)) == a * b + Neg(a * b), by=[mul_add, mul_neg])
# .have(a * b + Neg(a * b) == Neg(a * b), by=[add_neg])
# .have(a * (-(b)) == Neg(a * b), by=[add_assoc, add_comm, add_zero])
# .qed())


neg_zero = prove(-zero == zero, by=[add_neg, add_zero])

neg_neg = prove(
    ForAll([a], -(-a) == a), by=[neg_zero, add_neg, add_assoc, add_comm, add_zero]
)
mul_lt_neg = (
    Theorem(ForAll([a, b, c], a < b, c < zero, b * c < a * c))
    .fixes(a, b, c)
    .assumes(a < b)
    .assumes(c < zero)
    .have(zero < -c, by=[lt_neg, neg_zero])
    .have(a * (-c) < b * (-c), by=[mul_lt_mono])
    .have(-(a * c) < -(b * c), by=[mul_neg_left, mul_comm])
    .have(-(-(b * c)) < -(-(a * c)), by=[lt_neg])
    .have(b * c < a * c, by=[neg_neg])
    .qed()
)
# mul_lt_mono


lt_eps_zero = (
    Theorem(ForAll([eps], Not(eps < zero)))
    .fixes(eps)
    .assumes(eps < zero)
    .have(eps * eps == zero)
    .have(zero * eps < eps * eps, by=[mul_lt_neg])
    .have(zero < eps * eps, by=[mul_zero])
    .have(zero != zero, by=[lt_ne])
    .qed()
)


inf_mul_eps = (
    Theorem(ForAll([eps, a], (eps * a) * (eps * a) == zero))
    .fixes(eps, a)
    .have(eps * eps == zero)
    .have((eps * a) * (eps * a) == (eps * eps) * (a * a), by=[mul_assoc, mul_comm])
    .have((eps * eps) * (a * a) == zero, by=[mul_zero])
    .qed()
)

p = Theorem(ForAll([eps, a], zero < a, zero < a + eps)).fixes(eps, a).assumes(zero < a)


two = define("two", [], one + one)()
contracts[two.decl] = prove(
    Real(two), by=[two.decl.defn, add_real, contracts[one.decl]]
)

two_pos = (
    Theorem(
        zero < two
    )  # , by=[lt_zero_one, add_lt_mono, two.decl.defn, zero.decl.contract, add_zero, lt_trans])
    .have(zero < one, by=[lt_zero_one])
    .have(zero + one < one + one, by=[add_lt_mono])
    .have(one < one + one, by=[add_zero])
    .have(zero < two, by=[two.defn, zero.contract, lt_trans])
    .qed()
    # .qed(by=[two.decl.defn])
)

mul_one_right = prove(ForAll([a], a * one == a), by=[mul_comm, mul_one])

add_half = (
    Theorem(ForAll([a], a * inv(two) + a * inv(two) == a))
    .fixes(a)
    .have(zero < two, by=[two_pos])
    .have(zero != two, by=[lt_ne])
    .have(two * inv(two) == one, by=[mul_inv])
    .have((two * inv(two)) * a == one * a, by=[])
    .have((two * inv(two)) * a == a, by=[mul_assoc, mul_one])
    .have(two * (a * inv(two)) == a, by=[mul_comm, mul_assoc])
    .have(two * (a * inv(two)) == a, by=[mul_inv, mul_comm, mul_assoc, mul_one])
    .have((one + one) * (a * inv(two)) == a, by=[two.defn])
    .have(a * inv(two) + a * inv(two) == a, by=[mul_add_distrib_right, mul_one])
    .qed()
    # .have(two * (a * inv(two)) == a, by=[mul_inv, mul_comm, mul_assoc, mul_one])
)

# prove(ForAll([a], a * inv(two) + a * inv(two) == a), by=[mul_inv, mul_comm, mul_assoc, mul_one, two.decl.defn, contracts[one.decl], mul_add_distrib_right, mul_one])
