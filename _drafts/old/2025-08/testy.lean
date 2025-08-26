@[extern "myadd"]
opaque myadd (a b : UInt64) : UInt64


def myadd2 (a b : UInt64) : UInt64 := a + b

-- @[extern cpp inline "#1 + #2"]
-- opaque myadd3 (a b : UInt64) : UInt64
