// https://www.cs.utexas.edu/users/flame/laff/p4c/Notes/LAFFPfC.pdf


lemma Comm_and(p : bool, q :bool) ensures (p && q) == (q && p) {}  //&& p
lemma Comm_or(p : bool, q :bool) ensures (p || q) == (q || p) {}
lemma Impl_proj(p : bool, q :bool) ensures (p && q) ==> p {}


function mysum(n : nat) : nat {
  if n == 0 then
    0
  else
    (n + mysum(n - 1))

}

lemma mysum_closed(n: nat) ensures mysum(n) == (n + 1) * n / 2  {
  // None of this was necessary, but I wanted to be very explicit
  if n == 0 {
    calc {
       mysum(0);
    == 0;
    == (0 + 1) * 0 / 2;
    }
  } else {
    mysum_closed(n-1);
    calc {
       mysum(n);
    == n + mysum(n-1);
    == n + ((n- 1 + 1) * (n - 1)) / 2;
    == n + n * (n - 1) / 2;
    == n * (n + 1) / 2;
    }

  }
}


datatype Vec3 = V3(x:real, y:real, z:real)

function add(a : Vec3, b : Vec3) {
    a.x * b.y + a.y + b.y + a.z * b.z
}

