use std::cmp::Ordering;
use std::collections::VecDeque;
use std::fmt;
use std::time::Instant;

/// Graded lexicographic order used for monomials and polynomials.
fn lenlex<T: Ord>(xs: &[T], ys: &[T]) -> Ordering {
    xs.len().cmp(&ys.len()).then_with(|| xs.cmp(ys))
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Monom(Vec<u32>);

impl Ord for Monom {
    fn cmp(&self, other: &Self) -> Ordering {
        lenlex(&self.0, &other.0)
    }
}

impl PartialOrd for Monom {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Monom {
    /// Multiset union of variables.
    fn mul(&self, other: &Self) -> Self {
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::with_capacity(self.0.len() + other.0.len());
        while i < self.0.len() && j < other.0.len() {
            if self.0[i] <= other.0[j] {
                out.push(self.0[i]);
                i += 1;
            } else {
                out.push(other.0[j]);
                j += 1;
            }
        }
        out.extend_from_slice(&self.0[i..]);
        out.extend_from_slice(&other.0[j..]);
        Self(out)
    }

    /// Remove `other` as a submultiset.
    fn div(&self, other: &Self) -> Option<Self> {
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::with_capacity(self.0.len() - other.0.len().min(self.0.len()));
        while i < self.0.len() {
            if j < other.0.len() && self.0[i] == other.0[j] {
                i += 1;
                j += 1;
            } else if j < other.0.len() && self.0[i] > other.0[j] {
                return None;
            } else {
                out.push(self.0[i]);
                i += 1;
            }
        }
        (j == other.0.len()).then_some(Self(out))
    }

    /// Componentwise maximum of variable multiplicities.
    fn lcm(&self, other: &Self) -> Self {
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::with_capacity(self.0.len() + other.0.len());
        while i < self.0.len() || j < other.0.len() {
            let x = match (self.0.get(i), other.0.get(j)) {
                (Some(&x), Some(&y)) => x.min(y),
                (Some(&x), None) => x,
                (None, Some(&y)) => y,
                (None, None) => unreachable!(),
            };
            let i0 = i;
            let j0 = j;
            while self.0.get(i) == Some(&x) {
                i += 1;
            }
            while other.0.get(j) == Some(&x) {
                j += 1;
            }
            out.extend(std::iter::repeat_n(x, (i - i0).max(j - j0)));
        }
        Self(out)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Semi(Vec<Monom>);

type QR = (Semi, Semi);
type Overlap = (QR, QR);

impl Ord for Semi {
    fn cmp(&self, other: &Self) -> Ordering {
        lenlex(&self.0, &other.0)
    }
}

impl PartialOrd for Semi {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Semi {
    /// Build a polynomial in canonical sorted form.
    fn new(mut monoms: Vec<Monom>) -> Self {
        monoms.sort_unstable();
        Self(monoms)
    }

    /// Embed a generator.
    fn lit(x: u32) -> Self {
        Self(vec![Monom(vec![x])])
    }

    /// Embed a natural number as repeated empty monomials.
    fn of_int(n: usize) -> Self {
        Self(vec![Monom(Vec::new()); n])
    }

    /// Merge the two sorted multisets of monomials.
    fn add(&self, other: &Self) -> Self {
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::with_capacity(self.0.len() + other.0.len());
        while i < self.0.len() && j < other.0.len() {
            if self.0[i] <= other.0[j] {
                out.push(self.0[i].clone());
                i += 1;
            } else {
                out.push(other.0[j].clone());
                j += 1;
            }
        }
        out.extend_from_slice(&self.0[i..]);
        out.extend_from_slice(&other.0[j..]);
        Self(out)
    }

    /// Distributive product of every pair of monomials.
    fn mul(&self, other: &Self) -> Self {
        let mut out = Vec::with_capacity(self.0.len() * other.0.len());
        for m in &self.0 {
            for n in &other.0 {
                out.push(m.mul(n));
            }
        }
        Self::new(out)
    }

    /// Multiply by one monomial and a natural coefficient.
    fn shift_scale(&self, q: &Monom, coeff: usize) -> Self {
        let mut out = Vec::with_capacity(self.0.len() * coeff);
        for m in &self.0 {
            let mq = m.mul(q);
            out.extend(std::iter::repeat_n(mq, coeff));
        }
        Self::new(out)
    }

    /// Natural subtraction, failing if `other` is not contained.
    fn sub(&self, other: &Self) -> Option<Self> {
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::with_capacity(self.0.len().saturating_sub(other.0.len()));
        while j < other.0.len() {
            while i < self.0.len() && self.0[i] < other.0[j] {
                out.push(self.0[i].clone());
                i += 1;
            }
            if i == self.0.len() || self.0[i] != other.0[j] {
                return None;
            }
            i += 1;
            j += 1;
        }
        out.extend_from_slice(&self.0[i..]);
        Some(Self(out))
    }

    /// Coefficientwise maximum of two polynomials.
    fn union_max(&self, other: &Self) -> Self {
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::with_capacity(self.0.len().max(other.0.len()));
        while i < self.0.len() || j < other.0.len() {
            match (self.0.get(i), other.0.get(j)) {
                (Some(m), Some(n)) if m == n => {
                    let (i0, j0) = (i, j);
                    while self.0.get(i) == Some(m) {
                        i += 1;
                    }
                    while other.0.get(j) == Some(n) {
                        j += 1;
                    }
                    out.extend(std::iter::repeat_n(m.clone(), (i - i0).max(j - j0)));
                }
                (Some(m), Some(n)) if m < n => {
                    out.push(m.clone());
                    i += 1;
                }
                (Some(_), Some(n)) => {
                    out.push(n.clone());
                    j += 1;
                }
                (Some(m), None) => {
                    out.push(m.clone());
                    i += 1;
                }
                (None, Some(n)) => {
                    out.push(n.clone());
                    j += 1;
                }
                (None, None) => break,
            }
        }
        Self(out)
    }

    /// Greedily find `q, r` with `self = q * other + r`.
    fn divrem(&self, other: &Self) -> (Self, Self) {
        assert!(!other.0.is_empty(), "division by zero");
        let mut q = Vec::new();
        let mut r = self.clone();
        let lm = other.0.last().unwrap();
        let mut i = r.0.len();
        while i > 0 {
            let Some(qm) = r.0[i - 1].div(lm) else {
                i -= 1;
                continue;
            };
            let term = other.shift_scale(&qm, 1);
            if let Some(r1) = r.sub(&term) {
                q.push(qm);
                r = r1;
                i = r.0.len();
            } else {
                i -= 1;
            }
        }
        (Self::new(q), r)
    }

    /// Return both `(quotient, remainder)` views of each nontrivial overlap.
    fn overlaps_qr(&self, other: &Self) -> Vec<Overlap> {
        let mut res = Vec::new();
        let mut seen = Vec::new();
        let mut i = 0;
        while i < self.0.len() {
            let mut i1 = i + 1;
            while i1 < self.0.len() && self.0[i1] == self.0[i] {
                i1 += 1;
            }
            let c1 = i1 - i;
            let mut j = 0;
            while j < other.0.len() {
                let mut j1 = j + 1;
                while j1 < other.0.len() && other.0[j1] == other.0[j] {
                    j1 += 1;
                }
                let c2 = j1 - j;
                let cm = self.0[i].lcm(&other.0[j]);
                let qm1 = cm.div(&self.0[i]).unwrap();
                let qm2 = cm.div(&other.0[j]).unwrap();
                let c = lcm(c1, c2);
                let q1 = Self(vec![qm1.clone(); c / c1]);
                let q2 = Self(vec![qm2.clone(); c / c2]);
                let t1 = self.shift_scale(&qm1, c / c1);
                let t2 = other.shift_scale(&qm2, c / c2);
                let ov = t1.union_max(&t2);
                if !seen.contains(&ov) {
                    seen.push(ov.clone());
                    res.push(((q1, ov.sub(&t1).unwrap()), (q2, ov.sub(&t2).unwrap())));
                }
                j = j1;
            }
            i = i1;
        }
        res
    }
}

impl fmt::Display for Semi {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            return write!(f, "0");
        }
        let mut i = 0;
        while i < self.0.len() {
            if i != 0 {
                write!(f, " + ")?;
            }
            let mut i1 = i + 1;
            while i1 < self.0.len() && self.0[i1] == self.0[i] {
                i1 += 1;
            }
            if i1 - i != 1 {
                write!(f, "{}*", i1 - i)?;
            }
            let m = &self.0[i].0;
            if m.is_empty() {
                write!(f, "1")?;
            } else {
                let mut j = 0;
                while j < m.len() {
                    let mut j1 = j + 1;
                    while j1 < m.len() && m[j1] == m[j] {
                        j1 += 1;
                    }
                    let x = char::from_u32(u32::from(b'a') + m[j]).unwrap_or('?');
                    write!(f, "{x}")?;
                    if j1 - j != 1 {
                        write!(f, "^{}", j1 - j)?;
                    }
                    j = j1;
                }
            }
            i = i1;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Rule {
    lhs: Semi,
    rhs: Semi,
    marked: bool,
}

impl Rule {
    /// Orient an equation from larger to smaller.
    fn new(mut lhs: Semi, mut rhs: Semi) -> Self {
        if lhs < rhs {
            std::mem::swap(&mut lhs, &mut rhs);
        }
        Self {
            lhs,
            rhs,
            marked: false,
        }
    }
}

/// Reduce to normal form, optionally followed by some extra rules.
fn reduce_with(mut semi: Semi, rewrites: &[Rule], extra: &[Rule]) -> Semi {
    'again: loop {
        for rw in rewrites.iter().chain(extra) {
            let (q, r) = semi.divrem(&rw.lhs);
            let res = q.mul(&rw.rhs).add(&r);
            if res != semi {
                semi = res;
                continue 'again;
            }
        }
        return semi;
    }
}

fn reduce(semi: Semi, rewrites: &[Rule]) -> Semi {
    reduce_with(semi, rewrites, &[])
}

/// Normalize all critical pairs between two rules.
fn critical_pairs<'a>(
    rw: &'a Rule,
    rw1: &'a Rule,
    rules: &'a [Rule],
) -> impl Iterator<Item = Rule> + 'a {
    rw.lhs
        .overlaps_qr(&rw1.lhs)
        .into_iter()
        .filter_map(move |((q, r), (q1, r1))| {
            let lhs = reduce(q.mul(&rw.rhs).add(&r), rules);
            let rhs = reduce(q1.mul(&rw1.rhs).add(&r1), rules);
            (lhs != rhs).then(|| Rule::new(lhs, rhs))
        })
}

fn gcd(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn lcm(a: usize, b: usize) -> usize {
    a / gcd(a, b) * b
}

/// Basic completion with a FIFO equation queue.
fn naive_complete(eqs: Vec<Rule>) -> (Vec<Rule>, usize) {
    let mut pending: VecDeque<_> = eqs.into();
    let mut rws = Vec::new();
    let mut popped = 0;
    while let Some(eq) = pending.pop_front() {
        popped += 1;
        let lhs = reduce(eq.lhs, &rws);
        let rhs = reduce(eq.rhs, &rws);
        if lhs == rhs {
            continue;
        }
        let rw = Rule::new(lhs, rhs);
        if rws.contains(&rw) {
            continue;
        }
        let new = rws.len();
        rws.push(rw);
        for old in 0..=new {
            for eq in critical_pairs(&rws[new], &rws[old], &rws) {
                if !pending.contains(&eq) {
                    pending.push_back(eq);
                }
            }
        }
    }
    (rws, popped)
}

/// Huet completion: collapse left sides and compose right sides.
fn huet_complete(mut eqs: Vec<Rule>) -> Vec<Rule> {
    let mut rws = Vec::new();
    loop {
        while let Some(eq) = eqs.pop() {
            let lhs = reduce(eq.lhs, &rws);
            let rhs = reduce(eq.rhs, &rws);
            if lhs == rhs {
                continue;
            }
            let rw = Rule::new(lhs, rhs);

            let mut rws1 = vec![rw.clone()];
            for rw1 in &rws {
                let lhs1 = reduce(rw1.lhs.clone(), std::slice::from_ref(&rw));
                if lhs1 == rw1.lhs {
                    let rhs1 = reduce_with(rw1.rhs.clone(), &rws, std::slice::from_ref(&rw));
                    if rw1.lhs != rhs1 {
                        rws1.push(Rule::new(rw1.lhs.clone(), rhs1));
                    }
                } else {
                    eqs.push(Rule::new(lhs1, rw1.rhs.clone()));
                }
            }
            rws = rws1;
        }

        for i in 0..rws.len() {
            for j in 0..=i {
                for eq in critical_pairs(&rws[i], &rws[j], &rws) {
                    if !eqs.contains(&eq) {
                        eqs.push(eq);
                    }
                }
            }
        }
        if eqs.is_empty() {
            return rws;
        }
    }
}

/// Huet completion, pairing each rule only after it becomes unmarked.
fn huet_marked(mut eqs: Vec<Rule>) -> Vec<Rule> {
    let mut rws: Vec<Rule> = Vec::new();
    loop {
        while let Some(eq) = eqs.pop() {
            let lhs = reduce(eq.lhs, &rws);
            let rhs = reduce(eq.rhs, &rws);
            if lhs == rhs {
                continue;
            }
            let rw = Rule::new(lhs, rhs);

            let mut rws1 = vec![rw.clone()];
            for rw1 in &rws {
                let lhs1 = reduce(rw1.lhs.clone(), std::slice::from_ref(&rw));
                if lhs1 == rw1.lhs {
                    let rhs1 = reduce_with(rw1.rhs.clone(), &rws, std::slice::from_ref(&rw));
                    if rw1.lhs != rhs1 {
                        let mut rw2 = Rule::new(rw1.lhs.clone(), rhs1);
                        rw2.marked = rw1.marked;
                        rws1.push(rw2);
                    }
                } else {
                    eqs.push(Rule::new(lhs1, rw1.rhs.clone()));
                }
            }
            rws = rws1;
        }

        let Some(i) = rws.iter().position(|rw| !rw.marked) else {
            return rws;
        };
        let rw = rws[i].clone();
        rws[i].marked = true;

        for rw1 in &rws {
            for eq in critical_pairs(&rw, rw1, &rws) {
                if !eqs.contains(&eq) {
                    eqs.push(eq);
                }
            }
        }
    }
}

/// Assert Buchberger's criterion for the finished system.
fn check_complete(rules: &[Rule]) {
    for rw in rules {
        for rw1 in rules {
            assert!(critical_pairs(rw, rw1, rules).next().is_none());
        }
    }
}

fn main() {
    let a = Semi::lit(0);
    let one = Semi::of_int(1);
    let seed = Rule::new(one.add(&a.mul(&a)), a);

    let start = Instant::now();
    let (naive, popped) = naive_complete(vec![seed.clone()]);
    println!(
        "naive: {} rules, {popped} equations in {:?}",
        naive.len(),
        start.elapsed()
    );

    let start = Instant::now();
    let rules = huet_complete(vec![seed.clone()]);
    println!("Huet: {} rules in {:?}", rules.len(), start.elapsed());
    for rw in &rules {
        println!("{} -> {}", rw.lhs, rw.rhs);
    }

    let start = Instant::now();
    let marked = huet_marked(vec![seed]);
    println!(
        "Huet marked: {} rules in {:?}",
        marked.len(),
        start.elapsed()
    );

    let start = Instant::now();
    check_complete(&naive);
    check_complete(&rules);
    check_complete(&marked);
    println!("all systems complete ({:?})", start.elapsed());

    assert_eq!(Semi::of_int(0).add(&Semi::of_int(2)), Semi::of_int(2));
}
