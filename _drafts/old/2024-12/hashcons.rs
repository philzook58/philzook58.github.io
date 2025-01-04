//! ```cargo
//! [dependencies]
//! hash_cons ="0.2.0"
//! ```
use hash_cons::{HcTable, Hc};

// https://docs.rs/hash_cons/latest/hash_cons/
/// A simple boolean expression
#[derive(Hash, PartialEq, Eq, Debug)]
enum BoolExpr {
    Const(bool),
    And(Hc<BoolExpr>, Hc<BoolExpr>),
    Or(Hc<BoolExpr>, Hc<BoolExpr>),
    Not(Hc<BoolExpr>),
}

// Hashlog



fn main(){
    let table: HcTable<BoolExpr> = HcTable::new();
    let const_true = BoolExpr::Const(true);
    let hc_true: Hc<BoolExpr> = table.hashcons(const_true);
    let and1 = table.hashcons(BoolExpr::And(hc_true.clone(), hc_true.clone()));
    let and2 = table.hashcons(BoolExpr::And(hc_true.clone(), hc_true));
    println!("Hello, world! {:?} {} {}", and1, table.len(), and2 == and1);
    if let BoolExpr::And(BoolExpr::Const(true), b) = and1.as_ref() {
        println!(" b: {:?}", b);
    }
}